-- Copyright (C) 2026 BeamMP Ltd., BeamMP team and contributors.
-- Licensed under AGPL-3.0 (or later), see <https://www.gnu.org/licenses/>.
-- SPDX-License-Identifier: AGPL-3.0-or-later

--- MPProxyMeshGE API - real body meshes for proxy vehicles (see MPProxyGE).
-- A TSStatic renders every mesh of its shape file and has no per mesh visibility (engine fields: shapeName, skin,
-- dynamic, meshCulling, useInstanceRenderData, instanceColor0-2, forceDetail ...), and vehicle .dae files contain
-- every part variant of the model, without LODs. So per model + config we build a small filtered .dae:
--   1. part -> flexbody mesh index of the model (jbeam files of /vehicles/<model>/ only, one file per step)
--   2. wanted meshes = flexbodies of the parts in the config, minus interior/small/mechanical parts,
--      minus anything from /vehicles/common (wheels and tires are drawn as cylinders instead)
--   3. the model's .dae files are streamed in chunks and only the wanted <geometry>/<node> blocks are kept
--   4. the result is written to /temp/beammp/proxymeshes/ and reused for every proxy with the same mesh set
--      (also across sessions). Vehicle meshes are modelled in place in vehicle space, so no transforms are needed.
-- All of that runs in a coroutine with a per frame time budget. The only blocking step left is the engine
-- importing the small generated shape on its first use, which is rate limited (one new shape per interval).
-- Until a shape is ready the proxy stays a box.
-- @module MPProxyMeshGE

local M = {}

setmetatable(_G,{}) -- temporarily disable global notifications

local TIMER = (HighPerfTimer or hptimer)
local CACHE_DIR = "/temp/beammp/proxymeshes/"
local CACHE_VERSION = "v3" -- v3: one merged .dae per mesh set, source signature validation
local READ_CHUNK = 256 * 1024     -- bytes per read step (smaller steps keep each resume near the frame budget)
local FRAME_BUDGET_MS = 2         -- coroutine work per frame in game
local PRELOAD_BUDGET_MS = 40      -- while the join loading screen hides the stutter
local frameBudget = FRAME_BUDGET_MS
local MAX_MESHES = 60             -- per config
local MAX_NEW_OBJECTS_PER_PASS = 4
local NEW_SHAPE_INTERVAL = 2      -- seconds between first uses of not yet loaded shapes (engine import hitch)
local RELEASE_MARGIN = 50

local cfg = { enabled = true, distance = 500, maxProxies = 48, wheels = true }

local function readSettings()
	cfg.enabled = settings.getValue("proxyMeshEnabled", true) ~= false
	cfg.distance = tonumber(settings.getValue("proxyMeshDistance", 500)) or 500
	cfg.maxProxies = math.max(0, math.floor(tonumber(settings.getValue("proxyMaxMeshProxies", 48)) or 48))
	cfg.wheels = settings.getValue("proxyMeshWheels", true) ~= false
end

-- mesh names containing any of these are skipped (interior, mechanical, small or hidden parts)
local SKIP = {
	"_int", "interior", "dash", "gauge", "needle", "pedal", "seat", "steer", "shifter", "handbrake", "switch",
	"engine", "header", "intake", "radhose", "radiator", "exhaust", "muffler", "heatshield", "subframe", "suspension",
	"strut", "coilover", "spring", "shock", "brake", "rotor", "caliper", "hub", "axle", "driveshaft", "halfshaft",
	"diff", "transmission", "gearbox", "transfercase", "battery", "rollcage", "cage", "belt", "pulley", "fan",
	"alternator", "turbo", "supercharger", "intercooler", "fuel", "tank", "pipe", "hose", "wire", "bolt", "screw",
	"mount", "bracket", "carpet", "headliner", "doorpanel", "crap", "skidplate", "underbody", "tie", "lowerarm",
	"upperarm", "controlarm", "leaf", "linkage", "rack", "pump", "filter", "airbox", "wiper", "antenna", "decal",
	"license", "plate", "badge", "emblem", "mudflap", "net", "speaker", "radio", "cluster", "glovebox", "console",
}

local function isWantedMesh(name)
	local n = string.lower(name)
	for i = 1, #SKIP do
		if string.find(n, SKIP[i], 1, true) then return false end
	end
	return true
end

-- ============= STATE =============
local partIndex = {}      -- [model] = { [partName] = {meshName, ...} } | "building"
local shapes = {}         -- [key] = { state = "queued"|"building"|"ready"|"failed", paths = {}, bbox = {}, loaded = false }
local materialsLoaded = {} -- [model] = true
local jobs = {}           -- FIFO of { key, model, parts }
local currentJob = nil
local importedPaths = {}  -- [dae path] = true once a TSStatic used it this session (engine keeps the shape loaded)
local waitingLoad = {}    -- models with a ready shape waiting for the first-use interval (overlay)
local clock = 0
local nextNewShapeAllowed = 0

local pools = {}          -- [path] = { objectID, ... } free TSStatics
local liveCount = 0
local allObjects = {}  -- [objectID] = true, every TSStatic we created

local function hashString(s)
	if hashStringSHA256 then return string.sub(hashStringSHA256(s), 1, 16) end
	local h = 5381
	for i = 1, #s do h = (h * 33 + string.byte(s, i)) % 4294967296 end
	return string.format("%08x%d", h, #s)
end

local budgetTimer = nil
local function checkBudget()
	if budgetTimer and budgetTimer:stop() > frameBudget then coroutine.yield() end
end

-- ============= BUILD STEPS (inside the coroutine) =============
local function isOffsetModifier(row)
	local function nz(t) return type(t) == "table" and ((t.x or 0) ~= 0 or (t.y or 0) ~= 0 or (t.z or 0) ~= 0) end
	local s = row.scale
	return nz(row.pos) or nz(row.rot) or (type(s) == "table" and ((s.x or 1) ~= 1 or (s.y or 1) ~= 1 or (s.z or 1) ~= 1))
end

local function buildPartIndex(model)
	local diskFile = CACHE_DIR .. model .. "_parts_" .. CACHE_VERSION .. ".json"
	local files = FS:findFiles("/vehicles/" .. model .. "/", "*.jbeam", -1, false, false) or {}
	local sig = modelSignature(model)
	local cached = FS:fileExists(diskFile) and jsonReadFile(diskFile) or nil
	if cached and cached.sig == sig and type(cached.parts) == "table" then return cached.parts end

	local parts = {}
	for _, filename in ipairs(files) do
		local ok, data = pcall(jsonReadFile, filename)
		if ok and type(data) == "table" then
			for partName, part in pairs(data) do
				if type(part) == "table" and type(part.flexbodies) == "table" then
					local list, offset = {}, false
					for _, row in ipairs(part.flexbodies) do
						if type(row) == "table" then
							if row[1] ~= nil then
								local mesh = row[1]
								if type(mesh) == "string" and mesh ~= "mesh" and not offset then list[#list + 1] = mesh end
							else
								offset = isOffsetModifier(row) -- positioned meshes (mirrored/moved) would be misplaced
							end
						end
					end
					if #list > 0 then parts[partName] = list end
				end
			end
		end
		coroutine.yield() -- one jbeam file per step
	end
	FS:directoryCreate(CACHE_DIR, true)
	jsonWriteFile(diskFile, { sig = sig, fileCount = #files, parts = parts }, false)
	return parts
end

local function loadModelMaterials(model)
	if materialsLoaded[model] then return end
	local files = FS:findFiles("/vehicles/" .. model .. "/", "*materials.json", -1, true, false) or {}
	for _, filename in ipairs(files) do
		loadJsonMaterialsFile(filename) -- same as core_vehicle_manager.loadVehicleMaterialsDirectory
		coroutine.yield()
	end
	materialsLoaded[model] = true
end

local function updateBBox(bbox, geometryBlock)
	local arr = string.match(geometryBlock, '<float_array id="[^"]*positions%-array" count="%d+">([^<]*)</float_array>')
	if not arr then return end
	local i, n = 0, 0
	local x, y = 0, 0
	for num in string.gmatch(arr, "%S+") do
		local v = tonumber(num) or 0
		local axis = i % 3
		if axis == 0 then x = v elseif axis == 1 then y = v else
			if x < bbox[1] then bbox[1] = x end
			if x > bbox[4] then bbox[4] = x end
			if y < bbox[2] then bbox[2] = y end
			if y > bbox[5] then bbox[5] = y end
			if v < bbox[3] then bbox[3] = v end
			if v > bbox[6] then bbox[6] = v end
		end
		i = i + 1
		n = n + 1
		if n >= 3000 then n = 0 checkBudget() end
	end
end

--- Streams one .dae. keepGeom(id, name) picks geometry blocks (appended to geoms, ids to keptIds),
-- onNode(block, name, url) sees every flat scene node. geomsOnly stops after the geometry library.
local function scanDae(filename, keepGeom, onNode, geomsOnly, header, geoms, keptIds, bbox)
	local f = io.open(filename, "r")
	if not f then return false end
	local find, sub, match = string.find, string.sub, string.match
	local mode = "header"
	local buf, at = "", 1 -- unconsumed data is buf[at..]; buf is only rebuilt once per read chunk
	local eof = false
	while true do
		if not eof then
			local chunk = f:read(READ_CHUNK)
			if chunk then
				buf = (at > 1 and sub(buf, at) or buf) .. chunk -- one copy per chunk instead of one per geometry
				at = 1
			else
				eof = true
			end
		end
		local progressed = true
		while progressed do
			progressed = false
			if mode == "header" then
				local s = find(buf, "<library_geometries>", at, true)
				if s then
					header[#header + 1] = sub(buf, at, s - 1)
					at = s + 20
					mode = "geoms"
					progressed = true
				elseif #buf - at > 64 then
					header[#header + 1] = sub(buf, at, #buf - 64)
					at = #buf - 63
				end
			elseif mode == "geoms" then
				local s = find(buf, "<geometry ", at, true)
				local libEnd = find(buf, "</library_geometries>", at, true)
				if libEnd and (not s or libEnd < s) then
					at = libEnd + 21
					mode = geomsOnly and "done" or "prescene"
					progressed = true
				elseif s then
					local e = find(buf, "</geometry>", s, true)
					if e then
						local id, name = match(buf, '^<geometry id="([^"]*)" name="([^"]*)"', s)
						if id and keepGeom(id, name) then
							local block = sub(buf, s, e + 10) -- only kept blocks are copied
							geoms[#geoms + 1] = block
							keptIds[id] = true
							if bbox then -- per geometry local bounds, placed by the node transform later
								local gb = {math.huge, math.huge, math.huge, -math.huge, -math.huge, -math.huge}
								updateBBox(gb, block)
								bbox[id] = gb
							end
						end
						at = e + 11
						progressed = true
						checkBudget()
					else
						at = s -- wait for the rest of this geometry
					end
				elseif #buf - at > 32 then
					at = #buf - 31
				end
			elseif mode == "prescene" then
				local s = find(buf, "<visual_scene", at, true)
				if s then
					at = s + 13
					mode = "scene"
					progressed = true
				elseif #buf - at > 32 then
					at = #buf - 31
				end
			elseif mode == "scene" then
				local s = find(buf, "<node ", at, true)
				local sceneEnd = find(buf, "</visual_scene>", at, true)
				if sceneEnd and (not s or sceneEnd < s) then
					mode = "done"
				elseif s then
					local e = find(buf, "</node>", s, true)
					if e then
						local nested = find(buf, "<node ", s + 1, true)
						if not nested or nested > e then -- flat nodes only, nested ones are skipped
							local block = sub(buf, s, e + 6)
							local name = match(block, 'name="([^"]*)"')
							local url = match(block, 'instance_geometry url="#([^"]*)"')
							if name and url then onNode(block, name, url) end
						end
						at = e + 7
						progressed = true
					else
						at = s
					end
				elseif #buf - at > 32 then
					at = #buf - 31
				end
			end
		end
		if mode == "done" or eof then break end
		coroutine.yield() -- one chunk per step
	end
	f:close()
	return true
end

--- Streams one .dae and returns the filtered collada text (or nil if no wanted mesh is in it).
-- Meshes are matched by scene node name (what jbeam flexbodies reference). Exporters like Blender name
-- the geometry blocks differently ("Mesh.038"), those are fetched in a second pass by the node's url.
-- adds a node's geometry bounds to bbox, transformed by the node matrix (collada: row major, column vectors).
-- Some vehicle .dae files keep meshes in centimeters or offset with a scaled/translated node, raw vertex
-- bounds of those were hundreds of meters (the "bigger than the map" boxes).
local function mergeNodeBBox(bbox, block, gb)
	if not gb or gb[1] > gb[4] then return end
	local m = {}
	local mtx = string.match(block, "<matrix[^>]*>([^<]*)</matrix>")
	if mtx then for num in string.gmatch(mtx, "%S+") do m[#m + 1] = tonumber(num) or 0 end end
	if #m ~= 16 then m = {1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1} end
	for i = 0, 7 do
		local x = (i % 2 == 0) and gb[1] or gb[4]
		local y = (math.floor(i / 2) % 2 == 0) and gb[2] or gb[5]
		local z = (i < 4) and gb[3] or gb[6]
		local wx = m[1]*x + m[2]*y + m[3]*z + m[4]
		local wy = m[5]*x + m[6]*y + m[7]*z + m[8]
		local wz = m[9]*x + m[10]*y + m[11]*z + m[12]
		if wx < bbox[1] then bbox[1] = wx end
		if wx > bbox[4] then bbox[4] = wx end
		if wy < bbox[2] then bbox[2] = wy end
		if wy > bbox[5] then bbox[5] = wy end
		if wz < bbox[3] then bbox[3] = wz end
		if wz > bbox[6] then bbox[6] = wz end
	end
end

local function collectMaterials(block, mats)
	if not mats then return end
	for sym in string.gmatch(block, '<instance_material symbol="([^"]+)"') do
		mats[(string.gsub(sym, "%-material$", ""))] = true
	end
end

local function filterDae(filename, wanted, bbox, mats)
	local header, geoms, nodes, keptIds, missing = {}, {}, {}, {}, {}
	local missingCount = 0
	local geomBoxes = {}
	local function keepByName(id, name) return wanted[name] or wanted[string.gsub(id, "%-mesh$", "")] end
	local ok = scanDae(filename, keepByName, function(block, name, url)
		if not wanted[name] then return end
		if keptIds[url] then
			nodes[#nodes + 1] = block .. "\n"
			mergeNodeBBox(bbox, block, geomBoxes[url])
			collectMaterials(block, mats)
		elseif not missing[url] then missing[url] = block missingCount = missingCount + 1 end
	end, false, header, geoms, keptIds, geomBoxes)
	if not ok then return nil end
	if missingCount > 0 then
		scanDae(filename, function(id) return missing[id] ~= nil and not keptIds[id] end, function() end, true, {}, geoms, keptIds, geomBoxes)
		for url, block in pairs(missing) do
			if keptIds[url] then
				nodes[#nodes + 1] = block .. "\n"
				mergeNodeBBox(bbox, block, geomBoxes[url])
				collectMaterials(block, mats)
			end
		end
	end
	if #nodes == 0 then return nil end
	return { header = table.concat(header), geoms = geoms, nodes = nodes }
end

-- ============= MERGING =============
-- All filtered parts of one config go into a single .dae, so the engine imports one shape per mesh set.
-- ids are prefixed per source file (Blender names like "Mesh_038-mesh" repeat across files), materials,
-- effects and images are deduplicated by id. Files with a different <unit>/<up_axis> get their own output.
local function prefixIds(block, pre, refsToo)
	block = string.gsub(block, ' id="', ' id="' .. pre)
	if refsToo then
		block = string.gsub(block, '="#', '="#' .. pre) -- geometry internal references (sources, vertices)
	else
		block = string.gsub(block, 'url="#', 'url="#' .. pre) -- node -> geometry, material targets stay
	end
	return block
end

local function collectLib(header, lib, tag, seen, out)
	local inner = string.match(header, "<" .. lib .. ">(.-)</" .. lib .. ">")
	if not inner then return end
	for block, id in string.gmatch(inner, '(<' .. tag .. ' id="([^"]*)".-</' .. tag .. '>)') do
		if not seen[id] then seen[id] = true out[#out + 1] = block end
	end
end

local function daeSignature(header)
	return (string.match(header, "<unit[^>]*>") or "") .. (string.match(header, "<up_axis>(.-)</up_axis>") or "Z_UP")
end

local function mergeDae(list)
	local first = list[1].header
	local preamble = string.match(first, "^(.-)<asset>") or '<?xml version="1.0" encoding="utf-8"?>\n<COLLADA xmlns="http://www.collada.org/2005/11/COLLADASchema" version="1.4.1">\n'
	local out = { preamble, string.match(first, "<asset>.-</asset>") or "", "\n" }
	for _, lib in ipairs({ { "library_images", "image" }, { "library_effects", "effect" }, { "library_materials", "material" } }) do
		local seen, blocks = {}, {}
		for _, part in ipairs(list) do collectLib(part.header, lib[1], lib[2], seen, blocks) end
		if #blocks > 0 then out[#out + 1] = "<" .. lib[1] .. ">\n" .. table.concat(blocks, "\n") .. "\n</" .. lib[1] .. ">\n" end
	end
	out[#out + 1] = "<library_geometries>\n"
	for i, part in ipairs(list) do
		local pre = "f" .. i .. "_"
		for _, g in ipairs(part.geoms) do out[#out + 1] = prefixIds(g, pre, true) out[#out + 1] = "\n" end
		checkBudget()
	end
	out[#out + 1] = '</library_geometries>\n<library_visual_scenes>\n<visual_scene id="Scene" name="Scene">\n'
	for i, part in ipairs(list) do
		local pre = "f" .. i .. "_"
		for _, n in ipairs(part.nodes) do out[#out + 1] = prefixIds(n, pre, false) end
	end
	out[#out + 1] = '</visual_scene>\n</library_visual_scenes>\n<scene>\n<instance_visual_scene url="#Scene"/>\n</scene>\n</COLLADA>\n'
	return table.concat(out)
end

-- ============= CACHE VALIDATION =============
-- game version + count and total size of the model's jbeam/dae/json files (works for zips and mods alike)
local modelSigs = {}
local function modelSignature(model)
	if modelSigs[model] then return modelSigs[model] end
	local files = FS:findFiles("/vehicles/" .. model .. "/", "*", -1, false, false) or {}
	local n, total = 0, 0
	for i, f in ipairs(files) do
		local ext = string.match(f, "%.(%w+)$")
		if ext == "jbeam" or ext == "dae" or ext == "json" then
			local st = FS:stat(f)
			n, total = n + 1, total + (st and tonumber(st.filesize) or 0)
		end
		if i % 64 == 0 then coroutine.yield() end
	end
	local sig = tostring(beamng_version or "?") .. "|" .. n .. "|" .. total
	modelSigs[model] = sig
	return sig
end

local MAX_LEN, MAX_WIDTH, MAX_HEIGHT = 25, 6, 6
local function validBBox(b)
	if type(b) ~= "table" or #b ~= 6 then return false end
	for i = 1, 6 do if type(b[i]) ~= "number" or b[i] ~= b[i] or b[i] == math.huge or b[i] == -math.huge then return false end end
	local w, l, h = b[4] - b[1], b[5] - b[2], b[6] - b[3]
	return w > 0.1 and l > 0.1 and h > 0.1 and w <= MAX_WIDTH and l <= MAX_LEN and h <= MAX_HEIGHT
		and math.abs(b[1] + b[4]) < 20 and math.abs(b[2] + b[5]) < 30 -- roughly centered on the jbeam origin
end

local function finishBBox(shape, bbox, model)
	shape.minX = nil
	if not validBBox(bbox) then
		if bbox and bbox[1] and bbox[1] <= (bbox[4] or -math.huge) then
			log('W', 'MPProxyMeshGE', string.format("Ignoring implausible mesh bounds for %s: %s", tostring(model), table.concat(bbox, ", ")))
		end
		return
	end
	shape.minX, shape.minY, shape.minZ, shape.maxX, shape.maxY, shape.maxZ = bbox[1], bbox[2], bbox[3], bbox[4], bbox[5], bbox[6]
	-- jbeam vehicles stand on z = 0, use the mesh bottom only if that does not look like it
	shape.groundZ = (bbox[3] > -0.3 and bbox[3] < 0.7) and 0 or bbox[3]
end

-- BeamNG creates glow map materials (signals, lights) at spawn when no material file defines them
-- (lua/common/jbeam/materials.lua), a TSStatic does not, so do the same to avoid [NO-MATERIAL]
local function ensureMaterials(list)
	for _, name in ipairs(list or {}) do
		if not scenetree.findObject(name) then
			local mat = createObject("Material")
			if mat then
				mat.mapTo = name
				mat.canSave = false
				mat:registerObject(name)
			end
		end
	end
end

local function runJob(job)
	local shape = shapes[job.key]
	shape.state = "building"
	local metaFile = CACHE_DIR .. job.key .. ".json"
	local sig = modelSignature(job.model)
	local meta = FS:fileExists(metaFile) and jsonReadFile(metaFile) or nil
	if meta and meta.sig == sig and type(meta.paths) == "table" and #meta.paths > 0 then
		local allExist = true
		for _, p in ipairs(meta.paths) do if not FS:fileExists(p) then allExist = false end end
		if allExist then
			loadModelMaterials(job.model)
			ensureMaterials(meta.materials)
			shape.paths = meta.paths
			shape.fromCache = true -- built in an earlier session
			finishBBox(shape, meta.bbox, job.model)
			shape.state = "ready"
			return
		end
	end

	if type(partIndex[job.model]) ~= "table" then
		partIndex[job.model] = buildPartIndex(job.model)
	end
	local index = partIndex[job.model]
	local wanted, count = {}, 0
	for _, partName in ipairs(job.parts) do
		for _, mesh in ipairs(index[partName] or {}) do
			if count < MAX_MESHES and not wanted[mesh] and isWantedMesh(mesh) then
				wanted[mesh] = true
				count = count + 1
			end
		end
	end
	-- configs that differ only in non visual parts (tuning, engine, paint...) resolve to the same mesh set:
	-- share one set of files, so the engine imports (and caches as .cdae) each mesh set only once
	local meshList = {}
	for mesh in pairs(wanted) do meshList[#meshList + 1] = mesh end
	table.sort(meshList)
	local meshKey = job.model .. "_" .. CACHE_VERSION .. "_m" .. hashString(job.model .. "|" .. table.concat(meshList, ","))
	local meshMetaFile = CACHE_DIR .. meshKey .. ".json"
	if count > 0 and FS:fileExists(meshMetaFile) then
		local mm = jsonReadFile(meshMetaFile)
		local ok = mm and mm.sig == sig and type(mm.paths) == "table" and #mm.paths > 0
		if ok then for _, p in ipairs(mm.paths) do if not FS:fileExists(p) then ok = false end end end
		if ok then
			loadModelMaterials(job.model)
			ensureMaterials(mm.materials)
			jsonWriteFile(metaFile, mm, false)
			shape.paths = mm.paths
			shape.fromCache = true
			finishBBox(shape, mm.bbox, job.model)
			shape.state = "ready"
			return
		end
	end
	if count == 0 then
		log('W', 'MPProxyMeshGE', string.format("No proxy mesh for %s: none of its %d config parts has a usable flexbody mesh in /vehicles/%s/", job.model, #job.parts, job.model))
		shape.state = "failed" shape.reason = "no flexbody meshes for the config parts"
		return
	end

	local bbox = {math.huge, math.huge, math.huge, -math.huge, -math.huge, -math.huge}
	local daes = FS:findFiles("/vehicles/" .. job.model .. "/", "*.dae", -1, false, false) or {}
	local paths, mats = {}, {}
	FS:directoryCreate(CACHE_DIR, true)
	local groups, groupOrder = {}, {}
	for _, dae in ipairs(daes) do
		local part = filterDae(dae, wanted, bbox, mats)
		if part then
			local gsig = daeSignature(part.header)
			if not groups[gsig] then groups[gsig] = {} groupOrder[#groupOrder + 1] = gsig end
			table.insert(groups[gsig], part)
		end
		coroutine.yield()
	end
	for g, gsig in ipairs(groupOrder) do
		local out = CACHE_DIR .. meshKey .. "_" .. g .. ".dae"
		local text = mergeDae(groups[gsig])
		coroutine.yield()
		if writeFile(out, text) then paths[#paths + 1] = out end
		coroutine.yield()
	end
	if #paths == 0 then
		log('W', 'MPProxyMeshGE', string.format("No proxy mesh for %s: %d wanted meshes not found in %d .dae files of /vehicles/%s/", job.model, count, #daes, job.model))
		shape.state = "failed" shape.reason = "meshes not found in the .dae files"
		return
	end
	log('I', 'MPProxyMeshGE', string.format("Proxy mesh for %s ready (%d meshes, %d files)", job.model, count, #paths))
	loadModelMaterials(job.model)
	local matList = {}
	for name in pairs(mats) do matList[#matList + 1] = name end
	table.sort(matList)
	ensureMaterials(matList)
	local metaData = { sig = sig, paths = paths, bbox = validBBox(bbox) and bbox or nil, materials = matList }
	jsonWriteFile(metaFile, metaData, false)
	jsonWriteFile(meshMetaFile, metaData, false)
	shape.paths = paths
	finishBBox(shape, bbox, job.model)
	shape.state = "ready"
end

local function stepJobs()
	if not currentJob then
		local job = table.remove(jobs, 1)
		if not job then return end
		currentJob = { job = job, co = coroutine.create(runJob), started = clock, maxStepMs = 0, frames = 0 }
	end
	budgetTimer = TIMER()
	currentJob.frames = currentJob.frames + 1
	while currentJob and budgetTimer:stop() < frameBudget do
		local before = budgetTimer:stop()
		local ok, err = coroutine.resume(currentJob.co, currentJob.job)
		local stepMs = budgetTimer:stop() - before
		if stepMs > currentJob.maxStepMs then currentJob.maxStepMs = stepMs end
		if not ok then
			log('E', 'MPProxyMeshGE', "Building proxy mesh for "..tostring(currentJob.job.model).." failed: "..tostring(err))
			shapes[currentJob.job.key].state = "failed"
			currentJob = nil
		elseif coroutine.status(currentJob.co) == "dead" then
			local sh = shapes[currentJob.job.key]
			if sh and not sh.fromCache then
				log('I', 'MPProxyMeshGE', string.format("Build of %s took %.1f s over %d frames, longest step %.1f ms",
					currentJob.job.model, clock - currentJob.started, currentJob.frames, currentJob.maxStepMs))
			end
			currentJob = nil
		end
	end
	budgetTimer = nil
end

--- Returns the mesh key for a model + config and queues the build if needed.
-- @tparam string model jbeam name
-- @tparam table vcf vehicle config from the spawn packet (vcf.parts = { slot = partName })
local function request(model, vcf)
	if not model or type(vcf) ~= "table" or type(vcf.parts) ~= "table" then return nil end
	local parts = {}
	for _, partName in pairs(vcf.parts) do
		if type(partName) == "string" and partName ~= "" then parts[#parts + 1] = partName end
	end
	if vcf.mainPartName then parts[#parts + 1] = vcf.mainPartName end
	table.sort(parts)
	local key = model .. "_" .. CACHE_VERSION .. "_" .. hashString(model .. "|" .. table.concat(parts, ","))
	if M._onRequest then M._onRequest() end
	if not shapes[key] then
		shapes[key] = { state = "queued" }
		jobs[#jobs + 1] = { key = key, model = model, parts = parts }
	end
	return key
end

local function getShape(key)
	return key and shapes[key]
end

-- ============= TSSTATIC POOL =============
local function createStatic(path)
	local obj = createObject('TSStatic')
	if not obj then return nil end
	obj:setField('shapeName', 0, path)
	obj:setField('dynamic', 0, 'true')       -- moved every frame (same as trafficSignals)
	obj:setField('collisionType', 0, 'None')
	obj:setField('decalType', 0, 'None')
	obj.useInstanceRenderData = true         -- per instance paint (instanceColor*)
	obj.canSave = false
	obj:registerObject(Sim.getUniqueName("beammpProxyMesh"))
	liveCount = liveCount + 1
	allObjects[obj:getId()] = true
	return obj:getId()
end

local function takeStatic(path)
	local pool = pools[path]
	if pool and #pool > 0 then return table.remove(pool) end
	return createStatic(path)
end

local function returnStatic(path, id)
	local obj = scenetree.findObjectById(id)
	if not obj then liveCount = liveCount - 1 return end
	obj.hidden = true
	pools[path] = pools[path] or {}
	table.insert(pools[path], id)
end

local function paintString(paint)
	local c = paint and paint.baseColor
	if type(c) ~= "table" then return "0.6 0.6 0.6 1" end
	return string.format("%.3f %.3f %.3f %.3f", c[1] or 0.6, c[2] or 0.6, c[3] or 0.6, c[4] or 1)
end

local function attach(p, shape)
	p.meshObjects = {}
	local importTimer = TIMER()
	local newImport = false
	for _, path in ipairs(shape.paths) do if not importedPaths[path] then newImport = true end end
	for _, path in ipairs(shape.paths) do
		importedPaths[path] = true
		local id = takeStatic(path)
		if id then
			local obj = scenetree.findObjectById(id)
			if obj then
				local paints = p.vcf and p.vcf.paints or {}
				obj:setField('instanceColor', 0, paintString(paints[1]))
				obj:setField('instanceColor1', 0, paintString(paints[2] or paints[1]))
				obj:setField('instanceColor2', 0, paintString(paints[3] or paints[1]))
				obj.hidden = false
				p.meshObjects[#p.meshObjects + 1] = { path = path, id = id, obj = obj }
			end
		end
	end
	p.meshShape = shape
	if newImport then -- engine side shape import (synchronous, .cdae cached by the engine after the first time)
		log('I', 'MPProxyMeshGE', string.format("First use of %s mesh took %.1f ms", tostring(string.match(p.meshKey or "", "^(.-)_v%d")), importTimer:stop()))
	end
end

local function detach(p)
	if not p.meshObjects then return end
	for _, o in ipairs(p.meshObjects) do returnStatic(o.path, o.id) end
	p.meshObjects = nil
	p.meshShape = nil
end

--- Decision pass (4 Hz, called by MPProxyGE): picks the nearest proxies with a ready shape.
local candidates = {}
local function decide(vehicles, refPos)
	table.clear(candidates)
	table.clear(waitingLoad)
	table.clear(importedPaths)
	local release = cfg.distance + RELEASE_MARGIN
	for _, v in pairs(vehicles) do
		local p = v.proxy
		if p then
			local usable = cfg.enabled and v.isProxy and not v.isSpawned and not v.isDeleted and not v.proxyColliderID and p.hasData
			local d = usable and refPos:distance(p.rpos) or math.huge
			if p.meshObjects and (not usable or (d > release and not v.isFakeTest)) then detach(p) end
			-- MPProxyTest vehicles ignore the mesh distance (they are never drawn as boxes)
			if usable and (d < cfg.distance or v.isFakeTest) and p.meshKey then
				candidates[#candidates + 1] = { v = v, d = d }
			end
		end
	end
	table.sort(candidates, function(a, b) return a.d < b.d end)
	local created = 0
	for i, c in ipairs(candidates) do
		local p = c.v.proxy
		if i > cfg.maxProxies and not c.v.isFakeTest then
			if p.meshObjects then detach(p) end
		elseif not p.meshObjects then
			local shape = shapes[p.meshKey]
			if shape and shape.state == "ready" and created < MAX_NEW_OBJECTS_PER_PASS then
				if not shape.loaded and shape.paths then -- files already imported by another config of the same mesh set
					local all = true
					for _, path in ipairs(shape.paths) do if not importedPaths[path] then all = false break end end
					if all then shape.loaded = true end
				end
				if not shape.loaded and not c.v.isFakeTest and not shape.fromCache then
					-- first use of this shape: the engine imports it synchronously, so only one per interval
					if clock >= nextNewShapeAllowed then
						nextNewShapeAllowed = clock + NEW_SHAPE_INTERVAL
						shape.loaded = true
						attach(p, shape)
						created = created + 1
					else
						waitingLoad[#waitingLoad + 1] = c.v.jbeam or string.match(p.meshKey, "^(.-)_v%d") or "?"
					end
				else
					shape.loaded = true
					attach(p, shape)
					created = created + 1
				end
			end
		end
	end
end

local tmpV = vec3()
local org = vec3()
local axX, axY, axZ = vec3(), vec3(), vec3()
local unitX, unitY, unitZ = vec3(1,0,0), vec3(0,1,0), vec3(0,0,1)
local ffiFound = ffi and ffi.C and true or false
local drawCylinder = ffiFound and ffi.C.BNG_DBG_DRAW_Cylinder or nop
local wheelColor = color(25, 25, 25, 255)

local function toWorld(lx, ly, lz)
	return org.x + axX.x*lx + axY.x*ly + axZ.x*lz, org.y + axX.y*lx + axY.y*ly + axZ.y*lz, org.z + axX.z*lx + axY.z*ly + axZ.z*lz
end

--- Per frame, for a proxy that has mesh objects: moves them and draws the wheels. Returns true if drawn.
local function drawProxy(p, dist)
	local shape = p.meshShape
	if not p.meshObjects or not shape then return false end
	axX:setRotate(p.rrot, unitX)
	axY:setRotate(p.rrot, unitY)
	axZ:setRotate(p.rrot, unitZ)
	-- the packet position is the center of gravity, the mesh origin is the jbeam origin
	local cx = shape.minX and (shape.minX + shape.maxX) * 0.5 or 0
	local cy = shape.minY and (shape.minY + shape.maxY) * 0.5 or 0
	local cz = (shape.groundZ or 0) + (p.cogH or 0.5)
	org:set(p.rpos.x - (axX.x*cx + axY.x*cy + axZ.x*cz), p.rpos.y - (axX.y*cx + axY.y*cy + axZ.y*cz), p.rpos.z - (axX.z*cx + axY.z*cy + axZ.z*cz))
	local r = p.rrot
	for _, o in ipairs(p.meshObjects) do
		local obj = o.obj
		if obj then
			obj:setPosRot(org.x, org.y, org.z, r.x, r.y, r.z, r.w)
			obj:updateInstanceRenderData()
		end
	end
	if cfg.wheels and shape.minX then
		local W, L, H = shape.maxX - shape.minX, shape.maxY - shape.minY, shape.maxZ - shape.minZ
		local radius = math.min(math.max(H * 0.22, 0.28), 0.55)
		local gz = (shape.groundZ or 0) + radius
		local xo, xi = W * 0.5 - 0.03, W * 0.5 - 0.25
		local yf, yr = cy - L * 0.32, cy + L * 0.32
		for side = -1, 1, 2 do
			for _, y in ipairs({yf, yr}) do
				local x1, y1, z1 = toWorld(cx + side * xi, y, gz)
				local x2, y2, z2 = toWorld(cx + side * xo, y, gz)
				drawCylinder(x1, y1, z1, x2, y2, z2, radius, wheelColor, true)
			end
		end
	end
	return true
end

local buildTimer = nil -- lazy, see MPProxyGE.getPerfTimer
local buildStats = { ms = 0, frames = 0, maxMs = 0 }

-- ============= LOADING OVERLAY =============
local imgui = ui_imgui
local niceNames = {}
local function niceName(model)
	local n = niceNames[model]
	if n then return n end
	local ok, m = pcall(core_vehicles.getModel, model) -- cached by the game per model
	local info = ok and type(m) == "table" and m.model or nil
	if info and info.Name then
		n = (info.Brand and info.Brand ~= "" and not string.find(info.Name, info.Brand, 1, true)) and (info.Brand .. " " .. info.Name) or info.Name
	else
		n = tostring(model)
	end
	niceNames[model] = n
	return n
end

local overlayFlags = nil
local function drawOverlay()
	if not imgui or not imgui.Begin then return end
	local current = currentJob and currentJob.job.model or jobs[1] and jobs[1].model or waitingLoad[1]
	if not current then return end
	local more = #jobs + #waitingLoad + (currentJob and 1 or 0) - 1
	local text = "Loading vehicle " .. niceName(current) .. "..." .. (more > 0 and string.format(" (+%d more)", more) or "")
	if not overlayFlags then
		overlayFlags = imgui.flags(imgui.WindowFlags_NoTitleBar, imgui.WindowFlags_NoResize, imgui.WindowFlags_NoMove,
			imgui.WindowFlags_NoScrollbar, imgui.WindowFlags_NoCollapse, imgui.WindowFlags_NoDocking, imgui.WindowFlags_NoInputs,
			imgui.WindowFlags_AlwaysAutoResize, imgui.WindowFlags_NoSavedSettings, imgui.WindowFlags_NoFocusOnAppearing, imgui.WindowFlags_NoNav)
	end
	local vp = imgui.GetMainViewport()
	imgui.SetNextWindowPos(imgui.ImVec2(vp.Pos.x + vp.Size.x * 0.5, vp.Pos.y + 40), imgui.Cond_Always, imgui.ImVec2(0.5, 0))
	imgui.SetNextWindowBgAlpha(0.45)
	if imgui.Begin("##beammpProxyLoading", nil, overlayFlags) then
		imgui.Text(text)
	end
	imgui.End()
end

-- ============= JOIN PRELOAD =============
-- While joining, BeamMP's map loading screen is kept up (core_gamestate loading screen request, same as
-- career does) until the vehicles received on join have their meshes built and imported once, capped by
-- PRELOAD_TIMEOUT. Whatever is left continues in the background with the normal budget.
local PRELOAD_TAG = "beammpProxyPreload"
local PRELOAD_TIMEOUT = 25  -- seconds
local PRELOAD_FIRST_WAIT = 6 -- seconds to wait for the first spawn packets
local PRELOAD_QUIET = 2      -- seconds without new requests before finishing
local preload = nil

local function finishPreload(reason)
	if not preload then return end
	log('I', 'MPProxyMeshGE', string.format("Join preload finished after %.1f s (%s)", clock - preload.started, reason))
	preload = nil
	frameBudget = FRAME_BUDGET_MS
	guihooks.trigger('LoadingInfo', { message = "" })
	if core_gamestate and core_gamestate.requestExitLoadingScreen then core_gamestate.requestExitLoadingScreen(PRELOAD_TAG) end
end

local function startPreload()
	if preload or not cfg.enabled then return end
	if not (MPCoreNetwork and MPCoreNetwork.isMPSession and MPCoreNetwork.isMPSession()) then return end
	if not (core_gamestate and core_gamestate.requestEnterLoadingScreen) then return end
	preload = { started = clock, quietUntil = clock + PRELOAD_FIRST_WAIT }
	frameBudget = PRELOAD_BUDGET_MS
	core_gamestate.requestEnterLoadingScreen(PRELOAD_TAG)
	log('I', 'MPProxyMeshGE', "Join preload started")
end

M._onRequest = function()
	if preload then preload.quietUntil = math.max(preload.quietUntil, clock + PRELOAD_QUIET) end
end

-- imports every ready shape once (hidden pooled TSStatic), so the first real use does not hitch
local function preImport()
	local done = 0
	for _, shape in pairs(shapes) do
		if shape.state == "ready" and shape.paths and not shape.loaded then
			for _, path in ipairs(shape.paths) do
				if not importedPaths[path] then
					local t = TIMER()
					importedPaths[path] = true
					local id = takeStatic(path)
					if id then returnStatic(path, id) end
					log('I', 'MPProxyMeshGE', string.format("First use of %s mesh took %.1f ms (preload)", path, t:stop()))
					done = done + 1
				end
			end
			shape.loaded = true
			if done >= 1 then return true end -- one import per frame keeps the loading screen animating
		end
	end
	return done > 0
end

local function updatePreload()
	if not preload then return end
	local busy = currentJob ~= nil or #jobs > 0
	local imported = preImport()
	local current = currentJob and currentJob.job.model or jobs[1] and jobs[1].model
	if current then
		guihooks.trigger('LoadingInfo', { message = string.format("Preparing vehicles: %s (%d left)", tostring(current), #jobs + 1) })
	end
	if clock - preload.started > PRELOAD_TIMEOUT then finishPreload("timeout, continuing in background")
	elseif not busy and not imported and clock > preload.quietUntil then finishPreload("all vehicles ready") end
end

-- removes cache files of older CACHE_VERSIONs (and their engine .cdae copies)
local function cleanOldCache()
	local removed, bytes = 0, 0
	for _, dir in ipairs({ CACHE_DIR, "/temp" .. CACHE_DIR }) do
		for _, f in ipairs(FS:findFiles(dir, "*", 0, false, false) or {}) do
			local name = string.match(f, "([^/]+)$") or f
			local current = string.find(name, "_" .. CACHE_VERSION .. "_", 1, true) or string.find(name, "_parts_" .. CACHE_VERSION .. ".json", 1, true)
			if not current and name ~= "main.materials.json" then
				local st = FS:stat(f)
				bytes = bytes + (st and tonumber(st.filesize) or 0)
				FS:removeFile(f)
				removed = removed + 1
			end
		end
	end
	if removed > 0 then log('I', 'MPProxyMeshGE', string.format("Removed %d old proxy mesh cache files (%.0f MB)", removed, bytes / 1048576)) end
end

local function onUpdate(dtReal)
	clock = clock + (dtReal or 0)
	if not cfg.enabled then return end
	if currentJob or #jobs > 0 then
		if buildTimer == nil then
			local ok, t = pcall(function() return (hptimer and hptimer()) or (HighPerfTimer and HighPerfTimer()) end)
			buildTimer = ok and t or false
		end
		if buildTimer then buildTimer:stopAndReset() end
		stepJobs()
		if buildTimer then
			local ms = buildTimer:stop()
			buildStats.ms, buildStats.frames = buildStats.ms + ms, buildStats.frames + 1
			if ms > buildStats.maxMs then buildStats.maxMs = ms end
		end
	end
	updatePreload()
	if not preload then drawOverlay() end -- the loading screen shows progress during preload
end

--- Cache / pool statistics for MPProxyTest.
local function getStats(resetWindow)
	local out = { queued = #jobs + (currentJob and 1 or 0), building = currentJob and currentJob.job and currentJob.job.key or nil,
		ready = 0, failed = 0, liveObjects = liveCount,
		buildFrames = buildStats.frames, avgBuildMs = buildStats.frames > 0 and buildStats.ms / buildStats.frames or 0, maxBuildMs = buildStats.maxMs }
	for _, sh in pairs(shapes) do
		if sh.state == "ready" then out.ready = out.ready + 1 elseif sh.state == "failed" then out.failed = out.failed + 1 end
	end
	if resetWindow then buildStats.ms, buildStats.frames, buildStats.maxMs = 0, 0, 0 end
	return out
end

local function reset()
	table.clear(waitingLoad)
	table.clear(importedPaths)
	for id, _ in pairs(allObjects) do
		local obj = scenetree.findObjectById(id)
		if obj then obj:delete() end
	end
	allObjects = {}
	pools = {}
	liveCount = 0
	materialsLoaded = {} -- materials are invalidated on mission end (core_vehicle_manager does the same)
	shapes = {} -- rebuilt from the disk cache (cheap) on the next request
	jobs = {}
	currentJob = nil
end

--- Deletes the objects of a proxy that is going away (vehicle removed or swapped to real).
local function release(p)
	if p then detach(p) end
end

--- Clears the per proxy references after reset (objects are gone).
local function forget(p)
	if p then p.meshObjects = nil p.meshShape = nil p.meshKey = nil end
end

local function onSettingsChanged() readSettings() end
local function onExtensionLoaded()
	readSettings()
	local ok, err = pcall(cleanOldCache)
	if not ok then log('W', 'MPProxyMeshGE', "Cache cleanup failed: " .. tostring(err)) end
end

detectGlobalWrites() -- reenable global write notifications

M.request           = request
M.getShape          = getShape
M.decide            = decide
M.drawProxy         = drawProxy
M.release           = release
M.forget            = forget
M.reset             = reset
M.onUpdate          = onUpdate
M.getStats          = getStats
M.isEnabled         = function() return cfg.enabled end
M.onSettingsChanged = onSettingsChanged
M.onExtensionLoaded = onExtensionLoaded
M.onClientEndMission = function() finishPreload("mission ended") reset() end
M.onClientStartMission = startPreload
M.onInit = function() setExtensionUnloadMode(M, "manual") end

return M
