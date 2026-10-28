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
local CACHE_VERSION = "v1"
local READ_CHUNK = 1024 * 1024    -- bytes per read step
local FRAME_BUDGET_MS = 2         -- coroutine work per frame
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
	if budgetTimer and budgetTimer:stop() > FRAME_BUDGET_MS then coroutine.yield() end
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
	local cached = FS:fileExists(diskFile) and jsonReadFile(diskFile) or nil
	if cached and cached.fileCount == #files and type(cached.parts) == "table" then return cached.parts end

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
	jsonWriteFile(diskFile, { fileCount = #files, parts = parts }, false)
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

--- Streams one .dae and returns the filtered collada text (or nil if no wanted mesh is in it).
local function filterDae(filename, wanted, bbox)
	local f = io.open(filename, "r")
	if not f then return nil end
	local header, geoms, nodes, keptIds = {}, {}, {}, {}
	local mode = "header"
	local buf = ""
	local eof = false
	while true do
		if not eof then
			local chunk = f:read(READ_CHUNK)
			if chunk then buf = buf .. chunk else eof = true end
		end
		local progressed = true
		while progressed do
			progressed = false
			if mode == "header" then
				local s = string.find(buf, "<library_geometries>", 1, true)
				if s then
					header[#header + 1] = string.sub(buf, 1, s - 1)
					buf = string.sub(buf, s + 20)
					mode = "geoms"
					progressed = true
				elseif #buf > 64 then
					header[#header + 1] = string.sub(buf, 1, #buf - 64)
					buf = string.sub(buf, #buf - 63)
				end
			elseif mode == "geoms" then
				local s = string.find(buf, "<geometry ", 1, true)
				local libEnd = string.find(buf, "</library_geometries>", 1, true)
				if libEnd and (not s or libEnd < s) then
					buf = string.sub(buf, libEnd + 21)
					mode = "prescene"
					progressed = true
				elseif s then
					local e = string.find(buf, "</geometry>", s, true)
					if e then
						local block = string.sub(buf, s, e + 10)
						local id, name = string.match(block, '^<geometry id="([^"]*)" name="([^"]*)"')
						if id and (wanted[name] or wanted[string.gsub(id, "%-mesh$", "")]) then
							geoms[#geoms + 1] = block
							keptIds[id] = true
							updateBBox(bbox, block)
						end
						buf = string.sub(buf, e + 11)
						progressed = true
					else
						buf = string.sub(buf, s) -- wait for the rest of this geometry
					end
				elseif #buf > 32 then
					buf = string.sub(buf, #buf - 31)
				end
			elseif mode == "prescene" then
				local s = string.find(buf, "<visual_scene", 1, true)
				if s then
					buf = string.sub(buf, s + 13)
					mode = "scene"
					progressed = true
				elseif #buf > 32 then
					buf = string.sub(buf, #buf - 31)
				end
			elseif mode == "scene" then
				local s = string.find(buf, "<node ", 1, true)
				local sceneEnd = string.find(buf, "</visual_scene>", 1, true)
				if sceneEnd and (not s or sceneEnd < s) then
					mode = "done"
				elseif s then
					local e = string.find(buf, "</node>", s, true)
					if e then
						local block = string.sub(buf, s, e + 6)
						if not string.find(block, "<node ", 2, true) then -- flat nodes only, nested ones are skipped
							local name = string.match(block, 'name="([^"]*)"')
							local url = string.match(block, 'instance_geometry url="#([^"]*)"')
							if name and url and wanted[name] and keptIds[url] then nodes[#nodes + 1] = block .. "\n" end
						end
						buf = string.sub(buf, e + 7)
						progressed = true
					else
						buf = string.sub(buf, s)
					end
				elseif #buf > 32 then
					buf = string.sub(buf, #buf - 31)
				end
			end
		end
		if mode == "done" or eof then break end
		coroutine.yield() -- one chunk per step
	end
	f:close()
	if #nodes == 0 then return nil end
	return table.concat(header) .. "<library_geometries>\n" .. table.concat(geoms, "\n") ..
		"\n</library_geometries>\n<library_visual_scenes>\n<visual_scene id=\"Scene\" name=\"Scene\">\n" ..
		table.concat(nodes) .. "</visual_scene>\n</library_visual_scenes>\n<scene>\n<instance_visual_scene url=\"#Scene\"/>\n</scene>\n</COLLADA>\n"
end

local function finishBBox(shape, bbox)
	if bbox[1] > bbox[4] then return end
	shape.minX, shape.minY, shape.minZ, shape.maxX, shape.maxY, shape.maxZ = bbox[1], bbox[2], bbox[3], bbox[4], bbox[5], bbox[6]
	-- jbeam vehicles stand on z = 0, use the mesh bottom only if that does not look like it
	shape.groundZ = (bbox[3] > -0.3 and bbox[3] < 0.7) and 0 or bbox[3]
end

local function runJob(job)
	local shape = shapes[job.key]
	shape.state = "building"
	local metaFile = CACHE_DIR .. job.key .. ".json"
	local meta = FS:fileExists(metaFile) and jsonReadFile(metaFile) or nil
	if meta and type(meta.paths) == "table" and #meta.paths > 0 then
		local allExist = true
		for _, p in ipairs(meta.paths) do if not FS:fileExists(p) then allExist = false end end
		if allExist then
			loadModelMaterials(job.model)
			shape.paths = meta.paths
			finishBBox(shape, meta.bbox or {1, 1, 1, -1, -1, -1})
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
	if count == 0 then shape.state = "failed" return end

	local bbox = {math.huge, math.huge, math.huge, -math.huge, -math.huge, -math.huge}
	local daes = FS:findFiles("/vehicles/" .. job.model .. "/", "*.dae", -1, false, false) or {}
	local paths = {}
	FS:directoryCreate(CACHE_DIR, true)
	for i, dae in ipairs(daes) do
		local text = filterDae(dae, wanted, bbox)
		if text then
			local out = CACHE_DIR .. job.key .. "_" .. i .. ".dae"
			if writeFile(out, text) then paths[#paths + 1] = out end
		end
		coroutine.yield()
	end
	if #paths == 0 then shape.state = "failed" return end
	loadModelMaterials(job.model)
	jsonWriteFile(metaFile, { paths = paths, bbox = bbox[1] <= bbox[4] and bbox or nil }, false)
	shape.paths = paths
	finishBBox(shape, bbox)
	shape.state = "ready"
end

local function stepJobs()
	if not currentJob then
		local job = table.remove(jobs, 1)
		if not job then return end
		currentJob = { job = job, co = coroutine.create(runJob) }
	end
	budgetTimer = TIMER()
	while currentJob and budgetTimer:stop() < FRAME_BUDGET_MS do
		local ok, err = coroutine.resume(currentJob.co, currentJob.job)
		if not ok then
			log('E', 'MPProxyMeshGE', "Building proxy mesh for "..tostring(currentJob.job.model).." failed: "..tostring(err))
			shapes[currentJob.job.key].state = "failed"
			currentJob = nil
		elseif coroutine.status(currentJob.co) == "dead" then
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
	for _, path in ipairs(shape.paths) do
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
	local release = cfg.distance + RELEASE_MARGIN
	for _, v in pairs(vehicles) do
		local p = v.proxy
		if p then
			local usable = cfg.enabled and v.isProxy and not v.isSpawned and not v.isDeleted and not v.proxyColliderID and p.hasData
			local d = usable and refPos:distance(p.rpos) or math.huge
			if p.meshObjects and (not usable or d > release) then detach(p) end
			if usable and d < cfg.distance and p.meshKey then
				candidates[#candidates + 1] = { v = v, d = d }
			end
		end
	end
	table.sort(candidates, function(a, b) return a.d < b.d end)
	local created = 0
	for i, c in ipairs(candidates) do
		local p = c.v.proxy
		if i > cfg.maxProxies then
			if p.meshObjects then detach(p) end
		elseif not p.meshObjects then
			local shape = shapes[p.meshKey]
			if shape and shape.state == "ready" and created < MAX_NEW_OBJECTS_PER_PASS then
				if not shape.loaded then
					-- first use of this shape: the engine imports it synchronously, so only one per interval
					if clock >= nextNewShapeAllowed then
						nextNewShapeAllowed = clock + NEW_SHAPE_INTERVAL
						shape.loaded = true
						attach(p, shape)
						created = created + 1
					end
				else
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

local buildTimer = type(hptimer) == "function" and hptimer() or nil
local buildStats = { ms = 0, frames = 0, maxMs = 0 }

local function onUpdate(dtReal)
	clock = clock + (dtReal or 0)
	if not cfg.enabled then return end
	if currentJob or #jobs > 0 then
		if buildTimer then buildTimer:stopAndReset() end
		stepJobs()
		if buildTimer then
			local ms = buildTimer:stop()
			buildStats.ms, buildStats.frames = buildStats.ms + ms, buildStats.frames + 1
			if ms > buildStats.maxMs then buildStats.maxMs = ms end
		end
	end
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
local function onExtensionLoaded() readSettings() end

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
M.onSettingsChanged = onSettingsChanged
M.onExtensionLoaded = onExtensionLoaded
M.onClientEndMission = reset
M.onInit = function() setExtensionUnloadMode(M, "manual") end

return M
