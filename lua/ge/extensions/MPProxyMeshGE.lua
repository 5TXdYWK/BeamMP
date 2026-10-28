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
local CACHE_VERSION = "v5" -- v5: three LOD tier mesh sets per config, v4: triangle budget (smallest parts dropped), v3: one merged .dae per mesh set, signatures
local READ_CHUNK = 128 * 1024     -- bytes per read step (smaller steps keep each resume near the frame budget)
local FRAME_BUDGET_MS = 2         -- coroutine work per frame in game (proxyMeshFrameBudgetMs)
local PRELOAD_BUDGET_MS = 40      -- while the join loading screen hides the stutter
local frameBudget = FRAME_BUDGET_MS
local MAX_MESHES = 250            -- per config (the full tier keeps everything the config shows)
local MAX_NEW_OBJECTS_PER_PASS = 4
local SUSP_MAX_PROXIES = 8       -- nearest proxies with visual suspension (proxySuspension)
local MAX_DETACHES_PER_PASS = 6   -- mesh -> box changes per pass, farthest first, so a group leaving range spreads out
local NEW_SHAPE_INTERVAL = 2      -- seconds between first uses of not yet loaded shapes (engine import hitch)
local CACHED_SHAPE_INTERVAL = 0.5 -- same, when the engine already has a compiled .cdae of every file (cheaper load)
local RELEASE_MARGIN = 50

local cfg = { enabled = true, distance = 500, maxProxies = 48, wheels = true, targetFps = 0, triBudget = 60000, prebuild = false,
	lodFull = 20, lodParts = 60, lodShell = 150, frameBudget = FRAME_BUDGET_MS }

-- ============= LOD TIERS =============
-- Every config is built into three mesh sets: 1 = full (every mesh of the config), 2 = parts (interior, mechanical
-- and small trim left out, within the triangle budget), 3 = shell (only the biggest body panels). Further out
-- MPProxyGE draws a low poly car shape and, at the far end, a box in the paint colour.
local TIER_FULL, TIER_PARTS, TIER_SHELL = 1, 2, 3
local LOD_HYSTERESIS = 0.1 -- a tier boundary is moved out by this fraction (plus 3 m) for proxies already inside
local SHELL_MIN_TRIS = 3000

local function readSettings()
	cfg.enabled = settings.getValue("proxyMeshEnabled", true) ~= false
	cfg.distance = tonumber(settings.getValue("proxyMeshDistance", 500)) or 500
	cfg.maxProxies = math.max(0, math.floor(tonumber(settings.getValue("proxyMaxMeshProxies", 48)) or 48))
	cfg.wheels = settings.getValue("proxyMeshWheels", true) ~= false
	cfg.realWheels = settings.getValue("proxyMeshRealWheels", true) ~= false
	cfg.metallicPaint = settings.getValue("proxyMetallicPaint", true) ~= false
	cfg.skipStatic = settings.getValue("proxySkipStaticUpdates", true) ~= false
	cfg.suspension = settings.getValue("proxySuspension", false) == true
	cfg.suspDist = math.max(0, tonumber(settings.getValue("proxySuspensionDistance", 40)) or 40)
	cfg.realWheelsMax = math.max(0, math.floor(tonumber(settings.getValue("proxyMeshRealWheelsMax", 12)) or 12))
	cfg.targetFps = math.max(0, tonumber(settings.getValue("proxyTargetFps", 0)) or 0)
	cfg.triBudget = math.max(0, math.floor(tonumber(settings.getValue("proxyMeshTriangleBudget", 60000)) or 60000))
	cfg.prebuild = settings.getValue("proxyPrebuildModels", false) == true
	cfg.lodFull = math.max(0, tonumber(settings.getValue("proxyLodFullDistance", 20)) or 20)
	cfg.lodParts = math.max(cfg.lodFull, tonumber(settings.getValue("proxyLodPartsDistance", 60)) or 60)
	cfg.lodShell = math.max(cfg.lodParts, tonumber(settings.getValue("proxyLodShellDistance", 150)) or 150)
	cfg.frameBudget = math.min(math.max(tonumber(settings.getValue("proxyMeshFrameBudgetMs", FRAME_BUDGET_MS)) or FRAME_BUDGET_MS, 0.25), 20)
end

-- the mesh tier for a distance, nil beyond the mesh tiers; cur is the tier the proxy has now (hysteresis)
local function tierForDistance(d, cur)
	local bounds = { cfg.lodFull, cfg.lodParts, math.min(cfg.lodShell, cfg.distance) }
	for t = 1, 3 do
		local b = bounds[t]
		if cur and cur <= t then b = b * (1 + LOD_HYSTERESIS) + 3 end
		if d < b then return t end
	end
	return nil
end

-- ============= FRAME RATE TARGET =============
-- With proxyTargetFps set, the number of proxies drawn with meshes is lowered while the frame rate is under the
-- target and raised again when there is headroom. If several reductions in a row did not make frames faster,
-- the meshes are not what limits the frame rate: the old count comes back and we wait before trying again.
local FPS_WINDOW = 0.5
local fps = { sum = 0, frames = 0, cap = math.huge, reductions = 0, baseMs = 0, restore = math.huge, holdUntil = 0, inRange = 0 }

local function updateFpsCap(dtReal, now)
	if cfg.targetFps <= 0 then fps.cap = math.huge return end
	fps.sum, fps.frames = fps.sum + dtReal, fps.frames + 1
	if fps.sum < FPS_WINDOW then return end
	local ms = fps.sum / fps.frames * 1000
	fps.sum, fps.frames = 0, 0
	local target = 1000 / cfg.targetFps
	local current = math.min(fps.cap, fps.inRange)
	if ms > target * 1.05 then
		if now < fps.holdUntil or current <= 4 then fps.reductions = 0 return end
		if fps.reductions == 0 then fps.restore, fps.baseMs = fps.cap, ms end
		fps.reductions = fps.reductions + 1
		if fps.reductions > 3 and ms > fps.baseMs * 0.97 then -- did not help
			fps.cap, fps.holdUntil, fps.reductions = fps.restore, now + 15, 0
			return
		end
		fps.cap = math.max(4, math.floor(current * 0.85))
	else
		fps.reductions = 0
		if ms < target * 0.9 and fps.cap ~= math.huge then
			fps.cap = math.ceil(fps.cap * 1.1) + 1
			if fps.cap >= fps.inRange then fps.cap = math.huge end
		end
	end
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
local fallbackOf = {}     -- [config key] = key of the model's default config (shown while the config builds)
local defaultKeys = {}    -- [model] = key | false
local prebuildJobs = {}   -- background builds of default configs (proxyPrebuildModels), only when jobs is empty
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
local jobPhase = "start" -- what the running job does now, for the per step timings in the job log
local function setPhase(name) jobPhase = name end
local function checkBudget()
	if budgetTimer and budgetTimer:stop() > frameBudget then coroutine.yield() end
end

-- ============= BUILD STEPS (inside the coroutine) =============
local function isOffsetModifier(row)
	local function nz(t) return type(t) == "table" and ((t.x or 0) ~= 0 or (t.y or 0) ~= 0 or (t.z or 0) ~= 0) end
	local s = row.scale
	return nz(row.pos) or nz(row.rot) or (type(s) == "table" and ((s.x or 1) ~= 1 or (s.y or 1) ~= 1 or (s.z or 1) ~= 1))
end

-- flexbody rows that are never part of the body mesh sets: wheels, tires, hubcaps and brakes (bound to wheel /
-- tire / hubcap / wheelhub groups, they come from the wheel system), and rows placed by their own pos / rot /
-- scale (the body sets use the raw mesh position, those would end up at the vehicle origin)
local BODY_SKIP_GROUPS = { wheel = true, tire = true, tyre = true, hubcap = true, rim = true, wheelhub = true }
local function isWheelFlexRow(row)
	local last = row[#row]
	if #row > 1 and type(last) == "table" and last[1] == nil and isOffsetModifier(last) then return true end
	if type(row[2]) == "table" then
		for _, g in ipairs(row[2]) do
			local pre = type(g) == "string" and string.match(g, "^(%a+)_")
			if pre and BODY_SKIP_GROUPS[string.lower(pre)] then return true end
		end
	end
	return false
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
		checkBudget()
	end
	local sig = tostring(beamng_version or "?") .. "|" .. n .. "|" .. total
	modelSigs[model] = sig
	return sig
end

-- Finds the "flexbodies" array of every part in a jbeam text without decoding the file: a large jbeam (nodes,
-- beams, triangles of a body) took tens of ms in one jsonDecode. Strings, // and /* */ comments are skipped,
-- out[partName] = text of the part's flexbodies array (decoded alone, it is small). Returns false if the text
-- did not look like a jbeam (the caller then decodes the whole file).
-- array sections read for the wheel placement (wheelSecs[partName][key] = array text); nodes only of parts
-- that also have a wheel section (hubs, wheels, suspension), body node lists are big and not needed
local WHEEL_KEYS = { slots = true, slots2 = true, pressureWheels = true, hubWheels = true, variables = true, nodes = true }

local function extractFlexbodies(text, out, sections, wheelSecs)
	local find, sub, byte, match = string.find, string.sub, string.byte, string.match
	local pos, depth, n = 1, 0, 0
	local partName, flexStart = nil, nil
	local secStart, secKey = nil, nil -- engine / sound sections (sections[partName][key] = object text)
	local arrStart, arrKey = nil, nil -- wheel related array sections
	local partSecs, nodesFrom, nodesTo = nil, nil, nil
	local lastString, lastDepth, lastEnd = nil, -1, 0
	while true do
		local s = find(text, '[{}%[%]"/]', pos)
		if not s then break end
		local c = byte(text, s)
		if c == 34 then -- string
			local e = s + 1
			while true do
				local q = find(text, '["\\]', e)
				if not q then return false end
				if byte(text, q) == 92 then e = q + 2 else e = q break end
			end
			lastString, lastDepth, lastEnd = sub(text, s + 1, e - 1), depth, e
			pos = e + 1
		elseif c == 47 then -- comment
			local nx = byte(text, s + 1)
			if nx == 47 then local e = find(text, "\n", s + 2, true) pos = e and e + 1 or #text + 1
			elseif nx == 42 then local e = find(text, "*/", s + 2, true) pos = e and e + 2 or #text + 1
			else pos = s + 1 end
		elseif c == 123 or c == 91 then
			depth = depth + 1
			local isKey = lastString and lastDepth == depth - 1 and match(sub(text, lastEnd + 1, s - 1), "^%s*:%s*$")
			if depth == 2 and c == 123 then partName = isKey and lastString or nil partSecs, nodesFrom = nil, nil
			elseif depth == 3 and c == 91 and isKey and lastString == "flexbodies" and partName then flexStart = s
			elseif depth == 3 and c == 91 and isKey and partName and wheelSecs and WHEEL_KEYS[lastString] then arrStart, arrKey = s, lastString
			elseif depth == 3 and c == 123 and isKey and partName and sections
				and (lastString == "mainEngine" or sub(lastString, 1, 11) == "soundConfig") then secStart, secKey = s, lastString end
			lastString = nil
			pos = s + 1
		else
			if depth == 3 and flexStart and c == 93 then out[partName] = sub(text, flexStart, s) flexStart = nil end
			if depth == 3 and secStart and c == 125 then
				sections[partName] = sections[partName] or {}
				sections[partName][secKey] = sub(text, secStart, s)
				secStart = nil
			end
			if depth == 3 and arrStart and c == 93 then
				if arrKey == "nodes" then nodesFrom, nodesTo = arrStart, s
				else partSecs = partSecs or {} partSecs[arrKey] = sub(text, arrStart, s) end
				arrStart = nil
			end
			if depth == 2 then
				if partSecs then
					if nodesFrom and (partSecs.pressureWheels or partSecs.hubWheels) then partSecs.nodes = sub(text, nodesFrom, nodesTo) end
					wheelSecs[partName] = partSecs
				end
				partName, partSecs, nodesFrom = nil, nil, nil
			end
			depth = depth - 1
			if depth < 0 then return false end
			lastString = nil
			pos = s + 1
		end
		n = n + 1
		if n >= 400 then n = 0 checkBudget() end
	end
	return depth == 0
end

-- fields kept from the jbeam engine device and its sound sections (as read by combustionEngine.lua init)
local ENGINE_FIELDS = { idleRPM = true, maxRPM = true, revLimiterRPM = true, soundConfig = true, soundConfigExhaust = true, requiredEnergyType = true }
local SOUND_FIELDS = { sampleName = true, sampleFolder = true, mainGain = true, onLoadGain = true, offLoadGain = true,
	intakeMuffling = true, exhaustAudioMufflingBaseCoef = true }
local ENGINE_INDEX_VERSION = 4 -- part index files without this are rebuilt once (2: wheel sections, 3: wheel flexbodies, 4: no wheel meshes in the body lists)
local BODY_VERSION = 2 -- per config meta written before this is not reused as is (2: wheel / tire / brake meshes left out of the body)

local function keepFields(decoded, fields)
	local out, any = {}, false
	for k in pairs(fields) do
		local v = decoded[k]
		if type(v) == "number" or (type(v) == "string" and string.sub(v, 1, 1) ~= "$") then out[k] = v any = true end
	end
	return any and out or nil
end

-- engine[partName] = { mainEngine = {...}, [soundConfig section name] = {...} }
local function addEngineSections(engine, sectionTexts, filename)
	for partName, secs in pairs(sectionTexts) do
		for key, txt in pairs(secs) do
			local ok, d = pcall(jsonDecode, txt, filename)
			local kept = ok and type(d) == "table" and keepFields(d, key == "mainEngine" and ENGINE_FIELDS or SOUND_FIELDS) or nil
			if kept then
				engine[partName] = engine[partName] or {}
				engine[partName][key] = kept
			end
			checkBudget()
		end
	end
end

local engineIndex = {} -- [model] = engine sections by part (see addEngineSections)

-- ============= WHEEL SECTIONS (compact, for the wheel placement) =============
local WHEEL_OPTS = { radius = true, tireWidth = true, hubRadius = true, hubWidth = true, wheelOffset = true, offsetFromNode = true }
local wheelIndex = {}         -- [model] = { [partName] = compact wheel data } (model and /vehicles/common/<model>/)
local commonWheelIndex = nil  -- same for the shared tire / wheel / hubcap folders of /vehicles/common/
local COMMON_WHEEL_DIRS = { "tires", "wheels", "wheels_square", "hubcaps" }

local function scalar(v) return (type(v) == "number" or type(v) == "string") and v or nil end
local function vec3Raw(o) return type(o) == "table" and { scalar(o.x) or 0, scalar(o.y) or 0, scalar(o.z) or 0 } or false end

local function headerIndex(row, names)
	local idx = {}
	if type(row) ~= "table" then return idx end
	for i, v in ipairs(row) do if names[v] then idx[v] = i end end
	return idx
end

-- slots (child slot types / names, slot nodeOffset), variable defaults, wheel rows and options in order,
-- and node positions with their nodeOffset modifiers
local function compactWheelPart(secs, filename)
	local function dec(key)
		local t = secs[key]
		if not t then return nil end
		local ok, d = pcall(jsonDecode, t, filename)
		checkBudget()
		return ok and type(d) == "table" and d or nil
	end
	local out, any = {}, false
	local is2 = secs.slots2 ~= nil
	local sl = dec(is2 and "slots2" or "slots")
	if sl then
		local list = {}
		for _, row in ipairs(sl) do
			if type(row) == "table" and type(row[1]) == "string" and row[1] ~= "type" and row[1] ~= "name" then
				local e = { n = row[1], t = row[1] }
				if is2 then local a = row[2] e.t = type(a) == "table" and a[1] or (type(a) == "string" and a) or row[1] end
				for i = 2, #row do
					if type(row[i]) == "table" and row[i].nodeOffset then e.o = vec3Raw(row[i].nodeOffset) end
				end
				list[#list + 1] = e
			end
		end
		if #list > 0 then out.slots = list any = true end
	end
	local vars = dec("variables")
	if vars then
		local h = headerIndex(vars[1], { name = true, default = true })
		local di = h.default or 5
		local v = {}
		for i, row in ipairs(vars) do
			if i > 1 and type(row) == "table" and type(row[1]) == "string" and scalar(row[di]) then v[row[1]] = row[di] any = true end
		end
		if any then out.vars = v end
	end
	local pw = dec("pressureWheels") or dec("hubWheels")
	if pw then
		local h = headerIndex(pw[1], { ["node1:"] = true, ["node2:"] = true, wheelDir = true })
		local list = {}
		for i, row in ipairs(pw) do
			if type(row) == "table" then
				if row[1] == nil then -- options
					local o, has = {}, false
					for k in pairs(WHEEL_OPTS) do if scalar(row[k]) then o[k] = row[k] has = true end end
					if has then list[#list + 1] = { o = o } end
				elseif i > 1 and type(row[1]) == "string" and h["node1:"] and h["node2:"] then
					local last = row[#row]
					list[#list + 1] = { w = row[1], a = row[h["node1:"]], b = row[h["node2:"]], d = tonumber(row[h.wheelDir or 0]) or 1,
						s = type(last) == "table" and (last["steerAxisUp:"] ~= nil or last.steerAxisUp ~= nil) or nil }
				end
			end
		end
		if #list > 0 then out.pw = list any = true end
	end
	local nodes = dec("nodes")
	if nodes and out.pw then
		local list = {}
		for _, row in ipairs(nodes) do
			if type(row) == "table" then
				if row[1] == nil then
					if row.nodeOffset ~= nil then list[#list + 1] = { off = vec3Raw(row.nodeOffset) } end
				elseif type(row[1]) == "string" and row[1] ~= "id" and scalar(row[2]) and scalar(row[3]) and scalar(row[4]) then
					list[#list + 1] = { row[1], scalar(row[2]), scalar(row[3]), scalar(row[4]) }
				end
			end
		end
		if #list > 0 then out.nodes = list end
	end
	return any and out or nil
end

-- positioned flexbodies of the wheels (rim, tire, hubcap): mesh, the wheel names from its groups ("tire_FR" -> FR),
-- pos / rot / scale as written (values may be "$var" / "$=" expressions, evaluated per config)
local WHEEL_GROUPS = { wheel = true, tire = true, tyre = true, hubcap = true, rim = true }
local function compactWheelFlex(text, filename)
	if not (string.find(text, "tire_", 1, true) or string.find(text, "wheel_", 1, true) or string.find(text, "hubcap_", 1, true)) then return nil end
	local ok, rows = pcall(jsonDecode, text, filename)
	checkBudget()
	if not ok or type(rows) ~= "table" then return nil end
	local list = {}
	for _, row in ipairs(rows) do
		if type(row) == "table" and type(row[1]) == "string" and row[1] ~= "mesh" and type(row[2]) == "table" then
			local opt = row[#row]
			opt = (type(opt) == "table" and opt[1] == nil and type(opt.pos) == "table") and opt or nil
			local sides, seen, tire = {}, {}, nil
			for _, g in ipairs(row[2]) do
				local pre, side = string.match(type(g) == "string" and g or "", "^(%a+)_(.+)$")
				pre = pre and string.lower(pre)
				if pre and WHEEL_GROUPS[pre] and not seen[side] then seen[side] = true sides[#sides + 1] = side end
				if pre == "tire" or pre == "tyre" then tire = true end
			end
			if opt and #sides > 0 then
				list[#list + 1] = { m = row[1], w = sides, p = vec3Raw(opt.pos), r = vec3Raw(opt.rot) or nil, s = vec3Raw(opt.scale) or nil, t = tire }
			end
		end
	end
	return #list > 0 and list or nil
end

local function addWheelParts(into, wheelSecs, filename, flexTexts)
	for partName, secs in pairs(wheelSecs) do
		local c = compactWheelPart(secs, filename)
		if c then into[partName] = c end
	end
	for partName, text in pairs(flexTexts or {}) do
		local fb = compactWheelFlex(text, filename)
		if fb then
			into[partName] = into[partName] or {}
			into[partName].fb = fb
		end
	end
end

-- the shared tire / wheel folders, once (disk cached, rebuilt when the game version or file count changes)
local function buildCommonWheelIndex()
	local files = {}
	for _, dir in ipairs(COMMON_WHEEL_DIRS) do
		for _, f in ipairs(FS:findFiles("/vehicles/common/" .. dir .. "/", "*.jbeam", -1, false, false) or {}) do files[#files + 1] = f end
		checkBudget()
	end
	local sig = tostring(beamng_version or "?") .. "|" .. #files .. "|" .. ENGINE_INDEX_VERSION
	local diskFile = CACHE_DIR .. "common_" .. CACHE_VERSION .. "_wheels.json"
	local cached = FS:fileExists(diskFile) and jsonReadFile(diskFile) or nil
	if cached and cached.sig == sig and type(cached.parts) == "table" then return cached.parts end
	local parts, flexTexts, wheelSecs = {}, {}, {}
	for _, filename in ipairs(files) do
		local text = readFile(filename)
		checkBudget()
		if text then
			table.clear(flexTexts) table.clear(wheelSecs)
			if extractFlexbodies(text, flexTexts, nil, wheelSecs) then addWheelParts(parts, wheelSecs, filename, flexTexts) end
		end
		text = nil
		checkBudget()
	end
	FS:directoryCreate(CACHE_DIR, true)
	jsonWriteFile(diskFile, { sig = sig, parts = parts }, false)
	log('I', 'MPProxyMeshGE', string.format("Indexed wheel and tire parts of %d shared jbeam files", #files))
	return parts
end

local function buildPartIndex(model)
	local diskFile = CACHE_DIR .. model .. "_parts_" .. CACHE_VERSION .. ".json"
	local files = FS:findFiles("/vehicles/" .. model .. "/", "*.jbeam", -1, false, false) or {}
	local sig = modelSignature(model)
	local cached = FS:fileExists(diskFile) and jsonReadFile(diskFile) or nil
	if cached and cached.sig == sig and type(cached.parts) == "table" and cached.engineV == ENGINE_INDEX_VERSION then
		engineIndex[model] = type(cached.engine) == "table" and cached.engine or {}
		wheelIndex[model] = type(cached.wheels) == "table" and cached.wheels or {}
		return cached.parts
	end

	local parts = {}
	local engine = {}
	local wheels = {}
	local flexTexts, sectionTexts, wheelSecs = {}, {}, {}
	-- engines and their sound sections often live in /vehicles/common/<model>/ (only those sections are read there)
	local commonFiles = FS:findFiles("/vehicles/common/" .. model .. "/", "*.jbeam", -1, false, false) or {}
	for _, filename in ipairs(commonFiles) do
		local text = readFile(filename)
		checkBudget()
		if text then -- engine / sound sections and the hubs, suspensions and their slots
			table.clear(flexTexts) table.clear(sectionTexts) table.clear(wheelSecs)
			if extractFlexbodies(text, flexTexts, sectionTexts, wheelSecs) then
				addEngineSections(engine, sectionTexts, filename)
				addWheelParts(wheels, wheelSecs, filename, flexTexts)
			end
		end
		text = nil
		checkBudget()
	end
	for _, filename in ipairs(files) do
		table.clear(flexTexts)
		table.clear(sectionTexts)
		table.clear(wheelSecs)
		local data = nil
		local text = readFile(filename)
		checkBudget()
		local hasSound = text and string.find(text, "soundConfig", 1, true)
		if text then
			if extractFlexbodies(text, flexTexts, hasSound and sectionTexts or nil, wheelSecs) then
				addEngineSections(engine, sectionTexts, filename)
				addWheelParts(wheels, wheelSecs, filename, flexTexts)
				data = {}
				for partName, arr in pairs(flexTexts) do
					local ok, rows = pcall(jsonDecode, arr, filename)
					if ok and type(rows) == "table" then data[partName] = { flexbodies = rows } end
					checkBudget()
				end
			else
				local ok, decoded = pcall(jsonDecode, text, filename) -- unusual file: whole decode (one step)
				data = ok and decoded or nil
			end
		end
		text = nil
		if type(data) == "table" then
			for partName, part in pairs(data) do
				if type(part) == "table" and type(part.flexbodies) == "table" then
					local list, offset = {}, false
					for _, row in ipairs(part.flexbodies) do
						if type(row) == "table" then
							if row[1] ~= nil then
								local mesh = row[1]
								if type(mesh) == "string" and mesh ~= "mesh" and not offset and not isWheelFlexRow(row) then list[#list + 1] = mesh end
							else
								offset = isOffsetModifier(row) -- positioned meshes (mirrored/moved) would be misplaced
							end
						end
					end
					if #list > 0 then parts[partName] = list end
				end
			end
		end
		checkBudget()
	end
	FS:directoryCreate(CACHE_DIR, true)
	jsonWriteFile(diskFile, { sig = sig, fileCount = #files, parts = parts, engine = engine, wheels = wheels, engineV = ENGINE_INDEX_VERSION }, false)
	engineIndex[model] = engine
	wheelIndex[model] = wheels
	return parts
end

-- ============= WHEEL PLACEMENT OF A CONFIG =============
-- Follows the jbeam loader: the part tree of the config is walked in slot order (child sections come after the
-- parent's), later node definitions replace earlier ones, a slot's nodeOffset moves the nodes of its subtree
-- (x away from the center line: posX + sign(posX) * x, lua/common/jbeam/utils.lua), pressureWheels options apply
-- to the wheel rows after them, and each wheel is placed like lua/common/jbeam/sections/wheelTypes/pressureWheels.lua:
-- midpoint of node1/node2 (or offsetFromNode), moved by wheelOffset along the axis, tireWidth wide, radius.
local WHEEL_VERSION = 2 -- 2: named fields (mixed tables did not survive the json round trip), rim / tire meshes
local MAX_WHEEL_MESHES = 6 -- per wheel

-- jbeam values: numbers, "$var", or "$=expression" (arithmetic, comparisons, and/or/not, case(c1, v1, ..., default),
-- min/max/abs...). Unknown variables (also "$components.x") become nil like in the game's evaluator.
local EXPR_NAMES = { ["nil"] = true, ["true"] = true, ["false"] = true, ["and"] = true, ["or"] = true, ["not"] = true,
	__case = true, min = true, max = true, abs = true, floor = true, ceil = true, sqrt = true, clamp = true }
local EXPR_ENV = { min = math.min, max = math.max, abs = math.abs, floor = math.floor, ceil = math.ceil, sqrt = math.sqrt,
	clamp = function(x, a, b) return math.min(math.max(x, a), b) end,
	__case = function(...)
		local n = select("#", ...)
		local args = { ... }
		for i = 1, n - 1, 2 do if args[i] then return args[i + 1] end end
		if n % 2 == 1 then return args[n] end
		return nil
	end }
local exprCache = {}

local function evalVal(v, vars)
	if type(v) == "number" then return v end
	if type(v) ~= "string" then return nil end
	if string.sub(v, 1, 2) == "$=" then
		local expr = string.gsub(string.sub(v, 3), "%$([%w_%.]+)", function(n)
			local x = tonumber(vars["$" .. n])
			return x and string.format("(%.17g)", x) or "nil"
		end)
		expr = string.gsub(expr, "!=", "~=")
		expr = string.gsub(expr, "&&", " and ")
		expr = string.gsub(expr, "||", " or ")
		expr = string.gsub(expr, "case%(", "__case(")
		for name in string.gmatch(expr, "[%a_][%w_]*") do
			if not EXPR_NAMES[name] and not string.match(name, "^[eE]%d*$") then return nil end
		end
		if string.find(expr, "[^%w_%.%+%-%*/%(%)%s,<>=~^%%]") then return nil end
		local fn = exprCache[expr]
		if fn == nil then
			fn = loadstring("return " .. expr) or false
			if fn then setfenv(fn, EXPR_ENV) end
			exprCache[expr] = fn
		end
		if not fn then return nil end
		local ok, r = pcall(fn)
		return ok and tonumber(r) or nil
	elseif string.sub(v, 1, 1) == "$" then
		return tonumber(vars[v])
	end
	return tonumber(v)
end

local function resolveWheels(job)
	local vcf = job.vcf
	if type(vcf) ~= "table" or type(vcf.parts) ~= "table" then return nil, "no config data" end
	if commonWheelIndex == nil then
		setPhase("wheel index")
		commonWheelIndex = buildCommonWheelIndex()
	end
	setPhase("wheels")
	local idx, cidx = wheelIndex[job.model] or {}, commonWheelIndex or {}
	local function get(name) return idx[name] or cidx[name] end
	local vars = {}
	for _, partName in ipairs(job.parts) do
		local d = get(partName)
		if d and d.vars then for k, v in pairs(d.vars) do vars[k] = v end end
	end
	if type(vcf.vars) == "table" then for k, v in pairs(vcf.vars) do vars[k] = v end end
	local nodes, items, visited, flex = {}, {}, {}, {}
	local function visit(name, off, path, depth)
		if depth > 30 or visited[name] then return end
		visited[name] = true
		local d = get(name)
		if not d then return end
		if d.nodes then
			local cur = off
			for _, r in ipairs(d.nodes) do
				if r.off ~= nil then cur = r.off or off
				else nodes[r[1]] = { r[2], r[3], r[4], cur } end
			end
		end
		if d.pw then for _, it in ipairs(d.pw) do items[#items + 1] = it end end
		if d.fb then for _, fb in ipairs(d.fb) do flex[#flex + 1] = { fb, off } end end
		if d.slots then
			for _, sl in ipairs(d.slots) do
				local p = path .. sl.n .. "/"
				local child = vcf.parts[p] or vcf.parts[sl.n] or vcf.parts[sl.t]
				if type(child) == "string" and child ~= "" then visit(child, sl.o or off, p, depth + 1) end
			end
		end
		checkBudget()
	end
	visit(vcf.mainPartName or job.model, nil, "/", 0)
	local function moved(x, y, z, o)
		if o then
			local ox, oy, oz = evalVal(o[1], vars) or 0, evalVal(o[2], vars) or 0, evalVal(o[3], vars) or 0
			x = x + (x > 0 and 1 or (x < 0 and -1 or 0)) * ox
			y, z = y + oy, z + oz
		end
		return x, y, z
	end
	local function nodePos(name)
		local n = nodes[name]
		if not n then return nil end
		local x, y, z = evalVal(n[1], vars), evalVal(n[2], vars), evalVal(n[3], vars)
		if not (x and y and z) then return nil end
		return moved(x, y, z, n[4])
	end
	local opts, wheels, wheelAt = {}, {}, {}
	for _, it in ipairs(items) do
		if it.o then for k, v in pairs(it.o) do opts[k] = v end
		elseif it.w then
			local x1, y1, z1 = nodePos(it.a)
			local x2, y2, z2 = nodePos(it.b)
			if x1 and x2 then
				local ax, ay, az = x2 - x1, y2 - y1, z2 - z1
				local len = math.sqrt(ax * ax + ay * ay + az * az)
				if len > 1e-4 then
					ax, ay, az = ax / len, ay / len, az / len
					local hubWidth = evalVal(opts.hubWidth, vars) or len
					local mx, my, mz = (x1 + x2) * 0.5, (y1 + y2) * 0.5, (z1 + z2) * 0.5
					local ofn = evalVal(opts.offsetFromNode, vars)
					if ofn == 1 then mx, my, mz = x1 + ax * hubWidth * 0.5, y1 + ay * hubWidth * 0.5, z1 + az * hubWidth * 0.5
					elseif ofn == 2 then mx, my, mz = x2 - ax * hubWidth * 0.5, y2 - ay * hubWidth * 0.5, z2 - az * hubWidth * 0.5 end
					local wo = evalVal(opts.wheelOffset, vars)
					if wo then mx, my, mz = mx + ax * wo, my + ay * wo, mz + az * wo end
					local radius = evalVal(opts.radius, vars) or evalVal(opts.hubRadius, vars) or 0.5
					local width = evalVal(opts.tireWidth, vars) or hubWidth
					-- steered: rows with a steering axis, else the front wheels by name (FR, FL, F2R...)
					local steered = it.s or (type(it.w) == "string" and string.sub(it.w, 1, 1) == "F")
					local at = wheelAt[it.w] or (#wheels + 1) -- a later row of the same wheel replaces it (like the loader)
					wheelAt[it.w] = at
					wheels[at] = { x = mx, y = my, z = mz, ax = ax, ay = ay, az = az, r = radius, wd = width, s = steered or nil, n = it.w }
				end
			end
		end
	end
	-- rim / tire / hubcap meshes: flexbody pos moved like the part's nodes (same slot nodeOffset), stored relative
	-- to the wheel center, so a wheel object turns and rolls around its own origin
	local byName = {}
	for _, w in ipairs(wheels) do if type(w.n) == "string" then byName[w.n] = w end end
	for _, it in ipairs(flex) do
		local fb, off = it[1], it[2]
		local w = nil
		for _, side in ipairs(fb.w or {}) do w = w or byName[side] end
		local p = fb.p
		local lm = type(fb.m) == "string" and string.lower(fb.m) or ""
		local hidden = string.find(lm, "brake", 1, true) or string.find(lm, "disc", 1, true) or string.find(lm, "caliper", 1, true)
		if w and type(fb.m) == "string" and p and not hidden then -- brake parts sit behind the rim
			local x, y, z = evalVal(p[1], vars), evalVal(p[2], vars), evalVal(p[3], vars)
			if x and y and z then
				x, y, z = moved(x, y, z, off)
				local r, sc = fb.r or {}, fb.s or {}
				w.m = w.m or {}
				local dup = false
				for _, e in ipairs(w.m) do if e[1] == fb.m then dup = true end end
				if not dup and #w.m < MAX_WHEEL_MESHES then
					if fb.t then w.mt = true end -- has a tire mesh (else the drawn cylinder stays as the tire)
					w.m[#w.m + 1] = { fb.m, x - w.x, y - w.y, z - w.z, evalVal(r[1], vars) or 0, evalVal(r[2], vars) or 0, evalVal(r[3], vars) or 0,
						evalVal(sc[1], vars) or 1, evalVal(sc[2], vars) or 1, evalVal(sc[3], vars) or 1 }
				end
			end
		end
	end
	return wheels
end

-- keeps the wheels that make sense next to the body bounds; nil if none left
local function checkWheels(wheels, shape)
	if type(wheels) ~= "table" then return nil end
	local out = {}
	for _, w in ipairs(wheels) do
		local ok = w.r >= 0.1 and w.r <= 1.6 and w.wd >= 0.04 and w.wd <= 1.5
		if ok and shape.minX then
			ok = w.x > shape.minX - 1 and w.x < shape.maxX + 1 and w.y > shape.minY - 1 and w.y < shape.maxY + 1
				and w.z > shape.minZ - 1 and w.z < shape.maxZ + 1
		end
		if ok then out[#out + 1] = w end
	end
	return #out > 0 and out or nil
end

local function logWheels(job, wheels, note)
	if wheels then
		local rmin, rmax, wmin, wmax, meshes, names = math.huge, 0, math.huge, 0, 0, {}
		for _, w in ipairs(wheels) do
			rmin, rmax = math.min(rmin, w.r), math.max(rmax, w.r)
			wmin, wmax = math.min(wmin, w.wd), math.max(wmax, w.wd)
			for _, e in ipairs(w.m or {}) do meshes = meshes + 1 if not names[e[1]] then names[e[1]] = true names[#names + 1] = e[1] end end
		end
		log('I', 'MPProxyMeshGE', string.format("Proxy wheels for %s/%s: %d wheels, radius %.2f-%.2f m, width %.2f-%.2f m, %d rim/tire meshes (%s) (source: jbeam%s)",
			job.model, string.sub(job.key, -16), #wheels, rmin, rmax, wmin, wmax, meshes, table.concat(names, ", ", 1, math.min(#names, 6)), note or ""))
	else
		log('I', 'MPProxyMeshGE', string.format("Proxy wheels for %s/%s: estimated from the body bounds (source: estimate, %s)",
			job.model, string.sub(job.key, -16), note or "no wheel rows resolved"))
	end
end

-- ============= ENGINE SOUND OF A CONFIG =============
-- Same lookup as combustionEngine.lua init: the mainEngine device names its sound sections (soundConfig = intake,
-- soundConfigExhaust = exhaust), a section gives sampleFolder (default art/sound/blends/) .. sampleName ..
-- ".sfxBlend2D.json", whose eventName is the FMOD event. The exhaust is used when it resolves, else the intake.
local function blendEvent(folder, name)
	if type(name) ~= "string" then return nil end
	folder = folder or "art/sound/blends/"
	if string.sub(folder, 1, 1) ~= "/" then folder = "/" .. folder end
	local base = folder .. name .. ".sfxBlend"
	local data = jsonReadFile(base .. "2D.json") or jsonReadFile(base .. "2d.json")
	local ev = type(data) == "table" and data.eventName
	return type(ev) == "string" and ev ~= "" and ev or nil
end

local function resolveSound(job, cachedNote)
	if type(partIndex[job.model]) ~= "table" then
		setPhase("part index")
		partIndex[job.model] = buildPartIndex(job.model)
	end
	setPhase("engine sound")
	local index = engineIndex[job.model] or {}
	local me, sections = {}, {}
	for _, partName in ipairs(job.parts) do
		local e = index[partName]
		if e then
			for key, sec in pairs(e) do
				if key == "mainEngine" then for k, v in pairs(sec) do me[k] = v end
				else sections[key] = sections[key] or {} for k, v in pairs(sec) do sections[key][k] = v end end
			end
		end
	end
	local sound = { source = "fallback" }
	for _, which in ipairs({ { "soundConfigExhaust", "exhaust" }, { "soundConfig", "intake" } }) do
		local sec = sections[me[which[1]] or ""]
		local ev = sec and blendEvent(sec.sampleFolder, sec.sampleName)
		if ev then
			sound = { source = "jbeam", event = ev, kind = which[2], sample = sec.sampleName,
				mainGain = sec.mainGain, onLoadGain = sec.onLoadGain, offLoadGain = sec.offLoadGain,
				muffling = which[2] == "exhaust" and sec.exhaustAudioMufflingBaseCoef or sec.intakeMuffling }
			break
		end
	end
	sound.idleRPM, sound.maxRPM = tonumber(me.idleRPM), tonumber(me.revLimiterRPM) or tonumber(me.maxRPM)
	sound.diesel = me.requiredEnergyType == "diesel" or nil
	log('I', 'MPProxyMeshGE', string.format("Proxy engine sound for %s/%s: %s (source: %s%s%s)", job.model, string.sub(job.key, -16),
		sound.event or "type mapping", sound.source, sound.sample and (", " .. sound.kind .. " " .. sound.sample) or "", cachedNote or ""))
	return sound
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

-- triangles of a geometry block (triangles / polylist / polygons primitives, polygons counted as one each)
local function countTriangles(block)
	local n = 0
	for tag, count in string.gmatch(block, "<(%a+)[^>]-count=\"(%d+)\"") do
		if tag == "triangles" or tag == "polylist" or tag == "polygons" or tag == "tristrips" then n = n + (tonumber(count) or 0) end
	end
	return n
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
								gb.tris = countTriangles(block)
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
						checkBudget()
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
	local function addNode(block, url, name)
		local nb = {math.huge, math.huge, math.huge, -math.huge, -math.huge, -math.huge}
		mergeNodeBBox(nb, block, geomBoxes[url])
		mergeNodeBBox(bbox, block, geomBoxes[url])
		local size = nb[1] <= nb[4] and math.sqrt((nb[4]-nb[1])^2 + (nb[5]-nb[2])^2 + (nb[6]-nb[3])^2) or 0
		nodes[#nodes + 1] = { block = block .. "\n", url = url, name = name, tris = geomBoxes[url] and geomBoxes[url].tris or 0, size = size, mats = {} }
		collectMaterials(block, nodes[#nodes].mats)
	end
	local ok = scanDae(filename, keepByName, function(block, name, url)
		if not wanted[name] then return end
		if keptIds[url] then addNode(block, url, name)
		elseif not missing[url] then missing[url] = { block, name } missingCount = missingCount + 1 end
	end, false, header, geoms, keptIds, geomBoxes)
	if not ok then return nil end
	if missingCount > 0 then
		scanDae(filename, function(id) return missing[id] ~= nil and not keptIds[id] end, function() end, true, {}, geoms, keptIds, geomBoxes)
		for url, m in pairs(missing) do
			if keptIds[url] then addNode(m[1], url, m[2]) end
		end
	end
	if #nodes == 0 then return nil end
	local geomById = {}
	for _, g in ipairs(geoms) do
		local id = string.match(g, '^<geometry id="([^"]*)"')
		if id then geomById[id] = g end
	end
	return { header = table.concat(header), geomById = geomById, nodes = nodes }
end

-- keeps the biggest parts (by size) that fit into the triangle budget, over all files of a mesh set, and turns
-- the parts into the plain lists mergeDae wants (only geometries some kept node uses)
-- marks n.keep on the nodes that pass filter and fit the budget (biggest first); returns kept count and triangles
local function selectNodes(all, filter, budget, minSize)
	table.sort(all, function(a, b) return a.size > b.size end)
	local sum, kept = 0, 0
	for _, n in ipairs(all) do
		n.keep = false
		if (not filter or filter(n)) and n.size >= (minSize or 0) and (budget <= 0 or sum + n.tris <= budget or sum == 0) then
			n.keep = true
			sum, kept = sum + n.tris, kept + 1
		end
	end
	return kept, sum
end

-- the kept nodes of one file as the plain lists mergeDae wants (only geometries some kept node uses)
local function keptLists(part, mats)
	local nodes, geoms, used = {}, {}, {}
	for _, n in ipairs(part.nodes) do
		if n.keep then
			nodes[#nodes + 1] = n.block
			for m in pairs(n.mats) do mats[m] = true end
			if not used[n.url] and part.geomById[n.url] then used[n.url] = true geoms[#geoms + 1] = part.geomById[n.url] end
		end
	end
	return { header = part.header, nodes = nodes, geoms = geoms }
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
		for _, g in ipairs(part.geoms) do out[#out + 1] = prefixIds(g, pre, true) out[#out + 1] = "\n" checkBudget() end
	end
	out[#out + 1] = '</library_geometries>\n<library_visual_scenes>\n<visual_scene id="Scene" name="Scene">\n'
	for i, part in ipairs(list) do
		local pre = "f" .. i .. "_"
		for _, n in ipairs(part.nodes) do out[#out + 1] = prefixIds(n, pre, false) end
		checkBudget()
	end
	out[#out + 1] = '</visual_scene>\n</library_visual_scenes>\n<scene>\n<instance_visual_scene url="#Scene"/>\n</scene>\n</COLLADA>\n'
	return table.concat(out)
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
			checkBudget()
		end
	end
end

-- ============= REAL WHEEL MESHES =============
-- Each wheel of a config (rim, tire, hubcap flexbodies from resolveWheels) becomes a small .dae of its own: the
-- meshes are copied from the shared /vehicles/common/ (or the model's) .dae files with the jbeam flexbody
-- transform baked into their node matrix, relative to the wheel center. Wheels with the same meshes and
-- transform share the file (left and right differ by the flexbody rotation), so the engine imports each once.
-- They are built after the body meshes, when no body job waits.
local wheelFiles = {}     -- [wheel .dae path] = "queued" | "ready" | "failed"
local wheelJobs = {}      -- FIFO of wheel mesh builds
local wheelMeshFile = nil -- [mesh name] = source .dae where it was found (disk cached)
local wheelDaeList = {}   -- [model] = candidate source .dae files
local wheelMissing = {}   -- [mesh name] = true: searched this session without finding it
local WHEEL_FILES_CACHE = CACHE_DIR .. "wheelmeshes_" .. CACHE_VERSION .. "_files.json"
local MAX_WHEEL_FILE_TRIES = 12 -- source files scanned per mesh name that is not in the cache yet

local function wheelPath(w)
	if w.path ~= nil then return w.path end
	if type(w.m) ~= "table" or #w.m == 0 then w.path = false return false end
	local list = {}
	for _, e in ipairs(w.m) do
		list[#list + 1] = string.format("%s|%.3f|%.3f|%.3f|%.1f|%.1f|%.1f|%.3f|%.3f|%.3f", tostring(e[1]), e[2], e[3], e[4], e[5], e[6], e[7], e[8], e[9], e[10])
	end
	table.sort(list)
	w.path = CACHE_DIR .. "wheel_" .. CACHE_VERSION .. "_" .. hashString(table.concat(list, ";")) .. ".dae"
	return w.path
end

local function queueWheelMeshes(shape, model)
	if not cfg.realWheels or type(shape.wheels) ~= "table" then return end
	for _, w in ipairs(shape.wheels) do
		local path = wheelPath(w)
		if path and wheelFiles[path] == nil then
			if FS:fileExists(path) then wheelFiles[path] = "ready"
			else
				wheelFiles[path] = "queued"
				wheelJobs[#wheelJobs + 1] = { wheelJob = true, key = path, model = model, m = w.m }
			end
		end
	end
end

local function wheelCandidates(model)
	local list = wheelDaeList[model]
	if list then return list end
	list = {}
	for _, d in ipairs({ "/vehicles/common/wheels/", "/vehicles/common/tires/", "/vehicles/common/hubcaps/", "/vehicles/common/wheels_square/",
		"/vehicles/common/" .. model .. "/", "/vehicles/" .. model .. "/" }) do
		for _, f in ipairs(FS:findFiles(d, "*.dae", -1, false, false) or {}) do list[#list + 1] = f end
		checkBudget()
	end
	wheelDaeList[model] = list
	return list
end

-- how well a file path matches a mesh name: longest common prefix with one of its folder / file names
-- ("steelwheel_02a_16x8" -> .../steelwheel_02a/steelwheel_02a.dae, "tire_01a_18x9_26" -> tires/tires.dae)
local function nameScore(mesh, path)
	local m, best = string.lower(mesh), 0
	for comp in string.gmatch(string.lower(path), "[^/]+") do
		comp = string.gsub(comp, "%.dae$", "")
		local n = 0
		for i = 1, math.min(#m, #comp) do
			if string.byte(m, i) == string.byte(comp, i) then n = i else break end
		end
		if n > best then best = n end
	end
	return best
end

-- the node block with the flexbody transform (scale, rotation: euler +Z +X +Y intrinsic, then position relative to
-- the wheel center) applied in front of its own matrix; nil for nodes using other transform elements
local function bakeNode(block, e, unit)
	if string.find(block, "<translate", 1, true) or string.find(block, "<rotate", 1, true) or string.find(block, "<scale", 1, true) then return nil end
	local m = {}
	local mtx = string.match(block, "<matrix[^>]*>([^<]*)</matrix>")
	if mtx then for num in string.gmatch(mtx, "%S+") do m[#m + 1] = tonumber(num) or 0 end end
	if #m ~= 16 then m = {1,0,0,0, 0,1,0,0, 0,0,1,0, 0,0,0,1} end
	local rx, ry, rz = math.rad(e[5]), math.rad(e[6]), math.rad(e[7])
	local cx, sx, cy, sy, cz, sz = math.cos(rx), math.sin(rx), math.cos(ry), math.sin(ry), math.cos(rz), math.sin(rz)
	-- R = Rz * Rx * Ry
	local zx = { {cz, -sz * cx, sz * sx}, {sz, cz * cx, -cz * sx}, {0, sx, cx} }
	local R = {}
	for i = 1, 3 do
		R[i] = { zx[i][1] * cy - zx[i][3] * sy, zx[i][2], zx[i][1] * sy + zx[i][3] * cy }
	end
	local sc = { e[8], e[9], e[10] }
	local t = { e[2] / unit, e[3] / unit, e[4] / unit } -- node matrices are in file units
	local B = {}
	for i = 1, 3 do B[i] = { R[i][1] * sc[1], R[i][2] * sc[2], R[i][3] * sc[3], t[i] } end
	B[4] = { 0, 0, 0, 1 }
	local out = {}
	for i = 1, 4 do
		for j = 1, 4 do
			local v = 0
			for k = 1, 4 do v = v + B[i][k] * m[(k - 1) * 4 + j] end
			out[#out + 1] = string.format("%.7g", v)
		end
	end
	local newMtx = '<matrix sid="transform">' .. table.concat(out, " ") .. '</matrix>'
	if mtx then
		return (string.gsub(block, "<matrix[^>]*>[^<]*</matrix>", function() return newMtx end, 1))
	end
	return (string.gsub(block, "^(<node[^>]*>)", function(open) return open .. newMtx end, 1))
end

local function loadMaterialsNear(file)
	local dir = string.match(file, "^(.*/)") or "/"
	if materialsLoaded["dir:" .. dir] then return end
	materialsLoaded["dir:" .. dir] = true
	for _, mf in ipairs(FS:findFiles(dir, "*materials.json", 0, true, false) or {}) do
		loadJsonMaterialsFile(mf)
		coroutine.yield()
	end
end

local function runWheelJob(job)
	setPhase("wheel meshes")
	if wheelMeshFile == nil then
		local c = FS:fileExists(WHEEL_FILES_CACHE) and jsonReadFile(WHEEL_FILES_CACHE) or nil
		wheelMeshFile = (type(c) == "table" and c.sig == tostring(beamng_version or "?") and type(c.files) == "table") and c.files or {}
	end
	local need = {}
	for _, e in ipairs(job.m) do need[e[1]] = true end
	local found, scanned, learned = {}, {}, false
	local function scan(file, names)
		if scanned[file] then return end
		scanned[file] = true
		local part = filterDae(file, names, {math.huge, math.huge, math.huge, -math.huge, -math.huge, -math.huge}, nil)
		coroutine.yield()
		if not part then return end
		for _, n in ipairs(part.nodes) do
			if need[n.name] and not found[n.name] then
				found[n.name] = { part = part, node = n, file = file }
				if wheelMeshFile[n.name] ~= file then wheelMeshFile[n.name] = file learned = true end
			end
		end
	end
	local byFile = {}
	for name in pairs(need) do
		local f = wheelMeshFile[name]
		if f then byFile[f] = byFile[f] or {} byFile[f][name] = true end
	end
	for f, names in pairs(byFile) do if FS:fileExists(f) then scan(f, names) end end
	for name in pairs(need) do
		if not found[name] and not wheelMissing[name] then
			local rest = {}
			for n2 in pairs(need) do if not found[n2] then rest[n2] = true end end
			local scored = {}
			for _, f in ipairs(wheelCandidates(job.model)) do
				if not scanned[f] then scored[#scored + 1] = { f = f, s = nameScore(name, f) } end
			end
			table.sort(scored, function(a, b) return a.s > b.s end)
			checkBudget()
			for i = 1, math.min(#scored, MAX_WHEEL_FILE_TRIES) do
				if found[name] then break end
				scan(scored[i].f, rest)
			end
			if not found[name] then wheelMissing[name] = true end
		end
	end
	if learned then
		FS:directoryCreate(CACHE_DIR, true)
		jsonWriteFile(WHEEL_FILES_CACHE, { sig = tostring(beamng_version or "?"), files = wheelMeshFile }, false)
	end
	local groups, order, sig0, mats, used, names = {}, {}, nil, {}, 0, {}
	for _, e in ipairs(job.m) do
		local fnd = found[e[1]]
		local part = fnd and fnd.part
		local gsig = part and daeSignature(part.header)
		local up = part and (string.match(part.header, "<up_axis>(.-)</up_axis>") or "Z_UP")
		local unit = part and tonumber(string.match(part.header, '<unit[^>]-meter="([^"]+)"') or "1") or 1
		if unit <= 0 then unit = 1 end
		sig0 = sig0 or gsig
		local baked = part and up == "Z_UP" and gsig == sig0 and bakeNode(fnd.node.block, e, unit)
		if baked then
			local g = groups[part]
			if not g then g = { header = part.header, nodes = {}, geoms = {}, used = {}, file = fnd.file } groups[part] = g order[#order + 1] = g end
			g.nodes[#g.nodes + 1] = baked
			collectMaterials(baked, mats)
			local url = fnd.node.url
			if not g.used[url] and part.geomById[url] then g.used[url] = true g.geoms[#g.geoms + 1] = part.geomById[url] end
			used = used + 1
			names[#names + 1] = e[1]
		end
	end
	if used == 0 then
		wheelFiles[job.key] = "failed"
		log('W', 'MPProxyMeshGE', string.format("Proxy wheel mesh for %s: none of %d meshes found or usable (%s), drawn wheels stay", job.model, #job.m, job.m[1] and job.m[1][1] or "?"))
		return
	end
	setPhase("wheel merge")
	FS:directoryCreate(CACHE_DIR, true)
	local text = mergeDae(order)
	coroutine.yield()
	if not writeFile(job.key, text) then wheelFiles[job.key] = "failed" return end
	text = nil
	setPhase("materials")
	for _, g in ipairs(order) do loadMaterialsNear(g.file) end
	local matList = {}
	for name in pairs(mats) do matList[#matList + 1] = name end
	ensureMaterials(matList)
	wheelFiles[job.key] = "ready"
	log('I', 'MPProxyMeshGE', string.format("Proxy wheel mesh %s for %s: %d of %d meshes (%s) from %d files",
		string.match(job.key, "([^/]+)$"), job.model, used, #job.m, table.concat(names, ", "), #order))
end

local function runJob(job)
	local shape = shapes[job.key]
	shape.state = "building"
	setPhase("cache check")
	local metaFile = CACHE_DIR .. job.key .. ".json"
	local sig = modelSignature(job.model)
	local meta = FS:fileExists(metaFile) and jsonReadFile(metaFile) or nil
	if meta and meta.sig == sig and meta.bodyV == BODY_VERSION and type(meta.paths) == "table" and #meta.paths > 0 and type(meta.tiers) == "table" then
		local allExist = true
		for _, p in ipairs(meta.paths) do if not FS:fileExists(p) then allExist = false end end
		if allExist then
			if type(meta.sound) ~= "table" then
				meta.sound = resolveSound(job)
				jsonWriteFile(metaFile, meta, false)
			else
				log('I', 'MPProxyMeshGE', string.format("Proxy engine sound for %s/%s: %s (source: %s, cached)", job.model, string.sub(job.key, -16), meta.sound.event or "type mapping", tostring(meta.sound.source)))
			end
			shape.sound = meta.sound
			finishBBox(shape, meta.bbox, job.model)
			if meta.wheelV ~= WHEEL_VERSION then
				local w, why = resolveWheels(job)
				meta.wheels = checkWheels(w, shape) or false
				meta.wheelV = WHEEL_VERSION
				logWheels(job, meta.wheels or nil, why)
				jsonWriteFile(metaFile, meta, false)
			elseif meta.wheels then
				logWheels(job, meta.wheels, ", cached")
			end
			shape.wheels = meta.wheels or nil
			setPhase("materials")
			loadModelMaterials(job.model)
			ensureMaterials(meta.materials)
			shape.paths = meta.paths
			shape.tiers = meta.tiers
			shape.fromCache = true -- built in an earlier session
			finishBBox(shape, meta.bbox, job.model)
			shape.state = "ready"
			return
		end
	end

	shape.sound = resolveSound(job)
	setPhase("cache check")
	local index = partIndex[job.model]
	local wanted, count = {}, 0
	for _, partName in ipairs(job.parts) do
		for _, mesh in ipairs(index[partName] or {}) do
			if count < MAX_MESHES and not wanted[mesh] then -- the full tier keeps all, the others filter
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
	local meshKey = job.model .. "_" .. CACHE_VERSION .. "_m" .. hashString(job.model .. "|" .. cfg.triBudget .. "|" .. table.concat(meshList, ","))
	local meshMetaFile = CACHE_DIR .. meshKey .. ".json"
	if count > 0 and FS:fileExists(meshMetaFile) then
		local mm = jsonReadFile(meshMetaFile)
		local ok = mm and mm.sig == sig and type(mm.paths) == "table" and #mm.paths > 0 and type(mm.tiers) == "table"
		if ok then for _, p in ipairs(mm.paths) do if not FS:fileExists(p) then ok = false end end end
		if ok then
			setPhase("materials")
			loadModelMaterials(job.model)
			ensureMaterials(mm.materials)
			mm.sound = shape.sound -- per config, the mesh set is shared by configs with other engines
			finishBBox(shape, mm.bbox, job.model)
			local w, why = resolveWheels(job)
			shape.wheels = checkWheels(w, shape)
			logWheels(job, shape.wheels, why)
			mm.wheels, mm.wheelV, mm.bodyV = shape.wheels or false, WHEEL_VERSION, BODY_VERSION
			jsonWriteFile(metaFile, mm, false)
			mm.sound, mm.wheels, mm.wheelV, mm.bodyV = nil, nil, nil, nil
			shape.paths = mm.paths
			shape.tiers = mm.tiers
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
	setPhase("dae scan")
	for _, dae in ipairs(daes) do
		local part = filterDae(dae, wanted, bbox, nil)
		if part then
			local gsig = daeSignature(part.header)
			if not groups[gsig] then groups[gsig] = {} groupOrder[#groupOrder + 1] = gsig end
			table.insert(groups[gsig], part)
		end
		coroutine.yield()
	end
	local all = {}
	for _, gsig in ipairs(groupOrder) do for _, part in ipairs(groups[gsig]) do for _, n in ipairs(part.nodes) do all[#all + 1] = n end end end
	local maxSize = 0
	for _, n in ipairs(all) do if n.size > maxSize then maxSize = n.size end end
	local function visible(n) return isWantedMesh(n.name or "") end
	local selections = {
		[TIER_FULL] = function() return selectNodes(all, nil, 0, 0) end,
		[TIER_PARTS] = function() return selectNodes(all, visible, cfg.triBudget, 0) end,
		[TIER_SHELL] = function() return selectNodes(all, visible, math.max(SHELL_MIN_TRIS, math.floor(cfg.triBudget / 6)), maxSize * 0.25) end,
	}
	local tiers, prevKept, tierInfo = {}, nil, {}
	for t = 1, 3 do
		local kept, tris = selections[t]()
		if kept == 0 and t > 1 then tiers[t] = tiers[t - 1] -- nothing left for this tier, reuse the one before
		elseif kept == prevKept and t > 1 then tiers[t] = tiers[t - 1] -- same selection, same files
		else
			tiers[t] = {}
			for g, gsig in ipairs(groupOrder) do
				local lists = {}
				for _, part in ipairs(groups[gsig]) do
					local l = keptLists(part, mats)
					if #l.nodes > 0 then lists[#lists + 1] = l end
				end
				if #lists > 0 then
					local out = CACHE_DIR .. meshKey .. "_t" .. t .. "_" .. g .. ".dae"
					setPhase("merge")
					local text = mergeDae(lists)
					coroutine.yield()
					setPhase("write") -- table.concat + writeFile of one file: one step, measured as the worst step
					if writeFile(out, text) then tiers[t][#tiers[t] + 1] = out paths[#paths + 1] = out end
					text = nil
					coroutine.yield()
				end
			end
		end
		prevKept = kept
		tierInfo[#tierInfo + 1] = string.format("%d parts/%d tris", kept, tris)
	end
	log('I', 'MPProxyMeshGE', string.format("Proxy mesh tiers for %s: full %s, parts %s, shell %s", job.model, tierInfo[1], tierInfo[2], tierInfo[3]))
	if #paths == 0 then
		log('W', 'MPProxyMeshGE', string.format("No proxy mesh for %s: %d wanted meshes not found in %d .dae files of /vehicles/%s/", job.model, count, #daes, job.model))
		shape.state = "failed" shape.reason = "meshes not found in the .dae files"
		return
	end
	log('I', 'MPProxyMeshGE', string.format("Proxy mesh for %s ready (%d meshes, %d files)", job.model, count, #paths))
	setPhase("materials")
	loadModelMaterials(job.model)
	local matList = {}
	for name in pairs(mats) do matList[#matList + 1] = name end
	table.sort(matList)
	ensureMaterials(matList)
	local metaData = { sig = sig, paths = paths, tiers = tiers, bbox = validBBox(bbox) and bbox or nil, materials = matList }
	jsonWriteFile(meshMetaFile, metaData, false)
	finishBBox(shape, bbox, job.model)
	local wl, why = resolveWheels(job)
	shape.wheels = checkWheels(wl, shape)
	logWheels(job, shape.wheels, why)
	metaData.sound, metaData.wheels, metaData.wheelV, metaData.bodyV = shape.sound, shape.wheels or false, WHEEL_VERSION, BODY_VERSION
	jsonWriteFile(metaFile, metaData, false)
	shape.paths = paths
	shape.tiers = tiers
	shape.state = "ready"
end

local function stepJobs()
	if not currentJob then
		local job = table.remove(jobs, 1)
		if not job and #wheelJobs > 0 then job = table.remove(wheelJobs, 1) end
		if not job and cfg.prebuild then
			job = table.remove(prebuildJobs, 1)
			while job and shapes[job.key] and shapes[job.key].state ~= "queued" do job = table.remove(prebuildJobs, 1) end
		end
		if not job then return end
		currentJob = { job = job, co = coroutine.create(job.wheelJob and runWheelJob or runJob), started = clock, maxStepMs = 0, maxStepPhase = "", frames = 0,
			totalMs = 0, worstFrameMs = 0, phaseMs = {} }
		jobPhase = "start"
	end
	budgetTimer = TIMER()
	currentJob.frames = currentJob.frames + 1
	local cj = currentJob
	local frameMs = 0
	while currentJob and budgetTimer:stop() < frameBudget do
		local before = budgetTimer:stop()
		local phase = jobPhase
		local ok, err = coroutine.resume(currentJob.co, currentJob.job)
		local stepMs = budgetTimer:stop() - before
		frameMs = frameMs + stepMs
		cj.totalMs = cj.totalMs + stepMs
		cj.phaseMs[phase] = (cj.phaseMs[phase] or 0) + stepMs
		if stepMs > cj.maxStepMs then cj.maxStepMs, cj.maxStepPhase = stepMs, phase end
		if frameMs > cj.worstFrameMs then cj.worstFrameMs = frameMs end
		if not ok then
			log('E', 'MPProxyMeshGE', "Building proxy mesh for "..tostring(currentJob.job.model)..(currentJob.job.wheelJob and " (wheels)" or "").." failed: "..tostring(err))
			if currentJob.job.wheelJob then wheelFiles[currentJob.job.key] = "failed"
			elseif shapes[currentJob.job.key] then shapes[currentJob.job.key].state = "failed" end
			currentJob = nil
		elseif coroutine.status(currentJob.co) == "dead" then
			local sh = not cj.job.wheelJob and shapes[cj.job.key] or nil
			if sh and sh.state == "ready" then queueWheelMeshes(sh, cj.job.model) end
			local phases = {}
			for name, ms in pairs(cj.phaseMs) do if ms >= 0.05 then phases[#phases + 1] = string.format("%s %.1f", name, ms) end end
			table.sort(phases)
			log(cj.worstFrameMs > frameBudget * 3 and 'W' or 'I', 'MPProxyMeshGE', string.format(
				"Mesh job %s%s: total %.1f ms over %d frames (%.1f s), worst frame %.1f ms, longest step %.1f ms (%s); ms per step: %s",
				cj.job.model, cj.job.wheelJob and " (wheel meshes)" or ((sh and sh.fromCache) and " (from disk cache)" or ""), cj.totalMs, cj.frames, clock - cj.started,
				cj.worstFrameMs, cj.maxStepMs, cj.maxStepPhase, table.concat(phases, ", ")))
			currentJob = nil
		end
	end
	budgetTimer = nil
end

--- Returns the mesh key for a model + config and queues the build if needed.
-- @tparam string model jbeam name
-- @tparam table vcf vehicle config from the spawn packet (vcf.parts = { slot = partName })

local function configKey(model, vcf)
	local parts = {}
	for _, partName in pairs(vcf.parts) do
		if type(partName) == "string" and partName ~= "" then parts[#parts + 1] = partName end
	end
	if vcf.mainPartName then parts[#parts + 1] = vcf.mainPartName end
	table.sort(parts)
	return model .. "_" .. CACHE_VERSION .. "_" .. hashString(model .. "|" .. table.concat(parts, ",")), parts
end

-- the parts of a model's default configuration (its default .pc), or nil
local function defaultConfig(model)
	local ok, info = pcall(core_vehicles.getModel, model)
	local m = ok and type(info) == "table" and info.model or nil
	local pcName = m and m.default_pc
	if not pcName then return nil end
	local pc = jsonReadFile("/vehicles/" .. model .. "/" .. pcName .. ".pc")
	if type(pc) ~= "table" or type(pc.parts) ~= "table" then return nil end
	return { parts = pc.parts, mainPartName = pc.mainPartName or model, vars = type(pc.vars) == "table" and pc.vars or nil }
end

-- queues (or finds) the default config build of a model; cached ones go first, they resolve from disk at once
local function requestDefault(model, toBackground)
	if defaultKeys[model] ~= nil then return defaultKeys[model] or nil end
	local vcf = defaultConfig(model)
	if not vcf then defaultKeys[model] = false return nil end
	local key, parts = configKey(model, vcf)
	defaultKeys[model] = key
	if not shapes[key] then
		shapes[key] = { state = "queued" }
		local job = { key = key, model = model, parts = parts, vcf = vcf }
		if toBackground then prebuildJobs[#prebuildJobs + 1] = job
		elseif FS:fileExists(CACHE_DIR .. key .. ".json") then table.insert(jobs, 1, job)
		else jobs[#jobs + 1] = job end
	end
	return key
end

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
		jobs[#jobs + 1] = { key = key, model = model, parts = parts, vcf = vcf }
	end
	if fallbackOf[key] == nil then
		local dkey = requestDefault(model, false)
		fallbackOf[key] = (dkey and dkey ~= key) and dkey or false
	end
	return key
end

local function getShape(key)
	return key and shapes[key]
end

-- engine sound info of a config (or of the model's default config while the exact one builds), nil if unknown
local function getSound(key)
	local sh = key and shapes[key]
	if sh and sh.sound then return sh.sound end
	local fb = key and fallbackOf[key] and shapes[fallbackOf[key]]
	return fb and fb.sound or nil
end

-- ============= ENGINE IMPORTS =============
-- The first TSStatic of a .dae makes the engine load the shape synchronously (compiling a .cdae next to a /temp
-- copy the first time, loading that .cdae later). That cannot be sliced from Lua, so new imports are spread out.
local function tierPaths(shape, tier)
	return shape.tiers and (shape.tiers[tier] or shape.tiers[tostring(tier)]) or shape.paths
end

local cdaeCache = {} -- [dae path] = true/false: compiled .cdae seen on disk
local function hasCdae(path)
	local v = cdaeCache[path]
	if v == nil then
		local c = string.gsub(path, "%.dae$", ".cdae")
		v = FS:fileExists("/temp" .. c) or FS:fileExists(c)
		cdaeCache[path] = v
	end
	return v
end

-- nil when every file of the tier is loaded this session, else the wait between two such first uses
local function importInterval(shape, tier)
	local cached, any = true, false
	for _, path in ipairs(tierPaths(shape, tier)) do
		if not importedPaths[path] then any = true if not hasCdae(path) then cached = false end end
	end
	if not any then return nil end
	return cached and CACHED_SHAPE_INTERVAL or NEW_SHAPE_INTERVAL
end

-- ============= TSSTATIC POOL =============
local function createStatic(path, plain)
	local obj = createObject('TSStatic')
	if not obj then return nil end
	obj:setField('shapeName', 0, path)
	obj:setField('dynamic', 0, 'true')       -- moved every frame (same as trafficSignals)
	obj:setField('collisionType', 0, 'None')
	obj:setField('decalType', 0, 'None')
	obj.useInstanceRenderData = not plain    -- per instance paint (instanceColor*), not for wheels
	obj.canSave = false
	obj:registerObject(Sim.getUniqueName("beammpProxyMesh"))
	liveCount = liveCount + 1
	allObjects[obj:getId()] = true
	return obj:getId()
end

local function takeStatic(path, plain)
	local pool = pools[path]
	if pool and #pool > 0 then return table.remove(pool) end
	return createStatic(path, plain)
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

-- "metallic roughness clearcoat clearcoatRoughness" of one vcf paint
local function metallicString(paint)
	if type(paint) ~= "table" then return "0 0.5 0 0" end
	return string.format("%.3f %.3f %.3f %.3f", tonumber(paint.metallic) or 0, tonumber(paint.roughness) or 0.5,
		tonumber(paint.clearcoat) or 0, tonumber(paint.clearcoatRoughness) or 0)
end

local function attach(p, shape, tier)
	p.meshObjects = {}
	p.meshLast = nil -- new objects: place them on the next draw
	p.meshTier = tier
	local list = tierPaths(shape, tier)
	for _, path in ipairs(list) do
		local newImport = not importedPaths[path]
		local importTimer = newImport and TIMER() or nil
		importedPaths[path] = true
		local id = takeStatic(path)
		if importTimer then -- engine side shape import (synchronous); .cdae compiled the first time, then reused
			local ms = importTimer:stop()
			log(ms > 20 and 'W' or 'I', 'MPProxyMeshGE', string.format("Engine import of %s tier %d (%s): %.1f ms, compiled .cdae was %s",
				tostring(string.match(p.meshKey or "", "^(.-)_v%d")), tier, string.match(path, "([^/]+)$") or path, ms,
				cdaeCache[path] and "on disk" or "not on disk (compiled now)"))
		end
		if id then
			local obj = scenetree.findObjectById(id)
			if obj then
				local paints = p.vcf and p.vcf.paints or {}
				obj:setField('instanceColor', 0, paintString(paints[1]))
				obj:setField('instanceColor1', 0, paintString(paints[2] or paints[1]))
				obj:setField('instanceColor2', 0, paintString(paints[3] or paints[1]))
				if cfg.metallicPaint then -- same field and format the game sets on vehicles (core/vehicle/partmgmt.lua)
					for i = 1, 3 do obj:setField('metallicPaintData', i - 1, metallicString(paints[i] or paints[1])) end
				end
				obj.hidden = false
				p.meshObjects[#p.meshObjects + 1] = { path = path, id = id, obj = obj }
			end
		end
	end
	p.meshShape = shape
end

local function detachWheels(p)
	if not p.wheelObjects then return end
	for _, o in pairs(p.wheelObjects) do returnStatic(o.path, o.id) end
	p.wheelObjects = nil
	p.wheelShape = nil
end

-- real wheel objects for a proxy with body meshes, once every wheel file of its config is built; first imports
-- share the engine import interval with the body meshes
local function attachWheels(p, shape)
	local paths, newCount, allCdae = {}, 0, true
	for i, w in ipairs(shape.wheels) do
		local path = wheelPath(w)
		if path then
			if wheelFiles[path] == nil then queueWheelMeshes(shape, string.match(p.meshKey or "", "^(.-)_v%d") or "?") end
			if wheelFiles[path] == "queued" then return false end
			if wheelFiles[path] == "ready" then
				paths[i] = path
				if not importedPaths[path] then
					newCount = newCount + 1
					if not hasCdae(path) then allCdae = false end
				end
			end
		end
	end
	if next(paths) == nil then return false end
	if newCount > 0 then
		if clock < nextNewShapeAllowed then return false end
		nextNewShapeAllowed = clock + (allCdae and CACHED_SHAPE_INTERVAL or NEW_SHAPE_INTERVAL)
	end
	p.wheelObjects, p.wheelShape = {}, shape
	for i, path in pairs(paths) do
		local importTimer = not importedPaths[path] and TIMER() or nil
		importedPaths[path] = true
		local id = takeStatic(path, true)
		if importTimer then
			local ms = importTimer:stop()
			log(ms > 20 and 'W' or 'I', 'MPProxyMeshGE', string.format("Engine import of wheel %s (%s): %.1f ms, compiled .cdae was %s",
				string.match(path, "([^/]+)$") or path, tostring(shape.wheels[i].n), ms, cdaeCache[path] and "on disk" or "not on disk (compiled now)"))
		end
		local obj = id and scenetree.findObjectById(id)
		if obj then
			obj.hidden = false
			p.wheelObjects[i] = { path = path, id = id, obj = obj, roll = 0 }
		end
	end
	return true
end

local function detach(p)
	detachWheels(p)
	if not p.meshObjects then return end
	for _, o in ipairs(p.meshObjects) do returnStatic(o.path, o.id) end
	p.meshObjects = nil
	p.meshShape = nil
	p.meshFallback = nil
	p.meshTier = nil
end

--- Decision pass (4 Hz, called by MPProxyGE): picks the nearest proxies with a ready shape.
local candidates = {}
local function decide(vehicles, refPos)
	table.clear(candidates)
	table.clear(waitingLoad)
	local meshMax = math.min(cfg.distance, cfg.lodShell)
	local release = meshMax * (1 + LOD_HYSTERESIS) + 3
	local leaving = {}
	for _, v in pairs(vehicles) do
		local p = v.proxy
		if p then
			local usable = cfg.enabled and ((v.isProxy and not v.isSpawned) or v.proxyHandover ~= nil or v.hybridPaused) and not v.isDeleted and not v.proxyColliderID and p.hasData
			local d = usable and refPos:distance(p.rpos) or math.huge
			if p.meshObjects and not usable then detach(p) -- gone, real or collider: right away
			elseif p.meshObjects and d > release and not v.isFakeTest then leaving[#leaving + 1] = { p = p, d = d } end
			-- MPProxyTest vehicles ignore the mesh distance (they are never drawn as boxes)
			if usable and (d < release or v.isFakeTest) and p.meshKey then
				candidates[#candidates + 1] = { v = v, d = d }
			end
		end
	end
	-- out of range: farthest first, a few per pass
	table.sort(leaving, function(a, b) return a.d > b.d end)
	local detached = 0
	for _, l in ipairs(leaving) do
		if detached >= MAX_DETACHES_PER_PASS then break end
		detach(l.p)
		detached = detached + 1
	end
	table.sort(candidates, function(a, b) return a.d < b.d end)
	fps.inRange = #candidates
	local limit = math.min(cfg.maxProxies, fps.cap)
	local created = 0
	for i, c in ipairs(candidates) do
		local p = c.v.proxy
		if i > limit and not c.v.isFakeTest then
			if p.meshObjects and detached < MAX_DETACHES_PER_PASS then detach(p) detached = detached + 1 end
		elseif p.meshObjects and p.meshFallback and shapes[p.meshKey] and shapes[p.meshKey].state == "ready" and created < MAX_NEW_OBJECTS_PER_PASS then
			detach(p) -- the exact config is ready now, swap the default config mesh out (attached again below)
		end
		-- LOD tier: nearest first (candidates are sorted), switches share the per pass budget with new meshes
		local want = tierForDistance(c.d, p.meshTier) or (c.v.isFakeTest and TIER_SHELL) or nil
		if p.meshObjects and want ~= p.meshTier and created < MAX_NEW_OBJECTS_PER_PASS then
			if want then detach(p) -- attached again below with the new tier
			elseif detached < MAX_DETACHES_PER_PASS then detach(p) detached = detached + 1 end
		end
		if want and not p.meshObjects and not (i > limit and not c.v.isFakeTest) then
			local shape = shapes[p.meshKey]
			p.meshFallback = nil
			if not (shape and shape.state == "ready") then
				local fb = fallbackOf[p.meshKey] and shapes[fallbackOf[p.meshKey]]
				if fb and fb.state == "ready" then shape = fb p.meshFallback = true end
			end
			if shape and shape.state == "ready" and created < MAX_NEW_OBJECTS_PER_PASS then
				-- first use of a file this session (disk cached shapes too): the engine imports it synchronously,
				-- so only one such attach per interval (shorter when the compiled .cdae already exists)
				local interval = not c.v.isFakeTest and importInterval(shape, want) or nil
				if interval then
					if clock >= nextNewShapeAllowed then
						nextNewShapeAllowed = clock + interval
						attach(p, shape, want)
						created = created + 1
					else
						waitingLoad[#waitingLoad + 1] = c.v.jbeam or string.match(p.meshKey, "^(.-)_v%d") or "?"
					end
				else
					attach(p, shape, want)
					created = created + 1
				end
			end
		end
	end
	-- visual suspension: nearest proxies with meshes inside proxySuspensionDistance
	local suspLeft = cfg.suspension and SUSP_MAX_PROXIES or 0
	for _, c in ipairs(candidates) do
		local p = c.v.proxy
		p.suspOn = suspLeft > 0 and p.meshObjects ~= nil and c.d < cfg.suspDist or nil
		if p.suspOn then suspLeft = suspLeft - 1 end
	end
	-- real wheels: nearest proxies in the full / parts tiers
	local wheelsLeft = cfg.realWheels and cfg.realWheelsMax or 0
	for _, c in ipairs(candidates) do
		local p = c.v.proxy
		local want = wheelsLeft > 0 and p.meshObjects and p.meshShape and p.meshShape.wheels and p.meshTier and p.meshTier <= TIER_PARTS and true or false
		if want then wheelsLeft = wheelsLeft - 1 end
		if p.wheelObjects and (not want or p.wheelShape ~= p.meshShape) then detachWheels(p) end
		if want and not p.wheelObjects then attachWheels(p, p.meshShape) end
	end
end

local tmpV = vec3()
local org = vec3()
local axX, axY, axZ = vec3(), vec3(), vec3()
local unitX, unitY, unitZ = vec3(1,0,0), vec3(0,1,0), vec3(0,0,1)
local ffiFound = ffi and ffi.C and true or false
local drawCylinder = ffiFound and ffi.C.BNG_DBG_DRAW_Cylinder or nop
local wheelColor = color(25, 25, 25, 255)
local MAX_STEER = math.rad(30) -- drawn front wheel angle at full steering
local wheelDir, wheelUp, wheelQuat = vec3(), vec3(), quat()
local TWO_PI = 2 * math.pi

local function toWorld(lx, ly, lz)
	return org.x + axX.x*lx + axY.x*ly + axZ.x*lz, org.y + axX.y*lx + axY.y*ly + axZ.y*lz, org.z + axX.z*lx + axY.z*ly + axZ.z*lz
end

-- ============= VISUAL SUSPENSION =============
-- Nearest proxies only (proxySuspension): each wheel follows the ground under it within a small travel (a ray
-- down along the body's up axis, every few frames per wheel, staggered), spring-damped. The body mesh leans
-- with the acceleration of the proxy (braking dives, cornering rolls outward) and with the wheel offsets, also
-- spring-damped and clamped to a few degrees. The wheels stay where the ground is, only the body tilts.
local SUSP_TRAVEL = 0.12      -- m up / down from the jbeam wheel position
local SUSP_RAY_EVERY = 4      -- frames between two rays of the same wheel
local SUSP_RAY_ABOVE = 0.6    -- ray start above the wheel center
local SUSP_K, SUSP_C = 160, 18           -- wheel spring / damper (per unit mass)
local LEAN_K, LEAN_C = 45, 9             -- body lean spring / damper
local LEAN_MAX = math.rad(3.5)
local LEAN_PER_ACC = 0.0045              -- rad per m/s^2
local rayOrigin, rayDir = vec3(), vec3()
local suspFrame = 0

local function clampAbs(v, m) return v > m and m or (v < -m and -m or v) end

local function updateSuspension(p, shape, dt)
	local st = p.susp
	if not st then
		st = { off = {}, vel = {}, target = {}, seed = math.random(0, SUSP_RAY_EVERY - 1),
			pitch = 0, pitchV = 0, roll = 0, rollV = 0, heave = 0, ax = 0, ay = 0 }
		p.susp = st
	end
	if dt <= 0 then return st end
	-- body acceleration in jbeam axes (forward = -Y, left = +X), lightly filtered
	local v = p.svel
	if v then
		if st.lvx then
			local axw, ayw, azw = (v.x - st.lvx) / dt, (v.y - st.lvy) / dt, (v.z - st.lvz) / dt
			local fwd = -(axw * axY.x + ayw * axY.y + azw * axY.z)
			local left = axw * axX.x + ayw * axX.y + azw * axX.z
			local a = math.min(1, dt * 6)
			st.ax = st.ax + (clampAbs(fwd, 15) - st.ax) * a
			st.ay = st.ay + (clampAbs(left, 15) - st.ay) * a
		end
		st.lvx, st.lvy, st.lvz = v.x, v.y, v.z
	end
	-- wheels: ground under each, staggered rays
	local wheels = shape.wheels
	local sumF, nF, sumR, nR, sumL, nL, sumRt, nRt, sum, n = 0, 0, 0, 0, 0, 0, 0, 0, 0, 0
	local cy = shape.minY and (shape.minY + shape.maxY) * 0.5 or 0
	local yF, yR, xL, xR = 0, 0, 0, 0
	if wheels then
		rayDir:set(-axZ.x, -axZ.y, -axZ.z)
		for i, w in ipairs(wheels) do
			if (suspFrame + st.seed + i) % SUSP_RAY_EVERY == 0 then
				local px, py, pz = toWorld(w.x, w.y, w.z + SUSP_RAY_ABOVE)
				rayOrigin:set(px, py, pz)
				local maxD = SUSP_RAY_ABOVE + w.r + SUSP_TRAVEL + 0.3
				local d = castRayStatic(rayOrigin, rayDir, maxD)
				-- ground at d below the start: the wheel bottom should touch it
				st.target[i] = (d and d < maxD) and clampAbs(SUSP_RAY_ABOVE + w.r - d, SUSP_TRAVEL) or 0
			end
			local o, ov, t = st.off[i] or 0, st.vel[i] or 0, st.target[i] or 0
			ov = ov + (SUSP_K * (t - o) - SUSP_C * ov) * dt
			o = clampAbs(o + ov * dt, SUSP_TRAVEL)
			st.off[i], st.vel[i] = o, ov
			sum, n = sum + o, n + 1
			if w.y < cy then sumF, nF, yF = sumF + o, nF + 1, yF + w.y else sumR, nR, yR = sumR + o, nR + 1, yR + w.y end
			if w.x > 0 then sumL, nL, xL = sumL + o, nL + 1, xL + w.x else sumRt, nRt, xR = sumRt + o, nRt + 1, xR + w.x end
		end
	end
	-- lean targets: pitch > 0 is nose down (braking), roll > 0 lowers the left (+X) side
	local pitchT = st.ax * -LEAN_PER_ACC
	local rollT = -st.ay * LEAN_PER_ACC -- accelerating to the left (turning left): the right side goes down
	if nF > 0 and nR > 0 then
		local L = (yR / nR) - (yF / nF)
		if L > 0.5 then pitchT = pitchT + (sumR / nR - sumF / nF) / L end
	end
	if nL > 0 and nRt > 0 then
		local T = (xL / nL) - (xR / nRt)
		if T > 0.5 then rollT = rollT - (sumL / nL - sumRt / nRt) / T end
	end
	pitchT, rollT = clampAbs(pitchT, LEAN_MAX), clampAbs(rollT, LEAN_MAX)
	st.pitchV = st.pitchV + (LEAN_K * (pitchT - st.pitch) - LEAN_C * st.pitchV) * dt
	st.rollV = st.rollV + (LEAN_K * (rollT - st.roll) - LEAN_C * st.rollV) * dt
	st.pitch = clampAbs(st.pitch + st.pitchV * dt, LEAN_MAX)
	st.roll = clampAbs(st.roll + st.rollV * dt, LEAN_MAX)
	st.heave = n > 0 and (sum / n) * 0.5 or 0
	return st
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
	local bx, by, bz, qx, qy, qz, qw = org.x, org.y, org.z, r.x, r.y, r.z, r.w
	local susp = nil
	if p.suspOn and shape.wheels then
		local sdt = math.min(math.max(clock - (p.suspT or clock), 0), 0.1)
		p.suspT = clock
		susp = updateSuspension(p, shape, sdt)
		-- body: L = Rx(pitch) * Ry(roll) about the body center, then the heave along the body's up axis
		local th, ph = susp.pitch, susp.roll
		local ct, stt, cph, sph = math.cos(th), math.sin(th), math.cos(ph), math.sin(ph)
		local lyx, lyy, lyz = 0, ct, stt
		local lzx, lzy, lzz = sph, -cph * stt, cph * ct
		wheelDir:set(axX.x*lyx + axY.x*lyy + axZ.x*lyz, axX.y*lyx + axY.y*lyy + axZ.y*lyz, axX.z*lyx + axY.z*lyy + axZ.z*lyz)
		wheelUp:set(axX.x*lzx + axY.x*lzy + axZ.x*lzz, axX.y*lzx + axY.y*lzy + axZ.y*lzz, axX.z*lzx + axY.z*lzy + axZ.z*lzz)
		wheelQuat:setFromDir(wheelDir, wheelUp)
		qx, qy, qz, qw = wheelQuat.x, wheelQuat.y, wheelQuat.z, wheelQuat.w
		-- origin moves so the pivot (cx, cy, cz) stays put: o' = o + R (P - L P) + heave * up
		local rx_, ry_, rz_ = cx * cph + cz * sph, cy, -cx * sph + cz * cph
		local lpx, lpy, lpz = rx_, ry_ * ct - rz_ * stt, ry_ * stt + rz_ * ct
		local dx, dy, dz = cx - lpx, cy - lpy, cz - lpz + susp.heave
		bx = org.x + axX.x*dx + axY.x*dy + axZ.x*dz
		by = org.y + axX.y*dx + axY.y*dy + axZ.y*dz
		bz = org.z + axX.z*dx + axY.z*dy + axZ.z*dz
	else
		p.susp, p.suspT = nil, nil
	end
	-- parked / unchanged: the objects keep their transform, skip the engine calls
	local lb = p.meshLast
	local moved = not (cfg.skipStatic and lb and math.abs(lb[1] - bx) < 1e-4 and math.abs(lb[2] - by) < 1e-4 and math.abs(lb[3] - bz) < 1e-4
		and math.abs(lb[4] - qx) < 1e-6 and math.abs(lb[5] - qy) < 1e-6 and math.abs(lb[6] - qz) < 1e-6 and math.abs(lb[7] - qw) < 1e-6)
	if moved then
		lb = lb or {}
		lb[1], lb[2], lb[3], lb[4], lb[5], lb[6], lb[7] = bx, by, bz, qx, qy, qz, qw
		p.meshLast = lb
		for _, o in ipairs(p.meshObjects) do
			local obj = o.obj
			if obj then
				obj:setPosRot(bx, by, bz, qx, qy, qz, qw)
				obj:updateInstanceRenderData()
			end
		end
	end
	if (cfg.wheels or p.wheelObjects) and shape.wheels then -- real wheel objects are moved even with drawn wheels off
		-- jbeam wheels: centers, axes, radius and width in the same jbeam space as the body mesh
		local steer = math.max(-1, math.min(1, p.steer or 0)) * MAX_STEER
		local sc, ss = math.cos(steer), math.sin(steer)
		local objs = p.wheelShape == shape and p.wheelObjects or nil
		local dt = math.min(math.max(clock - (p.wheelT or clock), 0), 0.25)
		p.wheelT = clock
		-- rolling: forward speed (jbeam -Y) over the radius
		local vf = 0
		if objs and p.svel then vf = -(p.svel.x * axY.x + p.svel.y * axY.y + p.svel.z * axY.z) end
		for i, w in ipairs(shape.wheels) do
			local o = objs and objs[i]
			if o and o.obj then
				local roll = (o.roll + vf * dt / math.max(w.r, 0.1)) % TWO_PI
				o.roll = roll
				local st = w.s and steer or 0
				local cs, sn, cr, sr = math.cos(st), math.sin(st), math.cos(roll), math.sin(roll)
				-- wheel axes in jbeam space: roll about the axle (X), then steer about Z
				local yx, yy, yz = -sn * cr, cs * cr, sr
				local zx, zy, zz = sn * sr, -cs * sr, cr
				wheelDir:set(axX.x*yx + axY.x*yy + axZ.x*yz, axX.y*yx + axY.y*yy + axZ.y*yz, axX.z*yx + axY.z*yy + axZ.z*yz)
				wheelUp:set(axX.x*zx + axY.x*zy + axZ.x*zz, axX.y*zx + axY.y*zy + axZ.y*zz, axX.z*zx + axY.z*zy + axZ.z*zz)
				wheelQuat:setFromDir(wheelDir, wheelUp)
				local px, py, pz = toWorld(w.x, w.y, w.z + (susp and susp.off[i] or 0))
				local q = wheelQuat
				local l = o.last
				if not (cfg.skipStatic and l and math.abs(l[1] - px) < 1e-4 and math.abs(l[2] - py) < 1e-4 and math.abs(l[3] - pz) < 1e-4
					and math.abs(l[4] - q.x) < 1e-6 and math.abs(l[5] - q.y) < 1e-6 and math.abs(l[6] - q.z) < 1e-6 and math.abs(l[7] - q.w) < 1e-6) then
					l = l or {}
					l[1], l[2], l[3], l[4], l[5], l[6], l[7] = px, py, pz, q.x, q.y, q.z, q.w
					o.last = l
					o.obj:setPosRot(px, py, pz, q.x, q.y, q.z, q.w)
				end
			end
			if cfg.wheels and not (o and o.obj and w.mt) then -- drawn tire when there is no tire mesh
				local ax, ay, az = w.ax, w.ay, w.az
				if w.s and steer ~= 0 then ax, ay = ax * sc - ay * ss, ax * ss + ay * sc end
				local h = w.wd * 0.5
				local wz = w.z + (susp and susp.off[i] or 0)
				local x1, y1, z1 = toWorld(w.x - ax * h, w.y - ay * h, wz - az * h)
				local x2, y2, z2 = toWorld(w.x + ax * h, w.y + ay * h, wz + az * h)
				drawCylinder(x1, y1, z1, x2, y2, z2, w.r, wheelColor, true)
			end
		end
	elseif cfg.wheels and shape.minX then
		local W, L, H = shape.maxX - shape.minX, shape.maxY - shape.minY, shape.maxZ - shape.minZ
		local radius = math.min(math.max(H * 0.22, 0.28), 0.55)
		local gz = (shape.groundZ or 0) + radius
		local xo, xi = W * 0.5 - 0.03, W * 0.5 - 0.25
		local yf, yr = cy - L * 0.32, cy + L * 0.32 -- -Y is the front
		-- front wheels turn with the last steering input of the remote driver (BeamMP inputs packet, -1..1)
		local steer = math.max(-1, math.min(1, p.steer or 0)) * MAX_STEER
		local sx, sy = math.cos(steer), math.sin(steer)
		local half = (xo - xi) * 0.5
		for side = -1, 1, 2 do
			for w = 1, 2 do
				local y = w == 1 and yf or yr
				local mx = cx + side * (xi + xo) * 0.5
				local ax, ay = half, 0
				if w == 1 and steer ~= 0 then ax, ay = half * sx, half * sy end
				local x1, y1, z1 = toWorld(mx - ax, y - ay, gz)
				local x2, y2, z2 = toWorld(mx + ax, y + ay, gz)
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
	-- centered on its own size, horizontally in the middle and at 38% of the viewport height (any resolution)
	imgui.SetNextWindowPos(imgui.ImVec2(vp.Pos.x + vp.Size.x * 0.5, vp.Pos.y + vp.Size.y * 0.38), imgui.Cond_Always, imgui.ImVec2(0.5, 0.5))
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
	frameBudget = cfg.frameBudget
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
			for _, path in ipairs(shape.paths) do -- every tier
				if not importedPaths[path] then
					local t = TIMER()
					local cdae = hasCdae(path)
					importedPaths[path] = true
					local id = takeStatic(path)
					if id then returnStatic(path, id) end
					log('I', 'MPProxyMeshGE', string.format("Engine import of %s (loading screen preload): %.1f ms, compiled .cdae was %s",
						string.match(path, "([^/]+)$") or path, t:stop(), cdae and "on disk" or "not on disk (compiled now)"))
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

local prebuildStarted = false

local function onUpdate(dtReal)
	clock = clock + (dtReal or 0)
	suspFrame = suspFrame + 1
	if not cfg.enabled then return end
	updateFpsCap(dtReal or 0, clock)
	if currentJob or #jobs > 0 or #wheelJobs > 0 then
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
	if cfg.prebuild and not preload and not prebuildStarted and MPCoreNetwork and MPCoreNetwork.isMPSession and MPCoreNetwork.isMPSession() then
		prebuildStarted = true
		local ok, list = pcall(function() return core_vehicles.getModelList().models end) -- once per session
		local n = 0
		for name, info in pairs(ok and type(list) == "table" and list or {}) do
			if type(info) == "table" and info.Type ~= "Prop" and name ~= "unicycle" then
				if requestDefault(name, true) then n = n + 1 end
			end
		end
		log('I', 'MPProxyMeshGE', string.format("Prebuilding default config proxy meshes of %d models in the background", n))
	end
end

--- Cache / pool statistics for MPProxyTest.
local function getStats(resetWindow)
	local out = { queued = #jobs + (currentJob and 1 or 0), building = currentJob and currentJob.job and currentJob.job.key or nil,
		ready = 0, failed = 0, liveObjects = liveCount, fpsCap = fps.cap ~= math.huge and fps.cap or nil,
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
	table.clear(cdaeCache)
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
	prebuildJobs = {}
	wheelJobs = {}
	wheelFiles = {}
	fallbackOf = {}
	defaultKeys = {}
	prebuildStarted = false
	currentJob = nil
end

--- Deletes the objects of a proxy that is going away (vehicle removed or swapped to real).
local function release(p)
	if p then detach(p) end
end

--- Clears the per proxy references after reset (objects are gone).
local function forget(p)
	if p then p.meshObjects = nil p.meshShape = nil p.meshKey = nil p.wheelObjects = nil p.wheelShape = nil end
end

local function onSettingsChanged() readSettings() if not preload then frameBudget = cfg.frameBudget end end
-- TSStatics (body and wheel meshes) of an earlier load of this extension (Lua reload), by their name prefix
local function removeLeftovers()
	local n = 0
	for _, name in ipairs(scenetree.findClassObjects("TSStatic") or {}) do
		if string.find(name, "^beammpProxyMesh") then
			local obj = scenetree.findObject(name)
			if obj and not allObjects[obj:getId()] then obj:delete() n = n + 1 end
		end
	end
	if n > 0 then log('I', 'MPProxyMeshGE', string.format("Removed %d proxy mesh objects of an earlier load", n)) end
end

local function onExtensionLoaded()
	readSettings()
	if settings.getValue("proxyCleanupOnReload", true) ~= false then
		local ok, err = pcall(removeLeftovers)
		if not ok then log('W', 'MPProxyMeshGE', "Leftover cleanup failed: " .. tostring(err)) end
	end
	frameBudget = cfg.frameBudget
	local ok, err = pcall(cleanOldCache)
	if not ok then log('W', 'MPProxyMeshGE', "Cache cleanup failed: " .. tostring(err)) end
end

detectGlobalWrites() -- reenable global write notifications

M.request           = request
M.getShape          = getShape
M.getSound          = getSound
M.getLodSettings    = function() return cfg.lodFull, cfg.lodParts, math.min(cfg.lodShell, cfg.distance) end
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
