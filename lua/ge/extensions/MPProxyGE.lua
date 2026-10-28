-- Copyright (C) 2026 BeamMP Ltd., BeamMP team and contributors.
-- Licensed under AGPL-3.0 (or later), see <https://www.gnu.org/licenses/>.
-- SPDX-License-Identifier: AGPL-3.0-or-later

--- MPProxyGE API - Proxy vehicles for remote players.
-- Remote vehicles that are far away are not spawned as real BeamNG vehicles (which costs a multi second
-- stutter to spawn and a full physics simulation to keep). Instead they are kept as "proxies": the Vehicle
-- table in MPVehicleGE without a game object, moved by dead reckoning from the position packets and drawn
-- as an oriented, paint coloured box with the debug drawer (no scene objects are created).
-- Only the closest remote vehicles are swapped for real vehicles, rate limited and with hysteresis.
-- Optionally (proxyCollision) proxies close to the local vehicle get a pooled, simplified collision vehicle.
-- @module MPProxyGE

local M = {}

setmetatable(_G,{}) -- temporarily disable global notifications

-- ============= SETTINGS =============
local cfg = {
	enabled = true,
	spawnDist = 200,      -- proxy -> real when closer than this
	despawnDist = 260,    -- real -> proxy when further than this
	maxReal = 12,         -- max remote real vehicles (spawned + waiting in the spawn queue)
	spawnInterval = 3,    -- seconds between two real spawns (global)
	cooldown = 10,        -- seconds a vehicle is not swapped again after a swap
	drawDist = 3000,      -- proxies beyond this are not drawn
	collision = false,
	collisionRadius = 40,
	poolSize = 4,
	colliderModel = "simple_traffic",
}

local DESPAWN_INTERVAL = 0.5   -- seconds between two real -> proxy swaps (despawns are cheap, but not free)
local DECISION_INTERVAL = 0.25 -- seconds between two swap decision passes
local CAP_SWAP_MARGIN = 50     -- a real vehicle is only evicted for the cap if a proxy is this much closer
local MAX_EXTRAPOLATION = 0.6  -- seconds a packet is extrapolated at most
local SNAP_DISTANCE = 25       -- render position snaps instead of blending above this error
local POS_BLEND = 12           -- 1/s, how fast the rendered pose converges to the prediction
local DETAIL_DISTANCE = 600    -- full shaded box below, a single prism above
local COLLIDER_RELEASE_MARGIN = 15

local function readSettings()
	cfg.enabled = settings.getValue("enableProxyVehicles", true) ~= false
	cfg.autoReal = settings.getValue("proxyAutoReal", false) == true -- opt in: distance based real spawns
	cfg.spawnDist = tonumber(settings.getValue("proxyRealSpawnDistance", 200)) or 200
	cfg.despawnDist = math.max(tonumber(settings.getValue("proxyRealDespawnDistance", 260)) or 260, cfg.spawnDist + 20)
	cfg.maxReal = math.max(0, math.floor(tonumber(settings.getValue("proxyMaxRealVehicles", 12)) or 12))
	cfg.spawnInterval = math.max(0, tonumber(settings.getValue("proxyMinSpawnInterval", 3)) or 3)
	cfg.cooldown = math.max(0, tonumber(settings.getValue("proxySwapCooldown", 10)) or 10)
	cfg.drawDist = tonumber(settings.getValue("proxyDrawDistance", 3000)) or 3000
	cfg.collision = settings.getValue("proxyCollision", false) == true
	cfg.collisionRadius = tonumber(settings.getValue("proxyCollisionRadius", 40)) or 40
	cfg.poolSize = math.max(0, math.floor(tonumber(settings.getValue("proxyColliderPoolSize", 4)) or 4))
	cfg.colliderModel = settings.getValue("proxyColliderModel", "simple_traffic") or "simple_traffic"
end

-- ============= DIMENSIONS =============
-- {length, width, height} in meters. Rough values, replaced by a jbeam derived cache in a later phase.
local CLASS_DIMS = {
	car = {4.5, 1.85, 1.45},
	truck = {7.5, 2.5, 3.2},
	trailer = {8.0, 2.5, 3.0},
	prop = {1.5, 1.5, 1.5},
	unicycle = {0.6, 0.6, 1.8},
}
local MODEL_DIMS = {
	unicycle = CLASS_DIMS.unicycle,
	pickup = {5.4, 2.0, 1.9}, fullsize = {5.3, 2.0, 1.5}, etk800 = {4.9, 1.85, 1.45}, etki = {4.6, 1.75, 1.4},
	etkc = {4.6, 1.85, 1.35}, vivace = {4.3, 1.8, 1.45}, covet = {3.9, 1.7, 1.45}, sunburst2 = {4.4, 1.8, 1.45},
	bastion = {5.0, 1.95, 1.4}, legran = {4.8, 1.8, 1.4}, moonhawk = {5.2, 1.95, 1.35}, barstow = {5.1, 1.9, 1.35},
	burnside = {5.3, 2.0, 1.45}, bluebuck = {5.6, 2.0, 1.4}, miramar = {4.3, 1.6, 1.4}, pessima = {4.5, 1.7, 1.4},
	midsize = {4.6, 1.8, 1.4}, sbr = {4.4, 1.9, 1.25}, scintilla = {4.6, 2.05, 1.15}, bolide = {4.0, 1.9, 1.1},
	nine = {4.6, 1.85, 1.45}, wendover = {5.0, 1.9, 1.4}, bx = {4.5, 1.75, 1.3}, autobello = {3.2, 1.4, 1.3},
	lansdale = {5.0, 1.85, 1.7}, hopper = {4.0, 1.7, 1.8}, roamer = {4.9, 1.95, 1.9}, van = {5.0, 2.0, 2.1},
	wigeon = {3.0, 1.4, 1.5}, pigeon = {2.8, 1.3, 1.6}, atv = {2.1, 1.2, 1.2}, utv = {3.2, 1.6, 1.9},
	rockbouncer = {4.0, 2.2, 2.0}, md_series = {6.0, 2.2, 2.6}, midtruck = {6.5, 2.3, 2.8}, us_semi = {7.0, 2.6, 3.6},
	citybus = {12.0, 2.6, 3.2}, dumptruck = {8.5, 2.6, 3.5}, wl40 = {6.0, 2.5, 3.0}, racetruck = {5.5, 2.4, 2.8},
	caravan = {6.0, 2.3, 2.7}, cargotrailer = {5.0, 2.0, 2.2}, dryvan = {14.0, 2.6, 4.0}, flatbed = {14.0, 2.6, 1.6},
	tanker = {13.0, 2.6, 3.6}, simple_traffic = CLASS_DIMS.car,
}
local TYPE_TO_CLASS = { Car = "car", Truck = "truck", Trailer = "trailer", Prop = "prop", Automation = "car" }

-- hard limits for every proxy size (box, prism, mesh fallback), whatever the source
local MIN_DIM, MAX_LEN, MAX_WIDTH, MAX_HEIGHT = 0.3, 25, 6, 6
local function clampDim(v, maxV, default)
	v = tonumber(v)
	if not v or v ~= v then return default end
	return math.max(MIN_DIM, math.min(maxV, v))
end
local function setDims(p, L, W, H)
	p.L, p.W, p.H = clampDim(L, MAX_LEN, 4.5), clampDim(W, MAX_WIDTH, 1.9), clampDim(H, MAX_HEIGHT, 1.5)
end

local modelInfoCache = {} -- [jbeam] = { valid = bool, dims = {} }

local function getModelInfo(jbeam)
	if not jbeam then return { valid = false, dims = CLASS_DIMS.car } end
	local info = modelInfoCache[jbeam]
	if info then return info end
	-- core_vehicles.getModel is cached by the game after the first call per model, getModelList() is not
	-- (it rebuilds all filters) and must not be called per proxy
	local ok, model = pcall(core_vehicles.getModel, jbeam)
	local modelData = ok and type(model) == "table" and model.model or nil
	local dims = MODEL_DIMS[jbeam]
	if not dims then
		local class = modelData and TYPE_TO_CLASS[modelData.Type] or "car"
		dims = CLASS_DIMS[class] or CLASS_DIMS.car
	end
	info = { valid = modelData ~= nil, dims = dims }
	modelInfoCache[jbeam] = info
	return info
end

local function paintToColor(vcf)
	local paint = vcf and vcf.paints and vcf.paints[1]
	local c = paint and paint.baseColor
	if type(c) == "table" and c[1] then
		return { r = (c[1] or 0.5) * 255, g = (c[2] or 0.5) * 255, b = (c[3] or 0.5) * 255 }
	end
	return { r = 140, g = 140, b = 150 }
end

-- ============= STATE =============
local clock = 0
local decisionTimer = 0
local nextSpawnAllowed = 0
local nextDespawnAllowed = 0
local refPos = vec3()       -- distance reference (camera or local vehicle)
local localVehPos = vec3()
local hasLocalVeh = false

local colliders = {}        -- [gameVehicleID] = { serverVehicleID = string|nil, ready = bool }
local colliderCount = 0
local nextColliderSpawnAllowed = 0

-- garbage free temporaries
local tmpQ = quat()
local tmpV = vec3()
local axX, axY, axZ = vec3(), vec3(), vec3()
local unitX, unitY, unitZ = vec3(1,0,0), vec3(0,1,0), vec3(0,0,1)
local center = vec3()
local corners = {}
for i = 1, 8 do corners[i] = vec3() end

local ffiFound = ffi and ffi.C and true or false
local drawTriSolid = ffiFound and ffi.C.BNG_DBG_DRAW_TriSolid or nop
local drawSquarePrism = ffiFound and ffi.C.BNG_DBG_DRAW_SquarePrism or nop

--- Creates or refreshes the proxy data of a vehicle from its spawn/edit data.
-- @tparam table vehicle MPVehicleGE Vehicle
-- @tparam table spawnData decoded spawn packet (jbm, vcf, pos, rot)
local function initProxy(vehicle, spawnData)
	local p = vehicle.proxy
	if not p then
		p = {
			pos = vec3(), rot = quat(), vel = vec3(), rvel = vec3(),
			rpos = vec3(), rrot = quat(), t = clock, hasData = false, cooldownUntil = 0,
		}
		vehicle.proxy = p
		if spawnData and type(spawnData.pos) == "table" and spawnData.pos[1] then
			p.pos:set(spawnData.pos[1], spawnData.pos[2], spawnData.pos[3])
			p.rpos:set(p.pos)
			p.hasData = true
		end
		if spawnData and type(spawnData.rot) == "table" and spawnData.rot[4] then
			-- spawn packets carry veh:getRotation(), position packets carry quatFromDir(-dir, up), see applyVehSpawn
			p.rot:set(quat(0,0,1,0) * quat(spawnData.rot[1], spawnData.rot[2], spawnData.rot[3], spawnData.rot[4]))
			p.rrot:set(p.rot)
		end
	end
	local info = getModelInfo(spawnData and spawnData.jbm or vehicle.jbeam)
	setDims(p, info.dims[1], info.dims[2], info.dims[3])
	p.isPerson = (spawnData and spawnData.jbm or vehicle.jbeam) == "unicycle" -- walking player
	p.cogH = math.min(0.55, p.H * 0.4) -- position packets are at the center of gravity, not the ground
	local c = paintToColor(spawnData and spawnData.vcf)
	p.r, p.g, p.b = c.r, c.g, c.b
	p.vcfPaint = spawnData and spawnData.vcf and spawnData.vcf.paints and spawnData.vcf.paints[1] or nil
	p.validModel = info.valid
	p.dimsFromMesh = nil
	if spawnData and spawnData.vcf then
		p.vcf = spawnData.vcf
		if MPProxyMeshGE and not info.valid and not p.isPerson then
			log('W', 'MPProxyGE', "No proxy mesh for "..tostring(vehicle.serverVehicleString)..": model '"..tostring(spawnData.jbm or vehicle.jbeam).."' is not installed, drawing a box")
		end
		if MPProxyMeshGE and info.valid and not p.isPerson then
			local key = MPProxyMeshGE.request(spawnData.jbm or vehicle.jbeam, spawnData.vcf) -- async, box until ready
			if key ~= p.meshKey then MPProxyMeshGE.release(p) end
			p.meshKey = key
		end
	end
	return p
end

--- Called by positionGE for every decoded position packet of a vehicle without game object.
local function onPositionPacket(vehicle, decoded)
	if not decoded or type(decoded.pos) ~= "table" or type(decoded.rot) ~= "table" then return end
	local p = vehicle.proxy or initProxy(vehicle, nil)
	p.pos:set(decoded.pos[1], decoded.pos[2], decoded.pos[3])
	p.rot:set(decoded.rot[1], decoded.rot[2], decoded.rot[3], decoded.rot[4])
	if type(decoded.vel) == "table" then p.vel:set(decoded.vel[1], decoded.vel[2], decoded.vel[3]) else p.vel:set(0,0,0) end
	if type(decoded.rvel) == "table" then p.rvel:set(decoded.rvel[1], decoded.rvel[2], decoded.rvel[3]) else p.rvel:set(0,0,0) end
	p.t = clock
	if not p.hasData then
		p.rpos:set(p.pos)
		p.rrot:set(p.rot)
		p.hasData = true
	end
end

--- Seeds the proxy from a real vehicle that is about to be despawned, so it continues seamlessly.
local function seedFromVehicle(vehicle, veh)
	local p = vehicle.proxy or initProxy(vehicle, nil)
	local cx, cy, cz = be:getObjectOOBBCenterXYZ(veh:getID())
	p.pos:set(cx, cy, cz)
	tmpV:set(veh:getDirectionVectorXYZ())
	tmpV:setScaled(-1)
	axZ:set(veh:getDirectionVectorUpXYZ())
	p.rot:setFromDir(tmpV, axZ) -- same convention as the position packets (positionVE.getVehicleRotation)
	p.vel:set(veh:getVelocityXYZ())
	p.rvel:set(0,0,0)
	p.t = clock
	p.rpos:set(p.pos)
	p.rrot:set(p.rot)
	p.hasData = true
end

--- Snaps a proxy to a pose (server side reset).
local function snapProxy(vehicle, pos, rot)
	local p = vehicle.proxy
	if not p or not pos then return end
	p.pos:set(pos.x or pos[1], pos.y or pos[2], pos.z or pos[3])
	if rot and (rot.w or rot[4]) then p.rot:set(rot.x or rot[1], rot.y or rot[2], rot.z or rot[3], rot.w or rot[4]) end
	p.vel:set(0,0,0)
	p.rvel:set(0,0,0)
	p.t = clock
	p.rpos:set(p.pos)
	p.rrot:set(p.rot)
	p.hasData = true
end

-- in place normalized lerp of quaternions, garbage free
local function nlerpInto(out, a, b, t)
	local d = a.x*b.x + a.y*b.y + a.z*b.z + a.w*b.w
	local s = d < 0 and -t or t
	local t1 = 1 - t
	local x, y, z, w = a.x*t1 + b.x*s, a.y*t1 + b.y*s, a.z*t1 + b.z*s, a.w*t1 + b.w*s
	local len = math.sqrt(x*x + y*y + z*z + w*w)
	if len < 1e-9 then out:set(b.x, b.y, b.z, b.w) return end
	out:set(x/len, y/len, z/len, w/len)
end

--- Dead reckoning + smoothing for one proxy. Writes vehicle.position / vehicle.rotation.
local function predict(vehicle, p, dt)
	local age = math.min(math.max(clock - p.t, 0), MAX_EXTRAPOLATION)
	-- predicted position
	tmpV:set(p.vel)
	tmpV:setScaled(age)
	tmpV:setAdd(p.pos)
	-- predicted rotation, same formula as positionVE (rot * quatFromEuler(rvel * t))
	tmpQ:setFromEuler(p.rvel.x * age, p.rvel.y * age, p.rvel.z * age)
	tmpQ:setMul2(p.rot, tmpQ)

	if p.rpos:squaredDistance(tmpV) > SNAP_DISTANCE * SNAP_DISTANCE then
		p.rpos:set(tmpV)
		p.rrot:set(tmpQ)
	else
		local k = math.min(1, dt * POS_BLEND)
		p.rpos:setLerp(p.rpos, tmpV, k)
		nlerpInto(p.rrot, p.rrot, tmpQ, k)
	end
	vehicle.position:set(p.rpos)
	vehicle.rotation:set(p.rrot)
end

local function packColor(r, g, b, a)
	return color(r, g, b, a)
end

local function drawQuad(a, b, c, d, col)
	-- the debug drawer triangles are single sided, draw both windings so the winding order does not matter
	drawTriSolid(a.x, a.y, a.z, b.x, b.y, b.z, c.x, c.y, c.z, col, true)
	drawTriSolid(a.x, a.y, a.z, c.x, c.y, c.z, b.x, b.y, b.z, col, true)
	drawTriSolid(a.x, a.y, a.z, c.x, c.y, c.z, d.x, d.y, d.z, col, true)
	drawTriSolid(a.x, a.y, a.z, d.x, d.y, d.z, c.x, c.y, c.z, col, true)
end

local function shade(p, f, alpha)
	return packColor(p.r * f, p.g * f, p.b * f, alpha)
end

--- Draws an oriented box for the proxy. Only the up to 3 faces facing the camera are drawn.
local drawSphere = ffiFound and ffi.C.BNG_DBG_DRAW_Sphere or nop
local drawCylinder = ffiFound and ffi.C.BNG_DBG_DRAW_Cylinder or nop

local function drawProxy(p, camPos, dist)
	if p.isPerson then -- walking player: body cylinder + head, about 1.8 m tall
		local x, y, z = p.rpos.x, p.rpos.y, p.rpos.z - p.cogH
		local col = shade(p, 1, 230)
		drawCylinder(x, y, z, x, y, z + 1.45, 0.22, col, true)
		drawSphere(x, y, z + 1.65, 0.15, col, true)
		return
	end
	axX:setRotate(p.rrot, unitX)
	axY:setRotate(p.rrot, unitY)
	axZ:setRotate(p.rrot, unitZ)
	local hl, hw, hh = p.L * 0.5, p.W * 0.5, p.H * 0.5
	-- box center: the packet position is the cog, which sits roughly cogH above the ground
	center:set(axZ)
	center:setScaled(hh - p.cogH)
	center:setAdd(p.rpos)

	if dist > DETAIL_DISTANCE then
		-- far: one prism along the length axis, cheap
		tmpV:set(axY)
		tmpV:setScaled(hl)
		local x1, y1, z1 = center.x - tmpV.x, center.y - tmpV.y, center.z - tmpV.z
		local x2, y2, z2 = center.x + tmpV.x, center.y + tmpV.y, center.z + tmpV.z
		drawSquarePrism(x1, y1, z1, x2, y2, z2, p.W, p.H, p.W, p.H, shade(p, 1, 230), true)
		return
	end

	-- corners: index bits (x, y, z) -> sign
	for i = 1, 8 do
		local sx = (i - 1) % 2 == 0 and -hw or hw
		local sy = math.floor((i - 1) / 2) % 2 == 0 and -hl or hl
		local sz = math.floor((i - 1) / 4) == 0 and -hh or hh
		local c = corners[i]
		c:set(center.x + axX.x*sx + axY.x*sy + axZ.x*sz, center.y + axX.y*sx + axY.y*sy + axZ.y*sz, center.z + axX.z*sx + axY.z*sy + axZ.z*sz)
	end
	tmpV:set(camPos)
	tmpV:setSub(center)
	local dx, dy, dz = tmpV:dot(axX), tmpV:dot(axY), tmpV:dot(axZ)
	local c = corners
	-- top / bottom (z)
	if dz > hh then drawQuad(c[5], c[6], c[8], c[7], shade(p, 1.0, 235))
	elseif dz < -hh then drawQuad(c[1], c[2], c[4], c[3], shade(p, 0.4, 235)) end
	-- sides (x)
	if dx > hw then drawQuad(c[2], c[4], c[8], c[6], shade(p, 0.75, 235))
	elseif dx < -hw then drawQuad(c[1], c[3], c[7], c[5], shade(p, 0.75, 235)) end
	-- front / back (y)
	if dy > hl then drawQuad(c[3], c[4], c[8], c[7], shade(p, 0.6, 235))
	elseif dy < -hl then drawQuad(c[1], c[2], c[6], c[5], shade(p, 0.6, 235)) end
end

-- ============= COLLIDER POOL (experimental, proxyCollision) =============
-- Moving a TSStatic with setPosRot only moves its render mesh, the static collision used by the vehicle physics is
-- baked and only rebuilt with be:reloadCollision() (a full world rebuild, see core/dynamicProps.lua), so a moving
-- static collision box is not viable. The cheapest collision vehicles interact with are other vehicles, so a small
-- pool of simplified vehicles is spawned on demand, parked with setActive(0) and reused: they follow the proxy
-- through the regular positionVE mailbox ("vehPosPckt"..serverVehicleID), exactly like a real remote vehicle.

local function releaseCollider(gameVehicleID)
	local c = colliders[gameVehicleID]
	if not c then return end
	local vehicle = c.serverVehicleID and MPVehicleGE.getVehicleByServerID(c.serverVehicleID)
	if vehicle and vehicle.proxyColliderID == gameVehicleID then vehicle.proxyColliderID = nil end
	c.serverVehicleID = nil
	local veh = getObjectByID(gameVehicleID)
	if veh then
		veh:queueLuaCommand("if MPVehicleVE then MPVehicleVE.setServerID('') end")
		veh:setActive(0)
	end
end

local function applyColliderTarget(gameVehicleID)
	local c = colliders[gameVehicleID]
	local veh = getObjectByID(gameVehicleID)
	if not c or not veh or not c.serverVehicleID then return end
	veh:queueLuaCommand("if MPVehicleVE then MPVehicleVE.setVehicleType('R') MPVehicleVE.setServerID(mime.unb64('"..MPHelpers.b64encode(c.serverVehicleID).."')) end")
end

local function assignCollider(gameVehicleID, vehicle)
	local c = colliders[gameVehicleID]
	local veh = getObjectByID(gameVehicleID)
	local p = vehicle.proxy
	if not c or not veh or not p then return end
	c.serverVehicleID = vehicle.serverVehicleString
	vehicle.proxyColliderID = gameVehicleID
	if MPProxyMeshGE then MPProxyMeshGE.release(p) end
	veh:setActive(1)
	-- same rotation convention as the reset packets (onServerVehicleResetted)
	veh:setPositionRotation(p.rpos.x, p.rpos.y, p.rpos.z, p.rrot.x, p.rrot.y, p.rrot.z, p.rrot.w)
	if p.vcfPaint then
		pcall(extensions.core_vehicle_manager.liveUpdateVehicleColors, gameVehicleID, veh, 1, p.vcfPaint)
	end
	applyColliderTarget(gameVehicleID)
end

local function onColliderSpawned(gameVehicleID)
	colliders[gameVehicleID] = { serverVehicleID = nil }
	colliderCount = colliderCount + 1
end

--- Called by MPVehicleGE.onVehicleReady, the VE extensions of the collider are loaded now.
local function onColliderReady(gameVehicleID)
	if colliders[gameVehicleID] then applyColliderTarget(gameVehicleID) return true end
	return false
end

local function isCollider(gameVehicleID)
	return colliders[gameVehicleID] ~= nil
end

local function onColliderDestroyed(gameVehicleID)
	if colliders[gameVehicleID] then
		local c = colliders[gameVehicleID]
		local vehicle = c.serverVehicleID and MPVehicleGE.getVehicleByServerID(c.serverVehicleID)
		if vehicle and vehicle.proxyColliderID == gameVehicleID then vehicle.proxyColliderID = nil end
		colliders[gameVehicleID] = nil
		colliderCount = colliderCount - 1
	end
end

local function removeAllColliders()
	for gameVehicleID, _ in pairs(colliders) do
		local veh = getObjectByID(gameVehicleID)
		colliders[gameVehicleID] = nil
		if veh then veh:delete() end
	end
	colliders = {}
	colliderCount = 0
end

local function updateColliders(vehicles)
	if not cfg.enabled or not cfg.collision or not hasLocalVeh then
		for id, c in pairs(colliders) do if c.serverVehicleID then releaseCollider(id) end end
		return
	end
	local r2 = cfg.collisionRadius * cfg.collisionRadius
	local release2 = (cfg.collisionRadius + COLLIDER_RELEASE_MARGIN)^2
	-- release colliders that are not needed anymore
	for id, c in pairs(colliders) do
		if c.serverVehicleID then
			local v = vehicles[c.serverVehicleID]
			if not v or not v.isProxy or v.isSpawned or not v.proxy or v.proxy.rpos:squaredDistance(localVehPos) > release2 then
				releaseCollider(id)
			end
		end
	end
	-- find the closest proxy without collider inside the radius
	local best, bestD2 = nil, r2
	for _, v in pairs(vehicles) do
		if v.isProxy and not v.isSpawned and not v.isLocal and v.proxy and v.proxy.hasData and not v.proxyColliderID then
			local d2 = v.proxy.rpos:squaredDistance(localVehPos)
			if d2 < bestD2 then best, bestD2 = v, d2 end
		end
	end
	if not best then return end
	for id, c in pairs(colliders) do
		if not c.serverVehicleID and getObjectByID(id) then
			assignCollider(id, best)
			return
		end
	end
	-- no free collider, grow the pool (this spawn stutters, so it is rate limited together with real spawns)
	if colliderCount < cfg.poolSize and clock >= nextColliderSpawnAllowed and clock >= nextSpawnAllowed then
		nextColliderSpawnAllowed = clock + math.max(cfg.spawnInterval, 1)
		nextSpawnAllowed = clock + cfg.spawnInterval
		local id = MPVehicleGE.spawnProxyCollider(cfg.colliderModel, best.proxy.rpos, best.proxy.rrot)
		if id then
			onColliderSpawned(id)
			assignCollider(id, best)
		end
	end
end

-- ============= SWAP MANAGER =============
local function isEligibleForReal(v)
	return v.isProxy and not v.isSpawned and not v.isDeleted and not v.isIllegal and not v.spawnQueue
		and v.proxy and v.proxy.validModel ~= false and MPVehicleGE.hasSpawnData(v.serverVehicleString)
end

local function decide(vehicles, activeVehID)
	local realCount = 0
	local nearestCand, nearestCandD = nil, math.huge
	local farthestReal, farthestRealD = nil, -1
	local despawnCand, despawnCandD = nil, -1
	local despawn2 = cfg.despawnDist

	for serverVehicleID, v in pairs(vehicles) do
		if not v.isLocal and v:getOwner() then
			local d = refPos:distance(v.position)
			local p = v.proxy
			local cooled = not p or clock >= (p.cooldownUntil or 0)
			local isReal = v.isSpawned and v.gameVehicleID and v.gameVehicleID > 0
			local isPending = v.spawnQueue ~= nil and v.isProxy

			if isReal or isPending then
				realCount = realCount + 1
				local isActive = isReal and v.gameVehicleID == activeVehID
				if cooled and not isActive and not v.proxyForceReal then
					if not cfg.enabled then
						-- proxy mode off: nothing gets demoted
					elseif d > despawn2 and d > despawnCandD then -- demotion stays on, it never spawns anything
						despawnCand, despawnCandD = v, d
					end
					if d > farthestRealD then farthestReal, farthestRealD = v, d end
				end
			elseif isEligibleForReal(v) and cooled then
				-- only explicit requests (spectate / requestRealVehicle) unless distance based real spawns are enabled
				local wanted = (not cfg.enabled) or v.proxyForceReal or (cfg.autoReal and d < cfg.spawnDist)
				local dd = v.proxyForceReal and -1 or d
				if wanted and dd < nearestCandD then nearestCand, nearestCandD = v, dd end
			end
		end
	end

	-- real -> proxy: out of range
	if despawnCand and clock >= nextDespawnAllowed then
		nextDespawnAllowed = clock + DESPAWN_INTERVAL
		if MPVehicleGE.demoteToProxy(despawnCand.serverVehicleString) then
			if despawnCand.proxy then despawnCand.proxy.cooldownUntil = clock + cfg.cooldown end
			realCount = realCount - 1
		end
	end

	if not nearestCand then return end
	local limit = cfg.enabled and cfg.maxReal or math.huge

	-- real -> proxy: make room for a much closer proxy (cap reached)
	if realCount >= limit and cfg.enabled and cfg.autoReal and farthestReal and farthestReal ~= despawnCand
		and farthestRealD > nearestCandD + CAP_SWAP_MARGIN and clock >= nextDespawnAllowed then
		nextDespawnAllowed = clock + DESPAWN_INTERVAL
		if MPVehicleGE.demoteToProxy(farthestReal.serverVehicleString) then
			if farthestReal.proxy then farthestReal.proxy.cooldownUntil = clock + cfg.cooldown end
			realCount = realCount - 1
		end
	end

	-- proxy -> real, at most one per spawnInterval (forced ones, e.g. spectate, skip the interval)
	if (realCount < limit or nearestCand.proxyForceReal) and (clock >= nextSpawnAllowed or nearestCand.proxyForceReal) then
		nextSpawnAllowed = clock + cfg.spawnInterval
		if nearestCand.proxyColliderID then releaseCollider(nearestCand.proxyColliderID) end
		if MPProxyMeshGE then MPProxyMeshGE.release(nearestCand.proxy) end
		nearestCand.proxyForceReal = nil
		if MPVehicleGE.promoteToReal(nearestCand.serverVehicleString) then
			nearestCand.proxy.cooldownUntil = clock + cfg.cooldown
		end
	end
end

--- Per frame update, called by MPVehicleGE.onPreRender before nametags are drawn.
-- @tparam number dt
-- @tparam vec3 cameraPos distance reference (active vehicle, or camera in free cam)
-- @tparam number activeVehID game id of the vehicle the local player is in, or nil
-- perf / tier statistics for MPProxyTest (cheap counters, no allocations)
local perfTimer = nil -- created lazily, hptimer is not defined yet when extensions load
local function getPerfTimer()
	if perfTimer == nil then
		local ok, t = pcall(function() return (hptimer and hptimer()) or (HighPerfTimer and HighPerfTimer()) end)
		perfTimer = ok and t or false
	end
	return perfTimer or nil
end
local stats = { frames = 0, totalMs = 0, maxMs = 0, decideMs = 0, decides = 0, mesh = 0, box = 0, prism = 0, hidden = 0 }
local function resetPerf()
	stats.frames, stats.totalMs, stats.maxMs, stats.decideMs, stats.decides = 0, 0, 0, 0, 0
end

local function update(dt, cameraPos, activeVehID)
	local perfTimer = getPerfTimer()
	if perfTimer then perfTimer:stopAndReset() end
	clock = clock + dt
	refPos:set(cameraPos)
	local activeVeh = activeVehID and getObjectByID(activeVehID)
	hasLocalVeh = activeVeh ~= nil
	if activeVeh then localVehPos:set(activeVeh:getPositionXYZ()) end

	local vehicles = MPVehicleGE.getVehicles()
	local camX, camY, camZ = core_camera.getPositionXYZ()
	tmpV:set(camX, camY, camZ)
	local camPos = vec3(tmpV) -- one allocation per frame, not per proxy
	local drawDist2 = cfg.drawDist * cfg.drawDist
	local nMesh, nBox, nPrism, nHidden = 0, 0, 0, 0

	for _, v in pairs(vehicles) do
		local p = v.proxy
		if v.isProxy and not v.isSpawned and not v.isLocal and p and p.hasData then
			predict(v, p, dt)
			if not v.proxyColliderID and not v.isDeleted then
				local d2 = camPos:squaredDistance(p.rpos)
				if d2 < drawDist2 then
					local dist = math.sqrt(d2)
					-- tier 1: real body meshes (MPProxyMeshGE), tier 2: box, tier 3 (beyond drawDist): nametag only
					if p.meshObjects and MPProxyMeshGE and MPProxyMeshGE.drawProxy(p, dist) then
						nMesh = nMesh + 1
					elseif v.isFakeTest then
						nHidden = nHidden + 1 -- MPProxyTest vehicles are only ever shown as meshes
					else
						drawProxy(p, camPos, dist)
						if dist > DETAIL_DISTANCE then nPrism = nPrism + 1 else nBox = nBox + 1 end
					end
				else
					nHidden = nHidden + 1
				end
			end
		end
	end

	stats.mesh, stats.box, stats.prism, stats.hidden = nMesh, nBox, nPrism, nHidden

	decisionTimer = decisionTimer - dt
	local decideStart = perfTimer and perfTimer:stop() or 0
	local didDecide = decisionTimer <= 0
	if didDecide then
		decisionTimer = DECISION_INTERVAL
		decide(vehicles, activeVehID)
		updateColliders(vehicles)
		if MPProxyMeshGE then
			MPProxyMeshGE.decide(vehicles, refPos)
			for _, v in pairs(vehicles) do -- use the real mesh bounds for the box fallback once known
				local p = v.proxy
				if p and p.meshKey and not p.dimsFromMesh then
					local shape = MPProxyMeshGE.getShape(p.meshKey)
					if shape and shape.state == "ready" and shape.minX then
						setDims(p, shape.maxY - shape.minY, shape.maxX - shape.minX, shape.maxZ - (shape.groundZ or shape.minZ))
						p.dimsFromMesh = true
					end
				end
			end
		end
	end
	if perfTimer then
		local ms = perfTimer:stop()
		stats.frames = stats.frames + 1
		stats.totalMs = stats.totalMs + ms
		if ms > stats.maxMs then stats.maxMs = ms end
		if didDecide then
			stats.decides = stats.decides + 1
			stats.decideMs = stats.decideMs + (ms - decideStart)
		end
	end
end

--- Returns tier counts, collider usage and per frame cost of update(). Resets the perf window if resetWindow is set.
local function getStats(resetWindow)
	local out = { mesh = stats.mesh, box = stats.box, prism = stats.prism, hidden = stats.hidden,
		real = 0, realQueued = 0, proxies = 0, collidersUsed = 0, collidersPool = 0, timerAvailable = getPerfTimer() ~= nil,
		frames = stats.frames, avgMs = stats.frames > 0 and stats.totalMs / stats.frames or 0, maxMs = stats.maxMs,
		avgDecideMs = stats.decides > 0 and stats.decideMs / stats.decides or 0 }
	for _, v in pairs(MPVehicleGE.getVehicles()) do
		if not v.isLocal then
			if v.isSpawned then out.real = out.real + 1
			elseif v.isProxy then
				out.proxies = out.proxies + 1
				if v.proxyForceReal then out.realQueued = out.realQueued + 1 end
			end
		end
	end
	for _, c in pairs(colliders) do
		out.collidersPool = out.collidersPool + 1
		if c.serverVehicleID then out.collidersUsed = out.collidersUsed + 1 end
	end
	if resetWindow then resetPerf() end
	return out
end
M.getStats = getStats

--- Asks the manager to swap a proxy for a real vehicle as soon as possible (ignores distance, cap and interval).
local function requestReal(vehicle)
	if vehicle and vehicle.isProxy and not vehicle.isSpawned then
		vehicle.proxyForceReal = true
		decisionTimer = 0
		return true
	end
	return false
end

local function isEnabled()
	return cfg.enabled
end

local function getSettings()
	return cfg
end

local function reset()
	removeAllColliders()
	if MPProxyMeshGE then MPProxyMeshGE.reset() end
	nextSpawnAllowed, nextDespawnAllowed, nextColliderSpawnAllowed = 0, 0, 0
end

local function onSettingsChanged()
	readSettings()
	if not cfg.collision then
		for id, c in pairs(colliders) do if c.serverVehicleID then releaseCollider(id) end end
	end
end

local function onExtensionLoaded()
	readSettings()
end

detectGlobalWrites() -- reenable global write notifications

M.update              = update
M.initProxy           = initProxy
M.onPositionPacket    = onPositionPacket
M.seedFromVehicle     = seedFromVehicle
M.snapProxy           = snapProxy
M.requestReal         = requestReal
M.isEnabled           = isEnabled
M.getSettings         = getSettings
M.getModelInfo        = getModelInfo
M.reset               = reset
M.isCollider          = isCollider
M.onColliderReady     = onColliderReady
M.onColliderDestroyed = onColliderDestroyed
M.onSettingsChanged   = onSettingsChanged
M.onExtensionLoaded   = onExtensionLoaded
M.onInit = function() setExtensionUnloadMode(M, "manual") end

return M
