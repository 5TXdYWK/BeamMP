// BeamMP New UI?
// import bridge and route definitions
import { useBridge } from "@/bridge"
import { ROUTE_SOURCE_ID, routeRecords } from "./routes.js"
import { BEAMMP_ROUTE_NAME, BEAMMP_TOS_ROUTE_NAME, BEAMMP_LAUNCHER_ROUTE_NAME, BEAMMP_LOGIN_ROUTE_NAME } from "./shared/constants.js"
import { useBeamMPState } from "./shared/beammpState.js"
import { $translate } from "@/services/translation"
import { ACCENTS } from "@/common/components/base"
import { openConfirmation } from "@/services/popup"

// get lua and events interfaces
const { api, lua, events } = useBridge()
// note: here we use "low-level" events from the bridge because this file is not a Vue component
//       so, never forget to unsubscribe from events when the mod is unloaded

const { state } = useBeamMPState()

// mod root directory
const MOD_ROOT = "/ui/ui-vue/mods/BeamMP"

// title for the button and tabs
const TITLE = "BeamMP"
const TITLE_translationId = 'ui.common.beammp.title'

// 1 and 2. Register a Main Menu button. `addButton` is a function.
function addBeamMPMainMenuButton(addButton) {
  addButton({
    // Old Angular-compatible menu button shape.
    //translateid: TITLE_translationId,
    //icon: `${MOD_ROOT}/icons/account-multiple.svg`,
    //targetState: BEAMMP_ROUTE_NAME,

    // New Vue Way
    // main menu button title
    title: TITLE,
    // main menu button icon (must be a valid icon id from the bngIcons.js)
    iconId: "peopleOutline",
    // route to open when the button is pressed
    action: BEAMMP_ROUTE_NAME,
  })
}

// Vue records include component objects, while Lua only needs the serialisable route configuration.
function toLuaRoutes(records) {
  return records.map(record => ({
    name: record.name,
    path: record.path,
    meta: record.meta,
    ...(record.children ? { children: toLuaRoutes(record.children) } : {}),
  }))
}

// Register the Vue matcher first, then expose the same route to Lua navigation.
async function registerRoutes() {
  window.bngRoutes.add([{ path: ROUTE_SOURCE_ID, routes: routeRecords }])
  const result = await lua.extensions.ui_router_routeManager.registerModRoutes(
    ROUTE_SOURCE_ID,
    toLuaRoutes(routeRecords),
  )
  if (!result?.success) {
    window.bngRoutes.remove([ROUTE_SOURCE_ID])
    console.error("Failed to register BeamMP route", result?.errors)
  }
  return result
}

// Remove the Vue matcher first so navigation cannot target a stale component.
async function unregisterRoutes() {
  window.bngRoutes.remove([ROUTE_SOURCE_ID])
  await lua.extensions.ui_router_routeManager.unregisterModRoutes(
    ROUTE_SOURCE_ID,
    { fallbackRoute: "menu" },
  )
}

// The game hot-reloads every Vue mod (onUnload > re-eval > onLoad) whenever any mod adds files under
// /ui/ui-vue/mods/, e.g. while MPModManager activates server mods during a join. Unregistering our routes
// makes the route manager fall back to "menu", unmounting the BeamMP page and its loading overlay.
// This module and beammpState.js are re-evaluated on reload, so the snapshot lives on window.
const RELOAD_SNAPSHOT_KEY = "__beammpReloadSnapshot"
const RELOAD_SNAPSHOT_MAX_AGE_MS = 10000

function luaResult(command) {
  return new Promise(resolve => api.engineLua(command, data => resolve(data)))
}

// Remember the active BeamMP route (and the join overlay) before our routes go away.
async function saveReloadSnapshot() {
  window[RELOAD_SNAPSHOT_KEY] = null
  try {
    const current = await luaResult("(function() local c = extensions.ui_router and extensions.ui_router.getCurrent(); local r = c and c.request; if not r then return nil end; return {name = r.name, params = r.params} end)()")
    const name = current?.name
    if (typeof name !== "string" || !(name === BEAMMP_ROUTE_NAME || name.startsWith(BEAMMP_ROUTE_NAME + "."))) return
    window[RELOAD_SNAPSHOT_KEY] = {
      time: Date.now(),
      name,
      params: current.params && typeof current.params === "object" ? current.params : undefined,
      loadingOverlayVisible: state.loadingOverlayVisible.value,
      loadingStatus: state.loadingStatus.value,
      downloadingMods: state.downloadingMods.value,
    }
  } catch (err) {
    console.error("[BeamMP] Failed to save route before UI reload", err)
  }
}

// After a hot reload, return to the remembered BeamMP route unless a level has started loading meanwhile.
async function restoreReloadSnapshot() {
  const snapshot = window[RELOAD_SNAPSHOT_KEY]
  window[RELOAD_SNAPSHOT_KEY] = null
  if (!snapshot || Date.now() - snapshot.time > RELOAD_SNAPSHOT_MAX_AGE_MS) return

  try {
    const blocked = await luaResult("(function() local m = getMissionFilename and getMissionFilename(); local c = extensions.ui_router and extensions.ui_router.getCurrent(); local r = c and c.request; return (type(m) == 'string' and m ~= '') or not r or r.name ~= 'menu' end)()")
    if (blocked) return // in a level, loading one, or the user already moved elsewhere

    state.loadingOverlayVisible.value = Boolean(snapshot.loadingOverlayVisible)
    state.loadingStatus.value = snapshot.loadingStatus || ""
    state.downloadingMods.value = Array.isArray(snapshot.downloadingMods) ? snapshot.downloadingMods : []
    await lua.extensions.ui_router.navigate(snapshot.name, snapshot.params)
  } catch (err) {
    console.error("[BeamMP] Failed to restore route after UI reload", err)
  }
}

// convenience ID for for example #3
const TAB_ID = "beammp"
let removeRouteGuard = null
let activeBeamMPDialog = null

function escapeHtml(value) {
  return String(value ?? "")
    .replace(/&/g, "&amp;")
    .replace(/</g, "&lt;")
    .replace(/>/g, "&gt;")
    .replace(/\"/g, "&quot;")
    .replace(/'/g, "&#39;")
}


async function showBeamMPDialog(options = {}) {
  if (activeBeamMPDialog) return

  activeBeamMPDialog = openConfirmation(
    escapeHtml(options.title) || $translate.instant("ui.beammp.mdDialog.disconnectGeneric"),
    escapeHtml(options.text) || "",
    [
      {
        label: escapeHtml(options.okText) || $translate.instant("ui.beammp.mdDialog.returnToMenu"),
        value: "returnToMenu",
        extras: { default: true, confirm: true, accent: ACCENTS.main },
      },
      {
        label: $translate.instant("ui.beammp.mdDialog.continueOffline"),
        value: "continueOffline",
        extras: { cancel: true, outsideCancel: false, accent: ACCENTS.text },
      },
    ],
  )

  try {
    const result = await activeBeamMPDialog
    if (result === "returnToMenu") {
      api.engineLua(
        options.okLua
        || "if MPCoreNetwork and MPCoreNetwork.leaveServer then MPCoreNetwork.leaveServer(true) end",
      )
    }
  } finally {
    activeBeamMPDialog = null
  }
}

async function isLauncherConnected() {
	return new Promise(function(resolve, reject) {
		bngApi.engineLua("MPCoreNetwork.isLauncherConnected()", (data) => {
			resolve(data);
		});
	});
}

export async function onLoad() {
  events.on("onBeamMPShowVueDialog", showBeamMPDialog)

  // Register the standalone route before advertising its Main Menu button.
  const routeResult = await registerRoutes()
  if (routeResult?.success) {
    // This event is sent when we're in the main menu.
    events.on("MainMenuButtons", addBeamMPMainMenuButton)
    // Broadcast this event in case we already were in main menu when the mod loaded
    events.emit("BroadcastMainMenuButtons")
    await restoreReloadSnapshot()
  }

  // 3. A dedicated "BeamMP" pause tab.
  // tab must be registered before its buttons, so make sure to await for it
  await lua.extensions.ui_pause_actions.registerModTab({
    id: TAB_ID,
    label: TITLE,
    icon: "peopleOutline",
    //card2ComponentName: `${MOD_ROOT}/cards/BeamMPPausePlayersCard.vue`,
  })
  // then, register rail buttons for that tab
  await lua.extensions.ui_pause_actions.registerModButton({
    id: "beammp-pause-player-list",
    tabId: TAB_ID,
    label: $translate.instant("ui.common.beammp.playerList"),
    icon: "itemsTree",
    //componentName: `${MOD_ROOT}/cards/BeamMPPauseMainCard.vue`,
    componentName: `${MOD_ROOT}/cards/BeamMPPausePlayersCard.vue`,
  })
  await lua.extensions.ui_pause_actions.registerModButton({
    id: "beammp-pause-server-details	",
    tabId: TAB_ID,
    label: $translate.instant("ui.common.beammp.serverDetails"),
    icon: "globeSimplified",
    componentName: `${MOD_ROOT}/cards/BeamMPPauseServerDetailsRedirect.vue`,
  })

  removeRouteGuard?.()
  removeRouteGuard = vueRouter.beforeEach(async (to, from) => {
    if (to.name.startsWith(BEAMMP_ROUTE_NAME)) {
      var connected = await isLauncherConnected()
      

      if (!connected) {
        if (to.name !== BEAMMP_LAUNCHER_ROUTE_NAME) {
          return { name: BEAMMP_LAUNCHER_ROUTE_NAME }
        }
      }

      if (state.tosAccepted.value == false && to.name !== BEAMMP_TOS_ROUTE_NAME) {
        return { name: BEAMMP_TOS_ROUTE_NAME }
      }

      if (state.auth.value == null && to.name !== BEAMMP_LOGIN_ROUTE_NAME) {
        return { name: BEAMMP_LOGIN_ROUTE_NAME }
      }
      
    }
  }) 
}

export async function onUnload() {
  events.off("onBeamMPShowVueDialog", showBeamMPDialog)

  // stop listening for the Main Menu button - this is important to do to avoid memory leaks
  events.off("MainMenuButtons", addBeamMPMainMenuButton)
  events.emit("BroadcastMainMenuButtons") // poke buttons to update

  // remember where we were in case this is a hot reload, then remove the standalone route
  await saveReloadSnapshot()
  await unregisterRoutes()
  removeRouteGuard?.()
  removeRouteGuard = null

  // you can unregister buttons manually at any time like so:
  // await lua.extensions.ui_pause_actions.unregisterModButton("annas-toolbox-workshop")
  // await lua.extensions.ui_pause_actions.unregisterModButton("annas-toolbox-vehicle")

  // however, unregisterModTab already unregisters its buttons, so this call is enough for cleanup
  await lua.extensions.ui_pause_actions.unregisterModTab(TAB_ID)
}
