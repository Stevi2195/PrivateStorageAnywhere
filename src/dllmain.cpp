#include <windows.h>
#include <psapi.h>
#include <intrin.h>
#include <cstdio>
#include <cstring>
#include <string>

// ============================================================
//  Private Storage Anywhere
//
//  Opens the Camp Warehouse (Private Storage) and the 5 housing
//  chests (Gatherables, Dresser, Refrigerator, Symbol, Collecting)
//  from anywhere with a hotkey (defaults F4–F9) or controller
//  button (default LB + LeftStick for Private, LB + RightStick for
//  Gatherables).
//
//  See CHANGELOG.txt for version history.
// ============================================================

static uintptr_t g_gameBase = 0, g_imageSize = 0;
static bool g_ready = false;
static FILE* g_logFile = nullptr;
static HMODULE g_hModule = nullptr;
static HWND g_gameWindow = nullptr;
static WNDPROC g_originalWndProc = nullptr;
static bool g_enabled = true, g_debugLog = true;
// Trace mode: when 1 in INI, installs additional hooks on warehouse Init
// (vtable[1] = base+0xAA39E0), Show (vtable[51] = base+0xA9F4E0), and
// the panel-descriptor show primitive (base+0x346A3E0). Every call to
// any of these — plus every Handler call — logs a full warehouse state
// snapshot (+0x218, +0x2CD, +0x120, descriptor+0x269, descriptor+0x26A).
// Used to capture the exact call sequence the game runs during natural
// NPC warehouse-open in CD 1.10, so we can replicate it from the mod.
// MUST be 0 in normal use (very noisy log + 4 extra hooks).
static bool g_traceMode = false;
// Legacy "single hotkey" global. Kept for backwards compatibility with old
// INIs that used `Hotkey=...` instead of per-panel <Name>Hotkey keys.
// LoadConfig() overrides this with the INI value (default 0 = disabled).
// The runtime initial value here is also 0 so that no key fires before
// LoadConfig has run.
static DWORD g_hotkey = 0;
static DWORD g_modifierKey = 0;
static DWORD g_reloadKey = 0;
static char g_iniPath[MAX_PATH] = {};

// Resolved function addresses
static uintptr_t g_fnHandler = 0;
static uintptr_t g_fnModeSwitcher = 0, g_fnCanShow = 0, g_fnSetInventory = 0;
static uintptr_t g_fnSetTitle = 0;
static uintptr_t g_fnSetTitleDirect = 0;  // FUN_1434159c0: UTF-8 aware wchar text setter (bypasses bridge check)
static uintptr_t g_fnSetCursorVisible = 0;  // QOL: hides cursor immediately on warehouse close
static uintptr_t g_warehouseVtableEntry = 0;  // vtable address containing handler — used for auto-capture verification
static uintptr_t g_warehouseVtableStart = 0;  // vtable start of warehouse class — set on first successful capture
static uint32_t  g_modalDialogOff = 0;     // handler+N: move-quantity dialog pointer
static bool      g_modalOffValid  = true;  // set false once the slot at +g_modalDialogOff stops looking like a
                                           // modal-dialog pointer (handler-struct drift guard; disables modal tracking)
static uintptr_t g_langByteAddr = 0;      // address of language byte (resolved dynamically from Steam API init function)

// ItemDetailModal ("View Details" popup) tracking. The legacy 1.0.4.x ctor
// (base+0xC316D0) and dtor (base+0xB90360) addresses moved in 1.0.5.0; the
// canonical entry is now the open-handler FUN_140B4D310 (base+0xB4D310),
// found via the "ItemDetailModalMessage" string xref. We hook entry to
// increment the active count, then poll handler+0x258 (ModalDlgOff) for
// dismissal — when childCount goes to 0 the count is cleared. This avoids
// having to chase a dtor address that drifts every patch.
static volatile LONG g_itemDetailActiveCount = 0;
static uintptr_t g_addrItemDetailCtor = 0;

// Struct offsets — all resolved dynamically from game code at runtime (update-proof).
// Defaults match the build in which each offset was first discovered; they serve as
// a sane fallback if the dynamic resolver fails.  DO NOT use the default values
// directly in code — always go through these variables.
static uint32_t g_offActiveFlag   = 0x118;  // handler+N: u8 active flag (read by CanShow)
static uint32_t g_offPanelValue   = 0x110;  // handler+N: panel value (set by base-class 0x0e)
static uint32_t g_offBottomLabel  = 0x308;  // handler+N: cpp-ware-house-inventory-title node
static uint32_t g_offTopTitle     = 0x0E8;  // handler+N: top title text node (NpcInteractionTitle). Resolved via the
                                            // "selector-title-subtext-stage" binding chain (1.13.01: 0xF0); forced
                                            // to 0 (=write disabled) when the chain can't be cross-validated.
static uint32_t g_offSubObject    = 0x08;   // handler+N: ptr to sub-object (contains panelId)
static uint32_t g_offSubPanelId   = 0x92;   // subObject+N: u16 panelId
static uint32_t g_offModeByte     = 0xCA8;  // mainChar+N: u8 current mode
static uint32_t g_offSubByte      = 0xCA9;  // mainChar+N: u8 current sub-mode
static uint32_t g_offModeFlags    = 0xCB1;  // mainChar+N: mode flag array (7 bytes)
static uint32_t g_offSubtypes     = 0xCB8;  // mainChar+N: subtype array (15 bytes; matches g_savedSubtypes[15])
static uint32_t g_storeSubIndex   = 5;      // subtype index whose derived sub-mode emits the "store" view-tag.
                                            // VERSION-SPECIFIC (flips between updates): 1.09=5, 1.10=6, 1.12.00=5.
                                            // Re-find: decompile ModeSwitcher (base+0x721BD0 on 1.12.00),
                                            // read switch(sub), pick the case that appends the "store" string.
static uint32_t g_offDonationState = 0x330; // handler+N: first of 3 donation faction shorts (cleared on open)
static uintptr_t g_fnSetDonationFaction = 0; // handler for "SetDonationFaction" command — scanned for donation-state offset
// 0x15 "prepare" sub-object offsets — game's 0x15 dispatcher does 3 virtual calls on these.
// Must be validated non-null before sending an empty 0x15, otherwise the dispatcher crashes
// (sub-objects are only initialized after NPC interaction).  Resolved dynamically from the
// Handler body (scan for 3 consecutive `MOV RCX,[param_1+disp32]; MOV RAX,[RCX]; CALL [RAX+imm]`).
// Defaults match the pre-Apr-11 game layout; the Apr-23 layout is 0x2e8/0x2f8/0x320.
static uint32_t g_offPrepare1 = 0x2c8;
static uint32_t g_offPrepare2 = 0x2d8;
static uint32_t g_offPrepare3 = 0x300;
static uintptr_t g_mainCharGlobalPtr = 0;   // address of global singleton pointer; mainChar = *(*(globalPtr) + 0x48)

// Captured game state (accessed from multiple threads via Interlocked ops)
static volatile LONG64 g_mainChar = 0;
// Single handler slot. The Gatherables Chest uses the SAME UIGamePlayControlRootWarehouse2
// controller (same panelId 0x0058, same vtable) as Private Storage — they differ only in
// which SetInventory filter string is passed when opening. So we track one handler and
// switch inventories by re-calling SetInventory with the other string.
static volatile LONG64 g_handlerThis = 0;
// Save+restore for handler+0x110 (in 1.06 = PanelValue scalar; in 1.08 layout
// changed — may be a pointer slot, zeroing it crashes the natural NPC-open
// path that follows our mod's close). Captured at first F-key open, restored
// on close. -1 = not yet captured.
static volatile LONG64 g_savedPanelValueSlot = -1;
// false once the captured PanelValue slot holds a canonical pointer instead of a
// small type-id scalar — i.e. handler+g_offPanelValue has drifted to a different
// field. Then the override/restore writes are skipped so we never clobber a live
// pointer with a valid-but-wrong write (which SEH cannot catch).
static bool g_panelValueSlotValid = true;
static volatile LONG64 g_cursorObj = 0;
static volatile LONG g_warehouseActive = 0;

// CD 1.10 capture-and-replay groundwork (capture phase only for now).
// The warehouse VIEW only mounts when the menu-manager's "interaction target"
// (menuMgr+0x10C8) is set — which the game does only during a real warehouse
// interaction. We can't synthesise a valid target (guessing crashes), so we
// CAPTURE the real one the game produces during a natural open, validate it,
// and (later) replay it on hotkey. menuMgr = *(*(g_mainCharGlobalPtr)+0x90).
static volatile LONG64 g_capturedMenuTarget = 0;  // last non-null menuMgr+0x10C8 seen
static volatile LONG64 g_capturedMenuTargetVt = 0; // its vtable (for identity/validation)
static volatile LONG g_handlerHitCount = 0;
static volatile LONG g_canShowSeen118 = 0;  // set to 1 once +0x118 has been seen as 1
static volatile LONG g_canShowZeroCount = 0; // consecutive frames where +0x118==0 (de-bounce close detection)

// Active panel selector. F6 opens PRIVATE; F7/F8/F9/F12/Num0 open the housing
// chests directly. Each press is a fresh open from cold.
enum ActivePanel {
    PANEL_PRIVATE      = 0,  // CampWareHouse (Private Storage, ~640 slots)
    PANEL_GATHERABLES  = 1,  // Housing_GatheredMaterials (Gatherables Chest)
    PANEL_DRESSER      = 2,  // Housing_Dresser
    PANEL_REFRIGERATOR = 3,  // Housing_Refrigerator
    PANEL_SYMBOL       = 4,  // Housing_Symbol
    PANEL_COLLECTING   = 5,  // Housing_Collecting
    PANEL_COUNT        = 6,
};
static volatile LONG g_activePanel = PANEL_PRIVATE;

// Per-panel definition. initString feeds SetInventory; hotkey is the direct-
// open shortcut (0 = disabled). Each hotkey is a panel toggle: opens cold if
// warehouse is closed, otherwise closes the warehouse.
struct PanelDef {
    const char* name;                // English logging name
    char        initString[256];     // SetInventory filter (overridable via INI)
    DWORD       hotkey;              // Keyboard VK code, 0 = no dedicated hotkey
    DWORD       modifier;            // Keyboard VK code, 0 = no modifier
    WORD        controllerButton;    // XInput button mask, 0 = no button
    WORD        controllerModifier;  // XInput hold-this-first mask, 0 = no modifier
    int         psButtonByteOff;     // PS5/PS4 HID: byte offset from buttons1; -1 = unbound
    BYTE        psButtonBitMask;     // PS5/PS4 HID: bit mask within that byte
    int         psModifierByteOff;   // PS5/PS4 HID modifier byte offset; -1 = no modifier
    BYTE        psModifierBitMask;   // PS5/PS4 HID modifier bit mask
    int         tabIndex;            // handler+0x1E0 value for this panel (-1 = don't write)
};
// tabIndex = handler+0x1E0 value to write before SetInventory. The slot-grid
// renderer (FUN_140A78690 @ base+0xA78690) reads sub[handler+0x1E0]+0x218 to
// pick which channel feeds items. With a 2-token initString
// ("Character;ChannelX"), ChannelX always lands in sub[1] — so tabIndex=1 for
// every chest panel. Private is left at -1 (don't write) because the keyboard
// hotkey already works with the game's natural state and we don't want to
// disturb that.
// Code defaults match the shipped INI defaults. Fields per row:
//   name, initString, hotkey, modifier, xiButton, xiModifier,
//   psButtonByteOff, psButtonBitMask, psModifierByteOff, psModifierBitMask,
//   tabIndex
// Keyboard defaults: F4..F9 (one per panel). Controller defaults: only
// Private + Gatherables get controller bindings; the other housing chests
// are keyboard-only (rows of 0/-1). PS5/PS4 mirrors the controller layout:
// L1+L3 → Private, L1+R3 → Gatherables.
static PanelDef g_panels[PANEL_COUNT] = {
    { "Private",      "Character,Focus,True;CampWareHouse,Focus,True",              0x73 /*F4*/,  0, 0x0040 /*LStick*/, 0x0100 /*LB*/, 1, 0x40 /*L3*/, 1, 0x01 /*L1*/, -1 },
    { "Gatherables",  "Character,Focus,True;Housing_GatheredMaterials,Focus,True",  0x74 /*F5*/,  0, 0x0080 /*RStick*/, 0x0100 /*LB*/, 1, 0x80 /*R3*/, 1, 0x01 /*L1*/,  1 },
    { "Dresser",      "Character,Focus,True;Housing_Dresser,Focus,True",            0x75 /*F6*/,  0, 0, 0, -1, 0, -1, 0,  1 },
    { "Refrigerator", "Character,Focus,True;Housing_Refrigerator,Focus,True",       0x76 /*F7*/,  0, 0, 0, -1, 0, -1, 0,  1 },
    { "Symbol",       "Character,Focus,True;Housing_Symbol,Focus,True",             0x77 /*F8*/,  0, 0, 0, -1, 0, -1, 0,  1 },
    { "Collecting",   "Character,Focus,True;Housing_Collecting,Focus,True",         0x78 /*F9*/,  0, 0, 0, -1, 0, -1, 0,  1 },
};
// Per-panel last/current state for PS button edge detection (parallel to g_panels[]).
static bool g_panelPsLastDown[PANEL_COUNT] = {};
static bool g_panelPsCurrentDown[PANEL_COUNT] = {};
static bool g_panelPsModifierDown[PANEL_COUNT] = {};
// Per-panel last-down state for XInput button edge detection (parallel to g_panels[]).
// Keeps the XInput per-panel logic structurally identical to the DirectInput version
// (which uses g_panelPsLastDown) — each panel tracks its own rising edge instead of
// sharing the global g_prevButtons mask. This avoids cross-panel interference and
// makes the two paths trivially auditable.
static bool g_panelXiLastDown[PANEL_COUNT] = {};
// XInput B-button last-down state (parallel to g_circleWasDown for DualSense Circle).
static bool g_xiBWasDown = false;

// Per-panel panelValue (handler+0x110). The game sets this from a type-0x05 sub-command
// in the 0x0e-show packet (parsed as uint64 from string via strtoull). Our 0x0e packet
// has no sub-commands, so panelValue stays at 0 and the container isn't bound.
// Workaround: after the 0x0e call, write panelValue manually for the active panel.
// For Gatherables we look up the per-session ID via the global Inventory-Type
// hash-map at runtime (see LookupInventoryTypeId).
static volatile LONG g_privatePanelValueCfg     = 0;       // 0 = no override
static volatile LONG g_gatherablesPanelValueCfg = 0;       // 0 = use runtime lookup

// Resolved addresses (Weg F).
// DAT_145e8f768 holds a POINTER to the canonical "Housing_GatheredMaterials" string.
// FUN_14ee1ecd0 takes a string pointer and writes a 16-bit panel-ID into out param 2.
// Internally it walks a global lookup table populated at game-init.
static uintptr_t g_pHGMStringSlot = 0;       // Address of the slot holding the string pointer
static uintptr_t g_fnTypeNameLookup = 0;     // Address of the lookup function

// Cached panel-id resolved via hash-map lookup once per session.
static volatile LONG g_resolvedGatherablesId = 0;  // 0 = not resolved yet, -1 = lookup failed

// Container vtable for the panel-bound object at handler+0x170. Starts at 0
// and is auto-relearned at runtime by the sticky observer (5 consecutive
// sightings of the same vtable pointer → adopted as canonical). Used to
// validate sticky-restore candidates so we don't write a stale heap pointer.
static uintptr_t g_addrContainerVtable      = 0;

// InventoryInfoManager singleton ptr-of-ptr. Layout (verified via Ghidra
// FUN_1404e9780 — GetInventoryInfo by InventoryKey):
//   *(mgr + 0x08) = uint32 count
//   *(mgr + 0x50) = InventoryInfo*[] (8 bytes per entry, indexed by key)
// InventoryInfo + 0x48 = ushort base slot count (default 10 for housing,
// 640 for CampWareHouse). FUN_1404de7c0 reads it as the "max slots" base
// before adding character expansions. Patching this at runtime updates
// every consumer (UI, item put-in, etc).
static uintptr_t g_addrInventoryInfoMgrPtr  = 0;  // resolved dynamically via SetInventory scan (drift-resistant)

// Per-panel sticky-binding state. When a warehouse panel is active and the
// game has written a valid container pointer into handler+0x170, we save it
// indexed by the currently-active panel. On a later open/switch to that
// panel we restore the saved pointer (after validating its vtable). Without
// per-panel storage, all housing panels would share Gatherables's container
// and show the wrong items.
static volatile LONG64 g_panelStickyContainer[PANEL_COUNT] = {};
// Marks "mod owns this sticky for the current session" — set when mod writes
// a known-good container (factory-create / sticky-restore), cleared on panel
// close. While set, the observer must NOT overwrite the sticky from
// handler+0x170 — that pointer can be a game-recycled placeholder during
// active warehouse, not the chest-specific container we wrote.
static volatile LONG g_panelStickyOwnedByMod[PANEL_COUNT] = {};
// Tracks which panel's container is currently bound to handler+0x170. When
// we switch to a different panel, we force a re-bind so SetInventory sees
// the correct inventory pool.
static volatile LONG g_currentBoundPanel = -1;

// In-place handler/sub-field patching for housing chests: when F7 opens GC
// we don't replace the container at handler+0x170 (that crashes — and pre-
// NPC it's NULL anyway). Instead we save + patch a few specific fields on
// the warehouse handler that control panel-mode and capacity, then restore
// them on close. Values originally from post-NPC memory diff +
// runtime field-scan (handler+0x39C identified as the max-slots field).
static volatile LONG   g_savedCamp_9C      = 0;
static volatile LONG   g_savedCamp_A0      = 0;
static volatile LONG   g_savedCamp_84      = 0;
static volatile LONG   g_savedCamp_B8      = 0;
static volatile LONG   g_savedCamp_39C     = 0;   // handler+0x39C = max-slots
static volatile LONG   g_campValuesSaved   = 0;

// Diff-Snapshot scaffolding: handler-object + sub-object + container-object
// (handler+0x170 → container). The container holds max-slots/capacity etc.
#define HANDLER_SNAPSHOT_SIZE  0x800
#define SUB_SNAPSHOT_SIZE      0x800
#define CONT_SNAPSHOT_SIZE     0x800
static uint8_t g_snapshotBefore[HANDLER_SNAPSHOT_SIZE]    = {};
static uint8_t g_snapshotAfter[HANDLER_SNAPSHOT_SIZE]     = {};
static uint8_t g_subSnapshotBefore[SUB_SNAPSHOT_SIZE]     = {};
static uint8_t g_subSnapshotAfter[SUB_SNAPSHOT_SIZE]      = {};
static uint8_t g_contSnapshotBefore[CONT_SNAPSHOT_SIZE]   = {};
static uint8_t g_contSnapshotAfter[CONT_SNAPSHOT_SIZE]    = {};
static volatile LONG64 g_subSnapshotAddr                  = 0;
static volatile LONG64 g_contBeforeAddr                   = 0;
static volatile LONG g_snapshotState = 0;
static DWORD g_diffSnapshotKey = 0x79;  // VK_F10
static DWORD g_diffSnapshotModifier = 0;

// Set by the hotkey handler right before posting WM_TRIGGER_WAREHOUSE. The Open path
// in TriggerWarehouse reads this and sets g_activePanel accordingly, then resets it.
static volatile LONG g_nextOpenPanel = PANEL_PRIVATE;

// Saved mode bytes for restore on close
static uint8_t g_savedModes[7] = {};
static uint8_t g_savedSubtypes[15] = {};
// In CD 1.10 the panel-manager mounts UI views by tag-list derived from
// mainChar[+0xCA9] (sub byte). WareHouseView2.html is tagged "store
// ingamemenu" — only mounts when sub == 6 (dialog/store) or 0xE
// (ingamemenu). The mod's old approach kept sub at the gameplay value
// (0xF/0x10) and tweaked auxiliary mode flags at +0xCB1/+0xCB8; that
// happened to work in 1.06-1.09 via side effects but in 1.10 the view
// stays unmounted → no panel. New: force sub = 6 (store) on open and
// restore the original on close, mirroring what natural NPC-open does.
static uint8_t g_savedSubByte = 0xFF;
static bool    g_savedSubByteValid = false;
// NOTE: g_cursorShownByMod removed — not needed, we always hide cursor on close
static volatile LONG g_modeByteLock = 0;  // Spinlock for mode byte read/write
static volatile LONG g_modeSwitchByMod = 0;  // 1 when WE call fnMode, 0 otherwise
static volatile ULONGLONG g_openTimestamp  = 0;  // GetTickCount64 at warehouse open (grace period)
static volatile ULONGLONG g_closeTimestamp = 0;  // GetTickCount64 at last close (re-open cooldown)
static volatile LONG64 g_lastModalPassed = 0;   // ModalMessageView addr when ESC was last passed to game for a modal

// Forward declaration (defined later in Utilities section)
static void Log(const char* fmt, ...);
static uint16_t GetGatherablesPanelId(void);
static uint16_t LookupInventoryTypeId(uintptr_t pTypeHash);
static uint16_t GetPanelTypeId(int panelIdx);
static uintptr_t ResolveContainerForPanelId(uintptr_t handler, uint16_t panelId);
static void InitWarehousePanel(uintptr_t handler, const char* initString);
static bool TriggerWarehouseViewMount(void);
static void TriggerWarehouseViewUnmount(void);
static void LogModalState(const char* prefix);

// Pending-close flags. Set on press while warehouse is active, cleared on
// release-driven close OR on warehouse close from any other path. Defined
// here (instead of next to the input handlers) so TriggerWarehouse's
// close branch can reset them without a forward declaration.
static volatile LONG g_pendingCircleClose = 0;  // PS5/PS4 Circle (HID)
static volatile LONG g_pendingBClose      = 0;  // XInput B

// DLL hot-reload signal. Worker threads (InputThread, InventoryInfo poller)
// poll this and exit the loop when set. On normal process exit the OS
// terminates threads before DllMain runs so this is irrelevant; on
// FreeLibrary hot-reload the flag gives workers a chance to bail before
// the image is unmapped under them.
static volatile LONG g_shutdown = 0;

// Diagnostic epoch — bumped on every F-press (TriggerWarehouse open path).
// HookedCanShow's entry/mismatch loggers reset their per-epoch counters
// when they see a new value here. Lets us see CanShow polls AFTER each
// F-press cycle, not just the first 10 calls from program start.
static volatile LONG g_diagEpoch = 0;

static uintptr_t ResolveContainerForPanelId(uintptr_t handler, uint16_t panelId);

// GetInitStringForActive: returns the SetInventory filter string for the currently active panel.
static inline const char* GetInitStringForActive() {
    LONG i = InterlockedCompareExchange(&g_activePanel, 0, 0);
    if (i < 0 || i >= PANEL_COUNT) i = PANEL_PRIVATE;
    return g_panels[i].initString;
}

// Hook cleanup: every InstallHook/InstallCanShowHook adds itself to this
// table on success, and DLL_PROCESS_DETACH iterates it to restore every
// patched site so a DLL unload (hot-reload of the ASI) leaves the game in
// a clean state — no stale JMP into freed trampoline memory.
struct HookEntry {
    uintptr_t addr;
    int       size;
    uint8_t   orig[28];
};
static HookEntry g_hookTable[16] = {};
static int       g_hookCount    = 0;



#define WM_TRIGGER_WAREHOUSE (WM_USER + 602)
#define WM_INIT_WAREHOUSE    (WM_USER + 603)
static volatile LONG g_initPending = 0;     // 1 = InputThread should post WM_INIT_WAREHOUSE
static volatile LONG g_initRetryCount = 0;  // retry counter for deferred warehouse init

// ============================================================
//  Raw Input — DualSense / DualShock button detection
//  The game uses WM_INPUT (Raw Input + HID) for controller input.
//  We intercept WM_INPUT in the already-hooked WndProc to detect
//  buttons on Sony controllers (works for DirectInput/HID).
// ============================================================

// Sony Vendor ID
#define SONY_VID 0x054C
// Known Sony controller PIDs
#define DS4_PID_1   0x05C4  // DualShock 4 v1
#define DS4_PID_2   0x09CC  // DualShock 4 v2
#define DS5_PID     0x0CE6  // DualSense
#define DS5_EDGE    0x0DF2  // DualSense Edge

// Circle button bit (always active for close-on-release)
#define CIRCLE_BIT  0x40    // bit 6 in buttons1 (byte offset 0)

// PSButton bindings are now per-panel (see PanelDef::psButtonByteOff/Mask).
// Edge state arrays live next to g_panels[].

static bool g_circleWasDown = false;

// Cached device identification (so we only call GetRawInputDeviceInfo once per handle)
static HANDLE g_cachedHidDevice = nullptr;
static bool   g_cachedIsSony = false;
static int    g_cachedReportOffset = -1;  // offset to buttons1 byte (-1 = unknown)

// Parsed button state from last WM_INPUT
static bool g_lastCircle   = false;

static void IdentifyHidDevice(HANDLE hDevice) {
    if (hDevice == g_cachedHidDevice) return;
    g_cachedHidDevice = hDevice;
    g_cachedIsSony = false;
    g_cachedReportOffset = -1;

    RID_DEVICE_INFO info = {};
    info.cbSize = sizeof(RID_DEVICE_INFO);
    UINT sz = sizeof(info);
    if (GetRawInputDeviceInfoA(hDevice, RIDI_DEVICEINFO, &info, &sz) == (UINT)-1) return;
    if (info.dwType != RIM_TYPEHID) return;
    if (info.hid.dwVendorId != SONY_VID) return;

    g_cachedIsSony = true;
    WORD pid = (WORD)info.hid.dwProductId;
    // DualShock 4: buttons1 at report byte 5 (USB) / byte 5 (BT w/ report ID stripped)
    // DualSense:   buttons1 at report byte 8 (USB report 0x01) / byte 9 (BT report 0x31)
    // Note: Raw Input strips the report ID for USB, keeps it for BT
    if (pid == DS4_PID_1 || pid == DS4_PID_2) {
        g_cachedReportOffset = 5;  // DualShock 4 USB
    } else if (pid == DS5_PID || pid == DS5_EDGE) {
        g_cachedReportOffset = 8;  // DualSense USB
    }
}

// Parses Circle + per-panel PSButton/PSModifier state from WM_INPUT HID
// report. Stores results in g_lastCircle, g_panelPsCurrentDown[],
// g_panelPsModifierDown[].
static void ParseSonyButtons(LPARAM lParam) {
    g_lastCircle = false;
    for (int i = 0; i < PANEL_COUNT; i++) {
        g_panelPsCurrentDown[i] = false;
        g_panelPsModifierDown[i] = false;
    }

    UINT dwSize = 0;
    GetRawInputData((HRAWINPUT)lParam, RID_INPUT, nullptr, &dwSize, sizeof(RAWINPUTHEADER));
    if (dwSize == 0 || dwSize > 1024) return;

    BYTE buf[1024];
    if (GetRawInputData((HRAWINPUT)lParam, RID_INPUT, buf, &dwSize, sizeof(RAWINPUTHEADER)) == (UINT)-1)
        return;

    RAWINPUT* raw = (RAWINPUT*)buf;
    if (raw->header.dwType != RIM_TYPEHID) return;
    if (raw->data.hid.dwCount == 0 || raw->data.hid.dwSizeHid == 0) return;

    IdentifyHidDevice(raw->header.hDevice);
    if (!g_cachedIsSony || g_cachedReportOffset < 0) return;

    BYTE* report = raw->data.hid.bRawData;
    DWORD reportLen = raw->data.hid.dwSizeHid;

    // Handle Bluetooth reports with report ID prefix
    int offset = g_cachedReportOffset;
    if (reportLen > 40 && report[0] == 0x31) {
        // DualSense Bluetooth: report ID 0x31, data shifted by +1
        offset = 9;
    } else if (reportLen > 40 && report[0] == 0x11) {
        // DualShock 4 Bluetooth: report ID 0x11, buttons at offset 7
        offset = 7;
    }

    if ((DWORD)offset >= reportLen) return;

    // Circle is always at buttons1 (offset + 0) — used for close-on-release
    g_lastCircle = (report[offset] & CIRCLE_BIT) != 0;

    // Per-panel PSButton + PSModifier state. Each panel that has a binding
    // gets its current pressed state populated; panels without binding stay
    // false (and an unset modifier counts as "no modifier required" later).
    for (int i = 0; i < PANEL_COUNT; i++) {
        if (g_panels[i].psButtonByteOff >= 0) {
            int psOff = offset + g_panels[i].psButtonByteOff;
            if ((DWORD)psOff < reportLen)
                g_panelPsCurrentDown[i] = (report[psOff] & g_panels[i].psButtonBitMask) != 0;
        }
        if (g_panels[i].psModifierByteOff >= 0) {
            int modOff = offset + g_panels[i].psModifierByteOff;
            if ((DWORD)modOff < reportLen)
                g_panelPsModifierDown[i] = (report[modOff] & g_panels[i].psModifierBitMask) != 0;
        }
    }
}

// ============================================================
//  XInput (dynamic loading)
// ============================================================
struct XINPUT_GAMEPAD_LOCAL {
    WORD  wButtons;
    BYTE  bLeftTrigger;
    BYTE  bRightTrigger;
    SHORT sThumbLX, sThumbLY;
    SHORT sThumbRX, sThumbRY;
};
struct XINPUT_STATE_LOCAL {
    DWORD dwPacketNumber;
    XINPUT_GAMEPAD_LOCAL Gamepad;
};
typedef DWORD (WINAPI *PFN_XInputGetState)(DWORD, XINPUT_STATE_LOCAL*);
static PFN_XInputGetState g_pXInputGetState = nullptr;
static HMODULE g_hXInput = nullptr;
static WORD g_controllerButton = 0;
static WORD g_controllerModifier = 0;
static WORD g_prevButtons = 0;

// ============================================================
//  Utilities
// ============================================================
static void Log(const char* fmt, ...) {
    if (!g_logFile) return;
    va_list a; va_start(a, fmt);
    vfprintf(g_logFile, fmt, a); fprintf(g_logFile, "\n"); fflush(g_logFile);
    va_end(a);
}

// CRC32 of a file (for detecting modded game files in logs)
static uint32_t FileCRC32(const char* path) {
    static const uint32_t table[256] = {
        0x00000000,0x77073096,0xEE0E612C,0x990951BA,0x076DC419,0x706AF48F,0xE963A535,0x9E6495A3,
        0x0EDB8832,0x79DCB8A4,0xE0D5E91B,0x97D2D988,0x09B64C2B,0x7EB17CBF,0xE7B82D09,0x90BF1D9F,
        0x1DB71064,0x6AB020F2,0xF3B97148,0x84BE41DE,0x1ADAD47D,0x6DDDE4EB,0xF4D4B551,0x83D385C7,
        0x136C9856,0x646BA8C0,0xFD62F97A,0x8A65C9EC,0x14015C4F,0x63066CD9,0xFA0F3D63,0x8D080DF5,
        0x3B6E20C8,0x4C69105E,0xD56041E4,0xA2677172,0x3C03E4D1,0x4B04D447,0xD20D85FD,0xA50AB56B,
        0x35B5A8FA,0x42B2986C,0xDBBBC9D6,0xACBCF940,0x32D86CE3,0x45DF5C75,0xDCD60DCF,0xABD13D59,
        0x26D930AC,0x51DE003A,0xC8D75180,0xBFD06116,0x21B4F0B5,0x56B3C423,0xCFBA9599,0xB8BDA50F,
        0x2802B89E,0x5F058808,0xC60CD9B2,0xB10BE924,0x2F6F7C87,0x58684C11,0xC1611DAB,0xB6662D3D,
        0x76DC4190,0x01DB7106,0x98D220BC,0xEFD5102A,0x71B18589,0x06B6B51F,0x9FBFE4A5,0xE8B8D433,
        0x7807C9A2,0x0F00F934,0x9609A88E,0xE10E9818,0x7F6A0D6B,0x086D3D2D,0x91646C97,0xE6635C01,
        0x6B6B51F4,0x1C6C6162,0x856530D8,0xF262004E,0x6C0695ED,0x1B01A57B,0x8208F4C1,0xF50FC457,
        0x65B0D9C6,0x12B7E950,0x8BBEB8EA,0xFCB9887C,0x62DD1DDF,0x15DA2D49,0x8CD37CF3,0xFBD44C65,
        0x4DB26158,0x3AB551CE,0xA3BC0074,0xD4BB30E2,0x4ADFA541,0x3DD895D7,0xA4D1C46D,0xD3D6F4FB,
        0x4369E96A,0x346ED9FC,0xAD678846,0xDA60B8D0,0x44042D73,0x33031DE5,0xAA0A4C5F,0xDD0D7822,
        0x5005713C,0x270241AA,0xBE0B1010,0xC90C2086,0x5768B525,0x206F85B3,0xB966D409,0xCE61E49F,
        0x5EDEF90E,0x29D9C998,0xB0D09822,0xC7D7A8B4,0x59B33D17,0x2EB40D81,0xB7BD5C3B,0xC0BA6CAD,
        0xEDB88320,0x9ABFB3B6,0x03B6E20C,0x74B1D29A,0xEAD54739,0x9DD277AF,0x04DB2615,0x73DC1683,
        0xE3630B12,0x94643B84,0x0D6D6A3E,0x7A6A5AA8,0xE40ECF0B,0x9309FF9D,0x0A00AE27,0x7D079EB1,
        0xF00F9344,0x8708A3D2,0x1E01F268,0x6906C2FE,0xF762575D,0x806567CB,0x196C3671,0x6E6B06E7,
        0xFED41B76,0x89D32BE0,0x10DA7A5A,0x67DD4ACC,0xF9B9DF6F,0x8EBEEFF9,0x17B7BE43,0x60B08ED5,
        0xD6D6A3E8,0xA1D1937E,0x38D8C2C4,0x4FDFF252,0xD1BB67F1,0xA6BC5767,0x3FB506DD,0x48B2364B,
        0xD80D2BDA,0xAF0A1B4C,0x36034AF6,0x41047A60,0xDF60EFC3,0xA867DF55,0x316E8EEF,0x4669BE79,
        0xCB61B38C,0xBC66831A,0x256FD2A0,0x5268E236,0xCC0C7795,0xBB0B4703,0x220216B9,0x5505262F,
        0xC5BA3BBE,0xB2BD0B28,0x2BB45A92,0x5CB36A04,0xC2D7FFA7,0xB5D0CF31,0x2CD99E8B,0x5BDEAE1D,
        0x9B64C2B0,0xEC63F226,0x756AA39C,0x026D930A,0x9C0906A9,0xEB0E363F,0x72076785,0x05005713,
        0x95BF4A82,0xE2B87A14,0x7BB12BAE,0x0CB61B38,0x92D28E9B,0xE5D5BE0D,0x7CDCEFB7,0x0BDBDF21,
        0x86D3D2D4,0xF1D4E242,0x68DDB3F6,0x1FDA836E,0x81BE16CD,0xF6B9265B,0x6FB077E1,0x18B74777,
        0x88085AE6,0xFF0F6B70,0x66063BCA,0x11010B5C,0x8F659EFF,0xF862AE69,0x616BFFD3,0x166CCF45,
        0xA00AE278,0xD70DD2EE,0x4E048354,0x3903B3C2,0xA7672661,0xD06016F7,0x4969474D,0x3E6E77DB,
        0xAED16A4A,0xD9D65ADC,0x40DF0B66,0x37D83BF0,0xA9BCAE53,0xDEBB9EC5,0x47B2CF7F,0x30B5FFE9,
        0xBDBDF21C,0xCABAC28A,0x53B39330,0x24B4A3A6,0xBAD03605,0xCDD706FF,0x54DE5729,0x23D967BF,
        0xB3667A2E,0xC4614AB8,0x5D681B02,0x2A6F2B94,0xB40BBE37,0xC30C8EA1,0x5A05DF1B,0x2D02EF8D
    };
    FILE* f = fopen(path, "rb");
    if (!f) return 0;
    uint32_t crc = 0xFFFFFFFF;
    uint8_t buf[4096];
    size_t n;
    while ((n = fread(buf, 1, sizeof(buf), f)) > 0)
        for (size_t i = 0; i < n; i++)
            crc = table[(crc ^ buf[i]) & 0xFF] ^ (crc >> 8);
    fclose(f);
    return crc ^ 0xFFFFFFFF;
}

// ============================================================
//  Localization — read game language and return translated title
//  Language byte is resolved dynamically via FindLanguageByte():
//    1. FindString("koreana") → Steam language string (index 0)
//    2. Scan .rdata for pointer to "koreana" → language table start
//    3. Find code referencing the table → Steam API init function
//    4. Scan forward for MOV byte [rip+disp32], reg → language byte write
//  SetTitle (FUN_1433ab4b0) stores text as raw char bytes in nodes.
//  Only the bridge/redirect path (FUN_1434159c0 via node+0xA8)
//  properly decodes UTF-8 to wchar_t (via FUN_141010f90).
//  When no bridge exists, the renderer zero-extends each byte,
//  garbling multi-byte UTF-8 (Korean/CJK/Cyrillic/accented chars).
//  Fix: after SetTitle, call SetTitleDirect on node renderers.
// ============================================================
static int GetGameLanguage() {
    if (!g_langByteAddr) return 1; // EN
    __try {
        uint8_t lang = *(uint8_t*)g_langByteAddr;
        if (lang > 13) return 1; // unknown → EN
        return (int)lang;
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        return 1; // EN
    }
}

static const char* GetPrivateStorageTitle() {
    // NOTE: Do NOT use u8"" prefix with \x hex escapes!
    // MSVC /utf-8 + u8"" double-encodes bytes > 0x7F (\xEA → C3 AA instead of EA).
    // Plain "" with \x escapes produces the raw bytes we need.
    switch (GetGameLanguage()) {
        case  0: return "\xEA\xB0\x9C\xEC\x9D\xB8 \xEC\xB0\xBD\xEA\xB3\xA0";     // KR: 개인 창고
        case  1: return "Private Storage";                                            // EN
        case  2: return "\xE5\x80\x8B\xE4\xBA\xBA\xE5\x80\x89\xE5\xBA\xAB";       // JP: 個人倉庫
        case  3: return "\xD0\x9B\xD0\xB8\xD1\x87\xD0\xBD\xD0\xBE\xD0\xB5 \xD1\x85\xD1\x80\xD0\xB0\xD0\xBD\xD0\xB8\xD0\xBB\xD0\xB8\xD1\x89\xD0\xB5"; // RU
        case  4: return "\xC3\x96zel Depo";                                          // TR: Özel Depo
        case  5: return "Almac\xC3\xA9n Privado";                                    // ES: Almacén Privado
        case  6: return "Almac\xC3\xA9n Privado";                                    // MX: Almacén Privado
        case  7: return "Entrep\xC3\xB4t Priv\xC3\xA9";                             // FR: Entrepôt Privé
        case  8: return "Privates Lager";                                             // DE
        case  9: return "Magazzino Privato";                                          // IT
        case 10: return "Prywatny Magazyn";                                           // PL
        case 11: return "Armaz\xC3\xA9m Privado";                                    // BR: Armazém Privado
        case 12: return "\xE5\x80\x8B\xE4\xBA\xBA\xE5\x80\x89\xE5\xBA\xAB";       // TW: 個人倉庫
        case 13: return "\xE4\xB8\xAA\xE4\xBA\xBA\xE4\xBB\x93\xE5\xBA\x93";       // CN: 个人仓库
        default: return "Private Storage";
    }
}

static const char* GetGatherablesTitle() {
    // EN confirmed via in-game NPC visit: "Gatherables Chest". Other languages
    // are best-effort guesses — confirm at NPC chest in each language and
    // update strings if needed.
    switch (GetGameLanguage()) {
        case  0: return "\xEC\x88\x98\xEC\xA7\x91 \xEC\x83\x81\xEC\x9E\x90";              // KR: 수집 상자
        case  1: return "Gatherables Chest";                                                // EN (confirmed)
        case  2: return "\xE6\x8E\xA1\xE9\x9B\x86\xE7\x89\xA9\xE3\x83\x81\xE3\x82\xA7\xE3\x82\xB9\xE3\x83\x88"; // JP: 採集物チェスト
        case  3: return "\xD0\xA1\xD1\x83\xD0\xBD\xD0\xB4\xD1\x83\xD0\xBA \xD1\x81\xD0\xB1\xD0\xBE\xD1\x80\xD0\xB0";  // RU: Сундук сбора
        case  4: return "Toplama Sand\xC4\xB1\xC4\x9F\xC4\xB1";                            // TR
        case  5: return "Cofre de Recolecci\xC3\xB3n";                                      // ES
        case  6: return "Cofre de Recolecci\xC3\xB3n";                                      // MX
        case  7: return "Coffre de R\xC3\xA9" "colte";                                     // FR
        case  8: return "Sammeltruhe";                                                      // DE
        case  9: return "Baule da Raccolta";                                                // IT
        case 10: return "Skrzynia Zbiorcza";                                                // PL
        case 11: return "Ba\xC3\xBA de Coleta";                                            // BR
        case 12: return "\xE6\x8E\xA1\xE9\x9B\x86\xE5\xAE\x9D\xE7\xAE\xB1";                // TW
        case 13: return "\xE9\x87\x87\xE9\x9B\x86\xE5\xAE\x9D\xE7\xAE\xB1";                // CN
        default: return "Gatherables Chest";
    }
}

// Per-language titles for the additional housing panels.
// NOTE: these are best-effort translations — these housing chests
// have no in-game UI key (only the internal channel name "Housing_*"
// which the player never sees), so the mod must supply its own text
// rather than calling the game's localizer.  If any translation feels
// off in a specific language, override via the INI (future work) or
// edit the string here. Encoding rule: plain "" with \x hex escapes
// (NOT u8"") — MSVC /utf-8 + u8"" double-encodes bytes > 0x7F.
static const char* GetDresserTitle() {
    switch (GetGameLanguage()) {
        case  0: return "\xEC\x84\x9C\xEB\x9E\x8D\xEC\x9E\xA5";                                    // KR: 서랍장
        case  1: return "Dresser";                                                                    // EN
        case  2: return "\xE5\x8C\x96\xE7\xB2\xA7\xE5\x8F\xB0";                                    // JP: 化粧台
        case  3: return "\xD0\x9A\xD0\xBE\xD0\xBC\xD0\xBE\xD0\xB4";                                // RU: Комод
        case  4: return "\xC5\x9Eifonyer";                                                            // TR: Şifonyer
        case  5: return "Tocador";                                                                    // ES
        case  6: return "Tocador";                                                                    // MX
        case  7: return "Commode";                                                                    // FR
        case  8: return "Kommode";                                                                    // DE
        case  9: return "Cassettone";                                                                 // IT
        case 10: return "Komoda";                                                                     // PL
        case 11: return "C\xC3\xB4moda";                                                             // BR: Cômoda
        case 12: return "\xE6\x8A\xBD\xE5\xB1\x89\xE6\xAB\x83";                                    // TW: 抽屜櫃
        case 13: return "\xE6\x8A\xBD\xE5\xB1\x89\xE6\x9F\x9C";                                    // CN: 抽屉柜
        default: return "Dresser";
    }
}
static const char* GetRefrigeratorTitle() {
    switch (GetGameLanguage()) {
        case  0: return "\xEB\x83\x89\xEC\x9E\xA5\xEA\xB3\xA0";                                    // KR: 냉장고
        case  1: return "Refrigerator";                                                               // EN
        case  2: return "\xE5\x86\xB7\xE8\x94\xB5\xE5\xBA\xAB";                                    // JP: 冷蔵庫
        case  3: return "\xD0\xA5\xD0\xBE\xD0\xBB\xD0\xBE\xD0\xB4\xD0\xB8\xD0\xBB\xD1\x8C\xD0\xBD\xD0\xB8\xD0\xBA"; // RU: Холодильник
        case  4: return "Buzdolab\xC4\xB1";                                                          // TR: Buzdolabı
        case  5: return "Frigor\xC3\xAD" "fico";                                                    // ES: Frigorífico
        case  6: return "Refrigerador";                                                               // MX
        case  7: return "R\xC3\xA9" "frig\xC3\xA9rateur";                                          // FR: Réfrigérateur
        case  8: return "K\xC3\xBChlschrank";                                                        // DE: Kühlschrank
        case  9: return "Frigorifero";                                                                // IT
        case 10: return "Lod\xC3\xB3wka";                                                            // PL: Lodówka
        case 11: return "Geladeira";                                                                  // BR
        case 12: return "\xE5\x86\xB0\xE7\xAE\xB1";                                                  // TW: 冰箱
        case 13: return "\xE5\x86\xB0\xE7\xAE\xB1";                                                  // CN: 冰箱
        default: return "Refrigerator";
    }
}
static const char* GetSymbolTitle() {
    switch (GetGameLanguage()) {
        case  0: return "\xEC\x8B\xAC\xEB\xB3\xBC \xEC\xB0\xBD\xEA\xB3\xA0";                       // KR: 심볼 창고
        case  1: return "Symbol Storage";                                                             // EN
        case  2: return "\xE3\x82\xB7\xE3\x83\xB3\xE3\x83\x9C\xE3\x83\xAB\xE5\x80\x89\xE5\xBA\xAB"; // JP: シンボル倉庫
        case  3: return "\xD0\xA1\xD0\xBA\xD0\xBB\xD0\xB0\xD0\xB4 \xD1\x81\xD0\xB8\xD0\xBC\xD0\xB2\xD0\xBE\xD0\xBB\xD0\xBE\xD0\xB2"; // RU: Склад символов
        case  4: return "Sembol Deposu";                                                              // TR
        case  5: return "Almac\xC3\xA9n de S\xC3\xAD" "mbolos";                                    // ES: Almacén de Símbolos
        case  6: return "Almac\xC3\xA9n de S\xC3\xAD" "mbolos";                                    // MX
        case  7: return "Stockage de Symboles";                                                       // FR
        case  8: return "Symbol-Lager";                                                               // DE
        case  9: return "Deposito Simboli";                                                           // IT
        case 10: return "Magazyn Symboli";                                                            // PL
        case 11: return "Armaz\xC3\xA9m de S\xC3\xAD" "mbolos";                                    // BR
        case 12: return "\xE7\xAC\xA6\xE8\x99\x9F\xE5\x80\x89\xE5\xBA\xAB";                        // TW: 符號倉庫
        case 13: return "\xE7\xAC\xA6\xE5\x8F\xB7\xE4\xBB\x93\xE5\xBA\x93";                        // CN: 符号仓库
        default: return "Symbol Storage";
    }
}
static const char* GetCollectingTitle() {
    switch (GetGameLanguage()) {
        case  0: return "\xEC\x88\x98\xEC\xA7\x91 \xEC\xB0\xBD\xEA\xB3\xA0";                       // KR: 수집 창고
        case  1: return "Collecting Storage";                                                         // EN
        case  2: return "\xE3\x82\xB3\xE3\x83\xAC\xE3\x82\xAF\xE3\x82\xB7\xE3\x83\xA7\xE3\x83\xB3\xE5\x80\x89\xE5\xBA\xAB"; // JP: コレクション倉庫
        case  3: return "\xD0\xA1\xD0\xBA\xD0\xBB\xD0\xB0\xD0\xB4 \xD0\xBA\xD0\xBE\xD0\xBB\xD0\xBB\xD0\xB5\xD0\xBA\xD1\x86\xD0\xB8\xD0\xB9"; // RU: Склад коллекций
        case  4: return "Koleksiyon Deposu";                                                          // TR
        case  5: return "Almac\xC3\xA9n de Colecci\xC3\xB3n";                                       // ES: Almacén de Colección
        case  6: return "Almac\xC3\xA9n de Colecci\xC3\xB3n";                                       // MX
        case  7: return "Stockage de Collection";                                                     // FR
        case  8: return "Sammlungs-Lager";                                                            // DE
        case  9: return "Deposito Collezione";                                                        // IT
        case 10: return "Magazyn Kolekcji";                                                           // PL
        case 11: return "Armaz\xC3\xA9m de Cole\xC3\xA7\xC3\xA3o";                                  // BR: Armazém de Coleção
        case 12: return "\xE6\x94\xB6\xE8\x97\x8F\xE5\x80\x89\xE5\xBA\xAB";                        // TW: 收藏倉庫
        case 13: return "\xE6\x94\xB6\xE8\x97\x8F\xE4\xBB\x93\xE5\xBA\x93";                        // CN: 收藏仓库
        default: return "Collecting Storage";
    }
}

static const char* GetWarehouseTitle() {
    LONG i = InterlockedCompareExchange(&g_activePanel, 0, 0);
    switch (i) {
        case PANEL_PRIVATE:      return GetPrivateStorageTitle();
        case PANEL_GATHERABLES:  return GetGatherablesTitle();
        case PANEL_DRESSER:      return GetDresserTitle();
        case PANEL_REFRIGERATOR: return GetRefrigeratorTitle();
        case PANEL_SYMBOL:       return GetSymbolTitle();
        case PANEL_COLLECTING:   return GetCollectingTitle();
        default:                 return GetPrivateStorageTitle();
    }
}

// ============================================================
//  UTF-8 title fix — call SetTitleDirect (FUN_1434159c0) on
//  renderers found via bridge chain for proper UTF-8→wchar_t.
// ============================================================
static bool IsAscii(const char* s) {
    for (; *s; s++)
        if ((unsigned char)*s > 0x7F) return false;
    return true;
}

// Walk a UI node tree and call SetTitleDirect on any renderer found
// through the bridge chain: node+0xA8 → bridge → *(bridge+8) → renderer.
static bool SetTitleOnRenderer(uintptr_t node, const char* utf8Title, int depth) {
    if (!node || depth > 5) return false;
    __try {
        uintptr_t bridge = *(uintptr_t*)(node + 0xA8);
        if (bridge > 0x10000 && bridge < 0x7FFFFFFFFFFF) {
            uintptr_t renderer = *(uintptr_t*)(bridge + 8);
            if (renderer > 0x10000 && renderer < 0x7FFFFFFFFFFF) {
                if (g_fnSetTitleDirect) {
                    typedef uint8_t (__fastcall *PFN_STD)(uintptr_t, const char*, uint64_t, uint64_t);
                    ((PFN_STD)g_fnSetTitleDirect)(renderer, utf8Title, 0, 0);
                    Log("    SetTitleOnRenderer: OK depth=%d renderer=0x%llX",
                        depth, (unsigned long long)renderer);
                    return true;
                }
            }
        }
        // Recurse into children
        int32_t childCount = *(int32_t*)(node + 0x38);
        if (childCount > 0 && childCount < 100) {
            uintptr_t childArr = *(uintptr_t*)(node + 0x30);
            if (childArr > 0x10000 && childArr < 0x7FFFFFFFFFFF) {
                for (int i = 0; i < childCount; i++) {
                    uintptr_t child = *(uintptr_t*)(childArr + i * 8);
                    if (child > 0x10000 && child < 0x7FFFFFFFFFFF) {
                        if (SetTitleOnRenderer(child, utf8Title, depth + 1))
                            return true;
                    }
                }
            }
        }
    } __except (EXCEPTION_EXECUTE_HANDLER) {
        Log("    SetTitleOnRenderer: EXCEPTION depth=%d", depth);
    }
    return false;
}

// Read the active modal dialog pointer from the handler struct.
static uintptr_t ReadModalDialog(uintptr_t handler) {
    if (!g_modalDialogOff || !g_modalOffValid) return 0;
    __try {
        return *(uintptr_t*)(handler + g_modalDialogOff);
    } __except(EXCEPTION_EXECUTE_HANDLER) { return 0; }
}

// Check if a NEW sub-dialog (quantity/confirm dialog OR "View Details" popup)
// is visible. The two tracking sources are independent:
//
//   1. handler+0x258 (ModalDlgOff): the game writes a pointer here when a
//      quantity/confirm sub-dialog opens. childCount at +0x30 of the view
//      tells us if it still has visible children.
//
//   2. g_itemDetailActiveCount: incremented by the ItemDetailOpen hook
//      (FUN_140b55860 in 1.06) when the game processes an
//      "ItemDetailModalMessage" command. The "View Details" popup does NOT
//      register at handler+0x258 — only the hook sees it.
//
// CRITICAL: never let one source clear the other. Earlier versions cleared
// g_itemDetailActiveCount whenever +0x258 looked stale, which silently
// suppressed the Details popup detection — ESC then closed the warehouse
// instead of the popup.
static bool IsNewModalDialogVisible() {
    // Source #2 is always consulted first because it's independent of the
    // handler/+0x258 state and is the only source for Details popups.
    if (InterlockedCompareExchange(&g_itemDetailActiveCount, 0, 0) > 0) {
        return true;
    }

    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
    if (!handler) return false;

    __try {
        uintptr_t modalView = ReadModalDialog(handler);
        if (modalView > 0x10000 && modalView < 0x7FFFFFFFFFFF) {
            uint32_t childCount = *(uint32_t*)(modalView + 0x30);
            // childCount == 0: no modal visible.
            // childCount > 0x100: freed-memory garbage (modal was dismissed,
            // pointer not cleared — reading at the old address returns
            // whatever the allocator wrote). Treat as dismissed.
            if (childCount == 0 || childCount > 0x100) {
                InterlockedExchange64(&g_lastModalPassed, 0);
                // DO NOT touch g_itemDetailActiveCount here.
                return false;
            }
            uintptr_t lastPassed = (uintptr_t)InterlockedCompareExchange64(&g_lastModalPassed, 0, 0);
            if (lastPassed == modalView) return false;
            return true;
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    InterlockedExchange64(&g_lastModalPassed, 0);
    return false;
}

static DWORD ReadHexValue(const char* section, const char* key, DWORD defaultVal, const char* iniPath) {
    char buf[32];
    GetPrivateProfileStringA(section, key, "", buf, sizeof(buf), iniPath);
    if (buf[0] == '\0') return defaultVal;
    return (DWORD)strtoul(buf, nullptr, 16);
}

// Map a PSButton name string to (byte offset from buttons1, bit mask).
// Returns false for "none" or unknown names. Used both for the legacy
// global PSButton key and for per-panel <Name>PSButton overrides.
static bool ParsePSButtonName(const char* name, int* outOff, BYTE* outMask) {
    if (!name || !name[0] || _stricmp(name, "none") == 0) return false;
    struct Map { const char* n; int off; BYTE mask; };
    static const Map kMap[] = {
        { "Share",    1, 0x10 }, { "Options",  1, 0x20 },
        { "Circle",   0, 0x40 }, { "Triangle", 0, 0x80 },
        { "Square",   0, 0x10 }, { "Cross",    0, 0x20 },
        { "L1",       1, 0x01 }, { "R1",       1, 0x02 },
        { "L3",       1, 0x40 }, { "R3",       1, 0x80 },
        { "Touchpad", 2, 0x02 }, { "PS",       2, 0x01 }, { "Mute", 2, 0x04 },
    };
    for (const auto& m : kMap) {
        if (_stricmp(name, m.n) == 0) { *outOff = m.off; *outMask = m.mask; return true; }
    }
    return false;
}

static void LoadConfig(const char* p) {
    g_enabled = GetPrivateProfileIntA("Settings","Enabled",1,p)!=0;
    g_debugLog = GetPrivateProfileIntA("Settings","DebugLog",0,p)!=0;
    // TraceMode is a SEPARATE opt-in (default 0). It installs 8 diagnostic
    // hooks on the natural NPC-open pipeline, is very noisy, and several of
    // those hooks fail to install on drifted hardcoded RVAs. Keep it OFF for
    // normal use; DebugLog alone still logs resolver state + open flow.
    g_traceMode = GetPrivateProfileIntA("Settings","TraceMode",0,p)!=0;
    // Legacy "Hotkey" (single Private toggle). Default 0 = disabled. The
    // new per-panel layout uses PrivateHotkey=… for control. Keeping any
    // non-zero legacy default would silently steal whatever that key is
    // now assigned to in the per-panel layout (e.g. PrivateHotkey=F4).
    g_hotkey = ReadHexValue("Settings", "Hotkey", 0, p);
    g_modifierKey = ReadHexValue("Settings", "ModifierKey", 0, p);
    g_controllerButton = (WORD)ReadHexValue("Settings", "ControllerButton", 0, p);
    g_controllerModifier = (WORD)ReadHexValue("Settings", "ControllerModifier", 0, p);
    g_reloadKey = ReadHexValue("Settings", "ReloadKey", 0, p);

    g_diffSnapshotKey      = ReadHexValue("Settings", "DiffSnapshotKey",      0x79, p);
    g_diffSnapshotModifier = ReadHexValue("Settings", "DiffSnapshotModifier", 0,    p);

    InterlockedExchange(&g_privatePanelValueCfg,
        (LONG)ReadHexValue("Settings", "PrivatePanelValue",     0,      p));
    InterlockedExchange(&g_gatherablesPanelValueCfg,
        (LONG)ReadHexValue("Settings", "GatherablesPanelValue", 0x02D1, p));

    // Per-panel INI keys: <Name>Hotkey, <Name>Modifier, <Name>ControllerButton,
    // <Name>ControllerModifier (plus optional <Name>InitString override).
    // Defaults come from the g_panels[] static initializer.
    //
    // Private's controller config is also seeded from the legacy
    // ControllerButton/ControllerModifier keys above so existing user INIs
    // keep working without changes.
    g_panels[PANEL_PRIVATE].controllerButton   = g_controllerButton;
    g_panels[PANEL_PRIVATE].controllerModifier = g_controllerModifier;

    static const char* kIniKey[PANEL_COUNT] = {
        "Private", "Gatherables", "Dresser", "Refrigerator", "Symbol", "Collecting"
    };
    for (int i = 0; i < PANEL_COUNT; i++) {
        char keyName[64];
        snprintf(keyName, sizeof(keyName), "%sHotkey", kIniKey[i]);
        g_panels[i].hotkey = ReadHexValue("Settings", keyName, g_panels[i].hotkey, p);
        snprintf(keyName, sizeof(keyName), "%sModifier", kIniKey[i]);
        g_panels[i].modifier = ReadHexValue("Settings", keyName, g_panels[i].modifier, p);
        snprintf(keyName, sizeof(keyName), "%sControllerButton", kIniKey[i]);
        g_panels[i].controllerButton = (WORD)ReadHexValue("Settings", keyName, g_panels[i].controllerButton, p);
        snprintf(keyName, sizeof(keyName), "%sControllerModifier", kIniKey[i]);
        g_panels[i].controllerModifier = (WORD)ReadHexValue("Settings", keyName, g_panels[i].controllerModifier, p);
        snprintf(keyName, sizeof(keyName), "%sInitString", kIniKey[i]);
        char buf[256] = {};
        GetPrivateProfileStringA("Settings", keyName, g_panels[i].initString,
                                 buf, sizeof(buf), p);
        if (buf[0]) strncpy(g_panels[i].initString, buf, sizeof(g_panels[i].initString) - 1);
    }

    // PSButton + PSModifier (legacy globals) → seed Private's panel slot.
    // Existing user INIs with PSButton=Share keep working.
    char psBtn[32];
    GetPrivateProfileStringA("Settings", "PSButton", "none", psBtn, sizeof(psBtn), p);
    int legacyOff; BYTE legacyMask;
    if (ParsePSButtonName(psBtn, &legacyOff, &legacyMask)) {
        g_panels[PANEL_PRIVATE].psButtonByteOff = legacyOff;
        g_panels[PANEL_PRIVATE].psButtonBitMask = legacyMask;
    }
    char psMod[32];
    GetPrivateProfileStringA("Settings", "PSModifier", "none", psMod, sizeof(psMod), p);
    if (ParsePSButtonName(psMod, &legacyOff, &legacyMask)) {
        g_panels[PANEL_PRIVATE].psModifierByteOff = legacyOff;
        g_panels[PANEL_PRIVATE].psModifierBitMask = legacyMask;
    }

    // Per-panel <Name>PSButton + <Name>PSModifier overrides. Both use the
    // same button-name strings (Share, Circle, Cross, L1, R1, ...).
    for (int i = 0; i < PANEL_COUNT; i++) {
        char keyName[64];
        char buf[32] = {};
        snprintf(keyName, sizeof(keyName), "%sPSButton", kIniKey[i]);
        GetPrivateProfileStringA("Settings", keyName, "", buf, sizeof(buf), p);
        if (buf[0]) {
            int off; BYTE mask;
            if (ParsePSButtonName(buf, &off, &mask)) {
                g_panels[i].psButtonByteOff = off;
                g_panels[i].psButtonBitMask = mask;
            } else {
                g_panels[i].psButtonByteOff = -1;
                g_panels[i].psButtonBitMask = 0;
            }
        }

        snprintf(keyName, sizeof(keyName), "%sPSModifier", kIniKey[i]);
        buf[0] = '\0';
        GetPrivateProfileStringA("Settings", keyName, "", buf, sizeof(buf), p);
        if (buf[0]) {
            int off; BYTE mask;
            if (ParsePSButtonName(buf, &off, &mask)) {
                g_panels[i].psModifierByteOff = off;
                g_panels[i].psModifierBitMask = mask;
            } else {
                g_panels[i].psModifierByteOff = -1;
                g_panels[i].psModifierBitMask = 0;
            }
        }
    }
}

static uintptr_t ScanPattern(const uint8_t* pat, int len) {
    uint8_t* base = (uint8_t*)g_gameBase;
    for (DWORD i = 0; (DWORD)(i+len) <= g_imageSize; i++)
        if (memcmp(base+i, pat, len)==0) return g_gameBase+i;
    return 0;
}

// String-Xref helpers (from QuickMenuHotkeys)
static uintptr_t FindString(const char* str) {
    uint8_t* base = (uint8_t*)g_gameBase;
    int len = (int)strlen(str);
    for (DWORD i = 0; i + len + 1 < g_imageSize; i++) {
        if (base[i] == (uint8_t)str[0] &&
            memcmp(base + i, str, len + 1) == 0)
            return (uintptr_t)(base + i);
    }
    return 0;
}

static uintptr_t FindLEA(uintptr_t targetAddr, uintptr_t afterAddr = 0) {
    uint8_t* base = (uint8_t*)g_gameBase;
    DWORD start = afterAddr > g_gameBase ? (DWORD)(afterAddr - g_gameBase) : 0;
    for (DWORD i = start; i + 7 < g_imageSize; i++) {
        uint8_t* p = base + i;
        if ((p[0] == 0x48 || p[0] == 0x4C) && p[1] == 0x8D) {
            uint8_t modrm = p[2];
            if ((modrm & 0xC7) == 0x05) {
                int32_t disp = *(int32_t*)(p + 3);
                uintptr_t resolved = (uintptr_t)(p + 7) + disp;
                if (resolved == targetAddr)
                    return (uintptr_t)p;
            }
        }
    }
    return 0;
}

// Resolve the member offset a UI "selector-..." body attribute is bound to.
// The engine registers each selector attribute with a global descriptor:
//     LEA RDX,[attr-string]; LEA RCX,[DESCRIPTOR]; JMP registerFn      (thunk)
// and the owning control binds it to a member in its bind function:
//     LEA R8,[this+OFFSET]; LEA R9,[rip -> DESCRIPTOR]; CALL BindSelector
// Returns OFFSET, or 0 if any link is missing or the offset is ambiguous
// (multiple bind sites with different offsets).
static uint32_t ResolveSelectorMemberOffset(const char* attrName) {
    uintptr_t strVA = FindString(attrName);
    if (!strVA) return 0;
    // 1) registration thunk: LEA RDX,[rip->string] with LEA RCX,[rip->descriptor] nearby
    uintptr_t desc = 0;
    uintptr_t lea = 0;
    for (int guard = 0; guard < 8 && !desc; guard++) {
        lea = FindLEA(strVA, lea ? lea + 1 : 0);
        if (!lea) break;
        // The descriptor LEA always FOLLOWS the string LEA inside the same
        // thunk (LEA RDX,[str] +0; MOV r8d,1 +7; LEA RCX,[desc] +13). Never
        // scan backwards: thunks are packed at a 0x20-byte stride, so a
        // backward window would adopt the PREVIOUS attribute's descriptor.
        for (int d = 1; d <= 0x20; d++) {
            uint8_t* p = (uint8_t*)(lea + d);
            if (p[0] == 0x48 && p[1] == 0x8D && p[2] == 0x0D) {   // LEA RCX,[rip+disp32]
                int32_t disp = *(int32_t*)(p + 3);
                uintptr_t t = (uintptr_t)(p + 7) + disp;
                if (t > g_gameBase && t < g_gameBase + g_imageSize) { desc = t; break; }
            }
        }
    }
    if (!desc) return 0;
    // 2) bind sites: LEA R9,[rip->desc] (4C 8D 0D disp32); the LEA R8,[reg+disp]
    //    a few bytes earlier carries the member offset. Collect from ALL bind
    //    sites; adopt only if every site agrees on one offset.
    uint32_t offs[8]; int nOffs = 0;
    uint8_t* base = (uint8_t*)g_gameBase;
    for (DWORD i = 0x40; i + 7 < g_imageSize; i++) {   // 0x40: keep the back-walk inside the image
        uint8_t* p = base + i;
        if (p[0] != 0x4C || p[1] != 0x8D || p[2] != 0x0D) continue;
        int32_t disp = *(int32_t*)(p + 3);
        if ((uintptr_t)(p + 7) + disp != desc) continue;
        for (int b = 3; b <= 0x20; b++) {                     // walk back for LEA R8,[reg+disp]
            uint8_t* q = p - b;
            if ((q[0] != 0x4C && q[0] != 0x4D) || q[1] != 0x8D) continue;
            uint8_t modrm = q[2];
            if (((modrm >> 3) & 7) != 0) continue;            // reg field must be R8
            uint8_t mod = modrm & 0xC0, rm = modrm & 7;
            if (rm == 4) continue;                            // skip SIB ([rsp+...])
            uint32_t off;
            if (mod == 0x40) {                                // disp8 (signed — reject negative)
                if (q[3] >= 0x80) continue;
                off = q[3];
            }
            else if (mod == 0x80) off = *(uint32_t*)(q + 3);  // disp32
            else continue;
            if (off < 0x10 || off >= 0x2000) continue;
            bool dup = false;
            for (int k = 0; k < nOffs; k++) if (offs[k] == off) dup = true;
            if (!dup && nOffs < 8) offs[nOffs++] = off;
            break;
        }
    }
    return (nOffs == 1) ? offs[0] : 0;
}

// Auto-derive g_storeSubIndex from the already-resolved ModeSwitcher.
// ModeSwitcher's inner switch(sub) is a jump table; the case that appends the
// "store" view-tag is exactly the subtype index the mod must flag to mount the
// warehouse view. That index flips on almost every game update, so deriving it
// from code (instead of hardcoding) is the single biggest update-safety win.
// Returns the derived index [0,0x10], or -1 on ANY failure (caller keeps the
// hardcoded default — never worse than before). No capstone: hand byte-decode.
static int32_t ResolveStoreSubIndex() {
    if (!g_fnModeSwitcher) return -1;
    const uint32_t WIN = 0xA00;                       // ModeSwitcher body window
    uint8_t* fn = (uint8_t*)g_fnModeSwitcher;

    uintptr_t strStore = FindString("store");
    if (!strStore) return -1;

    // 1) The UNIQUE  LEA reg,[rip->"store"]  inside the ModeSwitcher body.
    //    LEA: (0x48|0x4C) 8D modrm(&0xC7==0x05) disp32.
    uintptr_t storeLea = 0; int storeHits = 0;
    for (uint32_t i = 0; i + 7 <= WIN; i++) {
        uint8_t* p = fn + i;
        if ((p[0] == 0x48 || p[0] == 0x4C) && p[1] == 0x8D && (p[2] & 0xC7) == 0x05) {
            int32_t disp = *(int32_t*)(p + 3);
            if ((uintptr_t)(p + 7) + disp == strStore) { storeLea = (uintptr_t)p; storeHits++; }
        }
    }
    if (storeHits != 1) return -1;                    // ambiguous / not found -> bail

    // 2) The inner switch(sub) dispatch:  mov r32,[rdi+rsi*4+disp32]
    //    opcode 8B, modrm mod=10 rm=100(SIB) -> (modrm&0xC7)==0x84,
    //    SIB 0xB7 (scale*4, index=rsi, base=rdi).  base rdi = image base
    //    (set by an earlier  lea rdi,[rip-x]).  Preceding  cmp esi,imm8 (83 FE ..)
    //    gives the entry count.  (The OUTER mode switch uses index=rax -> SIB 0x87,
    //    so requiring SIB==0xB7 selects the sub table.)
    uintptr_t tableVA = 0; uint32_t caseLimit = 0;
    for (uint32_t i = 0; i + 7 <= WIN; i++) {
        uint8_t* p = fn + i;
        if (p[0] == 0x8B && (p[1] & 0xC7) == 0x84 && p[2] == 0xB7) {
            tableVA = g_gameBase + *(uint32_t*)(p + 3);     // slots are image-base-relative
            for (int b = 3; b <= 0x12; b++) {                // cmp esi,imm8 -> entry count
                uint8_t* q = p - b;
                if (q < fn) break;
                if (q[0] == 0x83 && q[1] == 0xFE) { caseLimit = q[2]; break; }
            }
            break;
        }
    }
    if (!tableVA || !caseLimit || caseLimit > 0x40) return -1;
    uint32_t nEntries = caseLimit + 1;

    // 3) Read + sanity-check the whole jump table: every case target must land
    //    inside the ModeSwitcher body. This confirms tableVA and the image-base-
    //    relative slot encoding are right (guards a wrong dispatch match or a
    //    future 8-byte table) and bounds the search — cheaper and more robust than
    //    trying to locate the shared "lea rdi,[rip->imagebase]" base-register load,
    //    which sits far above the inner dispatch. The winning slot is the one whose
    //    case body linearly contains storeLea before the next case boundary (case
    //    blocks are laid out in address order).
    int32_t winner = -1;
    __try {
        uintptr_t lo = g_fnModeSwitcher, hi = g_fnModeSwitcher + WIN;
        uintptr_t tgts[0x41];
        for (uint32_t i = 0; i < nEntries; i++) {
            uintptr_t t = g_gameBase + *(uint32_t*)(tableVA + i * 4);
            if (t < lo || t >= hi) return -1;
            tgts[i] = t;
        }
        for (uint32_t i = 0; i < nEntries && winner < 0; i++) {
            uintptr_t nextB = hi;
            for (uint32_t j = 0; j < nEntries; j++)
                if (tgts[j] > tgts[i] && tgts[j] < nextB) nextB = tgts[j];
            if (storeLea >= tgts[i] && storeLea < nextB) winner = (int32_t)i;
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) { return -1; }

    if (winner < 0 || winner > 0x10) return -1;
    return winner;
}

static int FindAllCALLsAfter(uintptr_t from, int maxRange,
                              uintptr_t* targets, int maxTargets) {
    uint8_t* start = (uint8_t*)from;
    int count = 0;
    for (int i = 0; i < maxRange && count < maxTargets; i++) {
        if (start[i] == 0xE8) {
            int32_t rel = *(int32_t*)(start + i + 1);
            uintptr_t target = (uintptr_t)(start + i + 5) + rel;
            if (target > g_gameBase && target < g_gameBase + 0x10000000) {
                targets[count++] = target;
                i += 4;
            }
        }
    }
    return count;
}

// Find function start by scanning backwards for function boundary + prolog
static uintptr_t FindFunctionStart(uintptr_t addrInside, int maxBack = 0x1000) {
    for (int i = 1; i < maxBack; i++) {
        uint8_t* p = (uint8_t*)(addrInside - i);
        uint8_t prev = p[-1];
        // Function boundaries: RET (0xC3) or INT3 padding (0xCC)
        if (prev != 0xC3 && prev != 0xCC) continue;
        // Skip consecutive INT3 padding bytes
        if (prev == 0xCC && p[0] == 0xCC) continue;
        // mov [rsp+8], rcx  (48 89 4C 24 08)
        if (p[0] == 0x48 && p[1] == 0x89 && p[2] == 0x4C && p[3] == 0x24 && p[4] == 0x08)
            return (uintptr_t)p;
        // mov [rsp+disp8], rbx  (48 89 5C 24 XX) — any stack slot, common prolog
        if (p[0] == 0x48 && p[1] == 0x89 && p[2] == 0x5C && p[3] == 0x24)
            return (uintptr_t)p;
        // REX push rbp  (40 55)
        if (p[0] == 0x40 && p[1] == 0x55)
            return (uintptr_t)p;
        // REX push rsi  (40 56) — seen in small UI helpers like FUN_140b99b40
        if (p[0] == 0x40 && p[1] == 0x56)
            return (uintptr_t)p;
        // sub rsp, imm8  (48 83 EC xx)
        if (p[0] == 0x48 && p[1] == 0x83 && p[2] == 0xEC)
            return (uintptr_t)p;
        // push rbp; mov rbp, rsp  (55 48 89 E5)
        if (p[0] == 0x55 && p[1] == 0x48 && p[2] == 0x89 && p[3] == 0xE5)
            return (uintptr_t)p;
        // push rbp; sub rsp  (55 48 83 EC) or (55 48 81 EC)
        if (p[0] == 0x55 && p[1] == 0x48 && (p[2] == 0x83 || p[2] == 0x81) && p[3] == 0xEC)
            return (uintptr_t)p;
    }
    return 0;
}

static bool InitXInput() {
    const char* dlls[] = { "xinput1_4.dll", "xinput1_3.dll", "xinput9_1_0.dll" };
    for (int i = 0; i < 3; i++) {
        g_hXInput = LoadLibraryA(dlls[i]);
        if (!g_hXInput) continue;

        // Prefer ordinal 100 = XInputGetStateEx (undocumented, returns Guide
        // button + reads from the *fresh* slot rather than the cached
        // legacy slot). xinput9_1_0.dll has no ordinal 100 — fall through.
        g_pXInputGetState = (PFN_XInputGetState)GetProcAddress(g_hXInput, (LPCSTR)100);
        if (!g_pXInputGetState) {
            g_pXInputGetState = (PFN_XInputGetState)GetProcAddress(g_hXInput, "XInputGetState");
        }
        if (g_pXInputGetState) return true;
        FreeLibrary(g_hXInput);
        g_hXInput = nullptr;
    }
    return false;
}

// ============================================================
//  XInput IAT hook on game module
//
//  The game polls XInput from its own thread independently of the
//  mod. While the warehouse is open, that polling makes the game
//  treat B as Dodge and react to LB+LeftStick / similar combos —
//  the controller user gets a dodge roll on close and the open is
//  fought by the game's own input handling. (DirectInput / Sony HID
//  doesn't have this problem because the game's UI-cancel path
//  consumes Circle on the WM_INPUT route.)
//
//  Fix: IAT-hook XInputGetState on CrimsonDesert.exe so the GAME's
//  XInput reads come through us. The mod's own poll uses the direct
//  DLL export (g_pXInputGetState) which is not affected by the IAT.
//
//  Filter rules:
//    - while warehouse is mod-owned: clear B (no dodge),
//      clear configured per-panel buttons + their modifiers when
//      both are held (so combos that are bound to mod-actions never
//      reach the game)
//    - while warehouse is closed: clear the configured per-panel
//      combo only when both modifier+button are held simultaneously.
//      This way LB or LeftStick alone still work for game functions.
// ============================================================
static volatile PVOID  g_xinputIATSlot = nullptr;
static PFN_XInputGetState g_origXInputGetState_IAT = nullptr;

extern "C" DWORD WINAPI XInputGetState_Filtered(DWORD slot, XINPUT_STATE_LOCAL* state) {
    PFN_XInputGetState orig = g_origXInputGetState_IAT;
    if (!orig) return 1;
    DWORD r = orig(slot, state);
    if (r != 0 || !state || slot != 0) return r;

    WORD btns = state->Gamepad.wButtons;
    WORD clear = 0;

    // Per-panel combo masking: when modifier+button are both held,
    // hide the combo from the game so it can't react to it.
    for (int i = 0; i < PANEL_COUNT; i++) {
        WORD btn = g_panels[i].controllerButton;
        if (!btn || !(btns & btn)) continue;
        WORD modBit = g_panels[i].controllerModifier;
        if (modBit && !(btns & modBit)) continue;
        clear |= btn;
        if (modBit) clear |= modBit;
    }

    // B always masked while warehouse is mod-owned (no dodge).
    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0))
        clear |= 0x2000;

    state->Gamepad.wButtons = btns & ~clear;
    return r;
}

static bool InstallXInputIATHook(HMODULE gameModule) {
    if (!gameModule || g_xinputIATSlot) return false;
    auto* dos = (IMAGE_DOS_HEADER*)gameModule;
    if (dos->e_magic != IMAGE_DOS_SIGNATURE) return false;
    auto* nt = (IMAGE_NT_HEADERS*)((BYTE*)gameModule + dos->e_lfanew);
    if (nt->Signature != IMAGE_NT_SIGNATURE) return false;
    auto& dir = nt->OptionalHeader.DataDirectory[IMAGE_DIRECTORY_ENTRY_IMPORT];
    if (!dir.VirtualAddress) return false;

    auto* desc = (IMAGE_IMPORT_DESCRIPTOR*)((BYTE*)gameModule + dir.VirtualAddress);
    BYTE* base = (BYTE*)gameModule;
    for (; desc->Name; desc++) {
        const char* dllName = (const char*)(base + desc->Name);
        if (_strnicmp(dllName, "xinput", 6) != 0) continue;
        auto* origThunk = (IMAGE_THUNK_DATA*)(base + desc->OriginalFirstThunk);
        auto* iatThunk  = (IMAGE_THUNK_DATA*)(base + desc->FirstThunk);
        if (!origThunk->u1.AddressOfData) {
            // Bound import — OriginalFirstThunk may be 0; fall back to FirstThunk for names
            origThunk = iatThunk;
        }
        for (; origThunk->u1.AddressOfData; origThunk++, iatThunk++) {
            if (origThunk->u1.Ordinal & IMAGE_ORDINAL_FLAG64) continue;
            auto* byName = (IMAGE_IMPORT_BY_NAME*)(base + origThunk->u1.AddressOfData);
            if (strcmp((char*)byName->Name, "XInputGetState") != 0) continue;

            DWORD oldProt;
            if (!VirtualProtect(&iatThunk->u1.Function, sizeof(void*),
                                PAGE_READWRITE, &oldProt)) {
                return false;
            }
            g_origXInputGetState_IAT = (PFN_XInputGetState)(uintptr_t)iatThunk->u1.Function;
            iatThunk->u1.Function = (ULONGLONG)(uintptr_t)&XInputGetState_Filtered;
            VirtualProtect(&iatThunk->u1.Function, sizeof(void*), oldProt, &oldProt);
            g_xinputIATSlot = &iatThunk->u1.Function;
            return true;
        }
    }
    return false;
}

static void RemoveXInputIATHook() {
    if (!g_xinputIATSlot || !g_origXInputGetState_IAT) return;
    DWORD oldProt;
    if (VirtualProtect((LPVOID)g_xinputIATSlot, sizeof(void*),
                       PAGE_READWRITE, &oldProt)) {
        *(ULONGLONG*)g_xinputIATSlot = (ULONGLONG)(uintptr_t)g_origXInputGetState_IAT;
        VirtualProtect((LPVOID)g_xinputIATSlot, sizeof(void*), oldProt, &oldProt);
    }
    g_xinputIATSlot = nullptr;
}

// ============================================================
//  Game Hooks
// ============================================================
// TraceMode helper: dump warehouse-controller state plus the linked
// panel-descriptor state in one log line. Used by the trace hooks below
// to capture the exact field-by-field sequence the game runs during a
// natural NPC warehouse open. Reads everything under SEH so partial /
// stale objects do not crash. desc fields (+0x269 / +0x26A) are only
// read when handler+0x120 is a non-NULL pointer.
static void TraceDumpWhState(uintptr_t handler, const char* prefix) {
    if (!handler) { Log("    %s: this=0x0", prefix); return; }
    __try {
        uintptr_t vt   = *(uintptr_t*)handler;
        uintptr_t s218 = *(uintptr_t*)(handler + 0x218);
        uint8_t   s2CD = *(uint8_t*)(handler + 0x2CD);
        uintptr_t s120 = *(uintptr_t*)(handler + 0x120);
        uint8_t   d269 = 0, d26A = 0;
        bool      descOk = false;
        if (s120 > 0x10000 && s120 < 0x7FFFFFFFFFFF) {
            d269 = *(uint8_t*)(s120 + 0x269);
            d26A = *(uint8_t*)(s120 + 0x26A);
            descOk = true;
        }
        Log("    %s: this=0x%llX vt=base+0x%llX +0x218=0x%llX +0x2CD=%u +0x120=0x%llX%s",
            prefix, (unsigned long long)handler,
            vt > g_gameBase ? (unsigned long long)(vt - g_gameBase) : (unsigned long long)vt,
            (unsigned long long)s218, (unsigned)s2CD, (unsigned long long)s120,
            descOk ? "" : " (desc not readable)");
        if (descOk) {
            Log("      desc=0x%llX +0x269=%u +0x26A=%u",
                (unsigned long long)s120, (unsigned)d269, (unsigned)d26A);
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("    %s: state-read EXCEPTION (this=0x%llX)", prefix, (unsigned long long)handler);
    }
}

extern "C" void __fastcall CaptureOnHandler(void* thisPtr, void* rdx, void* r8, void* r9) {
    InterlockedIncrement(&g_handlerHitCount);
    if (g_traceMode) {
        uint8_t cmdByte = 0xFF;
        __try { if (rdx) cmdByte = *(uint8_t*)rdx; } __except(EXCEPTION_EXECUTE_HANDLER) {}
        Log("[TRACE] Handler#%ld this=0x%llX cmd=0x%02X r8=0x%llX r9=0x%llX",
            (long)g_handlerHitCount,
            (unsigned long long)(uintptr_t)thisPtr, (unsigned)cmdByte,
            (unsigned long long)(uintptr_t)r8, (unsigned long long)(uintptr_t)r9);
        TraceDumpWhState((uintptr_t)thisPtr, "Handler-entry");
    }
    // Multi-instance tracker (additive — does NOT change the first-hit capture
    // policy below). 1.10's natural NPC-open builds a fresh Warehouse2 instance
    // per opening via the descriptor's spawn-instance slot, so the shell we
    // captured at boot may never receive the engine's real Init. This ring
    // logs every distinct Handler-this we ever see so the trace can show
    // whether multiple instances coexist. Capacity is intentionally small (4)
    // and overflow is silently ignored — purely a diagnostic.
    if (g_traceMode) {
        static volatile LONG64 g_seenHandlerThis[4] = { 0, 0, 0, 0 };
        uintptr_t self = (uintptr_t)thisPtr;
        bool known = false;
        int firstFree = -1;
        for (int i = 0; i < 4; ++i) {
            LONG64 cur = InterlockedCompareExchange64(&g_seenHandlerThis[i], 0, 0);
            if ((uintptr_t)cur == self) { known = true; break; }
            if (cur == 0 && firstFree < 0) firstFree = i;
        }
        if (!known && firstFree >= 0) {
            if (InterlockedCompareExchange64(&g_seenHandlerThis[firstFree],
                                             (LONG64)self, 0) == 0) {
                Log("[TRACE] Handler-instance ring: new slot[%d]=0x%llX (capacity 4)",
                    firstFree, (unsigned long long)self);
            }
        }
    }

    if (g_handlerHitCount == 1 && !g_handlerThis) {
        InterlockedExchange64(&g_handlerThis, (LONG64)(uintptr_t)thisPtr);
        Log("CAPTURED warehouse controller via handler: 0x%llX",
            (unsigned long long)(uintptr_t)thisPtr);
        __try {
            // CRITICAL DIAGNOSTIC: log the vtable of the captured object so we
            // can tell whether it matches g_warehouseVtableStart. If it does
            // NOT match, our HookedCanShow will never recognise this object
            // (vtable-match check at line ~1367 fails), and the game polls
            // some OTHER CanShow override that we didn't hook — explaining
            // why the panel never renders even with handler captured.
            uintptr_t capturedVt = *(uintptr_t*)thisPtr;
            Log("  Captured vtable: 0x%llX (base+0x%llX) — %s g_warehouseVtableStart=base+0x%llX",
                (unsigned long long)capturedVt,
                capturedVt > g_gameBase ? (unsigned long long)(capturedVt - g_gameBase) : (unsigned long long)capturedVt,
                (capturedVt == g_warehouseVtableStart) ? "MATCH" : "MISMATCH vs",
                g_warehouseVtableStart > g_gameBase ? (unsigned long long)(g_warehouseVtableStart - g_gameBase) : 0ULL);
            uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + g_offSubObject);
            if (sub) {
                uint16_t realId = *(uint16_t*)((uint8_t*)sub + g_offSubPanelId);
                if (realId != 0xFFFF && realId != 0)
                    Log("  Dynamic panelId: 0x%04X", realId);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}

        // If a F-key trigger is currently waiting on init (warehouse object
        // was lazy-instantiated by the game after our F-press), run init
        // inline on the game thread NOW — mirrors HookedCanShow's first-open
        // fix. Without this, the deferred WM_INIT_WAREHOUSE poll in
        // InputThread may have already timed out by the time the game
        // instantiates the warehouse, leaving the user with no panel even
        // after Handler captured. Re-entrant Handler calls from inside
        // InitWarehousePanel are safe because g_handlerHitCount > 1 on the
        // re-entry path, so this capture block does NOT fire recursively.
        if (InterlockedCompareExchange(&g_initPending, 0, 0)) {
            InterlockedExchange(&g_initPending, 0);
            Log("  Handler-hook capture: running InitWarehousePanel inline (lazy-instantiation fix)");
            InitWarehousePanel((uintptr_t)thisPtr, GetInitStringForActive());
        }
    }

    // Block sub-commands in 0x15 handler when mod opened warehouse
    // (our SetInventory call handles items, skip game's NPC-context commands)
    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        __try {
            char* cmd = (char*)rdx;
            if (cmd && *cmd == 0x15) {
                uint32_t* pCount = (uint32_t*)(cmd + 0x10);
                if (*pCount > 0) {
                    Log("  Handler: blocking %u sub-commands", *pCount);
                    *pCount = 0;
                }
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }
}

// ---------- TraceMode-only hooks (warehouse Init / Show / panel-desc Show) -----
// Installed only when [Settings] TraceMode=1 in INI. Their only job is to
// log entry + a state snapshot. Each runs under SEH; if the game's call
// signature differs from what we expect, the worst case is one bogus log
// line. Original bytes are saved by InstallHook into g_hookTable so the
// DLL-unload path can restore them.
static volatile LONG g_traceInitHits   = 0;
static volatile LONG g_traceShowHits   = 0;
static volatile LONG g_traceDescHits   = 0;

// Helper: capture g_handlerThis from a verified Warehouse2 pointer if not
// already set. Used by Init/Binder hooks below as a fallback when the game
// doesn't call Handler before the user presses F-key (observed in 1.10
// fresh-load + immediate F-press scenario where Handler never fires and
// the mod's deferred WM_INIT_WAREHOUSE poll can't proceed without a
// captured handler). Verifies vtable matches the warehouse class before
// adopting; SEH-protected.
static void CaptureHandlerIfEmpty(void* candidate, const char* source) {
    if (!candidate) return;
    if (InterlockedCompareExchange64(&g_handlerThis, 0, 0)) return;
    __try {
        uintptr_t vt = *(uintptr_t*)candidate;
        if (vt != g_warehouseVtableStart) return;
        if (InterlockedCompareExchange64(&g_handlerThis, (LONG64)(uintptr_t)candidate, 0) == 0) {
            Log("CAPTURED warehouse via %s: 0x%llX (vtable match — Handler-hook fallback)",
                source, (unsigned long long)(uintptr_t)candidate);
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
}

extern "C" void __fastcall TraceOnWarehouseInit(void* thisPtr, void* outStatus) {
    LONG n = InterlockedIncrement(&g_traceInitHits);
    Log("[TRACE] Warehouse.Init#%ld (vtable[1]) this=0x%llX out=0x%llX",
        (long)n, (unsigned long long)(uintptr_t)thisPtr,
        (unsigned long long)(uintptr_t)outStatus);
    TraceDumpWhState((uintptr_t)thisPtr, "Init-entry");
    // Adopt this as handler if game hasn't called Handler yet (1.10 fix).
    CaptureHandlerIfEmpty(thisPtr, "Init");
}

extern "C" void __fastcall TraceOnWarehouseShow(void* thisPtr) {
    LONG n = InterlockedIncrement(&g_traceShowHits);
    Log("[TRACE] Warehouse.Show#%ld (vtable[51]) this=0x%llX",
        (long)n, (unsigned long long)(uintptr_t)thisPtr);
    TraceDumpWhState((uintptr_t)thisPtr, "Show-entry");
}

// Wrappers that ultimately reach FUN_140A9F4E0 ("Show" sink) — but each
// runs different side-effects first. Without hooking these distinctly we
// only see the sink fire and cannot tell which entry the natural NPC-open
// dialog actually uses. AA3BF0 = "Show + focus-handoff + SetInventoryName"
// (the strongest NPC-open candidate). A9D4A0 = "Show + focus-handoff only"
// (simpler wrapper for re-shows). Confirmed via Ghidra preflight.
static volatile LONG g_traceShowFocusHits  = 0;
static volatile LONG g_traceShowSimpleHits = 0;

extern "C" void __fastcall TraceOnWarehouseShowFocus(void* thisPtr) {
    LONG n = InterlockedIncrement(&g_traceShowFocusHits);
    Log("[TRACE] Warehouse.ShowFocus#%ld (FUN_140AA3BF0 — NPC-open candidate) this=0x%llX",
        (long)n, (unsigned long long)(uintptr_t)thisPtr);
    TraceDumpWhState((uintptr_t)thisPtr, "ShowFocus-entry");
}

extern "C" void __fastcall TraceOnWarehouseShowSimple(void* thisPtr) {
    LONG n = InterlockedIncrement(&g_traceShowSimpleHits);
    Log("[TRACE] Warehouse.ShowSimple#%ld (FUN_140A9D4A0 — re-show wrapper) this=0x%llX",
        (long)n, (unsigned long long)(uintptr_t)thisPtr);
    TraceDumpWhState((uintptr_t)thisPtr, "ShowSimple-entry");
}

// Panel-descriptor show primitive (FUN_14346A3E0). param_1 is a panel
// descriptor, NOT the warehouse controller — so the warehouse state-dump
// helper won't make sense here. Instead log the descriptor's own gate
// fields (+0x269 / +0x26A), its +0x120 parent panel-group pointer, AND
// its vtable. Warehouse descriptors share vtable base+0x4BC1028 — when
// we see PanelDescShow hit with that vtable, we know natural NPC-open
// is reaching the descriptor layer and we can correlate to the trace.
extern "C" void __fastcall TraceOnPanelDescShow(void* descPtr) {
    LONG n = InterlockedIncrement(&g_traceDescHits);
    __try {
        uintptr_t d   = (uintptr_t)descPtr;
        uintptr_t vt  = d ? *(uintptr_t*)d : 0;
        uintptr_t par = d ? *(uintptr_t*)(d + 0x120) : 0;
        uint8_t   v269 = d ? *(uint8_t*)(d + 0x269) : 0;
        uint8_t   v26A = d ? *(uint8_t*)(d + 0x26A) : 0;
        bool isWh = (vt == g_gameBase + 0x4BC1028);
        Log("[TRACE] PanelDescShow#%ld desc=0x%llX vt=base+0x%llX%s +0x120=0x%llX +0x269=%u +0x26A=%u",
            (long)n, (unsigned long long)d,
            vt > g_gameBase ? (unsigned long long)(vt - g_gameBase) : (unsigned long long)vt,
            isWh ? " [WAREHOUSE-DESC]" : "",
            (unsigned long long)par, (unsigned)v269, (unsigned)v26A);
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("[TRACE] PanelDescShow#%ld desc=0x%llX (state-read EXCEPTION)",
            (long)n, (unsigned long long)(uintptr_t)descPtr);
    }
}

// ---------- TraceMode-only hooks added after CD 1.10 architecture investigation -----
// The mod's existing Init/Show hooks on Warehouse2 vtable[1]/[51] never fire on
// the natural NPC-open path — proven by 06-Jun trace data. Ghidra deep-dive
// identified three more candidate functions and one read-only dump that together
// pinpoint the missing piece:
//   * FUN_140AA3910 — deleting destructor of Warehouse2; tracks instance lifecycle
//   * FUN_140A9C820 — master widget binder (the +0x2CD=1 writer); sole caller is
//     vtable[1] Init, so this hook proves whether NPC-open reaches the binder at
//     all and on WHICH this-pointer
//   * FUN_141004DE0 — panel-descriptor registry getter; logging its callers
//     reveals the engine-side OpenPanel dispatch site we never identified
//   * 8-slot dump of descriptor vtable @ base+0x4BC1028 — one slot is the
//     spawn-instance method we'd ultimately want to call directly
static volatile LONG g_traceDtorHits     = 0;
static volatile LONG g_traceBinderHits   = 0;
static volatile LONG g_traceRegGetHits   = 0;

// FUN_140AA3910 is the deleting destructor (confirmed via Ghidra: writes own
// vtable then chains to parent dtor FUN_140A9C5F0, with the standard
// (param_2 & 1) operator-delete tail). Hooking it gives us a per-instance
// death log + return-address (= the delete site). Combined with the heap-scan
// poller, this tells us instance lifecycle around natural NPC-open.
extern "C" void __fastcall TraceOnWarehouseDtor(void* thisPtr, int param2) {
    LONG n = InterlockedIncrement(&g_traceDtorHits);
    void* retAddr = _ReturnAddress();
    uintptr_t ret = (uintptr_t)retAddr;
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
    Log("[TRACE] Warehouse.Dtor#%ld this=0x%llX param2=%d ret=base+0x%llX %s captured=0x%llX",
        (long)n, (unsigned long long)(uintptr_t)thisPtr, param2,
        ret > g_gameBase ? (unsigned long long)(ret - g_gameBase) : (unsigned long long)ret,
        ((uintptr_t)thisPtr == handler) ? "SAME-AS-CAPTURED" : "DIFFERENT-INSTANCE",
        (unsigned long long)handler);
}

// FUN_140A9C820 is the master widget binder — the function that actually sets
// +0x2CD=1 once all sub-handlers (+0x218, +0x250...+0x2C8) are bound. Its
// only static caller is vtable[1] Init (FUN_140AA39E0). If this hook fires
// during natural NPC-open with a DIFFERENT this than g_handlerThis, the
// wrong-instance hypothesis is confirmed. If it never fires, natural open
// uses a parallel init mechanism that bypasses the binder.
extern "C" void __fastcall TraceOnWarehouseBinder(void* thisPtr, void* outStatus) {
    LONG n = InterlockedIncrement(&g_traceBinderHits);
    void* retAddr = _ReturnAddress();
    uintptr_t ret = (uintptr_t)retAddr;
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
    Log("[TRACE] Warehouse.Binder#%ld (FUN_140A9C820) this=0x%llX ret=base+0x%llX %s out=0x%llX",
        (long)n, (unsigned long long)(uintptr_t)thisPtr,
        ret > g_gameBase ? (unsigned long long)(ret - g_gameBase) : (unsigned long long)ret,
        ((uintptr_t)thisPtr == handler) ? "SAME-AS-CAPTURED" : "DIFFERENT-INSTANCE",
        (unsigned long long)(uintptr_t)outStatus);
    // Adopt as handler if not yet set (1.10 fallback when Handler never fires).
    CaptureHandlerIfEmpty(thisPtr, "Binder");
}

// FUN_141004DE0 is the panel-descriptor registry getter (returns
// &DAT_1460F9E50). Rate-limited (first 8 hits, then every 64th) because
// many panel-system ticks call it. Each hit logs the caller return-address
// — that's our hook on the engine-side OpenPanel/ShowPanel dispatch sites.
extern "C" void __fastcall TraceOnPanelRegistryGet() {
    LONG n = InterlockedIncrement(&g_traceRegGetHits);
    if (n > 8 && (n & 63) != 0) return;
    void* retAddr = _ReturnAddress();
    uintptr_t ret = (uintptr_t)retAddr;
    Log("[TRACE] PanelRegistryGet#%ld ret=base+0x%llX",
        (long)n, ret > g_gameBase ? (unsigned long long)(ret - g_gameBase) : (unsigned long long)ret);
}

// Read-only 8-slot dump of the panel-descriptor vtable shared by the WareHouse
// and CampWareHouse descriptors (base+0x4BC1028). Extracted to its own function
// because MSVC forbids __try inside any function with C++ objects requiring
// unwinding (ModThread has std::string). Called once from the install block
// when TraceMode is active.
static void TraceDumpDescriptorVtable() {
    if (!g_gameBase || !g_imageSize) return;
    __try {
        uintptr_t descVt = g_gameBase + 0x4BC1028;
        Log("[TRACE] DescVtable @ base+0x4BC1028 dump (8 slots):");
        for (int i = 0; i < 8; ++i) {
            uintptr_t slot = *(uintptr_t*)(descVt + i * 8);
            if (slot > g_gameBase && slot < g_gameBase + g_imageSize) {
                Log("  desc.vtable[%d] = base+0x%llX",
                    i, (unsigned long long)(slot - g_gameBase));
            } else {
                Log("  desc.vtable[%d] = 0x%llX (out-of-image or null)",
                    i, (unsigned long long)slot);
            }
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("[TRACE] DescVtable dump EXCEPTION (descriptor not yet constructed?)");
    }
}

// Walk the InventoryInfoManager singleton and patch every InventoryInfo's
// base slot count (ushort at +0x48) from 10 to 1000. Found via Ghidra:
// FUN_1404e9780 (GetInventoryInfo by InventoryKey) reads from
// *(manager + 0x50)[key], FUN_1404de7c0 reads (info + 0x48) as the slot base.
// Returns number of entries patched, or -1 if manager not yet loaded.
static int PatchInventoryInfoSlots() {
    if (!g_addrInventoryInfoMgrPtr) return -1;
    int patched = 0;
    __try {
        uintptr_t mgr = *(uintptr_t*)g_addrInventoryInfoMgrPtr;
        if (!mgr) return -1;
        uint32_t count = *(uint32_t*)(mgr + 8);
        uintptr_t arr  = *(uintptr_t*)(mgr + 0x50);
        if (!arr || count == 0 || count > 4096) return -1;
        for (uint32_t i = 0; i < count; i++) {
            uintptr_t info = *(uintptr_t*)(arr + i * 8);
            if (!info) continue;
            uint16_t* pSlots = (uint16_t*)(info + 0x48);
            if (*pSlots == 10) {
                *pSlots = 1000;
                patched++;
            }
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("PatchInventoryInfoSlots: SEH exception");
        return -1;
    }
    return patched;
}

// Fires whenever the game opens an ItemDetailModal ("View Details" popup) —
// hooked at FUN_140B4D310 (the "ItemDetailModalMessage" processor). The
// counter is cleared by IsNewModalDialogVisible when handler+0x258 reports
// the modal as gone (childCount==0 or pointer freed).
extern "C" void __fastcall CaptureOnItemDetailCtor(void* /*param_1*/, void* /*param_2*/) {
    InterlockedExchange(&g_itemDetailActiveCount, 1);
    Log("ItemDetailModal opened");
}

// Hook on FUN_140b80e00 — the filter-bar mode/submode setter.
// Logs every invocation: which filter object + which mode arg was passed,
// plus the object's current state. Compared against handler+0x1A8 in the
// InitWarehousePanel log line, this reveals:
//   - Whether natural NPC-open uses the same filter object as our F4 path
//   - What sequence of mode values the game flows through during init
//   - What parent-scope (filter+0x8) the game's filter object has
// Resolve mainChar from the game manager singleton: *(*(globalPtr) + 0x48)
static uintptr_t ResolveMainChar() {
    if (!g_mainCharGlobalPtr) return 0;
    __try {
        uintptr_t mgr = *(uintptr_t*)g_mainCharGlobalPtr;
        if (mgr) return *(uintptr_t*)(mgr + 0x48);
    } __except(EXCEPTION_EXECUTE_HANDLER) {}
    return 0;
}

// Resolve the menu-layer manager (menuMgr) WITHOUT a hardcoded global.
// The game update on 2026-06-19 (buildid 23816417) moved the absolute
// globals: the old hardcoded menuMgr global base+0x6066F90 now reads null
// ("ViewMount/ViewUnmount: lvl1 null"), which breaks the panel mount AND
// the vendor-menu soft-lock fix. But STRUCT OFFSETS survived this update
// (boot log shows BottomLabel 0x350, active flag 0x128, subtypes 0xCB8 etc.
// unchanged), so derive menuMgr from the same game-manager singleton the
// mainChar resolver already uses:
//   mgr     = *(g_mainCharGlobalPtr)        (dynamically resolved each build)
//   menuMgr = *(mgr + 0x90)                 (stable struct offset)
// and VALIDATE against the menuMgr->mainChar back-reference the game's own
// state tick relies on (menuMgr+0x11C0 == mainChar) plus a sane state byte
// (+0x105E in 0..4). If validation fails (an offset shifted), return 0 so
// the caller logs and bails instead of writing menu state to a wrong object.
static uintptr_t ResolveMenuMgr() {
    if (!g_mainCharGlobalPtr) return 0;
    uintptr_t mc = (uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
    __try {
        uintptr_t mgr = *(uintptr_t*)g_mainCharGlobalPtr;
        if (mgr <= 0x10000) return 0;
        uintptr_t menuMgr = *(uintptr_t*)(mgr + 0x90);
        if (menuMgr <= 0x10000) return 0;
        uintptr_t back = *(uintptr_t*)(menuMgr + 0x11C0);
        uint8_t   cur  = *(uint8_t*)(menuMgr + 0x105E);
        if (mc && back == mc && cur <= 4) return menuMgr;
        Log("  ResolveMenuMgr: validation FAILED (menuMgr=0x%llX back=0x%llX mc=0x%llX cur=0x%02X) "
            "— +0x90/+0x11C0/+0x105E offset may have shifted, need Ghidra on new build",
            (unsigned long long)menuMgr, (unsigned long long)back,
            (unsigned long long)mc, cur);
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  ResolveMenuMgr: EXCEPTION");
    }
    return 0;
}

// Mode-byte save/restore helpers. Both take the spinlock and wrap the
// memory access in SEH — but SEH only catches access violations. A
// resolved-wrong-but-mapped offset (e.g. resolver picks a neighbouring
// struct field) would silently overwrite unrelated game state without
// faulting. So we also gate on a plausibility check: the offsets must
// live in the mainChar mode/sub-mode cluster (~0xC00..0xE00 on every
// known build) AND maintain the expected relationship
// g_offSubtypes == g_offModeFlags + 7. If either invariant fails, the
// helper is a no-op + WARN — F-key open will silently get the wrong
// mode bytes, but we won't corrupt mainChar.
static bool ModeOffsetsPlausible() {
    uint32_t f = g_offModeFlags, s = g_offSubtypes;
    if (f < 0xC00 || f > 0xE00) return false;
    if (s < 0xC00 || s > 0xE00) return false;
    if (s != f + 7) return false;
    return true;
}

static void SafeSetupModeForWarehouse(uint8_t* mc) {
    if (!mc) return;
    if (!ModeOffsetsPlausible()) {
        Log("  SafeSetupModeForWarehouse SKIPPED — implausible resolved offsets (flags=0x%X subtypes=0x%X)",
            g_offModeFlags, g_offSubtypes);
        return;
    }
    while (InterlockedCompareExchange(&g_modeByteLock, 1, 0) != 0) { _mm_pause(); }
    __try {
        memcpy(g_savedModes,    mc + g_offModeFlags, 7);
        memcpy(g_savedSubtypes, mc + g_offSubtypes, 15);
        memset(mc + g_offModeFlags, 0, 7);
        memset(mc + g_offSubtypes, 0, 15);
        mc[g_offModeFlags + 4] = 1;
        // ROOT-CAUSE FIX: the game tick's mode-resolver scans
        // mc[g_offSubtypes+0..16] for the first non-zero entry and DERIVES
        // mc[g_offSubByte] from that index. The (mode=4,sub)->view-tag mapper
        // (ModeSwitcher FUN, 1.12.00 @ base+0x721BD0) then turns that sub
        // value into the view-tag list; WareHouseView2 only mounts when the
        // list contains "store". So we must set the subtype index whose
        // derived sub-mode emits the "store" tag. THIS INDEX MOVES between
        // game versions — Pearl Abyss has flipped it repeatedly:
        //   1.09:    store = sub 5
        //   1.10.xx: store = sub 6   (mod set index 6)
        //   1.12.00: store = sub 5   (verified: ModeSwitcher case 5 emits
        //                             "dialog"+"store"; case 6 = hud/minigame/qte)
        // Forcing mc[g_offSubByte] directly doesn't work (the resolver
        // overrides it back to the flag-derived value every tick), so the
        // flag-INDEX is the lever. g_storeSubIndex holds it.
        // RE-FIND after a game update: decompile the ModeSwitcher fn (the
        // string-xref-resolved base+0x721BD0), read its inner switch(sub),
        // and pick the case that appends the "store" string pointer.
        mc[g_offSubtypes + g_storeSubIndex] = 1;
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  SafeSetupModeForWarehouse EXCEPTION (offsets may be stale: flags=0x%X subtypes=0x%X)",
            g_offModeFlags, g_offSubtypes);
    }
    InterlockedExchange(&g_modeByteLock, 0);
}

static void SafeRestoreMode(uint8_t* mc) {
    if (!mc) return;
    if (!ModeOffsetsPlausible()) {
        Log("  SafeRestoreMode SKIPPED — implausible resolved offsets (flags=0x%X subtypes=0x%X)",
            g_offModeFlags, g_offSubtypes);
        return;
    }
    while (InterlockedCompareExchange(&g_modeByteLock, 1, 0) != 0) { _mm_pause(); }
    __try {
        memcpy(mc + g_offModeFlags, g_savedModes,    7);
        memcpy(mc + g_offSubtypes,  g_savedSubtypes, 15);
        // (sub byte is no longer forced on open — nothing to restore here)
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  SafeRestoreMode EXCEPTION (offsets may be stale: flags=0x%X subtypes=0x%X)",
            g_offModeFlags, g_offSubtypes);
    }
    InterlockedExchange(&g_modeByteLock, 0);
}

extern "C" void __fastcall CaptureModeSwitcher(void* rcx) {
    if (!g_mainChar) {
        uintptr_t mc = ResolveMainChar();
        if (mc > 0x10000000000ULL) {
            InterlockedExchange64(&g_mainChar, (LONG64)mc);
            Log("CAPTURED mainChar: 0x%llX (via singleton)", (unsigned long long)mc);

            // Capture cursorObj via pointer chain: mainChar+0x50 -> +0x60 -> deref -> +0x78
            __try {
                uintptr_t container = *(uintptr_t*)((uint8_t*)mc + 0x50);
                if (container) {
                    uintptr_t worldList = *(uintptr_t*)(container + 0x60);
                    if (worldList) {
                        uintptr_t world = *(uintptr_t*)worldList;
                        if (world) {
                            uintptr_t cursor = *(uintptr_t*)(world + 0x78);
                            if (cursor > 0x10000000000ULL) {
                                InterlockedExchange64(&g_cursorObj, (LONG64)cursor);
                                Log("CAPTURED cursorObj: 0x%llX", (unsigned long long)cursor);
                            }
                        }
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
        }
    }

    // Game calls ModeSwitcher every frame. While warehouse is open,
    // g_modeSwitchByMod stays 1 so this check is always skipped.
    // Close detection is handled by CanShow (+0x118 flag) and explicit
    // user actions (F6/ESC/Circle/B). This block only fires if
    // g_modeSwitchByMod was unexpectedly 0 (should not happen).
    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0) &&
        !InterlockedCompareExchange(&g_modeSwitchByMod, 0, 0)) {
        Log("  ModeSwitcher: unexpected game close detected, releasing warehouse");
        InterlockedExchange(&g_warehouseActive, 0);
        InterlockedExchange(&g_canShowSeen118, 0);
        InterlockedExchange(&g_modeSwitchByMod, 0);
        uint8_t* mc = (uint8_t*)(uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
        // Release the menu-layer too (idempotent if the game already did).
        TriggerWarehouseViewUnmount();
        SafeRestoreMode(mc);
    }
}

// ============================================================
//  CanShow Hook
// ============================================================
typedef char (__fastcall *PFN_CanShow)(void*);
static PFN_CanShow g_origCanShow = nullptr;

extern "C" char __fastcall HookedCanShow(void* thisPtr) {
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);

    // Diagnostic: log first few entry calls + unique vtables seen, RESET on
    // each F-press (TriggerWarehouse bumps g_diagEpoch). Helps triage when
    // auto-capture is silently failing — after a session where the user did
    // an NPC visit, the warehouse vtable SHOULD appear among the polled
    // panels and trigger auto-capture. If it never appears even after NPC
    // visit, the hooked CanShow function is wrong (different override).
    static volatile LONG s_diagEpochSeen = -1;
    static volatile LONG s_diagEntryCount = 0;
    static volatile LONG s_diagMissCount  = 0;
    static uintptr_t s_diagMissVts[20] = {};
    LONG epoch = InterlockedCompareExchange(&g_diagEpoch, 0, 0);
    if (InterlockedCompareExchange(&s_diagEpochSeen, 0, 0) != epoch) {
        InterlockedExchange(&s_diagEpochSeen, epoch);
        InterlockedExchange(&s_diagEntryCount, 0);
        InterlockedExchange(&s_diagMissCount, 0);
        for (int i = 0; i < 20; i++) s_diagMissVts[i] = 0;
    }
    if (g_traceMode && handler == 0 && InterlockedCompareExchange(&s_diagEntryCount, 0, 0) < 30) {
        LONG n = InterlockedIncrement(&s_diagEntryCount);
        __try {
            uintptr_t vt = *(uintptr_t*)thisPtr;
            Log("  CanShow ENTRY #%ld (epoch %ld): thisPtr=0x%llX vt=0x%llX (base+0x%llX) g_warehouseVtableStart=base+0x%llX warehouseActive=%ld",
                (long)n, (long)epoch, (unsigned long long)thisPtr, (unsigned long long)vt,
                vt > g_gameBase ? (unsigned long long)(vt - g_gameBase) : (unsigned long long)vt,
                g_warehouseVtableStart > g_gameBase ? (unsigned long long)(g_warehouseVtableStart - g_gameBase) : 0ULL,
                (long)InterlockedCompareExchange(&g_warehouseActive, 0, 0));
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // POST-CAPTURE diagnostic — after handler is captured, log CanShow polls
    // to verify whether the game ever calls our hook on the captured object.
    // If no log entries appear with "thisPtr == handler" after capture, then
    // the game polls a DIFFERENT CanShow override (likely via a different
    // inherited vtable slot than the one we hooked) — that explains the
    // "panel never renders even with handler captured" symptom.
    static volatile LONG s_diagPostCaptureCount = 0;
    if (g_traceMode && handler != 0 && InterlockedCompareExchange(&s_diagPostCaptureCount, 0, 0) < 30) {
        LONG n = InterlockedIncrement(&s_diagPostCaptureCount);
        __try {
            uintptr_t vt = *(uintptr_t*)thisPtr;
            const char* tag = ((uintptr_t)thisPtr == handler) ? "**HANDLER MATCH**" :
                              (vt == g_warehouseVtableStart)  ? "warehouse-vtable" :
                                                                "other-panel";
            Log("  CanShow POST-CAPTURE #%ld (epoch %ld): %s thisPtr=0x%llX vt=base+0x%llX warehouseActive=%ld",
                (long)n, (long)epoch, tag, (unsigned long long)thisPtr,
                vt > g_gameBase ? (unsigned long long)(vt - g_gameBase) : (unsigned long long)vt,
                (long)InterlockedCompareExchange(&g_warehouseActive, 0, 0));
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // Auto-capture warehouse controller by exact vtable match. All 6 panels
    // share this controller — the per-panel inventory binding happens via
    // SetInventory with the panel's filter string during InitWarehousePanel.
    if (g_warehouseVtableStart && (uintptr_t)thisPtr != handler) {
        __try {
            uintptr_t objVtable = *(uintptr_t*)thisPtr;
            if (objVtable == g_warehouseVtableStart) {
                uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + g_offSubObject);
                uint16_t panelId = sub ? *(uint16_t*)((uint8_t*)sub + g_offSubPanelId) : 0xFFFF;
                InterlockedExchange64(&g_handlerThis, (LONG64)(uintptr_t)thisPtr);
                handler = (uintptr_t)thisPtr;
                Log("AUTO-CAPTURED warehouse controller: 0x%llX (panelId=0x%04X)",
                    (unsigned long long)thisPtr, panelId);

                // Fix for first-open-empty: when we just captured the handler
                // AND a F6/F7 trigger is currently waiting on init, run
                // InitWarehousePanel inline on the game thread NOW. This is
                // the same thread that's about to render the panel, so when
                // CanShow returns the panel renders WITH our SetInventory +
                // PanelValue + Title already applied. The WM_INIT_WAREHOUSE
                // posted by InputThread later still runs but is a no-op
                // because g_initPending was cleared.
                if (InterlockedCompareExchange(&g_initPending, 0, 0)) {
                    InterlockedExchange(&g_initPending, 0);
                    Log("  CanShow: running InitWarehousePanel inline (first-open fix)");
                    InitWarehousePanel(handler, GetInitStringForActive());
                }
            } else if (g_traceMode && handler == 0 &&
                       InterlockedCompareExchange(&s_diagMissCount, 0, 0) < 20) {
                // Log first 20 distinct mismatched vtables — tells us whether
                // the RTTI scan latched onto the wrong class or whether the
                // warehouse object simply isn't being polled this epoch.
                bool seen = false;
                for (int i = 0; i < 20; i++) {
                    if (s_diagMissVts[i] == objVtable) { seen = true; break; }
                }
                if (!seen) {
                    LONG idx = InterlockedIncrement(&s_diagMissCount) - 1;
                    if (idx >= 0 && idx < 20) s_diagMissVts[idx] = objVtable;
                    Log("  CanShow vtable-mismatch #%ld (epoch %ld): thisPtr=0x%llX vt=0x%llX (base+0x%llX) expected=base+0x%llX",
                        (long)(idx + 1), (long)epoch, (unsigned long long)thisPtr,
                        (unsigned long long)objVtable,
                        objVtable > g_gameBase ? (unsigned long long)(objVtable - g_gameBase) : (unsigned long long)objVtable,
                        g_warehouseVtableStart > g_gameBase ? (unsigned long long)(g_warehouseVtableStart - g_gameBase) : 0ULL);
                }
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        // If we have not yet captured the handler (auto-capture above did
        // not match — e.g. game uses a sub-object vtable that differs from
        // the static RTTI vtable we resolved), we cannot tell warehouse
        // from other panels. Fall through to the original CanShow so the
        // game's own logic can render whichever panel is legitimately
        // active. Without this, every CanShow poll was returning 0 →
        // even the warehouse got suppressed → UI never appeared.
        if (handler == 0) {
            return g_origCanShow(thisPtr);
        }
        if ((uintptr_t)thisPtr == handler) {
            __try {
                uint8_t activeFlag = *(uint8_t*)((uint8_t*)thisPtr + g_offActiveFlag);
                if (activeFlag == 1) {
                    // Panel is alive — remember we've seen it active and reset
                    // the close-detection counter.
                    InterlockedExchange(&g_canShowSeen118, 1);
                    InterlockedExchange(&g_canShowZeroCount, 0);
                } else if (activeFlag == 0 && InterlockedCompareExchange(&g_canShowSeen118, 0, 0)) {
                    // Housing chest panels (Gatherables, Refrigerator, …)
                    // briefly write 0 to +0x118 during internal sub-state
                    // transitions. The auto-close detection here was the
                    // root cause of "second-time B doesn't close": a short
                    // burst of zero polls during the second open would set
                    // g_warehouseActive=0 prematurely, after which the
                    // controller thread treated B presses as "warehouse not
                    // open" and silently dropped them.
                    //
                    // Auto-close is only meaningful while the panel is NOT
                    // mod-owned. While g_modeSwitchByMod==1 the mod itself
                    // is driving the session — the only legitimate close in
                    // that mode is via TriggerWarehouse, never an in-flight
                    // game write to +0x118. So gate the detection on the
                    // mod NOT owning the mode-switch, and require a long
                    // 60-poll (~1 s) stability window even then.
                    if (InterlockedCompareExchange(&g_modeSwitchByMod, 0, 0)) {
                        return 1;  // mod-owned session — never auto-close
                    }
                    LONG zc = InterlockedIncrement(&g_canShowZeroCount);
                    if (zc < 60) {
                        return 1;  // keep showing, treat as transient
                    }
                    Log("  CanShow: game-initiated close detected (active flag 1→0, %ld stable zero polls)", zc);
                    InterlockedExchange(&g_warehouseActive, 0);
                    InterlockedExchange(&g_canShowSeen118, 0);
                    InterlockedExchange(&g_canShowZeroCount, 0);
                    InterlockedExchange(&g_modeSwitchByMod, 0);
                    uintptr_t mc = (uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
                    // Release the menu-layer too — if the game closed only the
                    // panel (+0x118) without a layer close, +0x105E would stay
                    // 1 and poison all later menu opens. Idempotent when the
                    // game already closed the layer itself.
                    TriggerWarehouseViewUnmount();
                    SafeRestoreMode((uint8_t*)mc);
                    return g_origCanShow(thisPtr);
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
            return 1;   // WareHouseView: force show
        }
        // Blanket suppress ALL other panels while warehouse is active.
        // Do NOT delegate to origCanShow here — it has internal side-effects
        // that corrupt game state and cause the warehouse to reappear during
        // subsequent NPC interactions.
        __try {
            uintptr_t sub = *(uintptr_t*)((uint8_t*)thisPtr + g_offSubObject);
            uint16_t pid = sub ? *(uint16_t*)((uint8_t*)sub + g_offSubPanelId) : 0xFFFF;
            uint8_t flag = *(uint8_t*)((uint8_t*)thisPtr + g_offActiveFlag);
            if (flag)
                Log("  CanShow: suppressed panel 0x%04X (active=%d, thisPtr=0x%llX)",
                    pid, flag, (unsigned long long)thisPtr);
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
        return 0;
    }
    return g_origCanShow(thisPtr);
}

// ============================================================
//  Hook Installation
// ============================================================

// Check if first N bytes contain RIP-relative instructions (ModRM.mod=00, R/M=101)
// that would break when relocated to a trampoline at a different address.
// NOTE: FF 25 (JMP [rip+disp32]) thunks are excluded — they work correctly in
// trampolines because the inline 8-byte target address is copied alongside.
// Opcodes (after optional REX) that take a single ModRM operand. RIP-
// relative addressing is signaled by ModRM (mod=00, r/m=101); a relocation
// would break the trampoline copy.
static bool IsModrmOpcode(uint8_t op) {
    // ALU r/m,r and r,r/m (8 op-pairs, 01..3B step 8 with +0/+2 variants)
    if (op == 0x01 || op == 0x03 || op == 0x09 || op == 0x0B ||
        op == 0x11 || op == 0x13 || op == 0x19 || op == 0x1B ||
        op == 0x21 || op == 0x23 || op == 0x29 || op == 0x2B ||
        op == 0x31 || op == 0x33 || op == 0x39 || op == 0x3B) return true;
    // 0x63 = MOVSXD, 0x85 = TEST, 0x87 = XCHG, 0x89/0x8B = MOV, 0x8D = LEA
    if (op == 0x63 || op == 0x85 || op == 0x87 ||
        op == 0x89 || op == 0x8B || op == 0x8D) return true;
    // 0x83 = ALU r/m, imm8 ; 0x81 = ALU r/m, imm32 ; 0xC6/C7 = MOV r/m, imm
    if (op == 0x83 || op == 0x81 || op == 0xC6 || op == 0xC7) return true;
    return false;
}

static bool ContainsRipRelative(uint8_t* code, int len) {
    for (int i = 0; i < len - 2; i++) {
        uint8_t b = code[i];
        // Non-REX: CALL [rip+disp32] = FF 15 xx xx xx xx (ModRM 0x15: mod=00, r/m=101)
        // (FF 25 is JMP thunk — safe to relocate because inline data follows, so skip it)
        if (b == 0xFF && i + 5 < len && code[i + 1] == 0x15) return true;
        // Non-REX MOV/LEA/ALU etc. with RIP-relative: opcode + ModRM(mod=00, r/m=101)
        if (IsModrmOpcode(b) && i + 5 < len && (code[i + 1] & 0xC7) == 0x05) return true;
        // REX-prefixed (0x40-0x4F): same checks on the byte after REX
        if (b >= 0x40 && b <= 0x4F && i + 2 < len) {
            uint8_t op = code[i + 1];
            if ((IsModrmOpcode(op) || op == 0x0F) && (code[i + 2] & 0xC7) == 0x05)
                return true;
            // REX + FF 15 (CALL [rip+disp32])
            if (op == 0xFF && i + 6 < len && code[i + 2] == 0x15) return true;
        }
    }
    return false;
}

// Decode a ModRM operand block length (not counting the opcode itself).
// Returns the number of bytes used by ModRM + optional SIB + optional disp.
// On x64, mod=00 / rm=101 is RIP-relative with a 4-byte displacement (NOT
// supported here as a hookable prolog instruction — caller should rely on
// ContainsRipRelative to abort, but the length calc is still correct).
static int ModRMLen(uint8_t modrm) {
    uint8_t mod = modrm >> 6;
    uint8_t rm  = modrm & 0x07;
    int sib  = (mod != 3 && rm == 4) ? 1 : 0;
    int disp = (mod == 0) ? (rm == 5 ? 4 : 0)  // RIP-relative at mod=0/rm=5
             : (mod == 1) ? 1
             : (mod == 2) ? 4
             :              0;                  // mod=3 → reg-reg, no disp
    return 1 + sib + disp;
}

// Find the smallest instruction boundary >= minBytes in a typical MSVC x86-64 prologue.
// Handles common prologue patterns: MOV [RSP+N], REG; PUSH; SUB RSP; LEA RBP; MOV RBP,RSP;
// CMP/TEST/XOR/SUB/ADD/AND/OR (ALU r/m,r and r,r/m); MOV r/m,imm32.
static int FindPrologBoundary(uint8_t* code, int minBytes) {
    int pos = 0;
    while (pos < minBytes && pos < 30) {
        uint8_t b = code[pos];
        // Single-byte PUSH: 50-57 (PUSH RAX..RDI)
        if (b >= 0x50 && b <= 0x57) { pos += 1; continue; }
        // REX.B + PUSH: 41 50-57 (PUSH R8..R15)
        if (b == 0x41 && code[pos+1] >= 0x50 && code[pos+1] <= 0x57) { pos += 2; continue; }
        // REX (empty) + PUSH: 40 50-57 (PUSH RAX..RDI with REX — MSVC emits this for RBP/RSI/RDI)
        if (b == 0x40 && code[pos+1] >= 0x50 && code[pos+1] <= 0x57) { pos += 2; continue; }
        // REX.W prefix (48..4F): all variants set REX.W=1 and differ only in
        // which register-extension bits (R/X/B) are set. Instruction-length
        // decoding is identical — only the register selection changes.
        if (b >= 0x48 && b <= 0x4F) {
            uint8_t op = code[pos+1];
            // ModRM-only ALU/MOV/TEST/XCHG/LEA ops (no immediate):
            //   01/03/09/0B/11/13/19/1B/21/23/29/2B/31/33/39/3B — ALU r/m,r and r,r/m
            //   85 (TEST), 87 (XCHG), 89 (MOV r/m,r), 8B (MOV r,r/m), 8D (LEA)
            bool modrmOnly =
                (op == 0x01) || (op == 0x03) || (op == 0x09) || (op == 0x0B) ||
                (op == 0x11) || (op == 0x13) || (op == 0x19) || (op == 0x1B) ||
                (op == 0x21) || (op == 0x23) || (op == 0x29) || (op == 0x2B) ||
                (op == 0x31) || (op == 0x33) || (op == 0x39) || (op == 0x3B) ||
                (op == 0x85) || (op == 0x87) || (op == 0x89) || (op == 0x8B) ||
                (op == 0x8D);
            // ALU r/m, imm8  (op group 1 with sign-extended byte)
            bool imm8  = (op == 0x83) || (op == 0xC6);
            // ALU r/m, imm32 (op group 1 with full dword)
            bool imm32 = (op == 0x81) || (op == 0xC7);
            // FF group (INC/DEC/CALL/JMP/PUSH r/m) — ModRM-only, sub-op in reg field
            bool ffGroup = (op == 0xFF);
            if (modrmOnly || imm8 || imm32 || ffGroup) {
                int operand = ModRMLen(code[pos+2]);
                int immLen  = imm8 ? 1 : imm32 ? 4 : 0;
                pos += 2 + operand + immLen;
                continue;
            }
        }
        // JMP [RIP+disp32] thunk: FF 25 xx xx xx xx + 8-byte inline address = 14 bytes
        if (b == 0xFF && code[pos+1] == 0x25) { pos += 14; continue; }
        // 66 89 modrm [sib] [disp] — operand-size override + MOV r/m16, r16
        // Seen in 1.06.00 ItemDetail open handler @ 0xB4D250 which starts with
        // `66 89 54 24 10` (MOV word ptr [RSP+0x10], DX) before the PUSH chain.
        if (b == 0x66 && code[pos+1] == 0x89) {
            uint8_t modrm = code[pos+2];
            uint8_t mod = modrm >> 6, rm = modrm & 0x07;
            if (mod == 0x00) {
                if (rm == 0x05) { pos += 7; continue; }            // [rip+disp32]
                if (rm == 0x04) { pos += 4; continue; }            // [SIB]
                pos += 3; continue;                                // [reg]
            }
            if (mod == 0x01) { pos += 4 + (rm == 0x04 ? 1 : 0); continue; }  // [reg+disp8] (+SIB)
            if (mod == 0x02) { pos += 7 + (rm == 0x04 ? 1 : 0); continue; }  // [reg+disp32] (+SIB)
            if (mod == 0x03) { pos += 3; continue; }                          // reg,reg
        }
        // Unknown — bail out to avoid infinite loop
        Log("  FindPrologBoundary: unknown opcode 0x%02X at pos %d", b, pos);
        return 0;
    }
    return pos;
}

static bool InstallHook(uintptr_t func, uintptr_t capture, const char* name, int hookSize = 0) {
    // Auto-compute hook size if not provided: find instruction boundary >= 14 bytes
    if (hookSize <= 0) {
        hookSize = FindPrologBoundary((uint8_t*)func, 14);
        if (hookSize < 14 || hookSize > 28) {
            Log("HOOK %s: ABORT — cannot find clean instruction boundary (got %d) at base+0x%llX",
                name, hookSize, (unsigned long long)(func - g_gameBase));
            return false;
        }
    }
    // ALL size + capacity validation runs BEFORE the stack buffer copy: an
    // explicit hookSize > sizeof(orig) from a caller would overrun the local
    // buffer otherwise. (sizeof orig used here matches the actual buffer.)
    uint8_t orig[32];
    if (hookSize < 14 || hookSize > (int)sizeof(orig) ||
        hookSize > (int)sizeof(g_hookTable[0].orig) ||
        g_hookCount >= (int)(sizeof(g_hookTable)/sizeof(g_hookTable[0]))) {
        Log("HOOK %s: ABORT — invalid hookSize %d or hook-table full", name, hookSize);
        return false;
    }
    memcpy(orig, (void*)func, hookSize);
    if (ContainsRipRelative(orig, hookSize)) {
        Log("HOOK %s: ABORT — RIP-relative instruction in first %d bytes (base+0x%llX)",
            name, hookSize, (unsigned long long)(func - g_gameBase));
        return false;
    }
    void* thunk = VirtualAlloc(nullptr,256,MEM_COMMIT|MEM_RESERVE,PAGE_EXECUTE_READWRITE);
    if (!thunk) return false;
    uint8_t* t = (uint8_t*)thunk;
    uintptr_t ret = func + hookSize;
    *t++=0x50;*t++=0x51;*t++=0x52;
    *t++=0x41;*t++=0x50;*t++=0x41;*t++=0x51;*t++=0x41;*t++=0x52;*t++=0x41;*t++=0x53;
    *t++=0x48;*t++=0x83;*t++=0xEC;*t++=0x20;
    *t++=0x48;*t++=0x8B;*t++=0x4C;*t++=0x24;*t++=0x48;
    *t++=0x48;*t++=0x8B;*t++=0x54;*t++=0x24;*t++=0x40;
    *t++=0x48;*t++=0xB8; *(uintptr_t*)t=capture; t+=8;
    *t++=0xFF;*t++=0xD0;
    *t++=0x48;*t++=0x83;*t++=0xC4;*t++=0x20;
    *t++=0x41;*t++=0x5B;*t++=0x41;*t++=0x5A;*t++=0x41;*t++=0x59;*t++=0x41;*t++=0x58;
    *t++=0x5A;*t++=0x59;*t++=0x58;
    memcpy(t,orig,hookSize); t+=hookSize;
    *t++=0xFF;*t++=0x25; *(uint32_t*)t=0; t+=4; *(uintptr_t*)t=ret; t+=8;
    DWORD op;
    VirtualProtect((void*)func,hookSize,PAGE_EXECUTE_READWRITE,&op);
    uint8_t* p=(uint8_t*)func;
    p[0]=0xFF;p[1]=0x25; *(uint32_t*)(p+2)=0; *(uintptr_t*)(p+6)=(uintptr_t)thunk;
    for (int i = 14; i < hookSize; i++) p[i] = 0x90; // NOP padding
    VirtualProtect((void*)func,hookSize,op,&op);
    FlushInstructionCache(GetCurrentProcess(),(void*)func,hookSize);
    g_hookTable[g_hookCount].addr = func;
    g_hookTable[g_hookCount].size = hookSize;
    memcpy(g_hookTable[g_hookCount].orig, orig, hookSize);
    g_hookCount++;
    Log("HOOK %s: OK base+0x%llX (size=%d)",name,(unsigned long long)(func-g_gameBase),hookSize);
    return true;
}

static bool InstallCanShowHook(uintptr_t func) {
    // Try to find a clean prolog boundary >= 14 bytes so the trampoline tail
    // doesn't sit mid-instruction. If the decoder hits an opcode it doesn't
    // know (REX variants other than 48/4C, exotic prologs, ...), fall back to
    // the historical fixed 14-byte cut + NOP padding. That fallback has
    // worked on every release from 1.06 to 1.09; the boundary search is a
    // best-effort upgrade, not a hard requirement.
    int hookSize = FindPrologBoundary((uint8_t*)func, 14);
    if (hookSize < 14 || hookSize > 20) {
        Log("HOOK CanShow: prolog boundary not detected (got %d), falling back to fixed 14 bytes", hookSize);
        hookSize = 14;
    }
    // Reserve the table slot BEFORE patching so an overflow can't leave a
    // live patch that DLL_PROCESS_DETACH can never restore. Mirrors
    // InstallHook's contract (line 1504-1507).
    if (hookSize > (int)sizeof(g_hookTable[0].orig) ||
        g_hookCount >= (int)(sizeof(g_hookTable)/sizeof(g_hookTable[0]))) {
        Log("HOOK CanShow: ABORT — hook-table full or hookSize %d exceeds slot capacity", hookSize);
        return false;
    }
    uint8_t orig[20]; memcpy(orig, (void*)func, hookSize);
    if (ContainsRipRelative(orig, hookSize)) {
        Log("HOOK CanShow: ABORT — RIP-relative instruction in first %d bytes (base+0x%llX)",
            hookSize, (unsigned long long)(func - g_gameBase));
        return false;
    }
    uint8_t* trampoline = (uint8_t*)VirtualAlloc(nullptr, 64, MEM_COMMIT|MEM_RESERVE, PAGE_EXECUTE_READWRITE);
    if (!trampoline) return false;
    memcpy(trampoline, orig, hookSize);
    trampoline[hookSize    ] = 0xFF; trampoline[hookSize + 1] = 0x25;
    *(uint32_t*)(trampoline + hookSize + 2) = 0;
    *(uintptr_t*)(trampoline + hookSize + 6) = func + hookSize;
    g_origCanShow = (PFN_CanShow)trampoline;
    DWORD op;
    VirtualProtect((void*)func, hookSize, PAGE_EXECUTE_READWRITE, &op);
    uint8_t* p = (uint8_t*)func;
    p[0] = 0xFF; p[1] = 0x25;
    *(uint32_t*)(p + 2) = 0;
    *(uintptr_t*)(p + 6) = (uintptr_t)&HookedCanShow;
    for (int i = 14; i < hookSize; i++) p[i] = 0x90; // NOP-pad tail of replaced instructions
    VirtualProtect((void*)func, hookSize, op, &op);
    FlushInstructionCache(GetCurrentProcess(), (void*)func, hookSize);
    // Capacity check already gated above; recording here is unconditional.
    g_hookTable[g_hookCount].addr = func;
    g_hookTable[g_hookCount].size = hookSize;
    memcpy(g_hookTable[g_hookCount].orig, orig, hookSize);
    g_hookCount++;
    Log("HOOK CanShow: OK base+0x%llX (size=%d)", (unsigned long long)(func - g_gameBase), hookSize);
    return true;
}

// ============================================================
//  Scope-actor binding for the active panel
// ============================================================
// In 1.05.0 SetInventory subscribes a channel and then fires the
// vtable[+0x20] "subscribe" virtual on an "actor" obtained via:
//   sub_controller[1]+0x8 → +0x60 = scope-root
//   FUN_1435115C0(scope-root) walks +0xa8/+0x50 chain looking for a node
//   with non-null +0x140 → returns *(node+0x140) as the actor
// Items are pushed during that subscribe call. If the actor is the wrong
// chest (e.g. previous panel's), wrong items render.
//
// This helper looks up the correct chest_object via the game's own
// FUN_143511520 (chest-registry indexed by type-id), then writes it into
// scope+0x140 so FUN_1435115C0 returns it on the very first iteration.
//
// Limitation: FUN_143511520 returns 0 if the chest's type_id is not in
// (scene+0xb0)+0xd8. That registry is filled by world-streaming, so for
// housing chests the player must have been in the camp area at least
// once. CampWareHouse (PRIVATE) is always loaded with the camp scene.

// ============================================================
//  Warehouse panel initialization (handler-dependent steps)
//  Called from TriggerWarehouse when handler is available, or
//  deferred via WM_INIT_WAREHOUSE when handler wasn't captured yet.
// ============================================================
// CD 1.10 context-free view-mount trigger (Ghidra-verified).
// Replicates only the menu-layer STATE WRITES the game's tick FUN_140782EE0
// performs on its open path (current/+0x105E=1, request/+0x105F=1). The
// tick itself is never called: it dereferences the interaction target
// (menuMgr+0x10C8) which faults on a cold remote open. subtypes[6]=1 (set
// by SafeSetupModeForWarehouse) drives the actual panel mount via the
// mode resolver; the state bytes keep the menu-layer machine consistent.
//
// menuMgr is resolved drift-proof via ResolveMenuMgr() — see that function.
// (The original 1.10 hardcoded global base+0x6066F90 was moved by the
// 2026-06-19 update; ResolveMenuMgr derives + validates it instead.)
//   menuMgr fields: +0x105E current, +0x105F request, +0x11C0 mainChar.
// All steps null-checked + SEH-guarded.
// Returns false ONLY when the menu-layer is already flagged open
// (+0x105E==1) — at TriggerWarehouse time that means a game menu session's
// close is still in flight (fast re-open after shop/cooking/bank) and the
// caller must abort instead of creating an invisible ghost session.
//
// NOTE on the event queue (append removed in v1.5.6): the game's writers
// pass *(holder+0x878) — the channel queue POINTER stored in the slot — to
// FUN_1403862B0; v1.5.5 passed the slot ADDRESS holder+0x878, so the
// append misread slot bytes as queue fields and faulted on every open
// (SEH-caught "EXCEPTION at step 'enqueue'"). No mod session ever delivered
// an event, and panels demonstrably mount fine via the sub=6 path alone.
// The append is deliberately OMITTED rather than fixed: a delivered open
// event would fire the game's menu-layer listener (LAB_140AA8E30 ->
// FUN_14A59D7D0 open transition), whose tick unconditionally dereferences
// the interaction context *(menuMgr+0x10C8) — a path never exercised by
// mod sessions and unsafe on a cold remote open. The queue is a one-way
// state-changed broadcast; natural sessions emit their own events, missing
// mod events are harmless (Ghidra-verified 2026-06-10).
static bool TriggerWarehouseViewMount() {
    const char* step = "start";
    __try {
        uintptr_t menuMgr = ResolveMenuMgr();
        if (menuMgr <= 0x10000) { Log("  ViewMount: menuMgr unresolved"); return true; }
        step = "read state";
        uint8_t cur = *(uint8_t*)(menuMgr + 0x105E);  // current state
        if (cur == 1) {
            // Do NOT touch the state bytes here — if a game session owns the
            // layer, overwriting +0x105F would interfere with its close.
            Log("  ViewMount: layer busy (+0x105E=1)");
            return false;
        }
        step = "write state";
        *(uint8_t*)(menuMgr + 0x105F) = 1;            // request open
        *(uint8_t*)(menuMgr + 0x105E) = 1;            // mark current=open
        Log("  ViewMount: state set (current=1, request=1)");
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  ViewMount: EXCEPTION at step '%s' (open continues)", step);
    }
    return true;
}

// Close counterpart of TriggerWarehouseViewMount (Ghidra-verified against
// CD 1.10). The menu-layer's NATURAL resting state is the pair
//   current (+0x105E) = 4, request (+0x105F) = 3
// — both the menuMgr constructor (FUN_14076F860: dword 0x03040000 written
// to +0x105C) and a completed natural close (FUN_14A59D7D0 request=2 ->
// tick sets current=4 + close event 4; fade end -> FUN_140AA8A10 sets
// request=3) park there. The request byte MUST end at 3, not 1/2: the
// state tick FUN_140782EE0 runs on every NPC-interaction edge and only
// CLEARS the mainChar menu-ownership flags (+0xCBD = subtypes[5] = the
// CINEMA sub-mode flag, +0xCC5 = subtypes[13] = mainmenu flag) when
// request==3; for any other parked value it re-asserts subtypes[5]=1.
// The mode resolver FUN_140709D60 derives the sub-mode from the FIRST
// non-zero subtype index, so a stuck subtypes[5]=1 (index 5, cinema)
// permanently shadows index 6 (store): merchant talks then zoom the
// camera (cinema layer) but never show the vendor/provisions/bank UI.
// A parked request=2 additionally lets the tick emit spurious close
// events on interaction edges and freezes the HUD interaction prompt
// (its re-show timer in FUN_140D90550 requires request in {1,3}).
// History: v1.5.5 parked (current=1, request=1) — flag poison plus
// current==1 swallowing every edge-triggered natural open. An interim
// test build parked (4, 2) — the flag poison remained. (4, 3) is the
// verified idle pair. No close event is appended — see the event-queue
// note at TriggerWarehouseViewMount (the queue is a one-way broadcast,
// missing/unpaired events are harmless).
static void TriggerWarehouseViewUnmount() {
    const char* step = "start";
    __try {
        uintptr_t menuMgr = ResolveMenuMgr();
        if (menuMgr <= 0x10000) { Log("  ViewUnmount: menuMgr unresolved"); return; }
        step = "write state";
        if (*(uint8_t*)(menuMgr + 0x105E) == 4) {
            // Layer already closed — still park the request byte at its
            // idle value so the tick's clear branch stays armed.
            *(uint8_t*)(menuMgr + 0x105F) = 3;
            Log("  ViewUnmount: already closed — request parked at 3 (idle)");
            return;
        }
        *(uint8_t*)(menuMgr + 0x105F) = 3;            // request = idle (ctor + post-close value)
        *(uint8_t*)(menuMgr + 0x105E) = 4;            // current = closed
        Log("  ViewUnmount: parked at (current=4, request=3)");
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  ViewUnmount: EXCEPTION at step '%s'", step);
    }
}

// ============================================================
//  Filter sub-controller probe (read-only diagnostic).
//
//  HISTORY / WHY THIS DOES NOT RENDER ANYTHING (Ghidra audit 2026-06-10):
//  The sub-controller at handler+0x1A8 with the 1.08 setter/render pair
//  (1.10: setter base+0xB9B8C0, render base+0xB99620) is NOT the category
//  tab bar (bag / armor / weapon / food / scroll / gem) shown in the
//  screenshots — it is a YEAR/MONTH date selector: +0xC0 = calendar year,
//  +0xC2 = month (1..12). The render scans a date-grouped document store
//  for entries whose SYSTEMTIME matches (year,month) and rebuilds that
//  date strip. Calling it on a remote/mod open faults for two independent
//  reasons that guarding alone cannot fix:
//    1. The render's tail unconditionally writes through *(filter+0x100)
//       and vcalls *(*(filter+0x100))+0x518/+0x510. On remote opens +0x100
//       holds an image/vtable pointer, not the heap list-control object a
//       natural NPC open installs → access violation (confirmed live:
//       "render EXCEPTION").
//    2. The item refill FUN_140609350 dereferences a document-context
//       chain *(*(DAT_146066F40+0x30)+0x50)+0x68+0x148 that only exists
//       after a real warehouse interaction.
//  Writing mode/sub directly is also wrong: (1,1) means "January, Year 1",
//  which matches no items. So the render call was removed entirely. This
//  helper now only LOGS the field values (useful if the category-tab work
//  is ever revisited) and never writes or calls into the game.
// ============================================================
static void ProbeFilterSubController(uintptr_t filterObj, const char* slotName) {
    __try {
        if (filterObj < 0x10000000000ULL) {
            Log("  Filter[%s]: slot empty (0x%llX)", slotName, (unsigned long long)filterObj);
            return;
        }
        uintptr_t scope   = *(uintptr_t*)(filterObj + 0x8);
        uint16_t  curMode = *(uint16_t*)(filterObj + 0xC0);
        uint16_t  curSub  = *(uint16_t*)(filterObj + 0xC2);
        uint32_t  mapCnt  = *(uint32_t*) (filterObj + 0xD8);
        uintptr_t ui100   = *(uintptr_t*)(filterObj + 0x100);
        uintptr_t ui108   = *(uintptr_t*)(filterObj + 0x108);
        Log("  Filter[%s]: obj=0x%llX scope=0x%llX mode=%u sub=%u mapCnt=%u "
            "ui100=0x%llX ui108=0x%llX (probe only — no render)",
            slotName, (unsigned long long)filterObj, (unsigned long long)scope,
            curMode, curSub, mapCnt,
            (unsigned long long)ui100, (unsigned long long)ui108);
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  Filter[%s]: probe EXCEPTION", slotName);
    }
}

static void InitWarehousePanel(uintptr_t handler, const char* initString) {
    // InvSaveData heap scan removed: ran synchronously on the input thread
    // and consistently produced 0 hits (~800ms stutter on first F6 open).
    // If the scan ever becomes useful again, run it from a worker thread.

    // Re-apply the 10 -> 1000 slot-count patch synchronously on every open.
    // The background worker only re-checks every ~3s, and the game resets the
    // InventoryInfo slot base back to 10 on a reload (save-load AND teleport /
    // zone transition). Without this, opening a housing chest in the short
    // window right after a teleport shows the vanilla capacity (10) until the
    // worker catches up. Patching here guarantees the box always opens at 1000.
    // Cheap + SEH-guarded; a no-op when the entries are already 1000.
    if (g_addrInventoryInfoMgrPtr) {
        int n = PatchInventoryInfoSlots();
        if (n > 0) Log("  Slot patch (on open): %d entries default 10 -> 1000", n);
    }

    // Clear stale modal dialog pointer from previous warehouse sessions.
    // Self-validate first: the slot must be 0 or a canonical heap pointer. If it
    // holds a small scalar / non-canonical value the handler struct has drifted and
    // +g_modalDialogOff is no longer the modal slot — skip the (valid-but-wrong,
    // SEH-uncatchable) write and disable modal tracking for this session.
    if (g_modalDialogOff && g_modalOffValid) {
        __try {
            uintptr_t cur = *(uintptr_t*)(handler + g_modalDialogOff);
            bool looksValid = (cur == 0) ||
                (cur >= 0x10000000000ULL && cur < 0x7FFFFFFFFFFFULL);
            if (looksValid) {
                *(uintptr_t*)(handler + g_modalDialogOff) = 0;
                Log("  Cleared stale modal pointer at +0x%X", g_modalDialogOff);
            } else {
                g_modalOffValid = false;
                Log("  Modal offset +0x%X looks relocated (0x%llX) — modal tracking disabled this build",
                    g_modalDialogOff, (unsigned long long)cur);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // CD 1.10 NOTE (Ghidra-verified 2026-06-07): rendering is gated by the
    // controller's render flag handler+0x2CD, which the Binder (FUN_140A9C820)
    // only sets once the warehouse VIEW is mounted by the menu-manager. That
    // mount path (FUN_14A59D7D0 / FUN_140782EE0 -> FUN_1403862B0) dereferences
    // interaction context (DAT_146066F40 chain, menuMgr+0x10C8) that does NOT
    // exist on a cold remote open, so calling those game functions directly
    // faults. Instead we replicate ONLY the context-free menu-layer state
    // writes of FUN_140782EE0's open path (see TriggerWarehouseViewMount;
    // the event append was removed in v1.5.6 — see the note there). The
    // actual mount is driven by subtypes[6]=1, set by
    // SafeSetupModeForWarehouse. This re-call is idempotent (logs "layer
    // busy" because the first call already set current=1).
    TriggerWarehouseViewMount();


    // CD 1.10 SUB-MODE FIX — 2026-06-07
    //
    // The REAL fix: WareHouseView2.html in uigameconfig2.xml is tagged
    // tag2="store ingamemenu" — the panel-manager only mounts this view
    // when mainChar[+0xCA9] (sub byte) is 6 (store) or 0xE (ingamemenu).
    // In all prior mod versions the sub byte was left at 0x10 (interaction)
    // and the view never mounted, so the panel could never render no matter
    // what the mod did to the warehouse instance / descriptor / queue.
    //
    // The fix is in SafeSetupModeForWarehouse, which now sets sub=6 on
    // open and restores the original on close. Once sub=6 the panel-manager
    // mounts WareHouseView2 on its next tick; the existing cmd 0x0E below
    // then sets the active flag and the panel renders naturally.
    //
    // All earlier 1.10-era inline attempts (Init pre-check, vt[51] Show,
    // multi-cmd 0x12/0x0D/0x15 sequence, descriptor +0x269 patch, direct
    // queue-insert via thunk_FUN_156137720) have been removed — they were
    // band-aids around the missing mount, and the queue-insert in
    // particular crashed the game in 2026-06-07 testing because it
    // bypassed engine state-machine guarantees.

    // Send an empty 0x15 (prepare) BEFORE 0x0E — the natural-open order
    // captured via Handler trace in 1.08. The 0x15 dispatcher makes three
    // virtual "prepare" calls on the sub-objects at g_offPrepare1/2/3
    // before iterating sub-commands; with count=0 only the prepares run.
    // These virtuals are vtable-dispatched (no static xrefs — the
    // "unanalyzed cold region" around 0x140ABBA10) and are the prime
    // candidate for constructing the filter tab-bar helper at
    // filter+0x100/+0x108 (in-place ctor FUN_14A668620), which natural
    // opens bind and remote opens were missing. The send existed through
    // v1.5.2 (tabs worked on mod opens in 1.08) and was lost in a later
    // rework — the stale "now sent earlier" comment outlived the code.
    // Guards unchanged from v1.5.1: all three sub-objects must be non-null
    // or the dispatcher crashes (they can be unset before the first NPC
    // interaction of a session).
    if (g_fnHandler) {
        __try {
            uintptr_t sub1 = *(uintptr_t*)(handler + g_offPrepare1);
            uintptr_t sub2 = *(uintptr_t*)(handler + g_offPrepare2);
            uintptr_t sub3 = *(uintptr_t*)(handler + g_offPrepare3);
            if (sub1 > 0x10000 && sub2 > 0x10000 && sub3 > 0x10000) {
                uint8_t emptyPacket[24] = {};
                emptyPacket[0] = 0x15;
                typedef void (__fastcall *PFN_Handler)(void*, void*, void*, void*);
                ((PFN_Handler)g_fnHandler)((void*)handler, nullptr, nullptr, (void*)emptyPacket);
                Log("  Empty 0x15 sent (prepare calls triggered, offs=%X/%X/%X)",
                    g_offPrepare1, g_offPrepare2, g_offPrepare3);
            } else {
                Log("  Empty 0x15 SKIPPED (sub-objects null: %llX/%llX/%llX at offs %X/%X/%X)",
                    (unsigned long long)sub1, (unsigned long long)sub2,
                    (unsigned long long)sub3,
                    g_offPrepare1, g_offPrepare2, g_offPrepare3);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Empty 0x15 EXCEPTION");
        }
    }

    // Now send cmd 0x0E — sets active flag + tells panel-manager to show.
    if (g_fnHandler) {
        __try {
            uint8_t showPacket[24] = {};
            showPacket[0] = 0x0E;
            typedef void (__fastcall *PFN_Handler)(void*, void*, void*, void*);
            ((PFN_Handler)g_fnHandler)((void*)handler, nullptr, nullptr, (void*)showPacket);
            Log("  Cmd 0x0E sent (v1.5.1-style + 1.10 desc+0x269 patch above)");
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Cmd 0x0E EXCEPTION — falling back to manual active-flag set");
            __try {
                *(uint8_t*)(handler + g_offActiveFlag) = 1;
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
        }
    }

    // Reset faction-donation state (3 shorts, 0xFFFF = no faction selected).
    if (g_offDonationState) {
        __try {
            uint16_t* ds = (uint16_t*)(handler + g_offDonationState);
            if (ds[0] != 0xFFFF || ds[1] != 0xFFFF || ds[2] != 0xFFFF) {
                ds[0] = 0xFFFF;
                ds[1] = 0xFFFF;
                ds[2] = 0xFFFF;
                Log("  Cleared donation state at +0x%X", g_offDonationState);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // Save original handler+0x110 before any mod write. In 1.06 this was a
    // PanelValue scalar (safe to write/clear). In 1.08 the handler struct
    // shifted (BottomLabel +0x28, ActiveFlag +0x10), so +0x110 might now host
    // a different field — possibly a pointer. Writing 0 on close would null a
    // pointer the game later derefs during natural NPC-open. Save once per
    // session; restore on close.
    if (InterlockedCompareExchange64(&g_savedPanelValueSlot, 0, 0) == -1) {
        __try {
            uintptr_t orig = *(uintptr_t*)(handler + g_offPanelValue);
            InterlockedExchange64(&g_savedPanelValueSlot, (LONG64)orig);
            // PanelValue is a small type-id scalar. A canonical pointer here means
            // the slot drifted to a different field — disable override/restore.
            g_panelValueSlotValid = (orig < 0x10000);
            Log("  Saved original handler+0x%X = 0x%llX (PanelValue slot%s)",
                g_offPanelValue, (unsigned long long)orig,
                g_panelValueSlotValid ? "" : " — looks relocated, override disabled");
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }

    // Override panelValue (handler+0x110) for the active panel. The 0x0e dispatcher
    // reads this from a type-0x05 sub-command in the packet (parsed via strtoull),
    // but our packet has no sub-commands so it defaults to 0. For Housing-Chests this
    // is required so the container is bound — otherwise SetInventory loads items but
    // the container metadata (max-slots etc.) stays at the Camp default.
    //
    // For Gatherables: prefer the runtime hash-map lookup (per-session ID), fall back
    // to INI-configured static value if lookup fails.
    {
        LONG act = InterlockedCompareExchange(&g_activePanel, 0, 0);
        if (act < 0 || act >= PANEL_COUNT) act = PANEL_PRIVATE;
        LONG pv  = 0;
        const char* src = "none";
        if (act == PANEL_PRIVATE) {
            pv = InterlockedCompareExchange(&g_privatePanelValueCfg, 0, 0);
            src = "INI";
        } else {
            // Per-panel lookup: each housing namespace (Gatherables, Dresser,
            // Refrigerator, Symbol, Collecting) maps to its own 2-byte type-id
            // via the same hash-map resolver. The id binds handler+0x110 to
            // the right container metadata.
            uint16_t resolved = GetPanelTypeId(act);
            if (resolved != 0xFFFF && resolved != 0) {
                pv = (LONG)resolved;
                src = "per-panel hash-map";
            } else {
                pv = InterlockedCompareExchange(&g_gatherablesPanelValueCfg, 0, 0);
                src = "INI fallback (Gatherables)";
            }
        }
        if (pv != 0 && g_panelValueSlotValid) {
            __try {
                *(uintptr_t*)(handler + g_offPanelValue) = (uintptr_t)pv;
                Log("  PanelValue override: handler+0x%X = 0x%llX (%s, source=%s)",
                    g_offPanelValue, (unsigned long long)(uintptr_t)pv,
                    g_panels[act].name, src);
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  PanelValue override EXCEPTION");
            }
        } else if (pv != 0 && !g_panelValueSlotValid) {
            Log("  PanelValue override SKIPPED (slot +0x%X looks relocated)", g_offPanelValue);
        }

        // Container at handler+0x170 is NULL without an NPC visit (the 0x0e
        // panel-show command, which would normally bind Camp's container, throws
        // an exception in our flow). So we can't patch a container that doesn't
        // exist. Instead, patch the handler & sub fields directly — these match
        // exactly the byte changes captured in the post-NPC memory diff.
        //
        // Per-panel field state from the diff (Camp default → GC after-NPC):
        //   handler+0x1D8 (u32):   0x00000000 → 0xFFFFFFFF
        //   handler+0x200 (u8 ):   0x01 → 0x00
        //   handler+0x2A8 (u32):   0xFFFFFFFF → 0x00000000
        //   sub+0x0B5     (u8 ):   0xD0 → 0xC0
        //   sub+0x0B6     (u8 ):   0x02 → 0x00
        //   sub+0x276     (u8 ):   0x02 → 0x00
        //   sub+0x435     (u8 ):   0x14 → 0x10  ← possibly the "10" we see
        //
        // Save originals on first F7, restore on F6 to avoid Camp regression.
        {
            __try {
                uintptr_t sub = *(uintptr_t*)(handler + 0x8);
                if (act != PANEL_PRIVATE) {  // any housing panel (Gatherables/Dresser/...)
                    if (!InterlockedCompareExchange(&g_campValuesSaved, 0, 0)) {
                        InterlockedExchange(&g_savedCamp_84, (LONG)*(uint32_t*)(handler + 0x1D8));
                        InterlockedExchange(&g_savedCamp_9C, (LONG)*(uint32_t*)(handler + 0x2A8));
                        InterlockedExchange(&g_savedCamp_A0,
                            sub ? (LONG)(uint32_t)(*(uint16_t*)(sub + 0xB5) | (*(uint8_t*)(sub + 0x276) << 16) | (*(uint8_t*)(sub + 0x435) << 24)) : 0);
                        InterlockedExchange(&g_savedCamp_B8, (LONG)(*(uint8_t*)(handler + 0x200)));
                        InterlockedExchange(&g_savedCamp_39C, (LONG)*(uint32_t*)(handler + 0x39C));
                        InterlockedExchange(&g_campValuesSaved, 1);
                        Log("  Saved Camp state: handler+0x1D8=0x%X +0x200=0x%X +0x2A8=0x%X "
                            "+0x39C=%u sub+0xB5=0x%X +0xB6=0x%X +0x276=0x%X +0x435=0x%X",
                            *(uint32_t*)(handler + 0x1D8),
                            (unsigned)*(uint8_t*)(handler + 0x200),
                            *(uint32_t*)(handler + 0x2A8),
                            *(uint32_t*)(handler + 0x39C),
                            sub ? (unsigned)*(uint8_t*)(sub + 0xB5) : 0,
                            sub ? (unsigned)*(uint8_t*)(sub + 0xB6) : 0,
                            sub ? (unsigned)*(uint8_t*)(sub + 0x276) : 0,
                            sub ? (unsigned)*(uint8_t*)(sub + 0x435) : 0);
                    }
                    // 1.05.0: handler-field patches kept (cosmetic max-slots),
                    // but sub-field patches DISABLED. The sub+0xB5/0xB6/0x276/
                    // 0x435 writes were derived from a 1.0.4.x post-NPC memory
                    // diff and may stomp 1.0.5.0 rendering state — e.g. block
                    // the channel-bind from propagating into the visible grid.
                    //
                    // 2026-05: handler+0x200 patch DISABLED. The 0x01→0x00
                    // transition was observed in the post-NPC memory diff,
                    // but writing 0x00 puts the panel into a state where
                    // the game's input pipeline consumes B-press events
                    // before they reach XInput's per-process state. Result:
                    // user presses B on Xbox controller, mod's InputThread
                    // polls XInput and never sees 0x2000, B-close fails for
                    // Gatherables / Refrigerator / Dresser / Symbol /
                    // Collecting (works fine for Private/Camp because that
                    // path doesn't enter this branch).
                    // 1.06.00: handler+0x1D8/+0x2A8 patches DISABLED. These
                    // offsets came from a 1.0.4.x post-NPC memory diff and
                    // 1.06 has restructured the handler struct — writing
                    // 0xFFFFFFFF / 0x00000000 to these slots corrupts state
                    // that 1.06 uses for housing-panel rendering, leading
                    // to a crash on first frame. The +0x39C max-slots patch
                    // is also redundant in 1.06 because PatchInventoryInfoSlots
                    // already bumped the per-info slot count to 1000 (see
                    // boot log: "InventoryInfo slot patch: 5 entries default 10 -> 1000").
                    // *(uint32_t*)(handler + 0x1D8) = 0xFFFFFFFF;  // 1.06: disabled
                    // *(uint32_t*)(handler + 0x2A8) = 0x00000000;  // 1.06: disabled
                    // *(uint32_t*)(handler + 0x39C) = 1000;        // 1.06: redundant (InventoryInfo patch covers it)

                    Log("  Handler patches SKIPPED for housing panel in 1.06 (1.05 memory-diff offsets corrupt 1.06 state)");

                } else {
                    if (InterlockedCompareExchange(&g_campValuesSaved, 0, 0)) {
                        *(uint32_t*)(handler + 0x1D8) = (uint32_t)InterlockedCompareExchange(&g_savedCamp_84, 0, 0);
                        *(uint8_t* )(handler + 0x200) = (uint8_t )InterlockedCompareExchange(&g_savedCamp_B8, 0, 0);
                        *(uint32_t*)(handler + 0x2A8) = (uint32_t)InterlockedCompareExchange(&g_savedCamp_9C, 0, 0);
                        *(uint32_t*)(handler + 0x39C) = (uint32_t)InterlockedCompareExchange(&g_savedCamp_39C, 0, 0);
                        if (sub) {
                            uint32_t packed = (uint32_t)InterlockedCompareExchange(&g_savedCamp_A0, 0, 0);
                            *(uint8_t*)(sub + 0xB5)  = (uint8_t)(packed       & 0xFF);
                            *(uint8_t*)(sub + 0xB6)  = (uint8_t)((packed >> 8 ) & 0xFF);
                            *(uint8_t*)(sub + 0x276) = (uint8_t)((packed >> 16) & 0xFF);
                            *(uint8_t*)(sub + 0x435) = (uint8_t)((packed >> 24) & 0xFF);
                        }
                        Log("  Restored Camp handler+sub state");
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  Handler/sub patch EXCEPTION");
            }
        }

        // Pre-clear stale bind: if handler+0x170 still holds the previous
        // panel's container, clear it so our FUN_140a754e0 call below cleanly
        // re-binds. Without this, FUN_140a754e0's pre-write check on +0x170
        // can keep the wrong container if its sub-resolution path bails.
        //
        // The actual bind+refresh now happens AFTER SetInventory, by calling
        // FUN_140a754e0(handler, sub) — the game's natural NPC-open routine.
        // v1.4.2 strategy: pre-clear stale + per-panel sticky restore.
        // SetInventory's unbind/rebind below does the actual refresh — no
        // explicit BindRefresh call needed.
        //
        // Helper: invalidate the multi-field cache at grid+0x560..0x5F0 so the
        // next FUN_140C55680(grid, source, _) call cannot short-circuit.
        // Without this, switching between panels keeps the previous panel's
        // grid content visible (cached source-key still matches old).
        // Per RE: setting +0x568 = -1 forces bVar3=false in the cache check.
        auto invalidateGridCache = [](uintptr_t handler) {
            __try {
                uintptr_t grid = *(uintptr_t*)(handler + 0x178);
                if (grid >= 0x10000000000ULL) {
                    *(short*)(grid + 0x568) = -1;
                    Log("  Grid cache invalidate: grid=0x%llX +0x568=-1",
                        (unsigned long long)grid);
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  Grid cache invalidate EXCEPTION");
            }
        };
        {
                LONG ap = act;  // captured earlier in this block
                uintptr_t existing = 0;
                __try { existing = *(uintptr_t*)(handler + 0x170); } __except(EXCEPTION_EXECUTE_HANDLER) {}

                LONG64 panelSticky = InterlockedCompareExchange64(&g_panelStickyContainer[ap], 0, 0);
                LONG curBound = InterlockedCompareExchange(&g_currentBoundPanel, 0, 0);

                // 1.08 finding from Ghidra: handler+0x170 is NOT a container slot
                // in this version — it's one of 7 sub-controller pointers managed
                // by the UIGamePlayControlRootMoveItem base class (FUN_140a84ab0
                // dtor frees slots +0x150/+0x160/+0x170/+0x180/+0x1D8/+0x220/+0x2F0).
                // Clearing it to NULL detaches a sub-controller the base class
                // expects when rendering — next natural NPC-open then derefs NULL
                // on the rendering path and crashes when items/UI pop up.
                bool needClear = false;  // (existing >= 0x10000000000ULL) && (curBound != ap);
                if (needClear) {
                    __try {
                        *(uintptr_t*)(handler + 0x170) = 0;
                        Log("  Container bind: cleared stale 0x%llX (was %s, opening %s)",
                            (unsigned long long)existing,
                            (curBound >= 0 && curBound < PANEL_COUNT) ? g_panels[curBound].name : "?",
                            g_panels[ap].name);
                        existing = 0;
                    } __except(EXCEPTION_EXECUTE_HANDLER) {
                        Log("  Container bind: clear EXCEPTION");
                    }
                }

                bool slotFinalized = false;
                if (existing >= 0x10000000000ULL) {
                    // Probe the existing pointer's vtable to catch the case
                    // where a game update shifts handler+0x170 to a struct
                    // field with random heap-looking content (false-positive
                    // "valid"). A real bound sub-controller/container has its
                    // vtable inside the game image; anything else is suspect.
                    uintptr_t existingVt = 0;
                    bool vtInImage = false;
                    __try {
                        existingVt = *(uintptr_t*)existing;
                        vtInImage = (existingVt >= g_gameBase && existingVt < g_gameBase + g_imageSize);
                    } __except(EXCEPTION_EXECUTE_HANDLER) {}
                    // Diagnostic-only: log the vtable origin, but ALWAYS keep
                    // the existing container. The "out-of-image" path is a
                    // false-positive — sub-controllers managed by the base-
                    // class dtor (see header comment for handler+0x170 above)
                    // legitimately hold heap-allocated vtables on this build.
                    // Earlier v1.5.4 cleared `existing` on OUT-of-image which
                    // would route housing-panels into NULL-out — that's the
                    // exact scenario the lines-1920 warning forbids.
                    Log("  Container bind: handler+0x170=0x%llX for %s — keep (vt=0x%llX %s)",
                        (unsigned long long)existing, g_panels[ap].name,
                        (unsigned long long)existingVt,
                        vtInImage ? "in-image" : "heap/relocated, normal for sub-controllers");
                    slotFinalized = true;
                }
                if (!slotFinalized) {
                  if (ap == PANEL_PRIVATE) {
                    // Private container is auto-captured by the game on F6
                    // (the AUTO-CAPTURED handler IS bound to its real Private
                    // container with vtable base+0x4A4ACA0). Do NOT replace it
                    // via the global array: array[0x59] returns a Housing-type
                    // wrapper (vtable base+0x4FDC728) which crashes SetInventory.
                    Log("  Container bind: Private — keeping game's auto-bound container (no array override)");
                    // 1.06.00: grid cache invalidate disabled for Private.
                    // The +0x568 cache-key offset is from 1.05; in 1.06 this
                    // slot may belong to a different field whose modification
                    // contributed to the first-frame crash.
                    Log("  Grid cache invalidate SKIPPED for Private (1.06 crash workaround)");
                  } else {
                    // Housing panels (F7+): The global container array is
                    // index-reachable per-panel, BUT the wrappers it returns
                    // have vtable base+0x4FDC728 which is NOT layout-compatible
                    // with what handler+0x170 expects (SetInventory crashes).
                    // Fall back to v1.4.2 behavior: restore from sticky cache
                    // if a real chest-NPC visit populated it earlier this
                    // session; otherwise leave NULL and let SetInventory's
                    // natural rebind populate handler+0x170.
                    if (panelSticky) {
                        bool stickyValid = false;
                        __try {
                            uintptr_t vt = *(uintptr_t*)(uintptr_t)panelSticky;
                            stickyValid = (vt >= g_gameBase && vt < g_gameBase + g_imageSize);
                        } __except(EXCEPTION_EXECUTE_HANDLER) { stickyValid = false; }
                        if (stickyValid) {
                        __try {
                            *(uintptr_t*)(handler + 0x170) = (uintptr_t)panelSticky;
                            // Mark sticky as mod-owned for this session so the
                            // observer leaves it alone (cleared on panel close).
                            InterlockedExchange(&g_panelStickyOwnedByMod[ap], 1);
                            // NOTE: do NOT set g_currentBoundPanel here — that
                            // breaks SetInventory's prevUnbind logic which
                            // checks (curBound != ap) and would skip the
                            // unbind of the previous panel's namespace.
                            // g_currentBoundPanel is set after SetInventory.
                            Log("  Container bind: restored %s sticky 0x%llX (mod-owned)",
                                g_panels[ap].name, (unsigned long long)panelSticky);
                        } __except(EXCEPTION_EXECUTE_HANDLER) {
                            Log("  Container bind: sticky write EXCEPTION");
                        }
                        // 1.06.00: grid cache invalidate disabled here too — the
                        // +0x568 cache slot referenced a 1.05 field that does
                        // not exist at the same offset in 1.06; writing -1 to
                        // whatever now lives there contributes to the post-open
                        // render crash. The natural SetInventory unbind+rebind
                        // performs the same cache flush via the game's own path.
                        // invalidateGridCache(handler);
                    } else {
                        Log("  Container bind: %s sticky 0x%llX stale (vtable mismatch) — clear",
                            g_panels[ap].name, (unsigned long long)panelSticky);
                        InterlockedExchange64(&g_panelStickyContainer[ap], 0);
                    }
                } else {
                    // 1.06.00 CRASH FIX (Dresser/Refrigerator/Symbol/Collecting
                    // with stored items): the v1.05 "reuse Private's chest"
                    // fallback worked because the 1.05 renderer treated the
                    // container at handler+0x170 as a reference object and
                    // pulled items via channel routing. In 1.06 the renderer
                    // reads items directly from the container's per-slot
                    // arrays — feeding it Private's chest with the housing
                    // channel-id bound to sub[1] reads garbage out of bounds
                    // and crashes on the first non-empty slot.
                    //
                    // We now NULL the container (handler+0x170 = 0) when no
                    // per-panel sticky exists. The renderer's NULL guard
                    // shows an empty grid instead of crashing. The trade-off
                    // is that the user must visit each housing chest's NPC
                    // at least once per session — then the sticky observer
                    // saves the real chest container and the upper branch
                    // (sticky-restore) takes over. Same behavior as v1.05
                    // for non-empty chests.
                    // CANONICAL GUARD (CD 1.13.00): handler+0x170 is only the
                    // container slot on builds where it holds a heap pointer.
                    // In 1.13 the handler reorganized and +0x170 now holds a
                    // sub-controller COUNT (small integer); writing 0 there
                    // corrupts the count -> wrong panels render / crash. Only
                    // NULL it when it currently looks like a pointer.
                    __try {
                        uintptr_t curVal = *(uintptr_t*)(handler + 0x170);
                        if (curVal >= 0x10000000000ULL && curVal < 0x7FFFFFFFFFFFULL) {
                            *(uintptr_t*)(handler + 0x170) = 0;
                            Log("  Container bind: %s no per-panel sticky — handler+0x170 cleared "
                                "(visit the chest NPC at least once per session to enable item display)",
                                g_panels[ap].name);
                        } else {
                            Log("  Container bind: %s — +0x170=0x%llX not a pointer (1.13+ layout), NOT cleared",
                                g_panels[ap].name, (unsigned long long)curVal);
                        }
                    } __except(EXCEPTION_EXECUTE_HANDLER) {
                        Log("  Container bind: NULL-out EXCEPTION");
                    }

                }
                }
                }  // close `if (!slotFinalized)`
        }
    }

    // Note: 0x15 (prepare) is now sent earlier in the InitWarehousePanel
    // command sequence (before 0x0E), matching the game's natural-open order
    // captured via Handler trace. Old duplicate 0x15 send removed.

    // 1.05 RE NOTE: Removed HideSubCtrl(+0x2E8) call — that offset holds the
    // tab-selector sub-controller, NOT the donation widget. Hiding it caused the
    // tabs/donation overlap visible in F6 screenshots. The real donation faction
    // byte lives at handler+0x239 (per FUN_14ad777b0); the donation render path
    // is gated by other handler fields, not by this sub-controller.

    // Load inventory items.
    //
    // 1.05.00 ANALYSIS (real SetInventory @ base+0xA7AB30):
    // The function tokenises with TWO delimiters — outer split on
    // DAT_1449e9268 (";"), inner split on DAT_1449e9264 (","). It iterates
    // *(handler + 0x140) sub-controller slots; for each piece it matches
    // token[0] against the Focus-mode strings (PTR_s_Focus_14492c220) and
    // binds the matching sub-controller via FUN_140c11530, writing the
    // channel-id into sub+0x218 and the focus-index into sub+0x248.
    //
    // This is the SAME flow that v1.3.2 used successfully on game 1.0.4.x
    // — a SINGLE call with the full multi-channel string. The earlier
    // "split-on-;" workaround targeted the WRONG function (SetChannels
    // @ base+0xA7B2A0, which has a 3-token-only reload branch); the
    // resolver override above now points g_fnSetInventory at the real
    // worker, so per-chunk splitting is no longer necessary — and is in
    // fact harmful, because each chunk only matches one sub-controller
    // index and leaves the others stale.
    // v1.4.2 unbind+rebind: SetInventory is idempotent on already-bound
    // namespaces (same namespace twice = no refresh). Force a true refresh
    // by sending a ",False" version first, then the real ",True" string.
    // This matches the natural chest-NPC flow: tear down previous binding,
    // then build new one — and is the mechanism that makes housing chests
    // load their own data instead of reusing whatever was bound last.
    // 1.05 RE finding: SetInventory (FUN_140a7ab30) parses tokens by ';' and
    // ',' and per token either subscribes (",True") or unsubscribes (",False")
    // the channel on the matching sub-controller slot. Critically, subscribe
    // does NOT replace prior subscriptions — they accumulate. So when we
    // switch panels, the previous panel's channel must be EXPLICITLY unbound,
    // otherwise the old binding stays active and items from the old chest
    // keep showing under the new panel's title (= the bug user reported).
    if (g_fnSetInventory && initString && *initString) {
        typedef void (__fastcall *PFN_SetInv)(void*, void*);
        auto buildUnbind = [](const char* src, char* dst, size_t dstSize) {
            if (!src || !*src) { dst[0] = 0; return; }
            strncpy(dst, src, dstSize - 1);
            dst[dstSize - 1] = 0;
            for (char* p = dst; *p; p++) {
                if ((p[0] == ',' || p[0] == ';') &&
                    (p[1] == 'T' || p[1] == 't') &&
                    (p[2] == 'R' || p[2] == 'r') &&
                    (p[3] == 'U' || p[3] == 'u') &&
                    (p[4] == 'E' || p[4] == 'e')) {
                    p[1] = 'F'; p[2] = 'a'; p[3] = 'l'; p[4] = 's';
                    size_t len = strlen(p + 5);
                    if (len + 6 < dstSize - (size_t)(p - dst)) {
                        memmove(p + 6, p + 5, len + 1);
                        p[5] = 'e';
                        p += 5;
                    }
                }
            }
        };

        // Append ",Default" (the warehouse's CategoryType attribute, verified
        // as token[0] of the game's category-type table at base+0x4D2A788) to
        // each ';'-separated bind segment. This makes SetInventory take its
        // 4-field branch, which runs the game's own category populate+render
        // pair (FUN_140C485D0 + FUN_140C48AF0) on each sub-widget — exactly
        // what a natural NPC open does via the widget Init FUN_140C3F900. The
        // item binding (channel id +0x218, focus index +0x248, show vtable+0x20)
        // is identical in the 3- and 4-field branches, so this only ADDS the
        // category tab bar and cannot affect item display. Only the BIND (True)
        // string gets the 4th field; unbind (False) stays 3-field — no point
        // populating tabs on a panel being hidden.
        auto buildBind = [](const char* src, char* dst, size_t dstSize) {
            dst[0] = 0;
            if (!src || !*src) return;
            size_t o = 0;
            const char* seg = src;
            while (*seg) {
                const char* semi = strchr(seg, ';');
                int segLen = semi ? (int)(semi - seg) : (int)strlen(seg);
                int n = _snprintf_s(dst + o, dstSize - o, _TRUNCATE, "%.*s,Default%s",
                                    segLen, seg, semi ? ";" : "");
                if (n <= 0) { dst[0] = 0; return; }   // overflow → caller falls back to 3-field
                o += n;
                if (!semi) break;
                seg = semi + 1;
            }
        };
        char bindStr[320] = {};
        buildBind(initString, bindStr, sizeof(bindStr));
        const char* bindArg = bindStr[0] ? bindStr : initString;

        char curUnbind[256] = {};
        buildUnbind(initString, curUnbind, sizeof(curUnbind));

        LONG curBound = InterlockedCompareExchange(&g_currentBoundPanel, 0, 0);
        LONG ap = InterlockedCompareExchange(&g_activePanel, 0, 0);
        if (ap < 0 || ap >= PANEL_COUNT) ap = PANEL_PRIVATE;

        // CHANNEL DIAGNOSTIC: dump sub-controller channel IDs + tab index. The
        // slot-grid renderer (FUN_140A78690 @ base+0xA78690) reads
        // sub[handler+0x1E0]+0x218 to pick which channel feeds items. If
        // sub[1]+0x218 stays at CampWareHouse after a Gatherables rebind, we
        // know thunk_FUN_14f07e700("Housing_*") silently failed and items come
        // from the leftover Camp channel.
        auto dumpChannelState = [handler](const char* tag) {
            __try {
                uint32_t  tabIdx  = *(uint32_t*)(handler + 0x1E0);
                uintptr_t subArr  = *(uintptr_t*)(handler + 0x138);
                uint32_t  subCnt  = *(uint32_t*)(handler + 0x140);
                uintptr_t flagArr = *(uintptr_t*)(handler + 0x158);
                if (subCnt > 16) subCnt = 16;
                char buf[512] = {};
                int  off = 0;
                for (uint32_t i = 0; i < subCnt; i++) {
                    uintptr_t sub = *(uintptr_t*)(subArr + i * 8);
                    short ch = (sub >= 0x10000000000ULL)
                                 ? *(short*)(sub + 0x218) : (short)0;
                    char  fl = (flagArr >= 0x10000000000ULL)
                                 ? *(char*)(flagArr + i) : (char)-1;
                    int n = _snprintf_s(buf + off, sizeof(buf) - off, _TRUNCATE,
                                        "[%u]ch=0x%04hX,fl=%d ", i, ch, (int)fl);
                    if (n <= 0) break;
                    off += n;
                }
                Log("  CHAN %s tab=%u %s", tag, tabIdx, buf);
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  CHAN %s EXCEPTION", tag);
            }
        };
        dumpChannelState("PRE ");

        // Set tab index BEFORE bind so any vfunc-0x20-triggered render sees the
        // correct slot. With a 2-token initString ("Character;ChannelX"),
        // ChannelX always lands in sub[1] — tabIndex=1 makes the renderer pick
        // sub[1]'s channel-id. Private is left at -1 (no write) because F6
        // already works with the game's natural state.
        if (g_panels[ap].tabIndex >= 0) {
            __try {
                uint32_t want = (uint32_t)g_panels[ap].tabIndex;
                uint32_t prev = *(uint32_t*)(handler + 0x1E0);
                // CANONICAL GUARD (CD 1.13.00): +0x1E0 is only the tab index
                // where it currently holds a small value. In 1.13 the handler
                // reorganized and +0x1E0 reads garbage (e.g. 0x5F400010);
                // writing the tab index there corrupts an unrelated field and
                // makes the close-path tab walk chase bad pointers -> crash.
                // Only write when the field already looks like a tab index.
                if (prev < 16) {
                    *(uint32_t*)(handler + 0x1E0) = want;
                    Log("  TabIdx write: handler+0x1E0 %u -> %u (panel=%s)",
                        prev, want, g_panels[ap].name);
                } else {
                    Log("  TabIdx write SKIPPED: handler+0x1E0=0x%X not a tab index (1.13+ layout, panel=%s)",
                        prev, g_panels[ap].name);
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  TabIdx write EXCEPTION");
            }
        }

        // Step 1: unbind the previously bound panel (if different from current).
        if (curBound >= 0 && curBound < PANEL_COUNT && curBound != ap) {
            char prevUnbind[256] = {};
            buildUnbind(g_panels[curBound].initString, prevUnbind, sizeof(prevUnbind));
            if (prevUnbind[0]) {
                __try {
                    ((PFN_SetInv)g_fnSetInventory)((void*)handler, (void*)prevUnbind);
                    Log("  SetInventory unbind PREV (%s, \"%s\")",
                        g_panels[curBound].name, prevUnbind);
                } __except(EXCEPTION_EXECUTE_HANDLER) {
                    Log("  SetInventory unbind PREV EXCEPTION");
                }
            }
        }

        // Step 2: standard unbind+rebind of the current panel (forces refresh).
        // 1.06.00: SetInventory IS needed — without it the panel renders the
        // previous NPC's inventory layout (donation widget, wrong slot count,
        // wrong tabs). The earlier crash was likely caused by the Grid cache
        // invalidate (handler+0x178->+0x568 = -1), not SetInventory. Grid
        // invalidate is now skipped for Private; SetInventory re-enabled.
        __try {
            if (curUnbind[0]) {
                ((PFN_SetInv)g_fnSetInventory)((void*)handler, (void*)curUnbind);
                Log("  SetInventory unbind CUR  (\"%s\")", curUnbind);
            }
            ((PFN_SetInv)g_fnSetInventory)((void*)handler, (void*)bindArg);
            Log("  SetInventory bind   CUR  (\"%s\")", bindArg);
            InterlockedExchange(&g_currentBoundPanel, ap);
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  SetInventory EXCEPTION (string=\"%s\")", initString);
        }

        dumpChannelState("POST");

        // Force-refresh: in 1.4.2 SetInventory subscribe alone refreshed the
        // grid. In 1.05.0 the grid render-state caches the previous panel's
        // items and SetInventory doesn't push new content. FUN_140A754E0
        // (= base+0xA754E0, "WarehouseRefresh") is the canonical
        // force-refresh: writes handler+0x170 from validated chest, calls
        // FUN_140A78690 (slot grid rebuild). If +0x2A5 (construction-success
        // flag) is 1 it also runs FUN_140A75F40 + FUN_140B8FB70 (full UI
        // rebuild). Guarded: we skip when +0x2A5=0 to avoid the NULL-children
        // crash a prior iteration hit.
        // RE-confirmed call signature for FUN_140A754E0:
        //   FUN_140A73920 calls it as FUN_140A754E0(handler, param_4)
        //   where param_4 is then walked via:
        //     param_4 -> +0xA8 -> +0x8  (or +0x140, or +0xA8+0x50 + walker)
        //   to reach the chest object (vtable check via DAT_145E215B0).
        //
        // The chest at handler+0x170 is what the WALKER FINDS — passing it as
        // param_2 makes the walk return NULL and crash on the vtable call.
        //
        // FUN_140A7AB30 (SetInventory) shows where the walker object lives
        // for a given sub-controller:
        //   walker = *(*(*(handler+0x138) + i*8) + 8) + 0x60
        //          = sub[i] -> +0x8 -> deref -> +0x60 -> deref
        // So the walker is one level above the chest, attached to each
        // sub-controller's outer scope.
        // Diagnostic probe: log the chest pointer at handler+0x170 plus the
        // walker pointer derived from the sub-controller chain.  Useful when
        // troubleshooting wrong-container symptoms.  The actual force-refresh
        // call this used to gate is permanently disabled — its contract
        // changed in 1.06 and the natural SetInventory rebind handles refresh
        // anyway.
        {
            uint8_t  a5    = 0;
            uintptr_t chest = 0;
            uintptr_t walker = 0;
            __try {
                a5    = *(uint8_t*)(handler + 0x2A5);
                chest = *(uintptr_t*)(handler + 0x170);
                uint32_t  tabIdx = *(uint32_t*)(handler + 0x1E0);
                uintptr_t subArr = *(uintptr_t*)(handler + 0x138);
                if (subArr >= 0x10000000000ULL) {
                    uintptr_t sub = *(uintptr_t*)(subArr + tabIdx * 8);
                    if (sub >= 0x10000000000ULL) {
                        uintptr_t scope = *(uintptr_t*)(sub + 0x8);
                        if (scope >= 0x10000000000ULL) {
                            walker = *(uintptr_t*)(scope + 0x60);
                        }
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
            Log("  Refresh probe: +0x2A5=0x%02X chest=0x%llX walker=0x%llX",
                a5, (unsigned long long)chest, (unsigned long long)walker);
        }
    }

    // v1.4.2 approach: NO explicit BindRefresh call. The SetInventory
    // unbind+rebind above + the game's own sub-controller "prepare" hooks
    // (triggered by the empty 0x15 packet) drive the actual data refresh.
    // Earlier 1.05.00 attempts to call FUN_140a754e0 directly turned out to
    // be the source of the cross-panel container leak (Step-3 iteration
    // resolved Private's sub for housing panels). Removed.
    // Fix bottom inventory label + top title
    if (g_fnSetTitle) {
        typedef uint8_t (__fastcall *PFN_SetTitle)(uintptr_t, const char*);
        PFN_SetTitle setTitle = (PFN_SetTitle)g_fnSetTitle;
        const char* title = GetWarehouseTitle();
        bool needUtf8Fix = !IsAscii(title);
        {
            LONG ap = InterlockedCompareExchange(&g_activePanel, 0, 0);
            if (ap < 0 || ap >= PANEL_COUNT) ap = PANEL_PRIVATE;
            Log("  Title selected: \"%s\" (active=%s)", title, g_panels[ap].name);
        }

        __try {
            uintptr_t bottomLabel = *(uintptr_t*)(handler + g_offBottomLabel);
            if (bottomLabel > 0x10000 && bottomLabel < 0x7FFFFFFFFFFF) {
                setTitle(bottomLabel, title);
                Log("  Bottom label (+0x%X) set: lang=%d needFix=%d",
                    g_offBottomLabel, GetGameLanguage(), needUtf8Fix);
                if (needUtf8Fix) {
                    bool fixed = SetTitleOnRenderer(bottomLabel, title, 0);
                    Log("  Bottom label UTF-8 fix: %s", fixed ? "OK" : "no renderer found");
                }
            } else {
                Log("  Bottom label (+0x%X) invalid pointer", g_offBottomLabel);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Bottom label (+0x%X) EXCEPTION", g_offBottomLabel);
        }

        __try {
            uintptr_t topNode = g_offTopTitle ? *(uintptr_t*)(handler + g_offTopTitle) : 0;
            if (topNode > 0x10000 && topNode < 0x7FFFFFFFFFFF) {
                uint8_t ret = setTitle(topNode, title);
                Log("  Top title (+0x%X) set: lang=%d ret=%u",
                    g_offTopTitle, GetGameLanguage(), (unsigned)ret);
                if (needUtf8Fix) {
                    bool fixed = SetTitleOnRenderer(topNode, title, 0);
                    Log("  Top title UTF-8 fix: %s", fixed ? "OK" : "no renderer found");
                }
            } else if (!g_offTopTitle) {
                Log("  Top title: no offset resolved this build — skipped");
            } else {
                // 1.08: handler+0xE8 is only populated AFTER the player has
                // visited a real warehouse NPC at least once this session
                // (the panel's NpcInteractionTitle widget is initialised
                // lazily via the natural NPC-open path).  Until then, the
                // top title shows the static HTML default ("Camp Provision"
                // / UI_WareHouse_Title localstring) and our override is
                // skipped silently — that's expected.
                Log("  Top title (+0x%X) not yet populated — visit any warehouse NPC once to enable per-panel override", g_offTopTitle);
            }
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("  Top title (+0x%X) EXCEPTION", g_offTopTitle);
        }
    }

    // Filter sub-controller: probe-only (see ProbeFilterSubController for
    // why nothing is rendered here). The slot at +0x1A8 is a year/month
    // date selector, not the category tab bar, and its render cannot run
    // safely on a remote open. Logged for diagnostics only.
    {
        uintptr_t f1 = 0, f2 = 0;
        __try { f1 = *(uintptr_t*)(handler + 0x1A8); } __except(EXCEPTION_EXECUTE_HANDLER) {}
        __try { f2 = *(uintptr_t*)(handler + 0x1C0); } __except(EXCEPTION_EXECUTE_HANDLER) {}
        ProbeFilterSubController(f1, "+0x1A8");
        if (f2 && f2 != f1) ProbeFilterSubController(f2, "+0x1C0");
    }

    // REVERTED 2026-06-07: the vtable[51] (FUN_140A9F4E0) ShowAndRegister
    // call was a 1.10-era addition that depended on Init having populated
    // +0x218/+0x2CD — which it never does on the captured shell. With the
    // cmd-sequence revert above, we go back to the v1.5.1 model where the
    // game's per-frame CanShow polling drives the open: our HookedCanShow
    // returns 1 while warehouseActive is set, and the game renders the
    // panel naturally. No explicit register-for-render call.

    LogModalState("  InitWarehousePanel done");
}

// ============================================================
//  F6 / Controller: Toggle Warehouse
// ============================================================
// ClearActivePanelState: hides a warehouse panel by replicating the game's 0x0f dispatcher
// logic without its unsafe scene-object lookup. Used by the F6-close path AND by the
// Switch-Key path — the latter reuses it to hide the current panel before re-initializing
// the other one. Does NOT touch mode bytes / g_warehouseActive — caller decides.
static void ClearActivePanelState(uintptr_t handler) {
    if (!handler) return;
    LONG ap = InterlockedCompareExchange(&g_activePanel, 0, 0);
    const char* apName = (ap >= 0 && ap < PANEL_COUNT) ? g_panels[ap].name : "?";
    __try {
        // Active-flag clear at g_offActiveFlag (=0x128 in 1.08) — dynamic, safe.
        *(uint8_t*)(handler + g_offActiveFlag) = 0;
        // PanelValue restore from saved original at +0x110. If we captured an
        // original value during the open, restore it; otherwise leave as-is
        // (writing 0 would corrupt 1.08 layout where +0x110 may host a non-
        // scalar field).
        {
            LONG64 saved = InterlockedCompareExchange64(&g_savedPanelValueSlot, 0, 0);
            if (saved != -1 && g_panelValueSlotValid) {
                *(uint64_t*)(handler + g_offPanelValue) = (uint64_t)saved;
            }
        }
        // Part 3: try to clear the scene-object render bit (equivalent to the
        // `*(uint8_t*)(scene+0x26A) &= 0xFE` step in 0x0f). Wrapped separately
        // so a missing scene object doesn't abort the clear.
        //
        // Diagnostic: log the addresses walked at each step so a failed
        // close on Gatherables/Refrigerator/etc. can be traced back to
        // exactly which pointer in the chain went null.
        bool sceneBitCleared = false;
        uintptr_t subObj = 0, a8 = 0, scene = 0;
        // BISECT: scene+0x26A render-bit clear also disabled for 1.08 diagnosis.
        // __try {
        //     subObj = *(uintptr_t*)(handler + 0x8);
        //     if (subObj) {
        //         a8 = *(uintptr_t*)(subObj + 0xA8);
        //         if (a8) {
        //             scene = *(uintptr_t*)(a8 + 0x10);
        //             if (scene) {
        //                 *(uint8_t*)(scene + 0x26A) &= 0xFE;
        //                 sceneBitCleared = true;
        //             }
        //         }
        //     }
        // } __except(EXCEPTION_EXECUTE_HANDLER) {}
        Log("  Panel [%s] hidden (direct state clear, scene bit %s) — subObj=0x%llX a8=0x%llX scene=0x%llX",
            apName,
            sceneBitCleared ? "cleared" : "skipped",
            (unsigned long long)subObj,
            (unsigned long long)a8,
            (unsigned long long)scene);

        // For housing chests (panel index != 0) the active sub-controller
        // lives at handler+0x138[handler+0x1E0], NOT at handler+0x8. The
        // Camp panel's sub at +0x8 has a different scene than the housing
        // sub, so clearing the Camp scene bit doesn't hide the housing
        // panel. Walk the active-tab chain and clear that scene bit too.
        if (ap != PANEL_PRIVATE) {
            __try {
                // CANONICAL-POINTER GUARD (added for CD 1.13.00): the handler
                // struct reorganized — the sub-controller array moved off
                // +0x138 and +0x1E0/+0x170 changed meaning. With a wrong
                // subArr this walk chased garbage-but-mapped pointers and the
                // final `*(tabScn+0x26A) &= 0xFE` corrupted live game memory
                // (no AV → SEH didn't catch it) → crash on the next frame.
                // Every hop is now validated to be a canonical user-space
                // heap pointer; a wrong offset makes the walk skip cleanly.
                auto canon = [](uintptr_t p){ return p >= 0x10000000000ULL && p < 0x7FFFFFFFFFFFULL; };
                uint32_t  tabIdx  = *(uint32_t*)(handler + 0x1E0);
                uintptr_t subArr  = *(uintptr_t*)(handler + 0x138);
                if (canon(subArr) && tabIdx < 16) {
                    uintptr_t tabSub  = *(uintptr_t*)(subArr + tabIdx * 8);
                    uintptr_t tabA8   = canon(tabSub) ? *(uintptr_t*)(tabSub + 0xA8) : 0;
                    uintptr_t tabScn  = canon(tabA8)  ? *(uintptr_t*)(tabA8  + 0x10) : 0;
                    if (canon(tabScn)) {
                        *(uint8_t*)(tabScn + 0x26A) &= 0xFE;
                        Log("  Panel [%s] tab-sub scene bit cleared — tabIdx=%u tabSub=0x%llX tabA8=0x%llX tabScn=0x%llX",
                            apName, tabIdx,
                            (unsigned long long)tabSub,
                            (unsigned long long)tabA8,
                            (unsigned long long)tabScn);
                    } else {
                        Log("  Panel [%s] tab-sub scene-bit walk: tabIdx=%u tabSub=0x%llX tabA8=0x%llX tabScn=0",
                            apName, tabIdx,
                            (unsigned long long)tabSub,
                            (unsigned long long)tabA8);
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {
                Log("  Panel [%s] tab-sub scene-bit walk EXCEPTION", apName);
            }
        }
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  Panel [%s] hide direct cleanup EXCEPTION", apName);
    }
}

// triggerKind: 0 = open, 1 = close (modal-aware, used by F-keys),
//              2 = force close (skip modal block — used by controller B/Circle
//              and per-panel buttons; the modal check at +0x258 can return
//              true on stale pointers from previous housing-chest sessions
//              and would otherwise block the close indefinitely).
static void TriggerWarehouse(int triggerKind = 0) {
    bool forceClose = (triggerKind == 2);
    uintptr_t mainChar = (uintptr_t)InterlockedCompareExchange64(&g_mainChar, 0, 0);
    if (!mainChar) { Log("NOT READY: mainChar"); return; }

    uint8_t* mc = (uint8_t*)mainChar;

    if (!InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
        // Re-open cooldown: when DualSense is mapped through Steam Input,
        // pressing Circle fires both the HID-Circle path AND the XInput-B
        // path. Each path posts its own WM_TRIGGER_WAREHOUSE, so the close
        // is followed by a second toggle that would re-open instantly.
        // Block any open request within 250ms of a close to absorb that
        // second message (and any other near-simultaneous controller
        // duplication).
        ULONGLONG now = GetTickCount64();
        ULONGLONG closedAt = g_closeTimestamp;
        if (closedAt && now - closedAt < 250) {
            Log("BLOCKED: re-open within %llu ms of close (cooldown)",
                (unsigned long long)(now - closedAt));
            return;
        }

        uint8_t curMode = mc[g_offModeByte];
        uint8_t curSub  = mc[g_offSubByte];
        // 1.08 game-state enum (verified via Ghidra decompile of the debug
        // state-name builder FUN_1406F1180):
        //
        // mode (mainChar+0xCA8):
        //   0=loading, 1=title, 2=characterselect, 3=gamedataloading,
        //   4=ingame-global, 5=logout, 6=clientgameplaytemp
        //
        // sub (mainChar+0xCA9) — only meaningful when mode==4 (ingame):
        //   4=photomode  5=dialog/store  6=cinema/cutscene
        //   7=minigame/qte  8/9/A=dialog/minigame/interaction
        //   B=gimmick  C=worldobserver
        //   D=mainmenu (inventory/map/quest journal overlay)
        //   E=ingamemenu (full pause menu)
        //   F=hud-info+hud-play+quickslot       (regular gameplay — SAFE)
        //   10=hud-info+hud-play+interaction    (NPC dialog approach — SAFE)
        //   0x11+ undefined in 1.08 (the old 1.06 "transient" assumption was
        //                            wrong; removed from the whitelist).
        //
        // Both bytes must be checked. Earlier mod versions only checked sub,
        // which let the loading screen through (mode=0 but sub still holds
        // a stale 0x0F from the previous gameplay frame).
        bool inGameplay = (curMode == 4) && (curSub == 0x0F || curSub == 0x10);
        if (!inGameplay) {
            Log("BLOCKED: unsafe state (mode=0x%02X sub=0x%02X)", curMode, curSub);
            return;
        }

        LONG targetPanel = InterlockedExchange(&g_nextOpenPanel, PANEL_PRIVATE);
        {
            LONG tp = targetPanel;
            if (tp < 0 || tp >= PANEL_COUNT) tp = PANEL_PRIVATE;
            Log("=== OPENING WAREHOUSE (%s) ===", g_panels[tp].name);
        }
        // Bump diagnostic epoch so HookedCanShow's per-press loggers reset.
        InterlockedIncrement(&g_diagEpoch);
        InterlockedExchange(&g_activePanel, targetPanel);
        SafeSetupModeForWarehouse(mc);

        InterlockedExchange(&g_canShowSeen118, 0);
        InterlockedExchange(&g_canShowZeroCount, 0);
        InterlockedExchange64(&g_lastModalPassed, 0);
        InterlockedExchange(&g_warehouseActive, 1);
        g_openTimestamp = GetTickCount64();

        InterlockedExchange(&g_modeSwitchByMod, 1);

        // Try to initialize the panel immediately if handler is already captured.
        // On first F6 after loading a save, the handler is typically NULL here because
        // auto-capture happens in HookedCanShow which runs on the same (game) thread.
        // A blocking Sleep loop would prevent the game from processing frames and
        // calling CanShow, so the handler would never be captured.
        // Instead, we defer initialization via WM_INIT_WAREHOUSE — the game gets to
        // process a frame, CanShow fires, the handler is captured, and our deferred
        // message picks it up.
        // CD 1.10: ALWAYS defer InitWarehousePanel (even when handler is
        // captured) so the game gets at least one tick to react to the
        // sub=6 mode change above. Without that delay, cmd 0x0E and Show
        // run before the panel-manager has rebuilt its mount list — and
        // the renderer ignores the warehouse because WareHouseView2 isn't
        // mounted yet (uigameconfig2.xml tag2="store" needs sub=6).
        InterlockedExchange(&g_initRetryCount, 0);
        InterlockedExchange(&g_initPending, 1);
        Log("  Init deferred 1+ frame so game can react to sub=6");

        // CD 1.10: trigger the view-mount NOW, independent of handler capture.
        // The mount works purely on the global menu-manager (not the warehouse
        // controller), so it must run even when the controller hasn't been
        // captured yet this session (cold F-key open with no prior world-object
        // open). InitWarehousePanel calls it again once the handler is captured;
        // the helper is idempotent (skips if already in the open state).
        if (!TriggerWarehouseViewMount()) {
            // Menu-layer still flagged open (+0x105E==1): a game menu
            // session's close is still in flight (fast re-open after shop /
            // cooking / bank). Proceeding would create a ghost session — the
            // warehouse can't take over the layer, but g_warehouseActive=1
            // would make HookedCanShow suppress every other panel. Roll back
            // cleanly; the user can simply press the hotkey again.
            Log("  OPEN ABORTED: menu-layer busy — rolled back (press hotkey again)");
            InterlockedExchange(&g_initPending, 0);
            InterlockedExchange(&g_warehouseActive, 0);
            InterlockedExchange(&g_modeSwitchByMod, 0);
            SafeRestoreMode(mc);
            InterlockedExchange(&g_activePanel, PANEL_PRIVATE);
            return;
        }

        Log("  Warehouse opened (mode=0x%02X sub=0x%02X)", mc[g_offModeByte], mc[g_offSubByte]);

    } else {
        // Block close while modal dialog is active — but only for non-forced
        // closes (F6/F7/etc). Controller closes always proceed because the
        // +0x258 modal pointer can hold stale data on housing chests, which
        // previously caused B and per-panel-combo presses to be silently
        // dropped on Gatherables/Dresser/Refrigerator/Symbol/Collecting.
        if (!forceClose && IsNewModalDialogVisible()) {
            uintptr_t h2 = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
            uintptr_t mv2 = h2 ? ReadModalDialog(h2) : 0;
            uint32_t cc2 = 0;
            if (mv2 > 0x10000 && mv2 < 0x7FFFFFFFFFFF) {
                __try { cc2 = *(uint32_t*)(mv2 + 0x30); } __except(EXCEPTION_EXECUTE_HANDLER) {}
            }
            Log("CLOSE BLOCKED: modal dialog still active (mv=0x%llX childCount=0x%X)",
                (unsigned long long)mv2, cc2);
            return;
        }
        Log("=== CLOSING WAREHOUSE ===");
        InterlockedExchange(&g_warehouseActive, 0);
        InterlockedExchange(&g_initPending, 0);
        // Clear any in-flight controller pending-close flags so a stray
        // release after this close doesn't trigger an immediate re-open.
        InterlockedExchange(&g_pendingBClose, 0);
        InterlockedExchange(&g_pendingCircleClose, 0);
        // Stamp close time for the re-open cooldown (see open branch).
        g_closeTimestamp = GetTickCount64();

        // Restore Camp handler state if a housing panel was active. The housing
        // open path patches handler+0x1D8/+0x200/+0x2A8/+0x39C — leaving them
        // dirty after close confuses subsequent F7 toggles (close-trigger fires
        // but the dirty state suppresses the visible close). Always undo here.
        {
            uintptr_t h = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
            if (h && InterlockedCompareExchange(&g_campValuesSaved, 0, 0)) {
                __try {
                    *(uint32_t*)(h + 0x1D8) = (uint32_t)InterlockedCompareExchange(&g_savedCamp_84, 0, 0);
                    *(uint8_t* )(h + 0x200) = (uint8_t )InterlockedCompareExchange(&g_savedCamp_B8, 0, 0);
                    *(uint32_t*)(h + 0x2A8) = (uint32_t)InterlockedCompareExchange(&g_savedCamp_9C, 0, 0);
                    *(uint32_t*)(h + 0x39C) = (uint32_t)InterlockedCompareExchange(&g_savedCamp_39C, 0, 0);
                    InterlockedExchange(&g_campValuesSaved, 0);
                    Log("  Restored Camp handler state on close");
                } __except(EXCEPTION_EXECUTE_HANDLER) {
                    Log("  Restore on close EXCEPTION");
                }
            }
        }

        // Close only the currently-active panel. The other slot (if captured) keeps its
        // pointer for the next session — its +0x118 flag is already 0 because CanShow
        // suppressed it while inactive. See ClearActivePanelState for the 0x0f-replay logic.
        ClearActivePanelState((uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0));

        // Hand the menu-layer back to the game BEFORE restoring the mode
        // bytes — mirrors the natural close order (close-init runs while
        // still in store mode, mode cleanup follows). Without this, +0x105E
        // stays 1 and every later vendor/provisions/bank/dispatch menu open
        // is silently swallowed (see TriggerWarehouseViewUnmount).
        TriggerWarehouseViewUnmount();

        SafeRestoreMode(mc);

        // QOL: Hide cursor immediately when closing warehouse
        if (g_fnSetCursorVisible) {
            uintptr_t cursor = (uintptr_t)InterlockedCompareExchange64(&g_cursorObj, 0, 0);
            if (cursor) {
                __try {
                    typedef void (__fastcall *PFN_SetCursorVisible)(void*, char, char);
                    ((PFN_SetCursorVisible)g_fnSetCursorVisible)((void*)cursor, 0, 1);
                    Log("  Cursor hidden via SetCursorVisible");
                } __except(EXCEPTION_EXECUTE_HANDLER) {}
            }
        }

        InterlockedExchange(&g_modeSwitchByMod, 0);
        // Reset to Private so the next F6 opens Private (not whichever panel was last active).
        InterlockedExchange(&g_activePanel, PANEL_PRIVATE);
        // NOTE: do NOT reset g_currentBoundPanel here. SetInventory subscribes
        // accumulate on the sub-controllers (sub+0x218 = channelId) until an
        // explicit ",False" unsub is sent for that exact channel. We need to
        // remember which panel's channels are currently subscribed so the next
        // open can unbind them via the "unbind PREV" path. Resetting to -1
        // skips that unbind and leaves the previous panel's channels active —
        // which is why F7+ after F6-Private kept showing Private's items.

        Log("  Warehouse closed (mode=0x%02X sub=0x%02X)", mc[g_offModeByte], mc[g_offSubByte]);

        // Release mod-ownership of all per-panel stickies. After close, the
        // observer is allowed to re-attribute containers it sees at +0x170
        // (e.g. from a real NPC visit later in the session).
        for (int i = 0; i < PANEL_COUNT; i++) {
            InterlockedExchange(&g_panelStickyOwnedByMod[i], 0);
        }

        // Modal popup state belongs to the closed warehouse — clear so a
        // stuck flag doesn't survive into the next session.
        InterlockedExchange(&g_itemDetailActiveCount, 0);

        // Force-close fallback for housing chests: ClearActivePanelState
        // works for Private (Camp panel) but doesn't always visually close
        // Gatherables / Refrigerator / Dresser / Symbol / Collecting. The
        // game's native ESC handler does additional sub-state cleanup we
        // can't replicate. Send a synthetic VK_ESCAPE through the original
        // WndProc so the game performs that cleanup. Safe here because:
        //   - we're already on the game thread (PostMessage dispatched us)
        //   - warehouseActive is already 0 → CanShow no longer force-shows
        //   - g_closeTimestamp is set → re-open cooldown blocks any
        //     accidental re-trigger from a controller path that races
        //   - g_originalWndProc bypasses our own hook so we don't recurse
        if (forceClose && g_originalWndProc && g_gameWindow) {
            __try {
                CallWindowProcA(g_originalWndProc, g_gameWindow,
                                WM_KEYDOWN, VK_ESCAPE, 0x00010001);
                CallWindowProcA(g_originalWndProc, g_gameWindow,
                                WM_KEYUP,   VK_ESCAPE, 0xC0010001);
            } __except(EXCEPTION_EXECUTE_HANDLER) {}
        }
    }
}

// ============================================================
//  Memory-Diff: capture handler-object snapshots before/after a regular chest-open
//  at the NPC, log which fields changed. Used to identify the container-bind writes
//  that the VM-protected dispatcher performs (since static decompilation is blocked).
// ============================================================
// Helper: log diff between two byte buffers, prefixing offset with the given label.
static void LogDiffRegion(const char* label, const uint8_t* before, const uint8_t* after, int size) {
    int totalChanged = 0;
    int runs = 0;
    for (int i = 0; i < size; ) {
        if (before[i] != after[i]) {
            int start = i;
            while (i < size && before[i] != after[i]) i++;
            int len = i - start;
            totalChanged += len;
            runs++;
            if (len == 1) {
                Log("  %s+0x%03X: u8  0x%02X -> 0x%02X",
                    label, start, before[start], after[start]);
            } else if (len == 2 && (start & 1) == 0) {
                Log("  %s+0x%03X: u16 0x%04X -> 0x%04X",
                    label, start, *(uint16_t*)&before[start], *(uint16_t*)&after[start]);
            } else if (len == 4 && (start & 3) == 0) {
                Log("  %s+0x%03X: u32 0x%08X -> 0x%08X",
                    label, start, *(uint32_t*)&before[start], *(uint32_t*)&after[start]);
            } else if (len == 8 && (start & 7) == 0) {
                Log("  %s+0x%03X: u64 0x%016llX -> 0x%016llX",
                    label, start,
                    (unsigned long long)*(uint64_t*)&before[start],
                    (unsigned long long)*(uint64_t*)&after[start]);
            } else {
                Log("  %s+0x%03X: run of %d bytes changed:", label, start, len);
                for (int j = 0; j < len; j++) {
                    Log("    %s+0x%03X: 0x%02X -> 0x%02X",
                        label, start + j, before[start + j], after[start + j]);
                }
            }
        } else {
            i++;
        }
    }
    Log("  %s total %d bytes changed in %d runs", label, totalChanged, runs);
}

// LookupInventoryTypeId: walk the global Inventory-Type hash-map (DAT_145f0da18)
// to resolve a 16-bit panel-ID for a given type-info pointer. Replicates the per-slot
// lookup logic from FUN_1415c1ae0 (which does this for all registered namespaces).
// Returns the resolved panel-ID, or 0xFFFF on failure.
//
// Layout of the hash-map at g_pInvTypeMap (offsets observed in FUN_1415c1ae0):
//   +0x60: u32 bucket count
//   +0x64: u32 total count (0 = empty)
//   +0x70: u8** buckets (each bucket is 0x100 bytes; first u32 = key count)
//   +0x78: u8** entries array (entry size = 8, target struct has hash@+4 and id@+6)
//
// The hash key for the lookup is the 16-bit truncation of the value at the type-info
// hash slot (e.g. *DAT_145e8f768 for Housing_GatheredMaterials).

// ResolveContainerForPanelId: walk sub->0x50->0xb0->0xd8 to get the global container
// array, then index it by panelId. Returns the container pointer at that slot,
// or 0 on failure / out-of-range.
static uintptr_t ResolveContainerForPanelId(uintptr_t handler, uint16_t panelId) {
    if (!handler) return 0;
    __try {
        uintptr_t sub = *(uintptr_t*)(handler + 0x8);
        if (!sub) return 0;
        uintptr_t lvl1 = *(uintptr_t*)(sub + 0x50);
        if (!lvl1) return 0;
        uintptr_t lvl2 = *(uintptr_t*)(lvl1 + 0xb0);
        if (!lvl2) return 0;
        uintptr_t arrStruct = *(uintptr_t*)(lvl2 + 0xd8);
        if (!arrStruct) return 0;
        uintptr_t arrPtr = *(uintptr_t*)arrStruct;
        uint32_t arrCnt = *(uint32_t*)(arrStruct + 8);
        if (!arrPtr || (uint32_t)panelId >= arrCnt) return 0;
        return *(uintptr_t*)(arrPtr + (uintptr_t)panelId * 8);
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        return 0;
    }
}

// LookupInventoryTypeId: call the game's own type-name → 16-bit ID resolver.
// pStringSlot is the address of an 8-byte slot that holds a pointer to the canonical
// game string (e.g. "Housing_GatheredMaterials" stored by the namespace setup function).
static uint16_t LookupInventoryTypeId(uintptr_t pStringSlot) {
    if (!pStringSlot || !g_fnTypeNameLookup) {
        Log("  Lookup: pStringSlot=0x%llX fn=0x%llX",
            (unsigned long long)pStringSlot, (unsigned long long)g_fnTypeNameLookup);
        return 0xFFFF;
    }
    __try {
        // FUN_1402ffe80 returns a pointer to a String-wrapper struct: { char* data; ... }
        // So pStringSlot → wrapper-ptr → wrapper[0] → actual string.
        char** wrapper = *(char***)pStringSlot;
        if (!wrapper) {
            Log("  Lookup: wrapper pointer is NULL — setup not yet run?");
            return 0xFFFF;
        }
        char* str = wrapper[0];
        if (!str) {
            Log("  Lookup: string pointer (wrapper[0]) is NULL");
            return 0xFFFF;
        }
        char preview[40] = {};
        for (int i = 0; i < 39 && str[i]; i++) preview[i] = str[i];
        Log("  Lookup: calling resolver with str=\"%s\"", preview);

        short outId = (short)0xFF;  // sentinel
        typedef int (__fastcall *PFN_Resolver)(char*, short*);
        int rc = ((PFN_Resolver)g_fnTypeNameLookup)(str, &outId);
        Log("  Lookup: resolver returned rc=%d, outId=0x%04X", rc, (unsigned)(uint16_t)outId);

        if (rc == 0 || outId == (short)0xFF) return 0xFFFF;
        return (uint16_t)outId;
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  Lookup: EXCEPTION");
        return 0xFFFF;
    }
}

// Resolve the cached Gatherables panel-ID via the Inventory-Type hash-map lookup.
// Idempotent — caches the result; returns 0xFFFF on failure.
static uint16_t GetGatherablesPanelId() {
    LONG cached = InterlockedCompareExchange(&g_resolvedGatherablesId, 0, 0);
    if (cached > 0) return (uint16_t)cached;
    if (cached < 0) return 0xFFFF;  // previous lookup failed, don't retry

    uint16_t id = LookupInventoryTypeId(g_pHGMStringSlot);
    if (id == 0xFFFF || id == 0) {
        InterlockedExchange(&g_resolvedGatherablesId, -1);
        Log("Gatherables panel-id lookup FAILED (hash-map not yet populated?)");
        return 0xFFFF;
    }
    InterlockedExchange(&g_resolvedGatherablesId, (LONG)id);
    Log("Gatherables panel-id resolved via hash-map: 0x%04X", id);
    return id;
}

// Per-panel resolved type-id cache. Filled lazily on first lookup. 0 = not
// yet resolved, -1 = resolution failed (don't retry every open).
static volatile LONG g_resolvedPanelId[PANEL_COUNT] = {};

// Extract the second token of a panel's InitString — that's the namespace
// name the game's hash-map maps to a 2-byte type-id (e.g. "Housing_Dresser"
// from "Character,Focus,True;Housing_Dresser,Focus,True"). Writes up to
// dstSize-1 chars + NUL into dst. Returns false if the string can't be parsed.
static bool ExtractPanelNamespace(const char* initString, char* dst, size_t dstSize) {
    if (!initString || !dst || dstSize < 2) return false;
    // Skip the first token ("Character,Focus,True") up to the first ';'.
    const char* p = strchr(initString, ';');
    if (!p) return false;
    p++;
    // Copy until ',' or end-of-string.
    size_t i = 0;
    while (*p && *p != ',' && i + 1 < dstSize) dst[i++] = *p++;
    dst[i] = '\0';
    return i > 0;
}

// Resolve a panel's type-id by feeding the namespace string from its
// InitString into the same resolver used for Gatherables. Idempotent —
// caches per-panel; returns 0xFFFF on failure.
static uint16_t GetPanelTypeId(int panelIdx) {
    if (panelIdx < 0 || panelIdx >= PANEL_COUNT) return 0xFFFF;
    if (panelIdx == PANEL_GATHERABLES) return GetGatherablesPanelId();

    LONG cached = InterlockedCompareExchange(&g_resolvedPanelId[panelIdx], 0, 0);
    if (cached > 0) return (uint16_t)cached;
    if (cached < 0) return 0xFFFF;

    if (!g_fnTypeNameLookup) return 0xFFFF;

    char ns[64] = {};
    if (!ExtractPanelNamespace(g_panels[panelIdx].initString, ns, sizeof(ns))) {
        Log("  Lookup: can't extract namespace from InitString for panel %s",
            g_panels[panelIdx].name);
        InterlockedExchange(&g_resolvedPanelId[panelIdx], -1);
        return 0xFFFF;
    }

    __try {
        Log("  Lookup: calling resolver with str=\"%s\" (panel %s)",
            ns, g_panels[panelIdx].name);
        short outId = (short)0xFF;
        typedef int (__fastcall *PFN_Resolver)(char*, short*);
        int rc = ((PFN_Resolver)g_fnTypeNameLookup)(ns, &outId);
        Log("  Lookup: resolver returned rc=%d, outId=0x%04X", rc, (unsigned)(uint16_t)outId);
        if (rc == 0 || outId == (short)0xFF) {
            InterlockedExchange(&g_resolvedPanelId[panelIdx], -1);
            Log("Panel %s type-id lookup FAILED", g_panels[panelIdx].name);
            return 0xFFFF;
        }
        InterlockedExchange(&g_resolvedPanelId[panelIdx], (LONG)(uint16_t)outId);
        Log("Panel %s type-id resolved: 0x%04X", g_panels[panelIdx].name, (uint16_t)outId);
        return (uint16_t)outId;
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  Lookup: EXCEPTION for panel %s", g_panels[panelIdx].name);
        InterlockedExchange(&g_resolvedPanelId[panelIdx], -1);
        return 0xFFFF;
    }
}

static void WalkAndLogChain(uintptr_t handler, const char* label) {
    __try {
        uintptr_t sub = *(uintptr_t*)(handler + 0x8);
        Log("  [%s] handler=0x%llX sub=0x%llX", label,
            (unsigned long long)handler, (unsigned long long)sub);
        if (!sub) { Log("  [%s] sub is NULL", label); return; }

        uintptr_t cur = sub;
        int hops = 0;
        while (hops < 8) {
            uintptr_t a8 = *(uintptr_t*)(cur + 0xa8);
            uintptr_t a8_p8 = a8 ? *(uintptr_t*)(a8 + 0x8) : 0;
            uint16_t pid = *(uint16_t*)(cur + 0x92);
            Log("  [%s] hop=%d cur=0x%llX panelId=0x%04X sub+0xa8=0x%llX sub+0xa8+8=0x%llX",
                label, hops, (unsigned long long)cur, pid,
                (unsigned long long)a8, (unsigned long long)a8_p8);
            if (a8 == 0 || a8_p8 == 0) {
                // Terminal — do container lookup
                uintptr_t lvl1 = *(uintptr_t*)(cur + 0x50);
                if (!lvl1) { Log("  [%s] terminal: cur+0x50 is NULL", label); return; }
                uintptr_t lvl2 = *(uintptr_t*)(lvl1 + 0xb0);
                if (!lvl2) { Log("  [%s] terminal: cur+0x50+0xb0 is NULL", label); return; }
                uintptr_t arr = *(uintptr_t*)(lvl2 + 0xd8);
                if (!arr) { Log("  [%s] terminal: cur+0x50+0xb0+0xd8 is NULL", label); return; }
                uintptr_t arrPtr = *(uintptr_t*)arr;
                uint32_t arrCnt = *(uint32_t*)(arr + 8);
                Log("  [%s] container array @ 0x%llX (count=%u)",
                    label, (unsigned long long)arr, arrCnt);
                if (pid != 0xFFFF && pid < arrCnt) {
                    uintptr_t containerPtr = *(uintptr_t*)(arrPtr + (uintptr_t)pid * 8);
                    Log("  [%s] CONTAINER for panelId 0x%04X = 0x%llX",
                        label, pid, (unsigned long long)containerPtr);
                } else {
                    Log("  [%s] panelId 0x%04X out of range (count=%u)", label, pid, arrCnt);
                }
                return;
            }
            cur = *(uintptr_t*)(cur + 0x60);
            if (!cur) { Log("  [%s] sub+0x60 chain ended at hop %d (NULL)", label, hops); return; }
            hops++;
        }
        Log("  [%s] chain too deep (>8 hops), aborting", label);
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("  [%s] EXCEPTION during chain walk", label);
    }
}

static void DoDiffSnapshot() {
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
    if (!handler) {
        Log("DIFF: no handler captured yet — open the warehouse once with F6 first");
        return;
    }
    LONG state = InterlockedCompareExchange(&g_snapshotState, 0, 0);
    if (state == 0) {
        Log("DIFF: BEFORE — chain walk:");
        WalkAndLogChain(handler, "BEFORE");
        __try {
            memcpy(g_snapshotBefore, (void*)handler, HANDLER_SNAPSHOT_SIZE);
            // Snapshot the container object pointed to by handler+0x170 (if non-NULL).
            uintptr_t contBefore = *(uintptr_t*)(handler + 0x170);
            InterlockedExchange64(&g_contBeforeAddr, (LONG64)contBefore);
            if (contBefore > 0x10000 && contBefore < 0x7FFFFFFFFFFFULL) {
                memcpy(g_contSnapshotBefore, (void*)contBefore, CONT_SNAPSHOT_SIZE);
                Log("DIFF: container ptr at handler+0x170 = 0x%llX (snapshotted)",
                    (unsigned long long)contBefore);
            } else {
                memset(g_contSnapshotBefore, 0, CONT_SNAPSHOT_SIZE);
                Log("DIFF: handler+0x170 = 0x%llX (NULL or invalid, skipped)",
                    (unsigned long long)contBefore);
            }
            uintptr_t sub = *(uintptr_t*)(handler + 0x8);
            if (sub > 0x10000 && sub < 0x7FFFFFFFFFFFULL) {
                memcpy(g_subSnapshotBefore, (void*)sub, SUB_SNAPSHOT_SIZE);
                InterlockedExchange64(&g_subSnapshotAddr, (LONG64)sub);
                Log("DIFF: BEFORE snapshot captured (handler=0x%llX, sub=0x%llX). Now go open the chest regularly, then press the hotkey again.",
                    (unsigned long long)handler, (unsigned long long)sub);
            } else {
                InterlockedExchange64(&g_subSnapshotAddr, 0);
                Log("DIFF: BEFORE snapshot captured (handler=0x%llX, sub-object missing/invalid). Go open the chest, press the hotkey again.",
                    (unsigned long long)handler);
            }
            InterlockedExchange(&g_snapshotState, 1);
        } __except(EXCEPTION_EXECUTE_HANDLER) {
            Log("DIFF: BEFORE snapshot read EXCEPTION");
        }
        return;
    }
    // state == 1 → capture after + diff
    Log("DIFF: AFTER — chain walk:");
    WalkAndLogChain(handler, "AFTER");
    __try {
        memcpy(g_snapshotAfter, (void*)handler, HANDLER_SNAPSHOT_SIZE);
        Log("DIFF: AFTER snapshot captured (handler=0x%llX). Computing changes:",
            (unsigned long long)handler);
        LogDiffRegion("handler", g_snapshotBefore, g_snapshotAfter, HANDLER_SNAPSHOT_SIZE);

        // Container-object diff
        uintptr_t contBefore = (uintptr_t)InterlockedCompareExchange64(&g_contBeforeAddr, 0, 0);
        uintptr_t contAfter  = *(uintptr_t*)(handler + 0x170);
        Log("  container: before=0x%llX after=0x%llX",
            (unsigned long long)contBefore, (unsigned long long)contAfter);
        if (contAfter > 0x10000 && contAfter < 0x7FFFFFFFFFFFULL) {
            memcpy(g_contSnapshotAfter, (void*)contAfter, CONT_SNAPSHOT_SIZE);

            // Scan the global container array for this pointer to find its index.
            __try {
                uintptr_t sub = *(uintptr_t*)(handler + 0x8);
                uintptr_t lvl1 = sub ? *(uintptr_t*)(sub + 0x50) : 0;
                uintptr_t lvl2 = lvl1 ? *(uintptr_t*)(lvl1 + 0xb0) : 0;
                uintptr_t arrStruct = lvl2 ? *(uintptr_t*)(lvl2 + 0xd8) : 0;
                if (arrStruct) {
                    uintptr_t arrPtr = *(uintptr_t*)arrStruct;
                    uint32_t arrCnt = *(uint32_t*)(arrStruct + 8);
                    int found = -1;
                    for (uint32_t i = 0; i < arrCnt; i++) {
                        if (*(uintptr_t*)(arrPtr + (uintptr_t)i * 8) == contAfter) {
                            found = (int)i;
                            break;
                        }
                    }
                    if (found >= 0) {
                        Log("  container: NPC container 0x%llX is at array index 0x%04X (=%d)",
                            (unsigned long long)contAfter, found, found);
                    } else {
                        Log("  container: NPC container 0x%llX NOT in global array (count=%u) — different lookup mechanism",
                            (unsigned long long)contAfter, arrCnt);
                    }
                }
            } __except(EXCEPTION_EXECUTE_HANDLER) {}

            if (contBefore == contAfter) {
                Log("  container: same pointer, comparing contents:");
                LogDiffRegion("container", g_contSnapshotBefore, g_contSnapshotAfter, CONT_SNAPSHOT_SIZE);
            } else {
                Log("  container: POINTER CHANGED — dumping new container's first 0x100 bytes:");
                for (int i = 0; i < 0x100; i += 0x10) {
                    Log("    cont+0x%03X: %02X %02X %02X %02X %02X %02X %02X %02X  %02X %02X %02X %02X %02X %02X %02X %02X",
                        i,
                        g_contSnapshotAfter[i+0], g_contSnapshotAfter[i+1],
                        g_contSnapshotAfter[i+2], g_contSnapshotAfter[i+3],
                        g_contSnapshotAfter[i+4], g_contSnapshotAfter[i+5],
                        g_contSnapshotAfter[i+6], g_contSnapshotAfter[i+7],
                        g_contSnapshotAfter[i+8], g_contSnapshotAfter[i+9],
                        g_contSnapshotAfter[i+10], g_contSnapshotAfter[i+11],
                        g_contSnapshotAfter[i+12], g_contSnapshotAfter[i+13],
                        g_contSnapshotAfter[i+14], g_contSnapshotAfter[i+15]);
                }
            }
        } else {
            Log("  container: handler+0x170 = 0x%llX (NULL or invalid)",
                (unsigned long long)contAfter);
        }

        // Sub-object diff — read the current sub pointer and compare against the one
        // we captured before. If the pointer changed, the sub-object itself was
        // re-bound, which is a strong signal in itself.
        uintptr_t subBefore = (uintptr_t)InterlockedCompareExchange64(&g_subSnapshotAddr, 0, 0);
        uintptr_t subAfter = *(uintptr_t*)(handler + 0x8);
        if (subBefore == 0 || subAfter == 0) {
            Log("  sub: skipped (before=0x%llX, after=0x%llX — one or both invalid)",
                (unsigned long long)subBefore, (unsigned long long)subAfter);
        } else if (subBefore != subAfter) {
            Log("  sub: POINTER CHANGED before=0x%llX after=0x%llX (re-bound)",
                (unsigned long long)subBefore, (unsigned long long)subAfter);
            memcpy(g_subSnapshotAfter, (void*)subAfter, SUB_SNAPSHOT_SIZE);
            // Diff the *new* sub-object against zero baseline (since pointer changed,
            // before/after of the same address would be meaningless)
            for (int i = 0; i < SUB_SNAPSHOT_SIZE; i++) g_subSnapshotBefore[i] = 0;
            LogDiffRegion("sub(NEW)", g_subSnapshotBefore, g_subSnapshotAfter, SUB_SNAPSHOT_SIZE);
        } else {
            memcpy(g_subSnapshotAfter, (void*)subAfter, SUB_SNAPSHOT_SIZE);
            Log("  sub: same pointer 0x%llX, comparing contents:", (unsigned long long)subAfter);
            LogDiffRegion("sub", g_subSnapshotBefore, g_subSnapshotAfter, SUB_SNAPSHOT_SIZE);
        }

        InterlockedExchange(&g_snapshotState, 0);
    } __except(EXCEPTION_EXECUTE_HANDLER) {
        Log("DIFF: AFTER snapshot read EXCEPTION");
        InterlockedExchange(&g_snapshotState, 0);
    }
}

// Snapshot of all relevant state for a single log line. Useful when
// B/Circle is blocked or when a close path runs — gives a complete
// picture of what IsNewModalDialogVisible saw and what the handler
// fields look like at that exact moment.
static void LogModalState(const char* prefix) {
    if (!g_debugLog) return;
    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
    uintptr_t modalView = handler ? ReadModalDialog(handler) : 0;
    uint32_t  childCount = 0;
    if (modalView > 0x10000 && modalView < 0x7FFFFFFFFFFF) {
        __try { childCount = *(uint32_t*)(modalView + 0x30); }
        __except(EXCEPTION_EXECUTE_HANDLER) {}
    }
    uintptr_t lastPassed = (uintptr_t)InterlockedCompareExchange64(&g_lastModalPassed, 0, 0);
    LONG itemDetail = InterlockedCompareExchange(&g_itemDetailActiveCount, 0, 0);
    uint8_t  af = 0;
    uint64_t pv = 0;
    if (handler) {
        __try {
            af = *(uint8_t*)(handler + g_offActiveFlag);
            pv = *(uint64_t*)(handler + g_offPanelValue);
        } __except(EXCEPTION_EXECUTE_HANDLER) {}
    }
    Log("%s state: handler=0x%llX +PV=0x%llX +0x%X=%u modalView=0x%llX "
        "childCount=0x%X lastPassed=0x%llX itemDetail=%ld activePanel=%ld",
        prefix, (unsigned long long)handler, (unsigned long long)pv,
        g_offActiveFlag, (unsigned)af,
        (unsigned long long)modalView, childCount, (unsigned long long)lastPassed,
        (long)itemDetail, (long)InterlockedCompareExchange(&g_activePanel, 0, 0));
}

// ============================================================
//  WndProc + Input
// ============================================================
// g_pendingCircleClose / g_pendingBClose now live near the file top
// (next to the diagnostic forward-decls) so TriggerWarehouse can clear them.

static LRESULT CALLBACK HookedWndProc(HWND h, UINT m, WPARAM w, LPARAM l) {
    if (m==WM_TRIGGER_WAREHOUSE) { TriggerWarehouse((int)w); return 0; }
    if (m==WM_INIT_WAREHOUSE) {
        // Deferred warehouse panel init — posted by InputThread (separate thread)
        // once the handler has been auto-captured by HookedCanShow.
        if (!InterlockedCompareExchange(&g_warehouseActive, 0, 0)) return 0;
        uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
        if (handler) {
            Log("  Deferred init: handler captured, initializing panel");
            InitWarehousePanel(handler, GetInitStringForActive());
        } else {
            Log("  Deferred init: WM_INIT_WAREHOUSE but handler still NULL");
        }
        return 0;
    }
    // Panel hotkeys via WM_KEYDOWN. The game's input system sometimes leaves
    // GetAsyncKeyState reporting "still down" after a tap — polling-based
    // edge detection then misses subsequent presses. WM_KEYDOWN delivers a
    // proper press event for every physical tap (and OS auto-repeat), with
    // lParam bit 30 indicating "previous state": 0 = new press, 1 = repeat.
    // We trigger only on bit 30 == 0 so a held key produces exactly one
    // toggle action.
    if (m == WM_KEYDOWN) {
        bool autoRepeat = (l & (1LL << 30)) != 0;
        if (!autoRepeat) {
            // ESC: warehouse-close (or pass-through to dismiss modal first).
            if (w == VK_ESCAPE && InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
                if (IsNewModalDialogVisible()) {
                    uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
                    if (handler) {
                        __try {
                            InterlockedExchange64(&g_lastModalPassed, (LONG64)ReadModalDialog(handler));
                        } __except(EXCEPTION_EXECUTE_HANDLER) {}
                    }
                    // The ItemDetailModal isn't tracked at handler+0x258, so
                    // the polling-based close-detection never clears the
                    // hook-set flag. Each ESC consumes one modal — passing
                    // it to the game closes the popup, so we clear the flag
                    // to mirror that. Subsequent F-key/ESC checks see fresh
                    // state.
                    InterlockedExchange(&g_itemDetailActiveCount, 0);
                    Log("ESC pressed -> modal up, passing through to game");
                    return CallWindowProcA(g_originalWndProc, h, m, w, l);
                }
                Log("ESC pressed -> closing warehouse");
                PostMessageA(h, WM_TRIGGER_WAREHOUSE, 1, 0);
                return 0;
            }
            // Per-panel hotkeys take precedence over the legacy single
            // hotkey. With the new defaults (F4=Private, F5=Gatherables,
            // F6=Dresser, F7=Refrigerator, F8=Symbol, F9=Collecting),
            // any legacy `g_hotkey` value would collide with one of these
            // panels — checking it first would shadow the per-panel
            // binding. Legacy default is now 0 (disabled).
            for (int i = 0; i < PANEL_COUNT; i++) {
                if (g_panels[i].hotkey == 0 || (DWORD)w != g_panels[i].hotkey) continue;
                bool modOk = (g_panels[i].modifier == 0) ||
                             (GetAsyncKeyState(g_panels[i].modifier) & 0x8000) != 0;
                if (!modOk) break;
                LONG warehouseActive = InterlockedCompareExchange(&g_warehouseActive, 0, 0);
                if (!warehouseActive) {
                    InterlockedExchange(&g_nextOpenPanel, i);
                    Log("HOTKEY %s (vk=0x%X) -> OPEN", g_panels[i].name, g_panels[i].hotkey);
                } else {
                    Log("HOTKEY %s (vk=0x%X) -> CLOSE", g_panels[i].name, g_panels[i].hotkey);
                }
                PostMessageA(h, WM_TRIGGER_WAREHOUSE, 1, 0);
                return 0;
            }
            // Legacy single hotkey — only fires if no per-panel hotkey
            // matched above. Kept for backwards compatibility with INIs
            // that still use `Hotkey=` instead of the per-panel keys.
            if (g_hotkey && (DWORD)w == g_hotkey) {
                bool modOk = (g_modifierKey == 0) ||
                             (GetAsyncKeyState(g_modifierKey) & 0x8000) != 0;
                if (modOk) {
                    PostMessageA(h, WM_TRIGGER_WAREHOUSE, 1, 0);
                    return 0;
                }
            }
        }
    }
    // --- Raw Input: DualSense / DualShock buttons ---
    if (m == WM_INPUT) {
        ParseSonyButtons(l);

        bool circleDown = g_lastCircle;

        // Per-panel PSButton rising edges → toggle that panel.
        // If a PSModifier is configured, it must also be held at the moment
        // the button is pressed (mirrors XInput ControllerModifier).
        for (int i = 0; i < PANEL_COUNT; i++) {
            if (g_panels[i].psButtonByteOff < 0) {
                g_panelPsLastDown[i] = false;
                continue;
            }
            bool down = g_panelPsCurrentDown[i];
            bool modOk = (g_panels[i].psModifierByteOff < 0) ||
                         g_panelPsModifierDown[i];
            if (down && !g_panelPsLastDown[i] && modOk) {
                if (InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
                    if (IsNewModalDialogVisible()) {
                        // Mirror ESC: clear stale ItemDetailModal flag so a
                        // popup dismissed via a non-ESC path doesn't block
                        // the next close press.
                        InterlockedExchange(&g_itemDetailActiveCount, 0);
                    } else {
                        // Force close: bypass TriggerWarehouse modal-block.
                        PostMessageA(h, WM_TRIGGER_WAREHOUSE, 2, 0);
                    }
                } else {
                    InterlockedExchange(&g_nextOpenPanel, i);
                    PostMessageA(h, WM_TRIGGER_WAREHOUSE, 0, 0);
                }
            }
            g_panelPsLastDown[i] = down;
        }

        // Circle pressed while warehouse open → mark pending close (don't close yet)
        if (circleDown && !g_circleWasDown && InterlockedCompareExchange(&g_warehouseActive, 0, 0)) {
            if (IsNewModalDialogVisible()) {
                InterlockedExchange(&g_itemDetailActiveCount, 0);
            } else {
                InterlockedExchange(&g_pendingCircleClose, 1);
            }
        }

        // Circle released after pending close → close (force, bypass modal-block).
        if (!circleDown && g_circleWasDown && InterlockedCompareExchange(&g_pendingCircleClose, 0, 0)) {
            InterlockedExchange(&g_pendingCircleClose, 0);
            PostMessageA(h, WM_TRIGGER_WAREHOUSE, 2, 0);
        }

        g_circleWasDown = circleDown;
    }
    return CallWindowProcA(g_originalWndProc, h, m, w, l);
}

static DWORD g_lastAct=0;
static DWORD WINAPI InputThread(LPVOID) {
    while (true) {
        Sleep(16);
        if (InterlockedCompareExchange(&g_shutdown, 0, 0)) return 0;
        if (!g_enabled||!g_ready||!g_gameWindow) continue;

        // INI hot-reload (always available, regardless of game state)
        static bool reloadDown = false;
        if (g_reloadKey) {
            bool rd = (GetAsyncKeyState(g_reloadKey)&0x8000)!=0;
            if (rd && !reloadDown) {
                reloadDown = true;
                LoadConfig(g_iniPath);
                Log("INI reloaded (hotkey 0x%02X)", g_reloadKey);
            } else if (!rd) reloadDown = false;
        }

        // DiffSnapshotKey — must be available regardless of safe-state, because the
        // chest UI puts the player into a non-safe sub-mode and would skip otherwise.
        static bool diffKeyDownGlobal = false;
        if (g_diffSnapshotKey) {
            bool d = (GetAsyncKeyState(g_diffSnapshotKey) & 0x8000) != 0;
            bool modOk = (g_diffSnapshotModifier == 0) || (GetAsyncKeyState(g_diffSnapshotModifier) & 0x8000) != 0;
            if (d && modOk && !diffKeyDownGlobal) {
                diffKeyDownGlobal = true;
                DWORD now = GetTickCount();
                if (now - g_lastAct >= 400) {
                    g_lastAct = now;
                    DoDiffSnapshot();
                }
            } else if (!d) diffKeyDownGlobal = false;
        }

        // Lazy-resolve mainChar from singleton if not yet captured
        if (!InterlockedCompareExchange64(&g_mainChar, 0, 0)) {
            uintptr_t resolved = ResolveMainChar();
            if (resolved > 0x10000000000ULL) {
                InterlockedExchange64(&g_mainChar, (LONG64)resolved);
                Log("mainChar: 0x%llX (singleton, deferred)", (unsigned long long)resolved);
            }
        }

        // Sticky-binding poller for handler+0x170. Captures the
        // chest_object pointer the game writes at +0x170 — both during
        // mod-warehouse-active sessions AND during natural NPC-visits in
        // the world. The latter is the only way to get the *correct*
        // chest_object for housing chests (Gatherables/Dresser/etc) —
        // factory-create produces Camp-clones with wrong items.
        //
        // Cross-panel mis-attribution is prevented by:
        //  1. tab-state-based ap resolution (handler+0x138[handler+0x1e0])
        //  2. dupOtherPanel guard (skip if cont already in another panel)
        //  3. mod-owned flag (skip if mod set this sticky in current session)
        {
            uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
            if (handler) {
                __try {
                    uintptr_t cont = *(uintptr_t*)(handler + 0x170);
                    if (cont >= 0x10000000000ULL) {
                        uintptr_t vt = *(uintptr_t*)cont;
                        // Self-healing across game updates: the hardcoded
                        // g_addrContainerVtable can drift between game versions
                        // (1.05.00 moved it). If the observed vtable is in the
                        // game module range and stable, adopt it. This restores
                        // sticky-binding on the very first warehouse open after
                        // an update — same UX as pre-update.
                        //
                        // SAFETY: require the SAME unknown vtable to be seen
                        // multiple consecutive times before adopting. A single
                        // observation could be a stale frame where a different
                        // UI controller was briefly bound — adopting it would
                        // cause every later sticky-restore to write the wrong
                        // type into handler+0x170 and crash on SetInventory.
                        bool vtInModule = (g_gameBase != 0) &&
                                          (vt >= g_gameBase) &&
                                          (vt <  g_gameBase + g_imageSize);
                        if (vtInModule && g_addrContainerVtable != vt) {
                            static uintptr_t s_relearnCandidate = 0;
                            static int       s_relearnSightings = 0;
                            if (vt == s_relearnCandidate) {
                                s_relearnSightings++;
                            } else {
                                s_relearnCandidate = vt;
                                s_relearnSightings = 1;
                            }
                            // Require 5 consecutive sightings of the same
                            // candidate before adopting it. At ~30Hz polling
                            // that's ~150ms of stable observation — far longer
                            // than a transient stale-frame artefact.
                            if (s_relearnSightings >= 5) {
                                Log("Container vtable: auto-relearned base+0x%llX (was base+0x%llX, stable for %d sightings)",
                                    (unsigned long long)(vt - g_gameBase),
                                    (unsigned long long)(g_addrContainerVtable - g_gameBase),
                                    s_relearnSightings);
                                g_addrContainerVtable = vt;
                                s_relearnCandidate = 0;
                                s_relearnSightings = 0;
                            }
                        }
                        if (g_addrContainerVtable && vt == g_addrContainerVtable) {
                            // Derive the panel index from the ACTIVE TAB SUB
                            // (handler+0x138[handler+0x1e0] -> +0x92 = panelId).
                            // This is the truthful source: it changes whenever
                            // the user opens any chest, including via NPC where
                            // our hotkey path was NOT involved (so g_activePanel
                            // would be stale and misattribute the container to
                            // the wrong panel slot, corrupting other stickies).
                            LONG ap = -1;
                            __try {
                                uintptr_t tabArr = *(uintptr_t*)(handler + 0x138);
                                uint32_t  tabIdx = *(uint32_t*)(handler + 0x1e0);
                                if (tabArr >= 0x10000000000ULL && tabIdx < 32) {
                                    uintptr_t tabSub = *(uintptr_t*)(tabArr + (uintptr_t)tabIdx * 8);
                                    if (tabSub >= 0x10000000000ULL) {
                                        uint16_t pid = *(uint16_t*)(tabSub + g_offSubPanelId);
                                        // Match against our cached per-panel type-ids.
                                        // PANEL_PRIVATE uses configured panelValueCfg
                                        // (typically 0x59 = CampWareHouse).
                                        for (int i = 0; i < PANEL_COUNT; i++) {
                                            uint16_t mine;
                                            if (i == PANEL_PRIVATE) {
                                                LONG pv = InterlockedCompareExchange(&g_privatePanelValueCfg, 0, 0);
                                                mine = (pv > 0 && pv < 0x10000) ? (uint16_t)pv : 0x59;
                                            } else {
                                                // Lazy-resolve via the game's own
                                                // type lookup — caches per panel,
                                                // returns 0xFFFF on failure.
                                                mine = GetPanelTypeId(i);
                                                if (mine == 0xFFFF) continue;
                                            }
                                            if (mine == pid) { ap = i; break; }
                                        }
                                    }
                                }
                            } __except(EXCEPTION_EXECUTE_HANDLER) { ap = -1; }
                            // Fall back to g_activePanel only if we couldn't
                            // resolve from the tab — last-resort heuristic.
                            if (ap < 0 || ap >= PANEL_COUNT) {
                                ap = InterlockedCompareExchange(&g_activePanel, 0, 0);
                                if (ap < 0 || ap >= PANEL_COUNT) ap = PANEL_PRIVATE;
                            }
                            // GUARD: skip if mod owns this panel's sticky for
                            // the current session. The game's natural-bind
                            // a few ms after our explicit write puts a
                            // different (recycled) container into +0x170;
                            // without this guard we'd overwrite mod's good
                            // container.
                            //
                            // BUG fix: the original `continue` here jumped
                            // ALL the way to the InputThread's while-loop
                            // top, skipping XInput polling and B-button
                            // detection on every iteration where the mod
                            // owned the sticky — i.e. the entire duration
                            // of any Gatherables/Dresser/etc. session. The
                            // user could press B but it was never seen.
                            // Now we skip only the sticky-save logic by
                            // wrapping the rest of this branch in an else.
                            if (InterlockedCompareExchange(&g_panelStickyOwnedByMod[ap], 0, 0)) {
                                static volatile LONG64 lastSkipLogged = 0;
                                if (InterlockedExchange64(&lastSkipLogged, (LONG64)cont)
                                        != (LONG64)cont) {
                                    Log("Sticky bind: skip [%s] save 0x%llX (mod-owned this session)",
                                        g_panels[ap].name, (unsigned long long)cont);
                                }
                            } else {
                            LONG64 prev = InterlockedCompareExchange64(&g_panelStickyContainer[ap], 0, 0);
                            // GUARD: containers are unique per panel. If `cont`
                            // is already cached for a *different* panel, our
                            // tab-based ap-resolver was racing against the
                            // game's tab-state update (e.g. re-open Private
                            // while the previous tabSub still pointed at
                            // Gatherables). Skip the save instead of silently
                            // overwriting another panel's good sticky.
                            bool dupOtherPanel = false;
                            for (int j = 0; j < PANEL_COUNT; j++) {
                                if (j == ap) continue;
                                LONG64 other = InterlockedCompareExchange64(&g_panelStickyContainer[j], 0, 0);
                                if (other == (LONG64)cont) { dupOtherPanel = true; break; }
                            }
                            if (dupOtherPanel) {
                                // First time we notice this collision per cont — log once.
                                static volatile LONG64 g_lastDupLogged = 0;
                                if (InterlockedExchange64(&g_lastDupLogged, (LONG64)cont) != (LONG64)cont) {
                                    Log("Sticky bind: skip [%s] save 0x%llX (already owned by another panel — tab-state race)",
                                        g_panels[ap].name, (unsigned long long)cont);
                                }
                            } else if (prev != (LONG64)cont) {
                                InterlockedExchange64(&g_panelStickyContainer[ap], (LONG64)cont);
                                InterlockedExchange(&g_currentBoundPanel, ap);
                                // Log only the FIRST sticky save per panel — once we have
                                // a valid container the user can re-open that panel later.
                                // Subsequent updates within a session are diagnostic noise.
                                if (prev == 0) {
                                    Log("Sticky bind [%s]: saved 0x%llX",
                                        g_panels[ap].name, (unsigned long long)cont);

                                    // Compact key-fields snapshot per panel. Useful after a
                                    // game update for sanity-checking that the chest layout
                                    // (cont+0x7E0/0x7E8/0x7F0/0x810) and handler+0x39C max-slots
                                    // field are still where we expect them. Verbose dump removed.
                                    __try {
                                        Log("  Sticky[%s] cont=0x%llX +0x7E0=0x%llX +0x7E8=%d +0x7F0=%lld +0x810=%llu  handler+0x39C=%u",
                                            g_panels[ap].name,
                                            (unsigned long long)cont,
                                            (unsigned long long)*(uint64_t*)(cont + 0x7E0),
                                            (int)*(int16_t*)(cont + 0x7E8),
                                            (long long)*(int64_t*)(cont + 0x7F0),
                                            (unsigned long long)*(uint64_t*)(cont + 0x810),
                                            *(uint32_t*)(handler + 0x39C));
                                    } __except(EXCEPTION_EXECUTE_HANDLER) {
                                        Log("  Sticky[%s] field-snapshot EXCEPTION", g_panels[ap].name);
                                    }
                                }
                            }
                            } // end else (sticky not mod-owned)
                        }
                    }
                } __except(EXCEPTION_EXECUTE_HANDLER) {}
            }
        }

        // Deferred warehouse init: handler wasn't available when F6 was pressed.
        // We poll from this thread (16ms interval) because PostMessage from WndProc
        // re-queues before the game renders a frame.  InputThread is a separate thread
        // so the game processes frames between our checks. Timeout is generous
        // (~30 s) because newer game builds lazy-instantiate the warehouse
        // controller — Handler may not fire until many frames after F-press.
        // CaptureOnHandler ALSO triggers init inline when it captures, so this
        // poll is mostly a safety net for builds where Handler fires soon
        // enough that the WM_INIT_WAREHOUSE path is faster.
        if (InterlockedCompareExchange(&g_initPending, 0, 0)) {
            uintptr_t handler = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
            if (handler) {
                InterlockedExchange(&g_initPending, 0);
                PostMessageA(g_gameWindow, WM_INIT_WAREHOUSE, 0, 0);
            } else {
                LONG retries = InterlockedIncrement(&g_initRetryCount);
                if (retries >= 1800) {  // ~30 seconds at 16ms
                    InterlockedExchange(&g_initPending, 0);
                    Log("  Deferred init: GAVE UP after %ld retries (~30 s) — no Handler call observed", retries);
                }
            }
        }

        // (Polling-thread safe-state check removed — TriggerWarehouse does
        // the authoritative mode+sub check using the verified 1.08 enum.
        // See the comment block in TriggerWarehouse for the mapping.)

        // Keyboard hotkeys (F6 + per-panel) are dispatched from HookedWndProc
        // via WM_KEYDOWN — see panel-hotkey block there. Polling here was
        // unreliable: the game's input system left GetAsyncKeyState reporting
        // "still down" after a tap, so subsequent presses missed the rising
        // edge. WM_KEYDOWN's lParam bit 30 (previous-key-state) gives a clean
        // press-vs-repeat signal independent of hardware-state polling.

        // Controller: XInput logic mirrors the DirectInput WM_INPUT path
        // structurally — same per-panel rising-edge detection with
        // per-panel last-down trackers, same modifier check at press time,
        // same direct-PostMessage pattern, same B/Circle press-pending →
        // release-close sequence. No inSafeState gate (TriggerWarehouse
        // rejects unsafe modes itself, matching DirectInput behaviour).
        if (g_pXInputGetState) {
            // Aggregate buttons across ALL XInput slots (0–3). Steam Input
            // remaps PS5 controllers to one slot, while a physical Xbox
            // controller takes another — polling only slot 0 made the mod
            // miss B presses on whichever device wasn't index 0. OR-merging
            // means any controller's B/L3/R3 press is seen.
            WORD buttons = 0;
            int liveSlots = 0;
            ULONGLONG nowHb = GetTickCount64();
            for (DWORD idx = 0; idx < 4; idx++) {
                XINPUT_STATE_LOCAL state;
                memset(&state, 0, sizeof(state));
                if (g_pXInputGetState(idx, &state) == 0) {
                    buttons |= state.Gamepad.wButtons;
                    liveSlots++;
                }
            }

            if (liveSlots > 0) {
                bool warehouseActiveBtn =
                    InterlockedCompareExchange(&g_warehouseActive, 0, 0) != 0;

                // Per-panel hold-to-close timers — each panel tracks how long
                // its open combo has been continuously held. If the user keeps
                // holding the combo AFTER the panel has opened, treat that as
                // a "hold to close" gesture. Helps users who don't realise the
                // combo needs to be re-pressed for toggle-close.
                static ULONGLONG s_panelHoldStart[PANEL_COUNT] = {0};
                static bool      s_panelHoldFiredClose[PANEL_COUNT] = {false};

                for (int i = 0; i < PANEL_COUNT; i++) {
                    WORD btn = g_panels[i].controllerButton;
                    if (!btn) {
                        g_panelXiLastDown[i] = false;
                        s_panelHoldStart[i] = 0;
                        s_panelHoldFiredClose[i] = false;
                        continue;
                    }
                    bool down = (buttons & btn) != 0;
                    WORD mod = g_panels[i].controllerModifier;
                    bool modOk = (mod == 0) || ((buttons & mod) != 0);
                    bool comboHeld = down && modOk;

                    // Rising-edge toggle
                    if (down && !g_panelXiLastDown[i] && modOk) {
                        if (warehouseActiveBtn) {
                            // Modal-aware close: when a quantity dialog or Details popup
                            // is up, pressing the panel-button should NOT force-close the
                            // warehouse. Clear our tracked itemDetail flag (so the game's
                            // own close path can dismiss the popup) and skip the close.
                            // Users press the button again after the popup is gone to
                            // close the warehouse.
                            if (IsNewModalDialogVisible()) {
                                InterlockedExchange(&g_itemDetailActiveCount, 0);
                                s_panelHoldFiredClose[i] = true;  // absorb hold-detection
                            } else {
                                InterlockedExchange(&g_itemDetailActiveCount, 0);
                                PostMessageA(g_gameWindow, WM_TRIGGER_WAREHOUSE, 2, 0);
                                s_panelHoldFiredClose[i] = true;
                            }
                        } else {
                            InterlockedExchange(&g_nextOpenPanel, i);
                            PostMessageA(g_gameWindow, WM_TRIGGER_WAREHOUSE, 0, 0);
                            s_panelHoldFiredClose[i] = false;
                        }
                        s_panelHoldStart[i] = nowHb;
                    }

                    // Hold-to-close after >700 ms continuous hold
                    if (comboHeld && warehouseActiveBtn &&
                        s_panelHoldStart[i] != 0 &&
                        !s_panelHoldFiredClose[i] &&
                        (nowHb - s_panelHoldStart[i]) >= 700) {
                        // Same modal guard as the rising-edge close path.
                        if (!IsNewModalDialogVisible()) {
                            InterlockedExchange(&g_itemDetailActiveCount, 0);
                            PostMessageA(g_gameWindow, WM_TRIGGER_WAREHOUSE, 2, 0);
                        } else {
                            InterlockedExchange(&g_itemDetailActiveCount, 0);
                        }
                        s_panelHoldFiredClose[i] = true;
                    }

                    if (!comboHeld) {
                        s_panelHoldStart[i] = 0;
                        s_panelHoldFiredClose[i] = false;
                    }

                    g_panelXiLastDown[i] = down;
                }

                // ---- B button (default close): mirrors DirectInput Circle.
                //  - Rising edge with a modal up (quantity dialog at +0x258
                //    or ItemDetailModal counter > 0): just clear the popup
                //    flag — game's own input handler will close the modal.
                //    Do NOT mark pending close so the release doesn't trigger
                //    warehouse-close on top of the modal-close.
                //  - Rising edge with no modal: mark pending. Falling edge
                //    triggers warehouse-close (force, bypass modal-block).
                bool bDown = (buttons & 0x2000) != 0;
                if (bDown && !g_xiBWasDown && warehouseActiveBtn) {
                    if (IsNewModalDialogVisible()) {
                        InterlockedExchange(&g_itemDetailActiveCount, 0);
                    } else {
                        InterlockedExchange(&g_pendingBClose, 1);
                    }
                }
                if (!bDown && g_xiBWasDown && InterlockedCompareExchange(&g_pendingBClose, 0, 0)) {
                    InterlockedExchange(&g_pendingBClose, 0);
                    PostMessageA(g_gameWindow, WM_TRIGGER_WAREHOUSE, 2, 0);
                }
                g_xiBWasDown = bDown;

                g_prevButtons = buttons;
            }
        }
    }
    return 0;
}

static HWND FindGameWindow(){
    DWORD myPid=GetCurrentProcessId();
    HWND h=nullptr;
    while((h=FindWindowExW(nullptr,h,L"WindowsLauncherClassName",L"Crimson Desert"))!=nullptr){
        DWORD pid=0;GetWindowThreadProcessId(h,&pid);
        if(pid==myPid)return h;
    }
    return nullptr;
}

// ============================================================
//  Pattern Scanning + Init
// ============================================================
static bool ResolveAddresses() {
    g_fnHandler = 0; g_fnModeSwitcher = 0; g_fnCanShow = 0;
    g_fnSetInventory = 0; g_fnSetTitle = 0;

    // ================================================================
    //  PRIMARY: String cross-reference chain (update-resistant)
    //  Handler → SetInventory, SetTitle, CanShow all derived from it
    // ================================================================

    // Step 1: Find Handler via "ShowPackageCampMoneyList" (unique string, 1 xref in binary)
    uintptr_t strSPCML = FindString("ShowPackageCampMoneyList");
    if (strSPCML) {
        Log("  String 'ShowPackageCampMoneyList' at base+0x%llX", (unsigned long long)(strSPCML - g_gameBase));
        uintptr_t leaAddr = FindLEA(strSPCML);
        if (leaAddr) {
            Log("  LEA at base+0x%llX", (unsigned long long)(leaAddr - g_gameBase));
            g_fnHandler = FindFunctionStart(leaAddr);
        }
    }
    Log("Handler:      %s base+0x%llX (string-xref)", g_fnHandler?"OK":"FAIL",
        g_fnHandler?(unsigned long long)(g_fnHandler-g_gameBase):0);

    // Step 2: Find SetInventory via "SetInventory" string → CALL target in Handler.
    //
    // 1.06.00 RE: the real SetInventory @ 0xA82F70 (1898 bytes) starts with
    // `48 89 4C 24 08; 55; 53; 56; 57; 41 54; 41 55; 41 56; 41 57` — NOT
    // `40 55` like in 1.05. The previous resolver rejected it and picked
    // the NEXT 40-55 CALL which is SetChannels @ 0xA836E0 (452 bytes, only
    // writes handler+0x350/+0x352/+0x354). Calling SetChannels with our
    // 2-token filter string skipped the inventory bind entirely and the
    // game crashed on first frame of rendering with a NULL container.
    //
    // Fix: accept any "big function" prolog. SetInventory candidates are
    // expected to be substantially larger than SetChannels (>=600 bytes),
    // so we additionally check that the CALL target body extends through
    // at least 0x200 bytes of plausible code (not a 0xC3 RET in first
    // 0x40 bytes — SetChannels is the only short candidate here).
    if (g_fnHandler) {
        uintptr_t strSetInv = FindString("SetInventory");
        if (strSetInv) {
            uintptr_t leaAddr = FindLEA(strSetInv, g_fnHandler);
            if (leaAddr && leaAddr < g_fnHandler + 0x1000) {
                uintptr_t targets[16];
                int n = FindAllCALLsAfter(leaAddr, 60, targets, 16);
                for (int i = 0; i < n; i++) {
                    uint8_t* p = (uint8_t*)targets[i];
                    // Accept any of the known SetInventory prologs:
                    //   1.05: 40 55                             (REX PUSH RBP)
                    //   1.06: 48 89 4C 24 08                    (MOV [RSP+8], RCX)
                    //   alt:  48 89 5C 24 ??                    (MOV [RSP+disp8], RBX)
                    //   alt:  48 83 EC ??                       (SUB RSP, imm8)
                    bool prologOk = false;
                    if (p[0] == 0x40 && p[1] == 0x55) prologOk = true;
                    else if (p[0] == 0x48 && p[1] == 0x89 && p[2] == 0x4C && p[3] == 0x24 && p[4] == 0x08) prologOk = true;
                    else if (p[0] == 0x48 && p[1] == 0x89 && p[2] == 0x5C && p[3] == 0x24) prologOk = true;
                    if (!prologOk) continue;
                    // Size guard: SetInventory is large (~1900 bytes in 1.05/1.06).
                    // SetChannels is small (~450 bytes) and contains a RET within
                    // the first 0x40 bytes; SetInventory does not. Use this to
                    // reject the small wrong-target.
                    bool earlyRet = false;
                    for (int k = 1; k < 0x40; k++) {
                        if (p[k] == 0xC3) { earlyRet = true; break; }
                    }
                    if (earlyRet) continue;
                    g_fnSetInventory = targets[i];
                    break;
                }
            }
        }
    }
    Log("SetInventory: %s base+0x%llX (string-xref)", g_fnSetInventory?"OK":"FAIL",
        g_fnSetInventory?(unsigned long long)(g_fnSetInventory-g_gameBase):0);

    // 1.06-era hardcoded SetInventory override removed in 1.5.4: the wrong-target
    // compare against 0xA836E0 could spuriously match in 1.09+ and redirect the
    // correct dynamic resolution to a stale 1.06 RVA, and the bare fallback to
    // 0xA82F70 would install on garbage bytes. The dynamic prolog+earlyRet
    // filter above already rejects SetChannels by size, so the override is
    // redundant on every supported build. Failure now logs and aborts cleanly.
    if (!g_fnSetInventory) {
        Log("SetInventory: WARN dynamic resolver failed — panel binding will not work this session");
    }

    // Step 3: Find SetTitle via "SetWareHouseInventoryName" string → CALL chain in Handler
    if (g_fnHandler) {
        uintptr_t strSetName = FindString("SetWareHouseInventoryName");
        if (strSetName) {
            uintptr_t leaAddr = FindLEA(strSetName, g_fnHandler);
            if (leaAddr && leaAddr < g_fnHandler + 0x1000) {
                // 1.13+: the branch loads the title node, then hands it to the setter:
                //     MOV r64, [handlerReg+disp32]    ; node (this is BottomLabel's load)
                //     ...
                //     MOV RCX, r64                    ; same register
                //     CALL setter                     ; E8 rel32
                // Register- and offset-flexible so it survives struct re-layouts.
                for (int i = 0; i < 0x140 && !g_fnSetTitle; i++) {
                    uint8_t* p = (uint8_t*)(leaAddr + i);
                    if (p[0] < 0x48 || p[0] > 0x4F || p[1] != 0x8B) continue;
                    if ((p[2] & 0xC0) != 0x80 || (p[2] & 0x07) == 0x04) continue;
                    uint32_t disp = *(uint32_t*)(p + 3);
                    if (disp < 0x100 || disp >= 0x1000) continue;
                    int nodeReg = (((p[0] >> 2) & 1) << 3) | ((p[2] >> 3) & 7);  // REX.R : ModRM.reg
                    for (int j = i + 7; j < i + 0x60; j++) {
                        uint8_t* q = (uint8_t*)(leaAddr + j);
                        if (q[0] != 0x48 && q[0] != 0x49) continue;
                        if (q[1] != 0x8B) continue;
                        if ((q[2] & 0xF8) != 0xC8) continue;           // mod=11, reg=RCX
                        int srcReg = ((q[0] & 1) << 3) | (q[2] & 7);   // REX.B : ModRM.rm
                        if (srcReg != nodeReg) continue;
                        if (q[3] != 0xE8) continue;
                        int32_t rel = *(int32_t*)(q + 4);
                        uintptr_t target = (uintptr_t)(q + 8) + rel;
                        if (target > g_gameBase && target < g_gameBase + g_imageSize)
                            g_fnSetTitle = target;
                        break;
                    }
                }
                if (!g_fnSetTitle) {
                    // pre-1.13 layout: SetTitle (prolog 40 55) called ~150 bytes below the LEA
                    uintptr_t targets[16];
                    int n = FindAllCALLsAfter(leaAddr, 200, targets, 16);
                    for (int i = 0; i < n; i++) {
                        uint8_t* p = (uint8_t*)targets[i];
                        if (p[0] == 0x40 && p[1] == 0x55 && targets[i] != g_fnSetInventory) {
                            g_fnSetTitle = targets[i];
                            break;
                        }
                    }
                }
            }
        }
    }
    Log("SetTitle:     %s base+0x%llX (string-xref)", g_fnSetTitle?"OK":"FAIL",
        g_fnSetTitle?(unsigned long long)(g_fnSetTitle-g_gameBase):0);

    // Step 3a: Extract bottom-label offset from the handler's SetWareHouseInventoryName branch.
    // The handler does:  uVar3 = *(undefined8 *)(param_1 + OFFSET);  ...  SetTitle(uVar3, text);
    // The LOAD ("mov r64, [rXX+disp32]", opcode 48 8B, ModRM mod=10) sits within ~0x100 bytes
    // before the CALL to SetTitle.  Take the MATCH NEAREST to the CALL.
    if (g_fnHandler && g_fnSetTitle) {
        uintptr_t strSetName = FindString("SetWareHouseInventoryName");
        if (strSetName) {
            uintptr_t leaAddr = FindLEA(strSetName, g_fnHandler);
            if (leaAddr && leaAddr < g_fnHandler + 0x1000) {
                // Locate the CALL to g_fnSetTitle after leaAddr
                uintptr_t callSite = 0;
                for (int i = 0; i < 400; i++) {
                    uint8_t* p = (uint8_t*)(leaAddr + i);
                    if (p[0] != 0xE8) continue;
                    int32_t rel = *(int32_t*)(p + 1);
                    if ((uintptr_t)(p + 5) + rel == g_fnSetTitle) {
                        callSite = leaAddr + i;
                        break;
                    }
                }
                if (callSite) {
                    // Walk backwards from callSite looking for MOV r64, [rXX+disp32]
                    // Encoding: REX.W (48-4F), 8B, ModRM (mod=10 → 0x80-0xBF), optional SIB, disp32
                    uint32_t bestDisp = 0;
                    for (uintptr_t a = callSite - 3; a > leaAddr; a--) {
                        uint8_t* p = (uint8_t*)a;
                        if (p[0] < 0x48 || p[0] > 0x4F) continue;
                        if (p[1] != 0x8B) continue;
                        if ((p[2] & 0xC0) != 0x80) continue;      // mod must be 10
                        int dispOff = 3;
                        if ((p[2] & 0x07) == 0x04) dispOff = 4;    // SIB byte present
                        uint32_t disp = *(uint32_t*)(p + dispOff);
                        if (disp >= 0x100 && disp < 0x1000) {
                            bestDisp = disp;
                            break;  // closest match wins
                        }
                    }
                    if (bestDisp) g_offBottomLabel = bestDisp;
                }
            }
        }
    }
    Log("BottomLabel:  %s offset=0x%X (handler → SetTitle callsite)",
        g_offBottomLabel ? "OK" : "FAIL", g_offBottomLabel);

    // Step 3b: TopTitle offset via the UI selector-attribute binding chain (1.13+).
    // The top header title is the NpcInteractionTitle widget's text node
    // (#NpcInteractionTitleText); the warehouse body attribute
    // "selector-title-subtext-stage" is bound to a member of the control.
    // Mechanism cross-check: resolving "selector-warehouse-inventory-title"
    // the same way must reproduce the BottomLabel offset that Step 3a
    // extracted from the SetWareHouseInventoryName branch. If anything
    // disagrees, DISABLE the top-title write instead of falling back to the
    // pre-1.13 default 0xE8 — since the 1.13 re-layout that slot holds a
    // DIFFERENT bound node, so a stale-default write would hit a wrong node.
    {
        uint32_t prevDefault = g_offTopTitle;
        uint32_t offTop   = ResolveSelectorMemberOffset("selector-title-subtext-stage");
        uint32_t offCheck = ResolveSelectorMemberOffset("selector-warehouse-inventory-title");
        if (offTop && offCheck && g_offBottomLabel && offCheck == g_offBottomLabel) {
            g_offTopTitle = offTop;
            Log("TopTitle:     OK offset=0x%X (selector binding chain; cross-check inv-title=0x%X == BottomLabel; default was 0x%X)",
                g_offTopTitle, offCheck, prevDefault);
        } else {
            g_offTopTitle = 0;
            Log("TopTitle:     DISABLED (binding chain top=0x%X check=0x%X bottomLabel=0x%X) — top title stays generic",
                offTop, offCheck, g_offBottomLabel);
        }
    }

    // Step 3c: Find SetDonationFaction handler via "SetDonationFaction" string-xref in
    // the main warehouse handler, and extract the donation-state struct offset.
    // The donation handler writes 3 shorts (faction type) and on the failure path
    // resets them to 0xFFFF via `MOV word [RDI+disp32], BX` where BX = 0xFFFF.
    // Encoding: 66 89 9F disp32 (ModRM 0x9F = mod=10, reg=011 (BX), r/m=111 (RDI)).
    // Generalize to any base register: 66 89 9X disp32 with mod=10, reg=011.
    //
    // The handler dispatches commands via `strcmp(...); JNZ skip; setup; CALL handler`.
    // strcmp always comes first after the LEA. We filter it out by call-target proximity
    // (library functions sit far from the Handler in the binary); the target handler is
    // always co-located within ~1 MB of the dispatcher Handler.
    if (g_fnHandler) {
        uintptr_t strDonation = FindString("SetDonationFaction");
        if (strDonation) {
            uintptr_t leaAddr = FindLEA(strDonation, g_fnHandler);
            if (leaAddr && leaAddr < g_fnHandler + 0x1000) {
                uintptr_t targets[16];
                int n = FindAllCALLsAfter(leaAddr, 200, targets, 16);
                for (int i = 0; i < n; i++) {
                    uintptr_t t = targets[i];
                    if (t == g_fnSetInventory || t == g_fnSetTitle) continue;
                    uintptr_t dist = (t > g_fnHandler) ? (t - g_fnHandler) : (g_fnHandler - t);
                    if (dist > 0x100000) continue;   // skip strcmp/library calls (far from Handler)
                    g_fnSetDonationFaction = t;
                    break;
                }
            }
        }
    }
    Log("SetDonationFaction: %s base+0x%llX",
        g_fnSetDonationFaction ? "OK" : "FAIL",
        g_fnSetDonationFaction ? (unsigned long long)(g_fnSetDonationFaction - g_gameBase) : 0);
    // Scan SetDonationFaction for `66 89 9X disp32` (MOV word [reg+disp32], BX)
    // Take the smallest disp32 found — that's the first of the 3 donation-state shorts.
    if (g_fnSetDonationFaction) {
        uint8_t* fn = (uint8_t*)g_fnSetDonationFaction;
        uint32_t smallest = 0;
        for (int j = 0; j < 0x400 - 7; j++) {
            // Must be: 0x66 (operand size prefix), 0x89 (MOV r/m16, r16), ModRM with
            // mod=10 and reg=011 (BX).  That's ModRM byte = 0x98 | r/m in [0..7] minus r/m=100 (SIB).
            if (fn[j] != 0x66 || fn[j+1] != 0x89) continue;
            uint8_t modrm = fn[j+2];
            if ((modrm & 0xC0) != 0x80) continue;     // mod=10
            if ((modrm & 0x38) != 0x18) continue;     // reg=011 (BX)
            if ((modrm & 0x07) == 0x04) continue;     // r/m != SIB
            uint32_t disp = *(uint32_t*)(fn + j + 3);
            if (disp < 0x100 || disp >= 0x1000) continue;
            if (!smallest || disp < smallest) smallest = disp;
        }
        if (smallest) g_offDonationState = smallest;
    }
    Log("DonationOff:  %s offset=0x%X (SetDonationFaction → MOV [reg+N],BX)",
        g_fnSetDonationFaction ? "OK" : "FALLBACK", g_offDonationState);

    // Step 3b: Find SetTitleDirect (FUN_1434159c0) from inside SetTitle.
    // SetTitle checks node+0xA8 (bridge). If bridge+8 (renderer) exists,
    // it calls SetTitleDirect(renderer, text) — which does proper UTF-8→wchar.
    // In the assembly: 1st E8 CALL = __chkstk, 2nd E8 CALL = SetTitleDirect.
    if (g_fnSetTitle) {
        uint8_t* p = (uint8_t*)g_fnSetTitle;
        int callNum = 0;
        for (int i = 0; i < 120; i++) {
            if (p[i] == 0xE8) {
                int32_t rel = *(int32_t*)(p + i + 1);
                uintptr_t target = (uintptr_t)(p + i + 5) + rel;
                if (target > g_gameBase && target < g_gameBase + g_imageSize) {
                    callNum++;
                    if (callNum == 2) {
                        g_fnSetTitleDirect = target;
                        break;
                    }
                }
                i += 4; // skip rel32
            }
        }
    }
    Log("SetTitleDir:  %s base+0x%llX (SetTitle internal)",
        g_fnSetTitleDirect?"OK":"FAIL",
        g_fnSetTitleDirect?(unsigned long long)(g_fnSetTitleDirect-g_gameBase):0);

    // Step 3d: Extract 0x15 "prepare" sub-object offsets directly from the Handler body.
    // The Handler's 0x15 path does three back-to-back virtual calls of the form:
    //     MOV RCX, [param_1+disp32]   ; REX 8B ModRM(mod=10, reg=001 RCX, r/m != SIB) disp32
    //     MOV RAX, [RCX]              ; 48 8B 01
    //     CALL [RAX+imm]              ; FF 50 disp8  OR  FF 90 disp32
    // Apr-11 layout: 0x2c8/0x2d8/0x300.  Apr-23 layout: 0x2e8/0x2f8/0x320.
    if (g_fnHandler) {
        uint8_t* fn = (uint8_t*)g_fnHandler;
        uint32_t offs[3] = {};
        int found = 0;
        for (int i = 0; i < 0x200 && found < 3; i++) {
            if (fn[i] < 0x40 || fn[i] > 0x4F) continue;        // REX prefix
            if (fn[i + 1] != 0x8B) continue;                    // MOV r64, r/m64
            uint8_t modrm = fn[i + 2];
            if ((modrm & 0xC0) != 0x80) continue;               // mod = 10 (disp32)
            if ((modrm & 0x38) != 0x08) continue;               // reg = 001 (RCX target)
            if ((modrm & 0x07) == 0x04) continue;               // skip SIB-encoded r/m
            uint32_t disp = *(uint32_t*)(fn + i + 3);
            if (disp < 0x100 || disp > 0x800) continue;         // plausible struct offset
            int movRaxPos = i + 7;
            if (fn[movRaxPos] != 0x48 || fn[movRaxPos + 1] != 0x8B || fn[movRaxPos + 2] != 0x01) continue;
            int callPos = movRaxPos + 3;
            if (fn[callPos] != 0xFF) continue;
            if (fn[callPos + 1] != 0x50 && fn[callPos + 1] != 0x90) continue;
            bool dup = false;
            for (int j = 0; j < found; j++) if (offs[j] == disp) { dup = true; break; }
            if (dup) continue;
            offs[found++] = disp;
        }
        if (found == 3) {
            g_offPrepare1 = offs[0];
            g_offPrepare2 = offs[1];
            g_offPrepare3 = offs[2];
        }
        Log("PrepareOffs:  %s offs=0x%X/0x%X/0x%X (handler scan)",
            found == 3 ? "OK" : "FALLBACK",
            g_offPrepare1, g_offPrepare2, g_offPrepare3);
    }

    // Step 4: Find CanShow via Handler's vtable (update-proof — scans all vtable entries)
    // CanShow signature: contains MOVZX reg, byte [reg+0x118] (reads the active flag).
    // We find ALL data references to g_fnHandler (could be in vtables, reloc tables, etc.),
    // verify each is a real vtable (adjacent entries are valid code pointers), then scan
    // the vtable for a function matching the CanShow signature.
    if (g_fnHandler) {
        uint8_t* base = (uint8_t*)g_gameBase;
        for (DWORD i = 0; i + 8 <= g_imageSize && !g_fnCanShow; i += 8) {
            if (*(uintptr_t*)(base + i) != g_fnHandler) continue;
            uintptr_t vtableEntry = g_gameBase + i;
            // Verify this is a real vtable: at least 4 adjacent entries should be valid code pointers
            int validCount = 0;
            for (int check = -4; check <= 4; check++) {
                uintptr_t addr = vtableEntry + check * 8;
                if (addr < g_gameBase || addr >= g_gameBase + g_imageSize - 8) continue;
                uintptr_t ptr = *(uintptr_t*)addr;
                if (ptr > g_gameBase && ptr < g_gameBase + g_imageSize) validCount++;
            }
            if (validCount < 4) continue;  // not a real vtable, skip
            if (!g_warehouseVtableEntry) g_warehouseVtableEntry = vtableEntry;
            // Scan vtable entries around the handler (±0x800 = up to 256 entries each way)
            uintptr_t vtableBase = (vtableEntry > g_gameBase + 0x800) ? vtableEntry - 0x800 : g_gameBase;
            uintptr_t vtableEnd = vtableEntry + 0x800;
            if (vtableEnd > g_gameBase + g_imageSize - 8) vtableEnd = g_gameBase + g_imageSize - 8;
            for (uintptr_t v = vtableBase; v <= vtableEnd && !g_fnCanShow; v += 8) {
                uintptr_t candidate = *(uintptr_t*)v;
                if (candidate <= g_gameBase || candidate >= g_gameBase + g_imageSize) continue;
                if (candidate == g_fnHandler) continue;
                // Resolve thunks (JMP [rip+disp32] or E9 rel32)
                uintptr_t resolved = candidate;
                uint8_t* t = (uint8_t*)candidate;
                if (t[0] == 0xFF && t[1] == 0x25) {
                    int32_t disp = *(int32_t*)(t + 2);
                    resolved = *(uintptr_t*)(candidate + 6 + disp);
                } else if (t[0] == 0xE9) {
                    int32_t rel = *(int32_t*)(t + 1);
                    resolved = candidate + 5 + rel;
                }
                if (resolved <= g_gameBase || resolved >= g_gameBase + g_imageSize) continue;
                // Check CanShow signature.  CanShow's hot path ends with:
                //     movzx eax, byte ptr [thisPtr+disp32]
                //     ret                              (optionally preceded by stack cleanup)
                // We require: MOVZX destination is EAX (reg field = 000), mod = 10 (disp32),
                // r/m != 100 (no SIB), and the instruction is followed within a few bytes by
                // a RET (C3).  Constraining reg=000 rules out the many unrelated MOVZX uses
                // that would otherwise produce false positives on arbitrary virtual functions.
                uint8_t* fn = (uint8_t*)resolved;
                uint32_t matchDisp = 0;
                for (int j = 0; j < 0x200 - 8 && !matchDisp; j++) {
                    uint8_t* p = fn + j;
                    int instrLen = 0;
                    uint32_t d = 0;
                    // Case A: 0F B6 8X disp32  (MOVZX eax/ecx/edx... from [reg+disp32])
                    // We want reg=000 (EAX), so modrm in 0x80-0x87 (but not 0x84 = SIB)
                    if (p[0] == 0x0F && p[1] == 0xB6 &&
                        (p[2] & 0xF8) == 0x80 && p[2] != 0x84) {
                        d = *(uint32_t*)(p + 3);
                        instrLen = 7;
                    }
                    // Case B: REX prefix + MOVZX (8 bytes total)
                    // REX byte 0x44 adds R bit to target reg — for EAX target no REX.R needed.
                    // REX 0x48 is W (64-bit), but MOVZX doesn't use W.  Only REX.B (0x41) would
                    // change the source base register.  Accept REX bytes 0x40-0x47 (no R bit).
                    else if (p[0] >= 0x40 && p[0] <= 0x47 &&
                             p[1] == 0x0F && p[2] == 0xB6 &&
                             (p[3] & 0xF8) == 0x80 && p[3] != 0x84) {
                        d = *(uint32_t*)(p + 4);
                        instrLen = 8;
                    }
                    if (!instrLen || d < 0x40 || d >= 0x2000) continue;
                    // Require a RET within 6 bytes after the MOVZX (allows short epilog like
                    // `add rsp, XX; ret` or `pop rbp; ret`).
                    bool retNearby = false;
                    for (int k = 0; k < 6; k++) {
                        if (p[instrLen + k] == 0xC3) { retNearby = true; break; }
                    }
                    if (!retNearby) continue;
                    matchDisp = d;
                }
                if (matchDisp) {
                    g_fnCanShow = resolved;
                    g_warehouseVtableEntry = vtableEntry;
                    g_offActiveFlag = matchDisp;
                    Log("  Vtable at base+0x%llX, CanShow at base+0x%llX (vtable offset 0x%llX), active flag offset 0x%X",
                        (unsigned long long)(vtableEntry - g_gameBase),
                        (unsigned long long)(resolved - g_gameBase),
                        (unsigned long long)(v - vtableEntry), matchDisp);
                }
            }
        }
    }
    Log("CanShow:      %s base+0x%llX (vtable)", g_fnCanShow?"OK":"FAIL",
        g_fnCanShow?(unsigned long long)(g_fnCanShow-g_gameBase):0);

    // Step 4a: Find vtable start via RTTI Complete Object Locator (vtable[-1])
    // In MSVC x64, vtable[-1] is a pointer to the RTTICompleteObjectLocator.
    // The COL has signature=1 (DWORD at offset 0) and pTypeDescriptor (RVA at offset 12)
    // pointing to a TypeDescriptor whose name starts with ".?AV".
    // Scan backwards from the handler entry to find this boundary.
    if (g_warehouseVtableEntry) {
        for (uintptr_t scan = g_warehouseVtableEntry - 8; scan > g_warehouseVtableEntry - 0x2000; scan -= 8) {
            uintptr_t colPtr = *(uintptr_t*)(scan - 8);  // candidate vtable[-1]
            if (colPtr <= g_gameBase || colPtr >= g_gameBase + g_imageSize - 24) continue;
            // Check RTTI COL signature (must be 1 for x64)
            if (*(uint32_t*)colPtr != 1) continue;
            // Check pTypeDescriptor RVA (offset 12 in COL) points to valid TypeDescriptor
            uint32_t tdRVA = *(uint32_t*)(colPtr + 12);
            uintptr_t tdAddr = g_gameBase + tdRVA;
            if (tdAddr <= g_gameBase || tdAddr >= g_gameBase + g_imageSize - 20) continue;
            // TypeDescriptor: vfptr(8) + spare(8) + name[0..3] = ".?AV"
            const char* tdName = (const char*)(tdAddr + 16);
            if (tdName[0] == '.' && tdName[1] == '?' && tdName[2] == 'A') {
                g_warehouseVtableStart = scan;
                Log("  Vtable start at base+0x%llX (handler offset 0x%llX, class=%.60s)",
                    (unsigned long long)(scan - g_gameBase),
                    (unsigned long long)(g_warehouseVtableEntry - scan), tdName);
                break;
            }
        }
        if (!g_warehouseVtableStart)
            Log("  Vtable start: FAIL (RTTI scan)");
    }

    // Step 4b: Modal dialog offset (update-proof modal detection)
    // Observed live (Apr-23 build, user-confirmed via field dump): the current-modal
    // pointer lives at handler + 0x258 — NOT in the 0x300-0x400 sub-controller slot
    // range where earlier builds kept it. All previous scan heuristics (store-pattern,
    // load-pattern, LEA-out-param) found false positives in 0x3XX because there are
    // unrelated struct fields there that match similar byte patterns. 0x258 sits in a
    // different part of the struct that the heuristics can't reach without producing
    // many false hits. Until we have a uniquely-identifying pattern, hardcode.
    g_modalDialogOff = 0x258;
    Log("ModalDlgOff:  OK offset=0x%X (hardcoded for Apr-23 1.0.4.1)", g_modalDialogOff);

    // Step 5a: Find mainChar singleton global
    // The game loads the manager singleton and reads the mode byte via:
    //   48 8B 05 <disp32>        MOV RAX, [RIP+global]      (singleton slot)
    //   48 8B <mm> 48            MOV reg, [RAX+0x48]        (mainChar = mgr+0x48)
    //   80 <cc> <off32>          CMP byte [reg+modeOff], i8 (mode byte in 0xC00-0xD00)
    // DRIFT NOTE (1.13.00 / build 24048742): the intermediate register is no
    // longer fixed to RCX (now RDX/RBX/... seen) and the mode-byte offset
    // moved 0xCA8 -> 0xCA0. The old hardcoded tail "48 8B 48 48 80 B9 A8 0C..."
    // stopped matching -> MainCharGlobal FAIL -> ResolveAddresses returned
    // false -> FATAL (mod didn't load at all). This scan is now
    // register-flexible (reg encoded by mm/cc) and offset-flexible (any
    // 0xC?? mode byte). mgr+0x48 == mainChar is unchanged across builds and
    // is verified at runtime by ResolveMainChar's downstream use. Also note:
    // this repacked binary has no ".text" section — code lives in ".shared";
    // the scan runs over the whole in-memory image (g_imageSize) so it covers
    // it regardless of section names. All 3 observed call sites resolve to the
    // same global (build 24048742: base+0x617FBC0), confirming uniqueness.
    {
        uint8_t* base = (uint8_t*)g_gameBase;
        for (DWORD i = 0; (size_t)i + 17 < g_imageSize; i++) {
            if (base[i] != 0x48 || base[i+1] != 0x8B || base[i+2] != 0x05) continue;   // MOV RAX,[rip+d]
            if (base[i+7] != 0x48 || base[i+8] != 0x8B) continue;                        // MOV reg,[RAX+..]
            uint8_t mm = base[i+9];
            if ((mm & 0xC7) != 0x40) continue;   // mod=01, rm=000 (base RAX)
            if (base[i+10] != 0x48) continue;    // disp8 == +0x48
            int destReg = (mm >> 3) & 7;
            if (base[i+11] != 0x80) continue;                 // CMP r/m8, imm8 (group)
            if (base[i+12] != (0xB8 | destReg)) continue;     // mod=10, /7=CMP, rm==destReg
            uint32_t off = *(uint32_t*)(base + i + 13);
            if (off < 0xC00 || off >= 0xD00) continue;        // mode byte in mainChar cluster
            int32_t disp = *(int32_t*)(base + i + 3);
            g_mainCharGlobalPtr = (uintptr_t)(base + i + 7) + disp;  // RIP after MOV RAX = base+i+7
            Log("MainCharGlobal: OK base+0x%llX (singleton scan, r%d, modeOff=0x%X)",
                (unsigned long long)(g_mainCharGlobalPtr - g_gameBase), destReg, off);
            break;
        }
        if (!g_mainCharGlobalPtr) Log("MainCharGlobal: FAIL (singleton pattern not found)");
    }

    // Step 5b: ModeSwitcher — string-xref + dynamic offset extraction
    // The ModeSwitcher function references 4 mainChar offsets in the 0x0C00-0x0D00 range:
    //   mode byte (u8), sub byte (u8), mode flags array (7 bytes), subtypes array (15 bytes)
    // Find any disp32 in that range — take min and max, derive the other offsets.

    // Helper lambda: scan function body for disp32 values in mainChar mode-byte range.
    // Strategy: collect all disp32 in 0xC00-0xD00, find the consecutive pair (X, X+1)
    // which identifies mode byte + sub byte. Then find the max disp for subtypes/flags.
    // Returns true and populates g_fnModeSwitcher + offsets on success.
    auto tryValidateModeSwitcher = [](uintptr_t candidate, int scanWindow, const char* method) -> bool {
        uint8_t* fn = (uint8_t*)candidate;
        // Collect all unique disp32 values in range
        uint32_t found[64];
        int nFound = 0;
        for (int k = 2; k < scanWindow - 4; k++) {
            uint8_t modrmA = fn[k - 1];
            uint8_t modrmB = fn[k - 2];
            bool caseA = ((modrmA & 0xC0) == 0x80) && ((modrmA & 0x07) != 0x04);
            bool caseB = ((modrmB & 0xC0) == 0x80) && ((modrmB & 0x07) == 0x04);
            if (!caseA && !caseB) continue;
            uint32_t disp = *(uint32_t*)(fn + k);
            if (disp < 0xC00 || disp >= 0xD00) continue;
            // Add if not already seen
            bool dup = false;
            for (int j = 0; j < nFound; j++) if (found[j] == disp) { dup = true; break; }
            if (!dup && nFound < 64) found[nFound++] = disp;
        }
        // Find the consecutive pair (X, X+1) — this is mode byte + sub byte
        uint32_t modeByte = 0;
        for (int i = 0; i < nFound; i++) {
            for (int j = 0; j < nFound; j++) {
                if (found[j] == found[i] + 1) { modeByte = found[i]; break; }
            }
            if (modeByte) break;
        }
        if (!modeByte) return false;
        // Find the max disp within modeByte+0x20 range (mode/sub/flags/subtypes are
        // clustered within ~0x20 bytes of each other in the mainChar struct)
        uint32_t maxDisp = 0;
        for (int i = 0; i < nFound; i++) {
            if (found[i] > modeByte + 1 && found[i] <= modeByte + 0x20 && found[i] > maxDisp)
                maxDisp = found[i];
        }
        // Need at least mode, sub, and one more offset for flags/subtypes
        if (!maxDisp) return false;
        g_fnModeSwitcher = candidate;
        g_offModeByte  = modeByte;
        g_offSubByte   = modeByte + 1;
        g_offSubtypes  = maxDisp;
        g_offModeFlags = maxDisp - 7;
        Log("ModeSwitcher: OK base+0x%llX (mode=0x%X sub=0x%X flags=0x%X subtypes=0x%X) [%s]",
            (unsigned long long)(candidate - g_gameBase),
            g_offModeByte, g_offSubByte, g_offModeFlags, g_offSubtypes, method);
        return true;
    };

    // PRIMARY: String-xref via "ingame-global" (unique string, update-resistant)
    {
        uintptr_t strIG = FindString("ingame-global");
        if (strIG) {
            uintptr_t leaAddr = FindLEA(strIG);
            if (leaAddr) {
                uintptr_t fnStart = FindFunctionStart(leaAddr);
                if (fnStart) {
                    tryValidateModeSwitcher(fnStart, 0xA00, "string-xref");
                }
            }
        }
    }

    // FALLBACK: Pattern scan with old + new prologs, extended scan window
    if (!g_fnModeSwitcher) {
        static const uint8_t pMS_old[] = {
            0x48,0x89,0x5C,0x24,0x08, 0x48,0x89,0x6C,0x24,0x10,
            0x48,0x89,0x74,0x24,0x18, 0x57, 0x48,0x81,0xEC,0xA0,0x00,0x00,0x00
        };
        static const uint8_t pMS_new[] = {
            0x48,0x89,0x5C,0x24,0x08, 0x48,0x89,0x74,0x24,0x18,
            0x55, 0x57, 0x41,0x56, 0x48,0x8B,0xEC
        };
        struct { const uint8_t* pat; int len; const char* tag; } patterns[] = {
            { pMS_new, sizeof(pMS_new), "pattern-new" },
            { pMS_old, sizeof(pMS_old), "pattern-old" },
        };
        uint8_t* base = (uint8_t*)g_gameBase;
        for (auto& p : patterns) {
            if (g_fnModeSwitcher) break;
            for (DWORD i = 0; (DWORD)(i + p.len) <= g_imageSize; i++) {
                if (memcmp(base + i, p.pat, p.len) != 0) continue;
                if (tryValidateModeSwitcher(g_gameBase + i, 0xA00, p.tag))
                    break;
            }
        }
    }
    if (!g_fnModeSwitcher) Log("ModeSwitcher: FAIL (no validated match)");

    // Auto-derive g_storeSubIndex (the subtype index whose ModeSwitcher case emits
    // the "store" view-tag). It flips almost every game update; deriving it makes
    // the mod self-correct instead of needing a manual Ghidra re-find. The hardcoded
    // default stays as a cross-checked fallback, so this is never worse than before.
    if (g_fnModeSwitcher) {
        int32_t derived = ResolveStoreSubIndex();
        if (derived >= 0) {
            if ((uint32_t)derived != g_storeSubIndex)
                Log("StoreSubIndex: DRIFT default=%u derived=%d (using derived)",
                    g_storeSubIndex, derived);
            else
                Log("StoreSubIndex: OK %d (auto-derived, matches default)", derived);
            g_storeSubIndex = (uint32_t)derived;
        } else {
            Log("StoreSubIndex: derive failed, keeping default %u", g_storeSubIndex);
        }
    }

    // Step 6: SetCursorVisible — removed.
    // The ModeSwitcher function (FUN_1406CE4A0) is a pure mode-string configurator
    // with no cursor-related callees.  The game handles cursor visibility natively
    // when entering/leaving storage mode via the mode byte system.
    g_fnSetCursorVisible = 0;

    // ================================================================
    //  FALLBACK: Old pattern scans if string-xref chain failed
    // ================================================================

    if (!g_fnSetInventory) {
        static const uint8_t pSI[] = {
            0x40,0x55, 0x53, 0x56, 0x57, 0x41,0x54, 0x41,0x55, 0x41,0x56, 0x41,0x57,
            0x48,0x8D,0xAC,0x24,0x18,0xFE,0xFF,0xFF,
            0x48,0x81,0xEC,0xE8,0x02,0x00,0x00
        };
        g_fnSetInventory = ScanPattern(pSI, sizeof(pSI));
        Log("SetInventory: %s base+0x%llX (FALLBACK pattern)", g_fnSetInventory?"OK":"FAIL",
            g_fnSetInventory?(unsigned long long)(g_fnSetInventory-g_gameBase):0);
    }

    // SetInventory final-check log is handled at the resolver site above (Step 2).

    if (!g_fnHandler && g_fnSetInventory) {
        // Old handler scan: CMP [RBX],0x15 + SetInventory CALL verify + backward search
        uintptr_t searchStart = g_gameBase;
        while (searchStart < g_gameBase + g_imageSize - 3) {
            uint8_t* s = (uint8_t*)searchStart;
            uintptr_t remaining = g_gameBase + g_imageSize - searchStart;
            uintptr_t cmpAddr = 0;
            for (uintptr_t k = 0; k + 3 <= remaining; k++) {
                if (s[k]==0x80 && s[k+1]==0x3B && s[k+2]==0x15) { cmpAddr = searchStart + k; break; }
            }
            if (!cmpAddr) break;
            bool verified = false;
            for (int i = 0; i < 0x500; i++) {
                uint8_t* p = (uint8_t*)(cmpAddr + i);
                if (p[0] == 0xE8) {
                    int32_t rel = *(int32_t*)(p + 1);
                    uintptr_t target = cmpAddr + i + 5 + rel;
                    if (target == g_fnSetInventory) { verified = true; break; }
                }
            }
            if (verified) {
                g_fnHandler = FindFunctionStart(cmpAddr);
                if (g_fnHandler) break;
            }
            searchStart = cmpAddr + 1;
        }
        Log("Handler:      %s base+0x%llX (FALLBACK pattern)", g_fnHandler?"OK":"FAIL",
            g_fnHandler?(unsigned long long)(g_fnHandler-g_gameBase):0);
    }

    if (!g_fnCanShow) {
        static const uint8_t pCSEnd[] = {
            0x41,0x0F,0xB6,0x81,0x18,0x01,0x00,0x00, 0x48,0x83,0xC4,0x28, 0xC3
        };
        uintptr_t csEnd = ScanPattern(pCSEnd, sizeof(pCSEnd));
        if (csEnd) {
            for (int i = 0; i < 0x100; i++) {
                uint8_t* p = (uint8_t*)(csEnd - i);
                if (p[0]==0x48 && p[1]==0x83 && p[2]==0xEC && p[3]==0x28 &&
                    p[4]==0x48 && p[5]==0x8B && p[6]==0x41 && p[7]==0x08) {
                    g_fnCanShow = csEnd - i; break;
                }
            }
        }
        Log("CanShow:      %s base+0x%llX (FALLBACK pattern)", g_fnCanShow?"OK":"FAIL",
            g_fnCanShow?(unsigned long long)(g_fnCanShow-g_gameBase):0);
    }

    if (!g_fnSetTitle) {
        static const uint8_t pST[] = {
            0x40, 0x55, 0x53, 0x56, 0x57, 0x41, 0x56,
            0x48, 0x8D, 0xAC, 0x24, 0x70, 0xF0, 0xFF, 0xFF,
            0xB8, 0x90, 0x10, 0x00, 0x00
        };
        g_fnSetTitle = ScanPattern(pST, sizeof(pST));
        Log("SetTitle:     %s base+0x%llX (FALLBACK pattern)", g_fnSetTitle?"OK":"FAIL",
            g_fnSetTitle?(unsigned long long)(g_fnSetTitle-g_gameBase):0);
    }

    // Step 7: Find language byte dynamically
    // The Steam API init function (FUN_140487400) compares Steam's language string
    // against a table of known languages ("koreana", "english", ...) and stores the
    // matching index as a single byte in a global variable.
    // Algorithm: find "koreana" string → find pointer table → find code reference →
    // scan forward for MOV byte [rip+disp32], reg (the write to the global).
    {
        uintptr_t strKoreana = FindString("koreana");
        if (strKoreana) {
            // Find pointer to "koreana" in .rdata (first entry of the language string table)
            uint8_t* base = (uint8_t*)g_gameBase;
            uintptr_t tableAddr = 0;
            for (DWORD i = 0; i + 8 <= g_imageSize; i += 8) {
                if (*(uintptr_t*)(base + i) == strKoreana) {
                    tableAddr = g_gameBase + i;
                    break;
                }
            }
            if (tableAddr) {
                // Find code that loads from this table: [reg + reg*8 + tableDisp]
                // The displacement is tableAddr - gameBase, encoded as 4 LE bytes in the instruction
                uint32_t tableDisp = (uint32_t)(tableAddr - g_gameBase);
                uint8_t* dispBytes = (uint8_t*)&tableDisp;
                uintptr_t codeRef = 0;
                // Scan code section (first ~60% of image) for the 4-byte displacement
                DWORD codeLimit = (DWORD)(g_imageSize * 6 / 10);
                for (DWORD i = 0; i + 4 <= codeLimit; i++) {
                    if (base[i] == dispBytes[0] && base[i+1] == dispBytes[1] &&
                        base[i+2] == dispBytes[2] && base[i+3] == dispBytes[3]) {
                        codeRef = g_gameBase + i + 4;  // right after the displacement
                        break;
                    }
                }
                if (codeRef) {
                    // Scan forward for MOV byte ptr [rip+disp32], reg8
                    // Encoding: (optional REX 40-4F) 88 modrm, where modrm & 0xC7 == 0x05
                    uint8_t* scan = (uint8_t*)codeRef;
                    for (int j = 0; j < 80; j++) {
                        bool hasRex = (scan[j] >= 0x40 && scan[j] <= 0x4F);
                        int opOff = hasRex ? j + 1 : j;
                        if (scan[opOff] == 0x88 && (scan[opOff+1] & 0xC7) == 0x05) {
                            int32_t disp = *(int32_t*)(scan + opOff + 2);
                            uintptr_t addr = (uintptr_t)(scan + opOff + 6) + disp;
                            if (addr > g_gameBase && addr < g_gameBase + g_imageSize) {
                                g_langByteAddr = addr;
                                break;
                            }
                        }
                    }
                }
            }
        }
        Log("LangByte:     %s base+0x%llX (koreana table scan)", g_langByteAddr?"OK":"FAIL",
            g_langByteAddr?(unsigned long long)(g_langByteAddr-g_gameBase):0);
    }

    // HGM string slot — dynamic resolution via string-xref.
    //
    // The game has a global slot that holds a pointer-to-wrapper-struct where
    // the wrapper's first field is char* "Housing_GatheredMaterials".  Setup
    // pattern in the binary (init function called once at startup):
    //     LEA  RCX, ["Housing_GatheredMaterials"]
    //     CALL FUN_140302e70     ; wrapper allocator, returns wrapper* in RAX
    //     MOV  [rip+global], RAX ; the global IS our HGM string slot
    //
    // We find the LEA, then scan forward for the post-call MOV that writes RAX
    // into a RIP-relative global.  Falls back to the 1.06 hardcoded slot if
    // the dynamic scan fails (so existing INI behavior is preserved either way).
    g_pHGMStringSlot   = 0;
    g_fnTypeNameLookup = 0;
    {
        uintptr_t strAddr = FindString("Housing_GatheredMaterials");
        uintptr_t leaAddr = strAddr ? FindLEA(strAddr, 0) : 0;
        if (leaAddr) {
            // Walk forward from LEA looking for MOV [rip+disp32], RAX.
            // Encoding: 48 89 05 disp32  (REX.W=1, opcode 89, ModRM=05).
            // Limit scan to 0x80 bytes — the wrapper alloc CALL is right after
            // the LEA and the MOV is right after the CALL.
            for (int i = 0; i < 0x80; i++) {
                uint8_t* p = (uint8_t*)(leaAddr + i);
                if (p[0] == 0x48 && p[1] == 0x89 && p[2] == 0x05) {
                    int32_t disp = *(int32_t*)(p + 3);
                    uintptr_t slot = (uintptr_t)(p + 7) + disp;
                    if (slot >= g_gameBase && slot < g_gameBase + g_imageSize) {
                        g_pHGMStringSlot = slot;
                        break;
                    }
                }
            }
        }
        if (g_pHGMStringSlot) {
            Log("HGM string slot: OK base+0x%llX (string-xref \"Housing_GatheredMaterials\")",
                (unsigned long long)(g_pHGMStringSlot - g_gameBase));
        } else {
            Log("HGM string slot: WARN string-xref scan failed — Gatherables type-id lookup disabled (INI fallback only)");
        }
    }
    Log("Type resolver:   DISABLED (function not re-resolved; INI fallback used for housing chests)");

    // Container vtable: NOT hardcoded — auto-relearned at runtime when the
    // first chest is opened (5 consecutive sightings of the same vtable
    // pointer at handler+0x170 → adopted as canonical). Starting at 0 means
    // the very first warehouse open skips the sticky-restore path for one
    // frame, then sticky-binding kicks in normally.
    g_addrContainerVtable = 0;

    // Dynamic resolver for the InventoryInfoMgr singleton slot — scan
    // SetInventory's body for the canonical load+deref pattern:
    //   [48|4C] 8B Y disp32        mov regX, [rip+disp32]   ← singleton slot
    //                              (Y encodes dest reg: 05=rax, 0D=rcx,
    //                               15=rdx, 1D=rbx, 25=rsp(no), 2D=rbp,
    //                               35=rsi, 3D=rdi; 4C prefix extends to r8-r15)
    //   ...                        (null-check / setup) ...
    //   [48..4D] 8B Z [0x60|0x70|0x78]
    //                              mov reg, [regX+0x60/+0x70/+0x78]
    //                              (Z's rm bits must match regX's encoding,
    //                               i.e. base reg of the deref is the same
    //                               reg the singleton was loaded into)
    // The +0x60/+0x70/+0x78 fields are the channel-id hash table on the
    // manager struct (per the original RE notes). Hardcoded RVAs drift
    // every game update (1.05=0x5EF1DC0, 1.06=0x5F28400, ...); this scan
    // re-locates the slot from SetInventory itself, which is already
    // resolved via the "ShowPackageCampMoneyList" string-xref.
    // Compiler may target any of rax/rcx/rdx/rbx/rbp/rsi/rdi (1.06 used
    // rax, post-1.06 update used rcx — hardcoded `48 8B 05` matcher missed it).
    g_addrInventoryInfoMgrPtr = 0;
    if (g_fnSetInventory) {
        uint8_t* fn = (uint8_t*)g_fnSetInventory;
        const int SCAN = 0x1000;   // SetInventory body is ~3 KB; cover full prologue + first half
        for (int i = 0; i + 7 < SCAN && !g_addrInventoryInfoMgrPtr; i++) {
            uint8_t rex = fn[i];
            if (rex != 0x48 && rex != 0x4C) continue;
            if (fn[i+1] != 0x8B) continue;
            uint8_t mrmLoad = fn[i+2];
            // RIP-relative: mod=00, rm=101 → (mrm & 0xC7) == 0x05
            if ((mrmLoad & 0xC7) != 0x05) continue;
            int loadDest = ((mrmLoad >> 3) & 0x07) | ((rex == 0x4C) ? 8 : 0);
            int32_t disp = *(int32_t*)(fn + i + 3);
            uintptr_t target = (uintptr_t)(fn + i + 7) + disp;
            if (target < g_gameBase || target >= g_gameBase + g_imageSize) continue;
            // Skip targets in the .text-style executable range; we want data slots.
            // Heuristic: data slots are well past the typical code region (>0x3000000).
            if (target - g_gameBase < 0x3000000) continue;
            // Look ahead within next 96 bytes for a deref `[REX] 8B [mod=01,rm=loadDest] [0x60|0x70|0x78]`.
            // REX prefix variants 48/49/4C/4D — bit 0 (REX.B) extends rm to r8-r15.
            bool hasMatchingDeref = false;
            for (int j = i + 7; j + 3 < i + 96 && j + 3 < SCAN; j++) {
                uint8_t rd = fn[j];
                bool isRex = (rd == 0x48 || rd == 0x49 || rd == 0x4C || rd == 0x4D);
                if (!isRex || fn[j+1] != 0x8B) continue;
                uint8_t mrm = fn[j+2];
                if ((mrm & 0xC0) != 0x40) continue;
                int rm = (mrm & 0x07) | ((rd & 0x01) ? 8 : 0);
                if (rm != loadDest) continue;
                uint8_t d8 = fn[j+3];
                if (d8 == 0x60 || d8 == 0x70 || d8 == 0x78) {
                    hasMatchingDeref = true;
                    break;
                }
            }
            if (hasMatchingDeref) {
                g_addrInventoryInfoMgrPtr = target;
                Log("Inventory mgr ptr:   OK base+0x%llX (SetInventory scan @ +0x%X, dest=r%d)",
                    (unsigned long long)(target - g_gameBase), i, loadDest);
            }
        }
    }
    if (!g_addrInventoryInfoMgrPtr) {
        Log("Inventory mgr ptr:   WARN dynamic scan failed — inventory slot expansion disabled this session");
    }

    // ItemDetailModal open handler — resolved dynamically via "ItemDetailModalMessage"
    // string LEA xref. The string is referenced inside the ctor function body; we walk
    // back from the LEA to the function prologue. Eliminates the 1.06 hardcoded
    // 0xB55860 which drifted on subsequent updates (silent ABORT in hook installer
    // → "View Details" popup never detected → ESC closes warehouse instead of popup).
    g_addrItemDetailCtor = 0;
    {
        uintptr_t strModal = FindString("ItemDetailModalMessage");
        if (strModal) {
            uintptr_t leaAddr = FindLEA(strModal);
            if (leaAddr) {
                uintptr_t fnStart = FindFunctionStart(leaAddr);
                if (fnStart) {
                    g_addrItemDetailCtor = fnStart;
                    Log("ItemDetailCtor:      OK base+0x%llX (string-xref \"ItemDetailModalMessage\")",
                        (unsigned long long)(fnStart - g_gameBase));
                }
            }
        }
        if (!g_addrItemDetailCtor) {
            Log("ItemDetailCtor:      WARN string-xref failed — \"View Details\" popup detection disabled (ESC may close warehouse instead of popup)");
        }
    }

    Log("Container vtable:    auto-relearn (5 consecutive sightings at handler+0x170)");

    return g_fnHandler && g_fnModeSwitcher && g_fnCanShow && g_fnSetInventory && g_mainCharGlobalPtr;
}

static DWORD WINAPI ModThread(LPVOID) {
    for(int i=0;i<120;i++){Sleep(1000);g_gameWindow=FindGameWindow();if(g_gameWindow)break;}
    if(!g_gameWindow)return 0;
    Sleep(10000);

    char dp[MAX_PATH];GetModuleFileNameA(g_hModule,dp,MAX_PATH);
    std::string ip(dp);size_t d=ip.rfind('.');if(d!=std::string::npos)ip=ip.substr(0,d);ip+=".ini";
    strncpy(g_iniPath, ip.c_str(), MAX_PATH-1);
    LoadConfig(g_iniPath);
    if(!g_enabled)return 0;
    if(g_debugLog){std::string lp=ip.substr(0,ip.rfind('.'))+".log";g_logFile=fopen(lp.c_str(),"w");}

    Log("=== Private Storage Anywhere v1.5.10 (CD 1.13.01) ===");
    {char cls[256]={};char ttl[256]={};GetClassNameA(g_gameWindow,cls,256);GetWindowTextA(g_gameWindow,ttl,256);
    Log("Game window: class='%s' title='%s'",cls,ttl);}
    g_gameBase=(uintptr_t)GetModuleHandleA("CrimsonDesert.exe");
    if(!g_gameBase){Log("FATAL: no game base");return 0;}
    MODULEINFO mi;GetModuleInformation(GetCurrentProcess(),(HMODULE)g_gameBase,&mi,sizeof(mi));
    g_imageSize=mi.SizeOfImage;
    Log("Base: 0x%llX  Size: 0x%X  LegacyHotkey: 0x%02X",
        (unsigned long long)g_gameBase, g_imageSize, g_hotkey);
    for (int i = 0; i < PANEL_COUNT; i++) {
        Log("  Panel[%d] %-12s: kb=0x%02X mod=0x%02X xi=0x%04X xiMod=0x%04X "
            "psBtn=(off=%d,mask=0x%02X) psMod=(off=%d,mask=0x%02X)",
            i, g_panels[i].name,
            g_panels[i].hotkey, g_panels[i].modifier,
            g_panels[i].controllerButton, g_panels[i].controllerModifier,
            g_panels[i].psButtonByteOff, g_panels[i].psButtonBitMask,
            g_panels[i].psModifierByteOff, g_panels[i].psModifierBitMask);
    }

    // Hash meta/0.papgt to detect modded game files (JSON mods etc.)
    // Find game root by locating \bin64\ in the DLL path (works regardless of subdirectory depth)
    {
        std::string metaPath(dp);
        size_t bin64pos = metaPath.rfind("\\bin64\\");
        if (bin64pos == std::string::npos)
            bin64pos = metaPath.rfind("\\bin64");  // DLL directly in bin64 (no trailing subdir)
        if (bin64pos != std::string::npos)
            metaPath = metaPath.substr(0, bin64pos);
        else {
            // Fallback: strip filename + one dir (legacy layout)
            size_t bs = metaPath.rfind('\\');
            if (bs != std::string::npos) metaPath = metaPath.substr(0, bs);
            bs = metaPath.rfind('\\');
            if (bs != std::string::npos) metaPath = metaPath.substr(0, bs);
        }
        metaPath += "\\meta\\0.papgt";
        uint32_t crc = FileCRC32(metaPath.c_str());
        if (crc) Log("meta/0.papgt CRC32: %08X", crc);
        else     Log("meta/0.papgt: NOT FOUND");
    }

    if(!ResolveAddresses()){Log("FATAL: pattern scan failed");return 0;}

    // Compute hook size: find clean instruction boundary >= 14 bytes; fall
    // back to fixed 15 if the decoder bails on an unknown opcode. Local —
    // original bytes for cleanup are recorded by InstallHook into g_hookTable.
    int hookSizeHandler = FindPrologBoundary((uint8_t*)g_fnHandler, 14);
    if (hookSizeHandler < 14) hookSizeHandler = 15;

    if(!InstallHook(g_fnHandler,(uintptr_t)&CaptureOnHandler,"Handler",hookSizeHandler)) return 0;
    // ModeSwitcher hook removed: mainChar is now resolved via singleton global,
    // and the dispatcher function has a different signature (4 args, not 1).
    if(!InstallCanShowHook(g_fnCanShow)) return 0;

    // ItemDetailOpen hook — 1.06 target is FUN_140b55860 (verified via the
    // "ItemDetailModalMessage" string LEA xref at +0xb55946). The hook
    // increments g_itemDetailActiveCount so ESC/B/Circle close the popup
    // first instead of closing the warehouse.
    if (g_addrItemDetailCtor) {
        if (!InstallHook(g_addrItemDetailCtor, (uintptr_t)&CaptureOnItemDetailCtor,
                         "ItemDetailOpen")) {
            Log("ItemDetailOpen hook FAILED — popup won't be detected");
        }
    }

    // -------- TraceMode: install diagnostic hooks on the natural NPC-open
    // pipeline so we can see the exact sequence Pearl Abyss runs in CD 1.10
    // when a player opens the warehouse the official way. Addresses are
    // hard-coded from Ghidra analysis of the 1.10 binary; if the user moves
    // to a different build we should re-verify these (the symptom would be
    // either a HOOK ABORT log line or a crash on the first natural open).
    if (g_traceMode) {
        Log("TraceMode ENABLED — installing 8 diagnostic hooks (Init/Show/ShowFocus/ShowSimple/PanelDescShow/Dtor/Binder/RegGet)");
        uintptr_t addrInit       = g_gameBase + 0xAA39E0;   // FUN_140AA39E0 — vtable[1]  Init
        uintptr_t addrShow       = g_gameBase + 0xA9F4E0;   // FUN_140A9F4E0 — vtable[51] Show (sink)
        uintptr_t addrShowFocus  = g_gameBase + 0xAA3BF0;   // FUN_140AA3BF0 — Show + focus + SetInventoryName wrapper
        uintptr_t addrShowSimple = g_gameBase + 0xA9D4A0;   // FUN_140A9D4A0 — Show + focus only wrapper
        uintptr_t addrDesc       = g_gameBase + 0x346A3E0;  // FUN_14346A3E0 — panel-desc show primitive
        uintptr_t addrDtor       = g_gameBase + 0xAA3910;   // FUN_140AA3910 — Warehouse2 deleting destructor
        uintptr_t addrBinder     = g_gameBase + 0xA9C820;   // FUN_140A9C820 — master widget binder (sets +0x2CD=1)
        uintptr_t addrRegGet     = g_gameBase + 0x1004DE0;  // FUN_141004DE0 — panel-descriptor registry getter
        if (!InstallHook(addrInit,       (uintptr_t)&TraceOnWarehouseInit,       "Trace.WhInit"))
            Log("Trace.WhInit hook FAILED — Init calls will not be logged");
        if (!InstallHook(addrShow,       (uintptr_t)&TraceOnWarehouseShow,       "Trace.WhShow"))
            Log("Trace.WhShow hook FAILED — Show-sink calls will not be logged");
        if (!InstallHook(addrShowFocus,  (uintptr_t)&TraceOnWarehouseShowFocus,  "Trace.WhShowFocus"))
            Log("Trace.WhShowFocus hook FAILED — ShowFocus wrapper calls will not be logged");
        if (!InstallHook(addrShowSimple, (uintptr_t)&TraceOnWarehouseShowSimple, "Trace.WhShowSimple"))
            Log("Trace.WhShowSimple hook FAILED — ShowSimple wrapper calls will not be logged");
        if (!InstallHook(addrDesc,       (uintptr_t)&TraceOnPanelDescShow,       "Trace.PanelDescShow"))
            Log("Trace.PanelDescShow hook FAILED — descriptor show calls will not be logged");
        if (!InstallHook(addrDtor,       (uintptr_t)&TraceOnWarehouseDtor,       "Trace.WhDtor"))
            Log("Trace.WhDtor hook FAILED — instance destruction will not be logged");
        if (!InstallHook(addrBinder,     (uintptr_t)&TraceOnWarehouseBinder,     "Trace.WhBinder"))
            Log("Trace.WhBinder hook FAILED — master widget binder calls will not be logged");
        // FUN_141004DE0 is tiny (likely just MOV+RET); InstallHook may abort
        // on prolog-too-short. Log the failure but keep going.
        if (!InstallHook(addrRegGet,     (uintptr_t)&TraceOnPanelRegistryGet,    "Trace.RegGet"))
            Log("Trace.RegGet hook FAILED (likely prolog < 14 bytes) — registry-getter callers will not be logged");

        // Read-only: dump 8 slots of the panel-descriptor vtable shared by
        // WareHouse and CampWareHouse (base+0x4BC1028). One of these slots is
        // the spawn-instance method natural NPC-open uses. Knowing its RVA
        // lets a future iteration call it directly from F-key. The SEH-
        // wrapped read lives in TraceDumpDescriptorVtable() because MSVC
        // forbids __try in ModThread (it has C++ unwind objects).
        TraceDumpDescriptorVtable();
    }

    // Resolve mainChar immediately from singleton (no need to wait for hook callback)
    {
        uintptr_t mc = ResolveMainChar();
        if (mc > 0x10000000000ULL) {
            InterlockedExchange64(&g_mainChar, (LONG64)mc);
            Log("mainChar: 0x%llX (singleton)", (unsigned long long)mc);
        } else {
            Log("mainChar: DEFERRED (singleton not ready yet)");
        }
    }

    InitXInput();

    // IAT-hook the game's XInputGetState so its own polling never sees
    // mod-bound combos or B-while-warehouse-open. Mod's own poll uses
    // g_pXInputGetState (direct DLL export) which bypasses the IAT.
    InstallXInputIATHook((HMODULE)g_gameBase);

    if(!IsWindow(g_gameWindow)){
        g_gameWindow=FindGameWindow();
        if(!g_gameWindow||!IsWindow(g_gameWindow)){Log("FATAL: game window invalid before WndProc hook");return 0;}
    }
    SetLastError(0);
    g_originalWndProc=(WNDPROC)SetWindowLongPtrA(g_gameWindow,GWLP_WNDPROC,(LONG_PTR)HookedWndProc);
    if(!g_originalWndProc&&GetLastError()!=0){Log("FATAL: WndProc hook failed (error=%lu)",GetLastError());return 0;}

    // Register for HID Gamepad raw input so we receive WM_INPUT for controllers
    // The game reads HID directly (ReadFile) so no WM_INPUT for gamepads arrives by default
    RAWINPUTDEVICE rid[2] = {};
    // Usage Page 0x01 = Generic Desktop, Usage 0x05 = Game Pad
    rid[0].usUsagePage = 0x01;
    rid[0].usUsage     = 0x05;
    rid[0].dwFlags     = RIDEV_INPUTSINK;  // receive even when not focused
    rid[0].hwndTarget  = g_gameWindow;
    // Usage Page 0x01 = Generic Desktop, Usage 0x04 = Joystick (some controllers report as joystick)
    rid[1].usUsagePage = 0x01;
    rid[1].usUsage     = 0x04;
    rid[1].dwFlags     = RIDEV_INPUTSINK;
    rid[1].hwndTarget  = g_gameWindow;
    RegisterRawInputDevices(rid, 2, sizeof(RAWINPUTDEVICE));

    g_ready=true;
    CreateThread(nullptr,0,InputThread,nullptr,0,nullptr);

    // ------- TraceMode diagnostic: PollerThread -------
    // 1.10 broke the mod because the natural NPC-open path doesn't go
    // through the Warehouse2 vtable functions we hook (Init/Show/...).
    // The captured warehouse stays in shell state forever even when
    // the player opens a chest at the NPC and the UI clearly renders.
    // Hypothesis: either NPC-open uses a DIFFERENT instance, or it sets
    // fields we don't watch. This poller answers both questions:
    //   (A) every 1s, snapshot the captured warehouse's key fields, log
    //       only when something changes. A natural NPC-open will produce
    //       a CHANGED log line if it touches the captured instance.
    //   (B) every 5s, HeapWalk all process heaps and find every other
    //       allocation whose first 8 bytes match g_warehouseVtableStart.
    //       Log every new instance + state changes. A natural NPC-open
    //       that uses a different instance will produce a NEW INSTANCE
    //       log line. Bounded to keep frame-time low.
    if (g_traceMode) {
        CreateThread(nullptr, 0, [](LPVOID) -> DWORD {
            Sleep(15000);
            Log("[POLL] PollerThread started (1s captured-diff, 5s heap-scan)");

            struct Snap {
                uintptr_t s120=0xCAFE, s128=0xCAFE, s218=0xCAFE, s270=0xCAFE,
                          s290=0xCAFE, s300=0xCAFE;
                uint8_t   s2CD=0xCD;
                bool      init=false;
            };
            auto readSnap = [](uintptr_t inst, Snap& out) -> bool {
                if (!inst) return false;
                __try {
                    out.s120 = *(uintptr_t*)(inst + 0x120);
                    out.s128 = *(uintptr_t*)(inst + 0x128);
                    out.s218 = *(uintptr_t*)(inst + 0x218);
                    out.s270 = *(uintptr_t*)(inst + 0x270);
                    out.s290 = *(uintptr_t*)(inst + 0x290);
                    out.s300 = *(uintptr_t*)(inst + 0x300);
                    out.s2CD = *(uint8_t*)(inst + 0x2CD);
                    return true;
                } __except(EXCEPTION_EXECUTE_HANDLER) { return false; }
            };
            auto differs = [](const Snap& a, const Snap& b) -> bool {
                return a.s120!=b.s120 || a.s128!=b.s128 || a.s218!=b.s218 ||
                       a.s270!=b.s270 || a.s290!=b.s290 || a.s300!=b.s300 ||
                       a.s2CD!=b.s2CD;
            };
            auto logSnap = [](uintptr_t inst, const char* tag, const Snap& s) {
                Log("[POLL] %s this=0x%llX +0x120=0x%llX +0x128=0x%llX "
                    "+0x218=0x%llX +0x270=0x%llX +0x290=0x%llX +0x2CD=%u +0x300=0x%llX",
                    tag, (unsigned long long)inst,
                    (unsigned long long)s.s120, (unsigned long long)s.s128,
                    (unsigned long long)s.s218, (unsigned long long)s.s270,
                    (unsigned long long)s.s290, (unsigned)s.s2CD,
                    (unsigned long long)s.s300);
            };

            Snap capturedPrev;
            struct Tracked { uintptr_t addr; Snap snap; };
            constexpr size_t MAX_TRACKED = 32;
            Tracked tracked[MAX_TRACKED] = {};
            size_t trackedCount = 0;

            int cycle = 0;
            while (!InterlockedCompareExchange(&g_shutdown, 0, 0)) {
                Sleep(1000);
                cycle++;

                // (A) Captured-warehouse state diff
                uintptr_t captured = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
                if (captured) {
                    Snap now;
                    if (readSnap(captured, now)) {
                        if (!capturedPrev.init) {
                            capturedPrev = now; capturedPrev.init = true;
                            logSnap(captured, "captured INITIAL", now);
                        } else if (differs(capturedPrev, now)) {
                            logSnap(captured, "captured CHANGED", now);
                            capturedPrev = now;
                        }
                    }
                }

                // (B) Heap-scan every 5 cycles
                if (cycle % 5 != 0) continue;
                if (!g_warehouseVtableStart) continue;

                DWORD numHeaps = GetProcessHeaps(0, nullptr);
                if (numHeaps == 0 || numHeaps > 64) continue;
                HANDLE heaps[64] = {};
                DWORD got = GetProcessHeaps(numHeaps, heaps);
                if (got == 0 || got > 64) continue;

                size_t foundThisScan = 0;
                bool newInstanceLogged = false;
                for (DWORD i = 0; i < got; i++) {
                    if (!heaps[i]) continue;
                    if (!HeapLock(heaps[i])) continue;
                    PROCESS_HEAP_ENTRY entry = {};
                    int walks = 0;
                    while (walks < 200000) {
                        BOOL ok = FALSE;
                        __try { ok = HeapWalk(heaps[i], &entry); }
                        __except(EXCEPTION_EXECUTE_HANDLER) { ok = FALSE; }
                        if (!ok) break;
                        walks++;
                        if (!(entry.wFlags & PROCESS_HEAP_ENTRY_BUSY)) continue;
                        if (entry.cbData < 0x400) continue;
                        uintptr_t obj = 0, vt = 0;
                        __try {
                            obj = (uintptr_t)entry.lpData;
                            vt  = *(uintptr_t*)obj;
                        } __except(EXCEPTION_EXECUTE_HANDLER) { continue; }
                        if (vt != g_warehouseVtableStart) continue;

                        foundThisScan++;
                        // Find or insert
                        size_t slot = trackedCount;
                        for (size_t j = 0; j < trackedCount; j++) {
                            if (tracked[j].addr == obj) { slot = j; break; }
                        }
                        if (slot == trackedCount) {
                            if (trackedCount >= MAX_TRACKED) continue;
                            tracked[trackedCount].addr = obj;
                            readSnap(obj, tracked[trackedCount].snap);
                            tracked[trackedCount].snap.init = true;
                            logSnap(obj, "NEW INSTANCE", tracked[trackedCount].snap);
                            trackedCount++;
                            newInstanceLogged = true;
                        } else {
                            Snap now;
                            if (readSnap(obj, now) && differs(tracked[slot].snap, now)) {
                                logSnap(obj, "INSTANCE CHANGED", now);
                                tracked[slot].snap = now;
                                newInstanceLogged = true;
                            }
                        }
                    }
                    HeapUnlock(heaps[i]);
                }
                if (newInstanceLogged || (cycle % 60 == 0)) {
                    Log("[POLL] Heap-scan cycle %d: %zu Warehouse2 instances live (tracked %zu)",
                        cycle, foundThisScan, trackedCount);
                }
            }
            return 0;
        }, nullptr, 0, nullptr);
    }

    // ------- CD 1.10 capture-only: render-gate (+0x2CD) watcher -------
    // Read-only. The warehouse panel renders only when controller+0x2CD == 1
    // (the Binder sets it once the view is mounted; Show is a no-op while 0).
    // The mod captures the real controller into g_handlerThis when the game
    // calls its Handler (a real world-object open does this). We poll that
    // controller's render gate + the fields that gate the mount, and log ONE
    // line whenever +0x2CD changes. Opening the warehouse via the WORLD OBJECT
    // (which DOES render) will flip +0x2CD 0->1 and reveal exactly which
    // companion fields the mount sets — the precursor we must reproduce.
    // No writes, SEH-guarded. Runs only when DebugLog is on.
    if (g_debugLog) {
        CreateThread(nullptr, 0, [](LPVOID) -> DWORD {
            uint8_t lastGate = 0xFF;
            while (!InterlockedCompareExchange(&g_shutdown, 0, 0)) {
                Sleep(250);
                uintptr_t ctrl = (uintptr_t)InterlockedCompareExchange64(&g_handlerThis, 0, 0);
                if (!ctrl) continue;
                __try {
                    uint8_t   gate = *(uint8_t*)(ctrl + 0x2CD);
                    if (gate != lastGate) {
                        uintptr_t s218 = *(uintptr_t*)(ctrl + 0x218);
                        uintptr_t s120 = *(uintptr_t*)(ctrl + 0x120);
                        uint8_t   s128 = *(uint8_t*)(ctrl + 0x128);
                        uint8_t   s2cc = *(uint8_t*)(ctrl + 0x2CC);
                        uint8_t   s2ca = *(uint8_t*)(ctrl + 0x2CA);
                        uintptr_t s1b0 = *(uintptr_t*)(ctrl + 0x1B0);
                        Log("[CAP] +0x2CD %u->%u  +0x218=0x%llX +0x120=0x%llX "
                            "+0x128=%u +0x2CC=%u +0x2CA=%u +0x1B0=0x%llX active=%ld",
                            (unsigned)lastGate, (unsigned)gate,
                            (unsigned long long)s218, (unsigned long long)s120,
                            (unsigned)s128, (unsigned)s2cc, (unsigned)s2ca,
                            (unsigned long long)s1b0,
                            (long)InterlockedCompareExchange(&g_warehouseActive, 0, 0));
                        lastGate = gate;
                    }
                } __except(EXCEPTION_EXECUTE_HANDLER) {}
            }
            return 0;
        }, nullptr, 0, nullptr);
    }


    // scan, see g_addrInventoryInfoMgrPtr resolver above) and rewrites every
    // InventoryInfo+0x48 with value 10 to 1000 — this is the *real* slot-
    // count field consumed by the UI. Manager loads some time after the
    // binary maps; poll once per second until we see a non-zero patch count,
    // then keep checking every 3s in case a save-load / teleport reset reverts
    // the values (the open path re-patches synchronously too — this worker is
    // the safety net for boxes opened at their real in-game chest). If the
    // singleton resolver failed at boot, the patch is
    // permanently unavailable this session — don't spawn the worker at all
    // instead of busy-spinning at 1 Hz forever.
    if (g_addrInventoryInfoMgrPtr) {
        CreateThread(nullptr, 0, [](LPVOID) -> DWORD {
            bool firstApplied = false;
            for (;;) {
                if (InterlockedCompareExchange(&g_shutdown, 0, 0)) return 0;
                int n = PatchInventoryInfoSlots();
                if (n > 0) {
                    if (!firstApplied) {
                        Log("InventoryInfo slot patch: %d entries default 10 -> 1000", n);
                        firstApplied = true;
                    } else {
                        Log("InventoryInfo slot patch: re-applied to %d entries (post-reload)", n);
                    }
                }
                Sleep(firstApplied ? 3000 : 1000);
            }
            return 0;
        }, nullptr, 0, nullptr);
    } else {
        Log("InventoryInfo worker: NOT STARTED (resolver failed at boot — slot expansion disabled)");
    }

    Log("=== READY! Press F6 to open Private Storage from anywhere ===");
    return 0;
}

BOOL APIENTRY DllMain(HMODULE h,DWORD r,LPVOID){
    if(r==DLL_PROCESS_ATTACH){g_hModule=h;DisableThreadLibraryCalls(h);CreateThread(nullptr,0,ModThread,nullptr,0,nullptr);}
    else if(r==DLL_PROCESS_DETACH){
        // Signal worker threads to exit BEFORE we touch shared resources.
        // We cannot WaitForSingleObject here (loader-lock deadlock risk),
        // so this is best-effort: workers next wakeup will see the flag.
        InterlockedExchange(&g_shutdown, 1);
        if(g_gameWindow&&g_originalWndProc)SetWindowLongPtrA(g_gameWindow,GWLP_WNDPROC,(LONG_PTR)g_originalWndProc);
        RemoveXInputIATHook();
        // Restore original bytes for every installed hook so a DLL unload
        // (hot-reload of the ASI) leaves the game in a clean state. The
        // table is populated by InstallHook + InstallCanShowHook.
        DWORD op;
        for (int i = 0; i < g_hookCount; i++) {
            HookEntry& e = g_hookTable[i];
            if (!e.addr || e.size <= 0) continue;
            VirtualProtect((void*)e.addr, e.size, PAGE_EXECUTE_READWRITE, &op);
            memcpy((void*)e.addr, e.orig, e.size);
            VirtualProtect((void*)e.addr, e.size, op, &op);
            FlushInstructionCache(GetCurrentProcess(), (void*)e.addr, e.size);
        }
        if(g_hXInput){FreeLibrary(g_hXInput);g_hXInput=nullptr;}
        if(g_logFile){
            FILE* lf = g_logFile;
            g_logFile = nullptr;  // gate Log() before fclose so racing worker writes are no-ops
            fprintf(lf, "=== Unloaded (hooks restored) ===\n");
            fclose(lf);
        }
    }
    return TRUE;
}
