-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Machine
import SeLe4n.Model.Object
import SeLe4n.Platform.Boot
import SeLe4n.Platform.RPi5.Board
import SeLe4n.Platform.RPi5.MmioAdapter
import SeLe4n.Platform.RPi5.BootContract
import SeLe4n.Platform.RPi5.RuntimeContract
import SeLe4n.Platform.RPi5.VSpaceBoot
import SeLe4n.Platform.Sim.BootContract
import SeLe4n.Platform.DeviceTree
import SeLe4n.Platform.FFI
import SeLe4n.Testing.Helpers

/-! # AK9 Platform Regression Suite — Phase AK9 audit remediation

Runtime regression checks for the AK9 Platform / Boot / DTB / MMIO
audit findings of WS-AN (see the *Workstream registry* of
`docs/REGISTERED_DEBT.md`, closed at `v0.30.11`):

- **AK9-A (P-H01)** — `mmioRead32` / `mmioRead64` enforce 4/8-byte
  alignment AND region-local bounds.
- **AK9-B (P-H02)** — `BootBoundaryContract.objectStoreEmptyAtBoot`
  renamed field asserts empty object store at boot.
- **AK9-C (P-M01)** — `irqHandlersReferenceNotifications` validates
  each IRQ handler ObjId refers to a notification object.
- **AK9-D (P-M02)** — `isDeviceRangeWithinRegion` tightens multi-byte
  write range to a single declared device region.
- **AK9-E (P-M03)** — `budgetSufficientCheck` fails closed on
  missing / wrong-variant SchedContext bindings.
- **AK9-F (P-M04/M05/M07)** — `classifyMemoryRegionChecked`,
  `applyMachineConfigChecked`, `findMemoryRegPropertyChecked`.
- **AK9-G (P-M06)** — `bootEnableInterruptsOp` mirrors HAL Phase 3.
-/

open SeLe4n
open SeLe4n.Model
open SeLe4n.Platform
open SeLe4n.Platform.RPi5
open SeLe4n.Platform.Boot
open SeLe4n.Platform.FFI
open SeLe4n.Testing

namespace SeLe4n.Testing.Ak9PlatformSuite

private def tag : String := "ak9-platform"

private def expect (label : String) (cond : Bool) : IO Unit :=
  expectCond tag label cond

-- ============================================================================
-- AK9-A: mmioRead32 / mmioRead64 alignment and range rejection
-- ============================================================================

/-- AK9-A: `mmioRead32` rejects a misaligned address with `.mmioUnaligned`. -/
def ak9a_01_mmioRead32_rejects_unaligned : IO Unit := do
  -- GIC distributor base + 2 is misaligned for a 32-bit read.
  let addr : PAddr := PAddr.ofNat (gicDistributorBase.toNat + 2)
  let st : SystemState := default
  -- Use the alignment predicate to drive the proof that this addr is unaligned.
  expect "AK9-A-01 mmioRead32 rejects unaligned"
    (match mmioRead32 addr st with
     | .error .mmioUnaligned => true
     | _ => false)

/-- AK9-A: `mmioRead64` rejects a misaligned address. -/
def ak9a_02_mmioRead64_rejects_unaligned : IO Unit := do
  let addr : PAddr := PAddr.ofNat (gicDistributorBase.toNat + 4)  -- 4-aligned, not 8
  let st : SystemState := default
  expect "AK9-A-02 mmioRead64 rejects unaligned"
    (match mmioRead64 addr st with
     | .error .mmioUnaligned => true
     | _ => false)

/-- AK9-A: `mmioRead32` rejects non-device addresses (e.g., RAM). -/
def ak9a_03_mmioRead32_rejects_ram : IO Unit := do
  -- An aligned address in the RAM region (base 0x0).
  let addr : PAddr := PAddr.ofNat 0x1000
  let st : SystemState := default
  expect "AK9-A-03 mmioRead32 rejects RAM address"
    (match mmioRead32 addr st with
     | .error .policyDenied => true
     | _ => false)

/-- AK9-A: `mmioRead32` succeeds on a valid GIC distributor address. -/
def ak9a_04_mmioRead32_accepts_gic : IO Unit := do
  let addr : PAddr := gicDistributorBase
  let st : SystemState := default
  expect "AK9-A-04 mmioRead32 accepts GIC distributor base"
    (match mmioRead32 addr st with
     | .ok _ => true
     | _ => false)

-- ============================================================================
-- AK9-D: isDeviceRangeWithinRegion region-local check
-- ============================================================================

/-- AK9-D: `isDeviceRangeWithinRegion` accepts a 4-byte range inside GIC dist. -/
def ak9d_01_range_within_gic_dist : IO Unit := do
  expect "AK9-D-01 4-byte range within GIC dist"
    (isDeviceRangeWithinRegion gicDistributorBase 4 = true)

/-- AK9-D: `isDeviceRangeWithinRegion` rejects a range that straddles the
    end of the RPi5 peripheral `.device` window into the following
    `.reserved` region. The peripheral window is
    `[0xFE000000, 0xFF850000)` in `rpi5MachineConfig.memoryMap`; a read
    starting 4 bytes before the end would extend past it. -/
def ak9d_02_range_crosses_boundary : IO Unit := do
  -- Peripheral window end = 0xFE000000 + 0x01850000 = 0xFF850000.
  -- Start 4 bytes before end, ask for 16 bytes → crosses into reserved.
  let addr : PAddr := PAddr.ofNat 0xFF84FFFC
  expect "AK9-D-02 cross-region range rejected"
    (isDeviceRangeWithinRegion addr 16 = false)

-- ============================================================================
-- AK9-B: objectStoreEmptyAtBoot rename
-- ============================================================================

/-- AK9-B: Sim boot contract's new-named predicate holds. -/
def ak9b_01_sim_objectStoreEmptyAtBoot : IO Unit := do
  -- The witness is a Prop — presence at compile-time is the check.
  let _ : Sim.simBootContract.objectStoreEmptyAtBoot :=
    Sim.simBootContract_objectStoreEmptyAtBoot_holds
  expect "AK9-B-01 sim objectStoreEmptyAtBoot" true

/-- AK9-B: RPi5 boot contract's new-named predicate holds. -/
def ak9b_02_rpi5_objectStoreEmptyAtBoot : IO Unit := do
  let _ : rpi5BootContract.objectStoreEmptyAtBoot :=
    rpi5BootContract_objectStoreEmptyAtBoot_holds
  expect "AK9-B-02 rpi5 objectStoreEmptyAtBoot" true

-- ============================================================================
-- AK9-C: irqHandlersReferenceNotifications
-- ============================================================================

/-- AK9-C: Empty IRQ table trivially passes handler-reference check. -/
def ak9c_01_empty_irqs_accepted : IO Unit := do
  let cfg : PlatformConfig := { irqTable := [], initialObjects := [] }
  expect "AK9-C-01 empty irqTable passes"
    (irqHandlersReferenceNotifications cfg = true)

/-- AK9-C: IRQ with missing handler ObjId rejected. -/
def ak9c_02_missing_handler_rejected : IO Unit := do
  -- IRQ pointing to ObjId 42 which does not exist in initialObjects.
  let cfg : PlatformConfig :=
    { irqTable := [{ irq := ⟨1⟩, handler := ObjId.ofNat 42 }],
      initialObjects := [] }
  expect "AK9-C-02 missing handler rejected"
    (irqHandlersReferenceNotifications cfg = false)

private def minimalNotif : Notification :=
  { state := .idle, waitingThreads := SeLe4n.NoDupList.empty }

private def minimalTcb (tid : ThreadId) : TCB :=
  { tid := tid
    priority := ⟨0⟩
    domain := ⟨0⟩
    cspaceRoot := ⟨0⟩
    vspaceRoot := ⟨0⟩
    ipcBuffer := (SeLe4n.VAddr.ofNat 0) }

private def mkNotifObjectEntry (oid : ObjId) : ObjectEntry :=
  { id := oid
    obj := .notification minimalNotif
    hSlots := fun cn h => by cases h
    hMappings := fun vs h => by cases h }

private def mkTcbObjectEntry (oid : ObjId) : ObjectEntry :=
  { id := oid
    obj := .tcb (minimalTcb ⟨oid.toNat⟩)
    hSlots := fun cn h => by cases h
    hMappings := fun vs h => by cases h }

/-- AK9-C: IRQ handler pointing to a non-notification object is rejected. -/
def ak9c_03_non_notification_rejected : IO Unit := do
  let oid : ObjId := ObjId.ofNat 10
  let cfg : PlatformConfig :=
    { irqTable := [{ irq := ⟨1⟩, handler := oid }],
      initialObjects := [mkTcbObjectEntry oid] }
  expect "AK9-C-03 TCB handler rejected"
    (irqHandlersReferenceNotifications cfg = false)

/-- AK9-C: IRQ handler pointing to a notification object is accepted. -/
def ak9c_04_notification_accepted : IO Unit := do
  let oid : ObjId := ObjId.ofNat 10
  let cfg : PlatformConfig :=
    { irqTable := [{ irq := ⟨1⟩, handler := oid }],
      initialObjects := [mkNotifObjectEntry oid] }
  expect "AK9-C-04 notification handler accepted"
    (irqHandlersReferenceNotifications cfg = true)

-- ============================================================================
-- AK9-F: classifyMemoryRegionChecked + applyMachineConfigChecked
--         + findMemoryRegPropertyChecked
-- ============================================================================

/-- AK9-F (P-M04): Empty platform map → `classifyMemoryRegionChecked` = none. -/
def ak9f_01_classify_empty_map : IO Unit := do
  let fdtRegion : FdtMemoryRegion := { base := 0x1000, size := 0x1000 }
  expect "AK9-F-01 classifyChecked empty map rejected"
    (classifyMemoryRegionChecked fdtRegion [] = none)

/-- AK9-F (P-M04): Non-empty map with address unmapped → none. -/
def ak9f_02_classify_unmapped : IO Unit := do
  let fdtRegion : FdtMemoryRegion := { base := 0xDEAD_0000, size := 0x1000 }
  let pm : List MemoryRegion :=
    [{ base := (SeLe4n.PAddr.ofNat 0x0), size := 0x1000, kind := .ram }]
  expect "AK9-F-02 classifyChecked unmapped rejected"
    (classifyMemoryRegionChecked fdtRegion pm = none)

/-- AK9-F (P-M04): Non-empty map with address in region → some kind. -/
def ak9f_03_classify_mapped : IO Unit := do
  let fdtRegion : FdtMemoryRegion := { base := 0x500, size := 0x100 }
  let pm : List MemoryRegion :=
    [{ base := (SeLe4n.PAddr.ofNat 0x0), size := 0x1000, kind := .ram }]
  expect "AK9-F-03 classifyChecked mapped returns kind"
    (classifyMemoryRegionChecked fdtRegion pm = some .ram)

/-- AK9-F (P-M05): `applyMachineConfigChecked` rejects malformed config
    (physicalAddressWidth = 0 fails MachineConfig.wellFormed). -/
def ak9f_04_applyMachineConfigChecked_rejects_zero_pa : IO Unit := do
  let ist : IntermediateState := mkEmptyIntermediateState
  let bad : MachineConfig := { defaultMachineConfig with physicalAddressWidth := 0 }
  let result := applyMachineConfigChecked ist bad
  expect "AK9-F-04 applyChecked rejects PA width = 0"
    (match result with | .error _ => true | _ => false)

/-- AK9-F (P-M05): `applyMachineConfigChecked` rejects `physicalAddressWidth > 52`. -/
def ak9f_05_applyMachineConfigChecked_rejects_pa_over_52 : IO Unit := do
  let ist : IntermediateState := mkEmptyIntermediateState
  let bad : MachineConfig := { defaultMachineConfig with physicalAddressWidth := 64 }
  let result := applyMachineConfigChecked ist bad
  expect "AK9-F-05 applyChecked rejects PA width > 52"
    (match result with | .error _ => true | _ => false)

/-- AK9-F (P-M05): `applyMachineConfigChecked` accepts default config. -/
def ak9f_06_applyMachineConfigChecked_accepts_default : IO Unit := do
  let ist : IntermediateState := mkEmptyIntermediateState
  let result := applyMachineConfigChecked ist defaultMachineConfig
  expect "AK9-F-06 applyChecked accepts defaultMachineConfig"
    (match result with | .ok _ => true | _ => false)

-- ============================================================================
-- AK9-G: bootEnableInterruptsOp mirrors HAL Phase 3
-- ============================================================================

/-- AK9-G: `bootEnableInterruptsOp` sets interruptsEnabled = true. -/
def ak9g_01_enables_interrupts : IO Unit := do
  let ist := bootFromPlatform { irqTable := [], initialObjects := [] }
  let after := bootEnableInterruptsOp ist
  expect "AK9-G-01 bootEnableInterruptsOp enables IRQs"
    (after.state.machine.interruptsEnabled = true)

/-- AK9-G: Default `bootFromPlatform` leaves interrupts disabled. -/
def ak9g_02_default_disabled : IO Unit := do
  let ist := bootFromPlatform { irqTable := [], initialObjects := [] }
  expect "AK9-G-02 bootFromPlatform default disabled"
    (ist.state.machine.interruptsEnabled = false)

/-- AK9-G: Full HAL-parity boot yields interrupts enabled. -/
def ak9g_03_withInterrupts_enables : IO Unit := do
  let ist := bootFromPlatformWithInterrupts { irqTable := [], initialObjects := [] }
  expect "AK9-G-03 bootFromPlatformWithInterrupts enables IRQs"
    (ist.state.machine.interruptsEnabled = true)

-- ============================================================================
-- End-to-end: bootFromPlatformChecked wires AK9-C, AK9-F, AK9-G together
-- ============================================================================

/-- AK9-C (end-to-end): `bootFromPlatformChecked` REJECTS a config whose IRQ
    handler references a non-existent ObjId. This exercises the full
    production check chain, not just the predicate. -/
def ak9ce_01_checked_boot_rejects_bad_irq : IO Unit := do
  let cfg : PlatformConfig :=
    { irqTable := [{ irq := ⟨1⟩, handler := ObjId.ofNat 99 }],
      initialObjects := [] }
  expect "AK9-CE-01 checked boot rejects bad IRQ"
    (match bootFromPlatformChecked cfg with
     | .error _ => true
     | .ok _ => false)

/-- AK9-C (end-to-end): `bootFromPlatformChecked` REJECTS when handler
    ObjId resolves to a non-notification variant (TCB). -/
def ak9ce_02_checked_boot_rejects_tcb_handler : IO Unit := do
  let oid : ObjId := ObjId.ofNat 5
  let cfg : PlatformConfig :=
    { irqTable := [{ irq := ⟨1⟩, handler := oid }],
      initialObjects := [mkTcbObjectEntry oid] }
  expect "AK9-CE-02 checked boot rejects TCB handler"
    (match bootFromPlatformChecked cfg with
     | .error _ => true
     | .ok _ => false)

/-- AK9-F (end-to-end): `bootFromPlatformChecked` REJECTS a config whose
    `machineConfig.physicalAddressWidth` exceeds 52. -/
def ak9fe_01_checked_boot_rejects_pa_over_52 : IO Unit := do
  let cfg : PlatformConfig :=
    { irqTable := [], initialObjects := [],
      machineConfig := { defaultMachineConfig with physicalAddressWidth := 64 } }
  expect "AK9-FE-01 checked boot rejects PA width > 52"
    (match bootFromPlatformChecked cfg with
     | .error _ => true
     | .ok _ => false)

/-- AK9-F (end-to-end): `bootFromPlatformChecked` REJECTS a config with a
    malformed MachineConfig (page size 0 fails `wellFormed`). -/
def ak9fe_02_checked_boot_rejects_malformed_machine_config : IO Unit := do
  let cfg : PlatformConfig :=
    { irqTable := [], initialObjects := [],
      machineConfig := { defaultMachineConfig with pageSize := 0 } }
  expect "AK9-FE-02 checked boot rejects malformed MachineConfig"
    (match bootFromPlatformChecked cfg with
     | .error _ => true
     | .ok _ => false)

/-- AK9-G (end-to-end): `bootFromPlatformChecked` emits a state with
    interrupts enabled on successful boot. -/
def ak9ge_01_checked_boot_enables_interrupts : IO Unit := do
  let cfg : PlatformConfig := { irqTable := [], initialObjects := [] }
  let ok : Bool :=
    match bootFromPlatformChecked cfg with
    | .ok ist => ist.state.machine.interruptsEnabled
    | .error _ => false
  expect "AK9-GE-01 checked boot enables interrupts" ok

-- ============================================================================
-- AK9-A: mmioReadByte rename + backwards-compat alias
-- ============================================================================

/-- AK9-A: The primary `mmioReadByte` function accepts a valid UART address. -/
def ak9a_05_mmioReadByte_accepts_uart : IO Unit := do
  let addr : PAddr := uart0Base
  let st : SystemState := default
  expect "AK9-A-05 mmioReadByte accepts UART base"
    (match mmioReadByte addr st with
     | .ok _ => true
     | _ => false)

set_option linter.deprecated false in
/-- AK9-A: Backwards-compat alias `mmioRead` produces the EXACT same byte
    value as `mmioReadByte` at a valid UART address, AND is a structural
    `@[inline]` alias so the two definitions reduce identically. -/
def ak9a_06_mmioRead_alias_matches_byte : IO Unit := do
  let addr : PAddr := uart0Base
  let st : SystemState := default
  -- Both must succeed AND return the same byte (the memory function is
  -- pure, so identical inputs guarantee identical outputs given identical
  -- gate behavior).
  let aliasByte : Option UInt8 :=
    match mmioRead addr st with | .ok (b, _) => some b | _ => none
  let primaryByte : Option UInt8 :=
    match mmioReadByte addr st with | .ok (b, _) => some b | _ => none
  expect "AK9-A-06 mmioRead alias byte matches mmioReadByte"
    (aliasByte.isSome && aliasByte == primaryByte)
  -- Negative: both reject the same RAM address with the same error.
  let ramAddr : PAddr := PAddr.ofNat 0x1000
  let aliasErr : Bool :=
    match mmioRead ramAddr st with
    | .error .policyDenied => true
    | _ => false
  let primaryErr : Bool :=
    match mmioReadByte ramAddr st with
    | .error .policyDenied => true
    | _ => false
  expect "AK9-A-06 mmioRead alias rejects RAM same as mmioReadByte"
    (aliasErr && primaryErr)

-- ============================================================================
-- AK9-A: positive correctness theorems
-- ============================================================================

/-- AK9-A: `mmioRead32` produces a success outcome at a valid GIC-400
    distributor address (the positive theorem existence witness is
    exercised at runtime). -/
def ak9a_07_mmioRead32_positive_success : IO Unit := do
  let addr : PAddr := gicDistributorBase
  let st : SystemState := default
  expect "AK9-A-07 mmioRead32 positive success at GIC dist"
    (match mmioRead32 addr st with
     | .ok _ => true
     | _ => false)

/-- AK9-A: `mmioRead64` positive success at an 8-byte aligned GIC-CPU address. -/
def ak9a_08_mmioRead64_positive_success : IO Unit := do
  let addr : PAddr := gicCpuInterfaceBase  -- 0xFF842000 is 8-byte aligned
  let st : SystemState := default
  expect "AK9-A-08 mmioRead64 positive success at GIC CPU iface"
    (match mmioRead64 addr st with
     | .ok _ => true
     | _ => false)

-- ============================================================================
-- AK9-H P-L2: readCStringChecked
-- ============================================================================

/-- AK9-H (P-L2): Out-of-bounds offset rejected with `.malformedBlob`. -/
def ak9h_01_readCStringChecked_rejects_oob : IO Unit := do
  let blob : ByteArray := ByteArray.mk #[0x41, 0x42, 0x00]  -- "AB\0"
  let result := readCStringChecked blob 100 256
  expect "AK9-H-01 readCStringChecked rejects OOB"
    (match result with
     | .error .malformedBlob => true
     | _ => false)

/-- AK9-H (P-L2): Fuel = 0 rejected with `.fuelExhausted`. -/
def ak9h_02_readCStringChecked_rejects_fuel_zero : IO Unit := do
  let blob : ByteArray := ByteArray.mk #[0x41, 0x42, 0x00]
  let result := readCStringChecked blob 0 0
  expect "AK9-H-02 readCStringChecked rejects fuel 0"
    (match result with
     | .error .fuelExhausted => true
     | _ => false)

/-- AK9-H (P-L2): Valid null-terminated string returns `.ok` with the string. -/
def ak9h_03_readCStringChecked_ok : IO Unit := do
  let blob : ByteArray := ByteArray.mk #[0x41, 0x42, 0x00, 0x00]  -- "AB\0\0"
  let result := readCStringChecked blob 0 256
  expect "AK9-H-03 readCStringChecked accepts valid string"
    (match result with
     | .ok (s, _) => s == "AB"
     | _ => false)

/-- AK9-H (P-L2): String without null terminator exhausts fuel. -/
def ak9h_04_readCStringChecked_fuel_exhausted_on_unterminated : IO Unit := do
  -- A blob with no null byte within the first 3 bytes and fuel=2 forces
  -- the fuel to reach 0 before finding a terminator.
  let blob : ByteArray := ByteArray.mk #[0x41, 0x42, 0x43]
  let result := readCStringChecked blob 0 2
  expect "AK9-H-04 readCStringChecked fuel exhausted on unterminated"
    (match result with
     | .error .fuelExhausted => true
     | _ => false)

-- ============================================================================
-- AN7-D.2 (PLT-M02/PLT-M03): RPi5 boot VSpaceRoot + DEF-P-L9 closure
-- ============================================================================

/-- AN7-D.2.8: `rpi5BootVSpaceRoot` is well-formed (ASID bounded, every
    mapping W^X, non-empty). -/
def an7d2_01_rpi5BootVSpaceRoot_wellFormed : IO Unit := do
  -- The theorem is discharged at compile time by `decide`; we exercise it
  -- by asserting every projected conjunct holds.  Failure at any one of
  -- these assertions surfaces a regression in either the boot root
  -- definition or the `wellFormed` predicate.
  expect "AN7-D.2-01 boot VSpaceRoot asid = 0"
    (RPi5.VSpaceBoot.rpi5BootVSpaceRoot.asid.val == 0)
  expect "AN7-D.2-01 boot VSpaceRoot mappings non-empty"
    (decide (RPi5.VSpaceBoot.rpi5BootVSpaceRoot.mappings.size > 0))
  -- Witness all three mapping permissions are wxCompliant by spot-check.
  expect "AN7-D.2-01 permsTextRX wxCompliant"
    (RPi5.VSpaceBoot.permsTextRX.wxCompliant)
  expect "AN7-D.2-01 permsDataRW wxCompliant"
    (RPi5.VSpaceBoot.permsDataRW.wxCompliant)
  expect "AN7-D.2-01 permsMmioRW wxCompliant"
    (RPi5.VSpaceBoot.permsMmioRW.wxCompliant)

/-- AN7-D.2.8: `rpi5BootVSpaceRoot` satisfies the per-root W^X predicate.
    A regression that introduces a W+X mapping (e.g., by flipping a
    permission constant to `execute := true, write := true`) fails
    `decide` at module compile time AND trips this runtime assertion. -/
def an7d2_02_rpi5BootVSpaceRoot_wxCompliant : IO Unit := do
  -- At runtime we can't directly evaluate the fold (it's decidable at
  -- compile time via `decide`).  We instead exercise it by inspecting the
  -- specific permissions used in the boot root and asserting they are
  -- wxCompliant one-by-one.  This anchors the three permission constants
  -- to their W^X witnesses.
  let allCompliant :=
    RPi5.VSpaceBoot.permsTextRX.wxCompliant &&
    RPi5.VSpaceBoot.permsDataRW.wxCompliant &&
    RPi5.VSpaceBoot.permsMmioRW.wxCompliant
  expect "AN7-D.2-02 all boot permissions wxCompliant" allCompliant
  -- Specific negative: permsTextRX must NOT have write flag
  expect "AN7-D.2-02 permsTextRX not writable"
    (!RPi5.VSpaceBoot.permsTextRX.write)
  -- Specific negative: permsDataRW must NOT have execute flag
  expect "AN7-D.2-02 permsDataRW not executable"
    (!RPi5.VSpaceBoot.permsDataRW.execute)
  -- Specific negative: permsMmioRW must NOT have execute or cacheable
  expect "AN7-D.2-02 permsMmioRW not executable"
    (!RPi5.VSpaceBoot.permsMmioRW.execute)
  expect "AN7-D.2-02 permsMmioRW not cacheable"
    (!RPi5.VSpaceBoot.permsMmioRW.cacheable)

/-- AN7-D.2.8: The boot VSpaceRoot's MMIO mappings cover the three
    canonical BCM2712 device regions.  A regression that drops (e.g.) the
    GIC CPU interface mapping breaks kernel boot on real silicon. -/
def an7d2_03_rpi5BootVSpaceRoot_covers_mmio_regions : IO Unit := do
  -- The boot root's mappings must cover UART0, GIC distributor, GIC CPU
  -- interface at their identity physical addresses.  We spot-check via
  -- RHTable.get? on each PAddr's corresponding VAddr.
  let uartVaddr : VAddr := VAddr.ofNat uart0Base.toNat
  let gicDistVaddr : VAddr := VAddr.ofNat gicDistributorBase.toNat
  let gicCpuVaddr : VAddr := VAddr.ofNat gicCpuInterfaceBase.toNat
  let root := RPi5.VSpaceBoot.rpi5BootVSpaceRoot
  expect "AN7-D.2-03 boot root maps UART0"
    (root.mappings[uartVaddr]?.isSome)
  expect "AN7-D.2-03 boot root maps GIC distributor"
    (root.mappings[gicDistVaddr]?.isSome)
  expect "AN7-D.2-03 boot root maps GIC CPU interface"
    (root.mappings[gicCpuVaddr]?.isSome)
  -- Each MMIO mapping should have the `permsMmioRW` permissions (not
  -- executable, not cacheable).
  match root.mappings[uartVaddr]? with
  | some (_, perms) =>
    expect "AN7-D.2-03 UART perms = permsMmioRW"
      (decide (perms = RPi5.VSpaceBoot.permsMmioRW))
  | none =>
    expect "AN7-D.2-03 UART mapping present (unreachable if prior assert holds)" false

/-- AN7-D.2.8 (audit remediation): The boot VSpaceRoot's `paddrBounded`
    conjunct witnesses that every mapped PA fits the BCM2712 44-bit PA
    range.  A regression that adds a PA ≥ 2^44 would fail `decide` on
    the aggregated fold and this runtime test would detect the lapse
    by spot-checking the six known bases. -/
def an7d2_04_rpi5BootVSpaceRoot_paddrBounded : IO Unit := do
  -- Every known base address is below 2^44 = 0x100000000000.
  let twoPow44 : Nat := 0x100000000000
  expect "AN7-D.2-04 kernelTextBase < 2^44"
    (decide (RPi5.VSpaceBoot.kernelTextBase.toNat < twoPow44))
  expect "AN7-D.2-04 kernelDataBase < 2^44"
    (decide (RPi5.VSpaceBoot.kernelDataBase.toNat < twoPow44))
  expect "AN7-D.2-04 kernelStackBase < 2^44"
    (decide (RPi5.VSpaceBoot.kernelStackBase.toNat < twoPow44))
  expect "AN7-D.2-04 uart0Base < 2^44"
    (decide (uart0Base.toNat < twoPow44))
  expect "AN7-D.2-04 gicDistributorBase < 2^44"
    (decide (gicDistributorBase.toNat < twoPow44))
  expect "AN7-D.2-04 gicCpuInterfaceBase < 2^44"
    (decide (gicCpuInterfaceBase.toNat < twoPow44))

-- ============================================================================
-- AN7-D.5 (PLT-M06): extractPeripherals recursive walk tests
-- ============================================================================

/-- Helper: build a 16-byte big-endian `reg` property encoding
    (base, size) as two 64-bit big-endian values.  Used by the
    depth-3+ DTB peripheral-walk tests below. -/
private def mkRegProperty (base size : UInt64) : ByteArray :=
  let baseBytes : Array UInt8 :=
    #[ ((base >>> 56) &&& 0xFF).toUInt8
     , ((base >>> 48) &&& 0xFF).toUInt8
     , ((base >>> 40) &&& 0xFF).toUInt8
     , ((base >>> 32) &&& 0xFF).toUInt8
     , ((base >>> 24) &&& 0xFF).toUInt8
     , ((base >>> 16) &&& 0xFF).toUInt8
     , ((base >>> 8)  &&& 0xFF).toUInt8
     , ( base         &&& 0xFF).toUInt8 ]
  let sizeBytes : Array UInt8 :=
    #[ ((size >>> 56) &&& 0xFF).toUInt8
     , ((size >>> 48) &&& 0xFF).toUInt8
     , ((size >>> 40) &&& 0xFF).toUInt8
     , ((size >>> 32) &&& 0xFF).toUInt8
     , ((size >>> 24) &&& 0xFF).toUInt8
     , ((size >>> 16) &&& 0xFF).toUInt8
     , ((size >>> 8)  &&& 0xFF).toUInt8
     , ( size         &&& 0xFF).toUInt8 ]
  ByteArray.mk (baseBytes ++ sizeBytes)

/-- Helper: make an `FdtNode` with `reg` + `compatible` properties. -/
private def mkPeripheral (name : String) (base : UInt64)
    (children : List FdtNode := []) : FdtNode :=
  { name
    properties :=
      [ { name := "reg", value := mkRegProperty base 0x1000 }
      , { name := "compatible", value := ByteArray.mk #[0x61, 0x72, 0x6D, 0x00] } ]  -- "arm\0"
    children }

/-- **PR #892 review round 5**: one `ranges` triple, in the 2/2/2 cell widths
this suite's `reg` helper already writes — child base, parent base, length. -/
private def mkRangesProperty (childBase parentBase length : UInt64) : ByteArray :=
  (mkRegProperty childBase parentBase) ++ (mkRegProperty length 0).extract 0 8

/-- **PR #892 review round 5 audit**: a one-cell property value, big-endian —
what `#address-cells` and `#size-cells` carry. -/
private def mkCellProperty (n : UInt32) : ByteArray :=
  ByteArray.mk
    #[ ((n >>> 24) &&& 0xFF).toUInt8
     , ((n >>> 16) &&& 0xFF).toUInt8
     , ((n >>> 8)  &&& 0xFF).toUInt8
     , ( n         &&& 0xFF).toUInt8 ]

/-- **PR #892 review round 5**: a bus node — a peripheral that also translates
its children's addresses through `ranges`.

It declares `#address-cells` and `#size-cells`, as a real bus node does: the
specification's defaults are 2 and **1**, so a bus whose children carry a
two-cell size must say so.  The fixture used to declare neither and rely on this
parser defaulting `#size-cells` to 2, which was itself a divergence from the
specification and from the Rust walker reading the same blob. -/
private def mkBus (name : String) (base : UInt64)
    (ranges : ByteArray) (children : List FdtNode := []) : FdtNode :=
  { name
    properties :=
      [ { name := "reg", value := mkRegProperty base 0x1000 }
      , { name := "compatible", value := ByteArray.mk #[0x61, 0x72, 0x6D, 0x00] }  -- "arm\0"
      , { name := "#address-cells", value := mkCellProperty 2 }
      , { name := "#size-cells", value := mkCellProperty 2 }
      , { name := "ranges", value := ranges } ]
    children }

/-- **PR #892 review round 5**: a node the firmware marked unavailable. -/
private def withStatus (node : FdtNode) (status : String) : FdtNode :=
  { node with
    properties := node.properties ++
      [ { name := "status"
          value := ByteArray.mk ((status.toList.map (fun c => UInt8.ofNat c.toNat)).toArray.push 0) } ] }

/-- AN7-D.5: `extractPeripherals` discovers peripherals at depth 3+ via
    the new recursive walk.  The previous 2-level walk (pre-AN7-D.5)
    would have missed the `level3-device` in this synthetic tree; the
    new recursive form finds it.

    **PR #892 review round 5**: the buses now carry `ranges`, and the addresses
    asserted are the **translated** ones.  Devicetree Specification v0.4 §2.3.8:
    a child's `reg` is in its parent bus's address space, and only `ranges` maps
    that space into the parent's.  This fixture used to give the buses no
    `ranges` at all and expect the children discovered at their raw addresses —
    which is what the walk did, and which is what the finding is about: a
    child-relative number reported as a physical one.  The nested devices are
    still discovered, at the addresses the translation gives them; the
    `ranges`-less case is its own test below. -/
def an7d5_01_extractPeripherals_depth3_discovery : IO Unit := do
  -- Build a depth-3 tree in which each bus translates its children, and the
  -- windows compose — level2's output has to land inside level1's window, which
  -- is the whole point of composing rather than applying the nearest `ranges`:
  --   level1-bus (depth 1)  reg 0x1000_0000; child [0, 0x2_0000_0000) → 0x1_0000_0000
  --     └─ level2-controller (depth 2)  reg 0x2000_0000 → 0x1_2000_0000
  --         child [0, 0x1_0000_0000) → 0x4000_0000 (in level1's child space)
  --         └─ level3-device (depth 3)  reg 0x3000_0000 → 0x7000_0000 → 0x1_7000_0000
  let deepTree : List FdtNode := [
    mkBus "level1-bus" 0x10000000 (mkRangesProperty 0 0x100000000 0x200000000) [
      mkBus "level2-controller" 0x20000000 (mkRangesProperty 0 0x40000000 0x100000000) [
        mkPeripheral "level3-device" 0x30000000 []
      ]
    ]
  ]
  let devices := extractPeripherals deepTree 1024
  -- All three levels should be discovered
  expect "AN7-D.5-01 level1-bus discovered"
    (devices.any (fun d => d.name == "level1-bus"))
  expect "AN7-D.5-01 level2-controller discovered"
    (devices.any (fun d => d.name == "level2-controller"))
  expect "AN7-D.5-01 level3-device discovered"
    (devices.any (fun d => d.name == "level3-device"))
  expect "AN7-D.5-01 exactly 3 devices total"
    (decide (devices.length = 3))
  -- The top-level bus is in the CPU's own space; the nested ones are translated
  -- once and twice.  A walk that reported raw child addresses would put
  -- level2-controller at 0x2000_0000 and level3-device at 0x3000_0000.
  expect "AN7-D.5-01 level1-bus keeps its physical address"
    (devices.any (fun d => d.name == "level1-bus" && d.base.toNat == 0x10000000))
  expect "AN7-D.5-01 level2-controller is translated once"
    (devices.any (fun d => d.name == "level2-controller" && d.base.toNat == 0x120000000))
  expect "AN7-D.5-01 level3-device is translated twice"
    (devices.any (fun d => d.name == "level3-device" && d.base.toNat == 0x170000000))
  expect "NEGATIVE AN7-D.5-01 no device keeps an untranslated child address"
    (!devices.any (fun d => d.base.toNat == 0x20000000 || d.base.toNat == 0x30000000))

/-- **PR #892 review round 5**: a bus with **no** `ranges` maps nothing into its
parent, so its children have no physical address and are not peripherals of this
machine (Devicetree Specification v0.4 §2.3.8).  The bus itself is still
discovered — it has an address in *its* parent's space. -/
def review5_bus_without_ranges_hides_its_children : IO Unit := do
  let tree : List FdtNode := [
    mkPeripheral "opaque-bus" 0x10000000 [
      mkPeripheral "unreachable-device" 0x20000000 []
    ]
  ]
  let devices := extractPeripherals tree 1024
  expect "review5 the bus itself is discovered"
    (devices.any (fun d => d.name == "opaque-bus"))
  expect "NEGATIVE review5 a child of a ranges-less bus is not discovered"
    (!devices.any (fun d => d.name == "unreachable-device"))
  expect "review5 exactly one device"
    (decide (devices.length = 1))

/-- **PR #892 review round 5**: an **empty** `ranges` is the identity mapping —
the child address space *is* the parent's — so a child keeps its own address. -/
def review5_empty_ranges_is_the_identity : IO Unit := do
  let tree : List FdtNode := [
    mkBus "transparent-bus" 0x10000000 (ByteArray.mk #[]) [
      mkPeripheral "child" 0x20000000 []
    ]
  ]
  let devices := extractPeripherals tree 1024
  expect "review5 a child under an empty ranges keeps its address"
    (devices.any (fun d => d.name == "child" && d.base.toNat == 0x20000000))

/-- **PR #892 review round 5**: an address outside every `ranges` window has no
translation, so the node is not reported at all rather than reported raw. -/
def review5_untranslatable_address_is_refused : IO Unit := do
  let tree : List FdtNode := [
    mkBus "narrow-bus" 0x10000000 (mkRangesProperty 0 0x100000000 0x1000) [
      mkPeripheral "outside-window" 0x20000000 []
    ]
  ]
  let devices := extractPeripherals tree 1024
  expect "NEGATIVE review5 an untranslatable child is not discovered"
    (!devices.any (fun d => d.name == "outside-window"))

/-- **PR #892 review round 5**: a node the firmware marked `disabled` is
hardware that is not there, and the classifier drops it — the Lean twin of the
round-4 `status` filter in `cmdline::find_ram_top_in_dtb`.  `okay` and `ok` are
the two operational spellings; every other value withholds the node. -/
def review5_disabled_peripheral_is_not_discovered : IO Unit := do
  let disabled := extractPeripherals
    [withStatus (mkPeripheral "uart" 0x10000000 []) "disabled"] 1024
  expect "NEGATIVE review5 a disabled peripheral is not discovered"
    (!disabled.any (fun d => d.name == "uart"))
  for status in ["okay", "ok"] do
    let operational := extractPeripherals
      [withStatus (mkPeripheral "uart" 0x10000000 []) status] 1024
    expect "review5 an explicitly operational peripheral is discovered"
      (operational.any (fun d => d.name == "uart"))
  for status in ["reserved", "fail", "fail-ecc", "okay-ish"] do
    let withheld := extractPeripherals
      [withStatus (mkPeripheral "uart" 0x10000000 []) status] 1024
    expect "NEGATIVE review5 a non-operational status withholds the peripheral"
      (!withheld.any (fun d => d.name == "uart"))
  -- An absent `status` is `okay`, which is what every other fixture relies on.
  expect "review5 an absent status is operational"
    ((extractPeripherals [mkPeripheral "uart" 0x10000000 []] 1024).any
      (fun d => d.name == "uart"))

/-- AN7-D.5: The walk terminates at `fuel = 0` regardless of tree depth. -/
def an7d5_02_extractPeripherals_zero_fuel_collapses : IO Unit := do
  let deepTree : List FdtNode := [
    mkPeripheral "top" 0x1000 [
      mkPeripheral "middle" 0x2000 [
        mkPeripheral "bottom" 0x3000 []
      ]
    ]
  ]
  let devices := extractPeripherals deepTree 0
  expect "AN7-D.5-02 zero-fuel returns empty list"
    (decide (devices.length = 0))

/-- AN7-D.5: The walk correctly skips nodes lacking `reg` or
    `compatible` properties. -/
def an7d5_03_extractPeripherals_skips_incomplete_nodes : IO Unit := do
  -- Node without any properties (no reg, no compatible) — should be skipped
  let incompleteNode : FdtNode :=
    { name := "no-props", properties := [], children := [] }
  let devices := extractPeripherals [incompleteNode] 1024
  expect "AN7-D.5-03 incomplete node skipped"
    (decide (devices.length = 0))

/-- AN7-D.5: The walk correctly excludes `memory@*` / `cpus` / `chosen`
    nodes from peripheral classification, even at deep nesting. -/
def an7d5_04_extractPeripherals_excludes_reserved_names : IO Unit := do
  -- Reserved-name nodes should NOT be reported as peripherals
  let treeWithReserved : List FdtNode := [
    mkPeripheral "legit-device" 0x10000 [],
    -- Even with proper reg+compatible, these names are excluded by classifier
    { name := "memory@0"
      properties :=
        [ { name := "reg", value := mkRegProperty 0x20000 0x1000 }
        , { name := "compatible", value := ByteArray.mk #[0x61, 0x72, 0x6D, 0x00] } ]
      children := [] },
    { name := "cpus"
      properties :=
        [ { name := "reg", value := mkRegProperty 0x30000 0x1000 }
        , { name := "compatible", value := ByteArray.mk #[0x61, 0x72, 0x6D, 0x00] } ]
      children := [] }
  ]
  let devices := extractPeripherals treeWithReserved 1024
  expect "AN7-D.5-04 only legit-device extracted"
    (decide (devices.length = 1))
  expect "AN7-D.5-04 legit-device is the one found"
    (devices.any (fun d => d.name == "legit-device"))

-- ============================================================================
-- Entry point
-- ============================================================================

-- ============================================================================
-- WS-RR RR7.27: the DeviceTree → PlatformConfig bridge, end to end
--
-- Register §6 finding 46: `DeviceTree.fromDtbFull` was documented as production
-- DTB parsing, carried a correctness theorem, and had zero consumers.  These
-- drive the whole chain a bootloader's blob now takes — parse, check the board
-- against the RPi5 binding, produce the boot configuration — including both
-- refusal arms, because a check that cannot refuse is not a check.
-- ============================================================================

/-- Big-endian 32-bit encoding, the width every FDT token and header field
takes. -/
private def be32 (n : Nat) : Array UInt8 :=
  #[ ((n >>> 24) &&& 0xFF).toUInt8
   , ((n >>> 16) &&& 0xFF).toUInt8
   , ((n >>> 8)  &&& 0xFF).toUInt8
   , ( n         &&& 0xFF).toUInt8 ]

/-- Big-endian 64-bit encoding — a two-cell `reg` address or size. -/
private def be64 (n : Nat) : Array UInt8 := be32 (n >>> 32) ++ be32 (n &&& 0xFFFFFFFF)

/-- A node name (or property string) as its null-terminated, 4-byte-padded
FDT encoding. -/
private def fdtString (s : String) : Array UInt8 :=
  let bytes := (s.toUTF8.toList.toArray).push 0
  let pad := (4 - bytes.size % 4) % 4
  bytes ++ Array.replicate pad (0 : UInt8)

/-- One `FDT_PROP` token: the tag, the value length, the strings-block offset
of the name, then the padded value. -/
private def fdtProp (nameOff : Nat) (value : Array UInt8) : Array UInt8 :=
  let pad := (4 - value.size % 4) % 4
  be32 0x00000003 ++ be32 value.size ++ be32 nameOff ++ value
    ++ Array.replicate pad (0 : UInt8)

private def fdtBeginNode (name : String) : Array UInt8 :=
  be32 0x00000001 ++ fdtString name

private def fdtEndNodeTok : Array UInt8 := be32 0x00000002
private def fdtEndTok : Array UInt8 := be32 0x00000009

/-- The strings block this fixture uses, and each name's offset in it. -/
private def stringsBlock : Array UInt8 :=
  fdtString "reg" ++ fdtString "device_type" ++ fdtString "compatible"
    ++ fdtString "status" ++ fdtString "#address-cells" ++ fdtString "#size-cells"

private def regNameOff : Nat := 0
private def deviceTypeNameOff : Nat := (fdtString "reg").size
private def compatibleNameOff : Nat :=
  (fdtString "reg").size + (fdtString "device_type").size
/-- **PR #892 review round 5**: the `status` property's offset — appended, so
every offset above is unchanged. -/
private def statusNameOff : Nat :=
  (fdtString "reg").size + (fdtString "device_type").size + (fdtString "compatible").size
/-- **PR #892 review round 5 audit**: the root's cell-count property offsets. -/
private def addressCellsNameOff : Nat := statusNameOff + (fdtString "status").size
private def sizeCellsNameOff : Nat := addressCellsNameOff + (fdtString "#address-cells").size

/-- **PR #892 review round 5 audit**: the root's `#address-cells` / `#size-cells`,
which govern its children's `reg`.

The Rust fixture builder has always written both (`build_dtb(address_cells,
size_cells, …)`); this one did not, and relied on the Lean parser defaulting
`#size-cells` to 2.  The specification's default is **1**, so the two builders
were producing different blobs for "the same" board — the same
one-question-two-answers shape as the parsers they feed. -/
private def rootCellProperties : Array UInt8 :=
  fdtProp addressCellsNameOff (be32 2) ++ fdtProp sizeCellsNameOff (be32 2)

/-- A peripheral node: `reg = <base size>` plus a `compatible` string, the two
properties `classifyPeripheralNode` requires. -/
private def peripheralNode (name : String) (base size : Nat) : Array UInt8 :=
  fdtBeginNode name
    ++ fdtProp regNameOff (be64 base ++ be64 size)
    ++ fdtProp compatibleNameOff (fdtString "arm,fixture")
    ++ fdtEndNodeTok

/-- Assemble a complete DTB blob: header, structure block, strings block. -/
private def assembleDtb (structBlock : Array UInt8) : ByteArray :=
  let offDtStruct := 40
  let offDtStrings := offDtStruct + structBlock.size
  let totalsize := offDtStrings + stringsBlock.size
  let header : Array UInt8 :=
    be32 0xD00DFEED ++ be32 totalsize ++ be32 offDtStruct ++ be32 offDtStrings
      ++ be32 40 ++ be32 17 ++ be32 16 ++ be32 0
      ++ be32 stringsBlock.size ++ be32 structBlock.size
  ByteArray.mk (header ++ structBlock ++ stringsBlock)

/-- A device tree for a board whose `/memory` node carries one `reg` pair per
entry of `regions` (base, size), plus the three MMIO windows the RPi5 binding
programs.  Several pairs is how the firmware reports a board whose RAM is not
one contiguous run — every RPi5 above 2 GiB. -/
private def boardDtbRegions (regions : List (Nat × Nat)) (withMmio : Bool := true) :
    ByteArray :=
  let regPairs := regions.foldl (fun acc r => acc ++ be64 r.1 ++ be64 r.2) #[]
  let memoryNode :=
    fdtBeginNode "memory@0"
      ++ fdtProp deviceTypeNameOff (fdtString "memory")
      ++ fdtProp regNameOff regPairs
      ++ fdtEndNodeTok
  let peripherals :=
    if withMmio then
      peripheralNode "serial@fe201000" 0xFE201000 0x1000
        ++ peripheralNode "interrupt-controller@ff841000" 0xFF841000 0x1000
        ++ peripheralNode "interrupt-controller@ff842000" 0xFF842000 0x2000
    else #[]
  assembleDtb (fdtBeginNode "" ++ rootCellProperties ++ memoryNode ++ peripherals ++ fdtEndNodeTok ++ fdtEndTok)

/-- A device tree for a board with `ramSize` bytes of RAM starting at 0. -/
private def boardDtb (ramSize : Nat) (withMmio : Bool := true) : ByteArray :=
  boardDtbRegions [(0, ramSize)] withMmio

/-- **PR #892 review round 5**: the canonical board's structure block, without
its closing `FDT_END_NODE` / `FDT_END`.

The header is consistent with it — `assembleDtb` computes every offset from the
block it is given — so this is exactly the shape the finding names: a blob whose
`/memory` node and peripherals parse and whose structure block then simply
stops.  Before this cut the walk returned the nodes it had and `fromDtbFull`
reported `.ok`. -/
private def unterminatedBoardDtb : ByteArray :=
  let memoryNode :=
    fdtBeginNode "memory@0"
      ++ fdtProp deviceTypeNameOff (fdtString "memory")
      ++ fdtProp regNameOff (be64 0 ++ be64 0xFC000000)
      ++ fdtEndNodeTok
  let peripherals :=
    peripheralNode "serial@fe201000" 0xFE201000 0x1000
      ++ peripheralNode "interrupt-controller@ff841000" 0xFF841000 0x1000
      ++ peripheralNode "interrupt-controller@ff842000" 0xFF842000 0x2000
  assembleDtb (fdtBeginNode "" ++ rootCellProperties ++ memoryNode ++ peripherals)

/-- **PR #892 review round 5**: the canonical board with an **unknown** token
where the terminator belongs — the other partial exit the walk used to accept. -/
private def unknownTokenBoardDtb : ByteArray :=
  let memoryNode :=
    fdtBeginNode "memory@0"
      ++ fdtProp deviceTypeNameOff (fdtString "memory")
      ++ fdtProp regNameOff (be64 0 ++ be64 0xFC000000)
      ++ fdtEndNodeTok
  assembleDtb (fdtBeginNode "" ++ rootCellProperties ++ memoryNode ++ be32 0x000000FF ++ fdtEndNodeTok ++ fdtEndTok)

/-- **PR #892 review round 5**: a board whose `/memory` node carries the given
`status`.  A withheld bank is DRAM the firmware says is not usable. -/
private def boardDtbWithMemoryStatus (status : String) : ByteArray :=
  let memoryNode :=
    fdtBeginNode "memory@0"
      ++ fdtProp deviceTypeNameOff (fdtString "memory")
      ++ fdtProp regNameOff (be64 0 ++ be64 0xFC000000)
      ++ fdtProp statusNameOff (fdtString status)
      ++ fdtEndNodeTok
  let peripherals :=
    peripheralNode "serial@fe201000" 0xFE201000 0x1000
      ++ peripheralNode "interrupt-controller@ff841000" 0xFF841000 0x1000
      ++ peripheralNode "interrupt-controller@ff842000" 0xFF842000 0x2000
  assembleDtb (fdtBeginNode "" ++ rootCellProperties ++ memoryNode ++ peripherals ++ fdtEndNodeTok ++ fdtEndTok)

/-- **PR #892 review round 5 audit**: a board that reports its RAM as **two**
`/memory` nodes rather than two `reg` pairs in one — a shape the specification
allows and firmware uses.  The Rust walker folds every node's extents into one
store; the Lean selector took the first node only. -/
private def twoMemoryNodeDtb : ByteArray :=
  let node := fun (name : String) (base size : Nat) =>
    fdtBeginNode name
      ++ fdtProp deviceTypeNameOff (fdtString "memory")
      ++ fdtProp regNameOff (be64 base ++ be64 size)
      ++ fdtEndNodeTok
  let peripherals :=
    peripheralNode "serial@fe201000" 0xFE201000 0x1000
      ++ peripheralNode "interrupt-controller@ff841000" 0xFF841000 0x1000
      ++ peripheralNode "interrupt-controller@ff842000" 0xFF842000 0x2000
  assembleDtb (fdtBeginNode "" ++ rootCellProperties
    ++ node "memory@0" 0 0xFC000000
    ++ node "memory@100000000" 0x100000000 0x100000000
    ++ peripherals ++ fdtEndNodeTok ++ fdtEndTok)

/-- **PR #892 review round 5 audit**: a board whose root declares **one**-cell
addresses and sizes, with a `reg` written at that width.  The Rust walker reads
the root's declaration; the Lean path read a fixed two-cell stride. -/
private def singleCellBoardDtb : ByteArray :=
  let rootCells := fdtProp addressCellsNameOff (be32 1) ++ fdtProp sizeCellsNameOff (be32 1)
  let memoryNode :=
    fdtBeginNode "memory@0"
      ++ fdtProp deviceTypeNameOff (fdtString "memory")
      ++ fdtProp regNameOff (be32 0 ++ be32 0xFC000000)
      ++ fdtEndNodeTok
  let peripherals :=
    peripheralNode "serial@fe201000" 0xFE201000 0x1000
      ++ peripheralNode "interrupt-controller@ff841000" 0xFF841000 0x1000
      ++ peripheralNode "interrupt-controller@ff842000" 0xFF842000 0x2000
  assembleDtb (fdtBeginNode "" ++ rootCells ++ memoryNode ++ peripherals
    ++ fdtEndNodeTok ++ fdtEndTok)

/-- **PR #892 review round 5 audit**: a `reg` that is not a whole number of
(address, size) pairs — three 64-bit cells where the pair is four. -/
private def truncatedRegBoardDtb : ByteArray :=
  let memoryNode :=
    fdtBeginNode "memory@0"
      ++ fdtProp deviceTypeNameOff (fdtString "memory")
      ++ fdtProp regNameOff (be64 0 ++ be64 0xFC000000 ++ be64 0x100000000)
      ++ fdtEndNodeTok
  assembleDtb (fdtBeginNode "" ++ rootCellProperties ++ memoryNode
    ++ fdtEndNodeTok ++ fdtEndTok)

/-- **PR #892 review round 5 audit**: a node named `memory@` with no unit
address.  `is_memory_node_name` refuses it on the Rust side. -/
private def emptyUnitAddressDtb : ByteArray :=
  let memoryNode :=
    fdtBeginNode "memory@"
      ++ fdtProp deviceTypeNameOff (fdtString "memory")
      ++ fdtProp regNameOff (be64 0 ++ be64 0xFC000000)
      ++ fdtEndNodeTok
  assembleDtb (fdtBeginNode "" ++ rootCellProperties ++ memoryNode
    ++ fdtEndNodeTok ++ fdtEndTok)

/-- **PR #892 review round 5**: a board whose only `memory@…` node is a child of
`/reserved-memory` — a carve-out, at depth 2, not the machine's RAM. -/
private def reservedMemoryOnlyDtb : ByteArray :=
  let carveOut :=
    fdtBeginNode "reserved-memory"
      ++ fdtBeginNode "memory@0"
        ++ fdtProp deviceTypeNameOff (fdtString "memory")
        ++ fdtProp regNameOff (be64 0 ++ be64 0xFC000000)
        ++ fdtEndNodeTok
      ++ fdtEndNodeTok
  assembleDtb (fdtBeginNode "" ++ rootCellProperties ++ carveOut ++ fdtEndNodeTok ++ fdtEndTok)

/-- The machine configuration the bridge binds for an accepted blob, read back
through the binding exactly as the hardware boot binds it. -/
private def boundMapOf (config : PlatformConfig) : List MemoryRegion :=
  (bindPlatformConfig RPi5Platform config).machineConfig.memoryMap

/-- The map of a variant, for comparison with `boundMapOf`. -/
private def variantMap (gib : Nat) : List MemoryRegion :=
  rpi5MemoryMapForConfig { ramSize := gib * 1024 * 1024 * 1024 }

/-- WS-RR RR7.27: the fixture blob parses — the precondition every case below
rests on, asserted separately so a broken fixture is distinguishable from a
broken check. -/
def deviceTreeBridge_01_fixture_blob_parses : IO Unit := do
  match DeviceTree.fromDtbFull (boardDtb 0xFC000000) rpi5MachineConfig.physicalAddressWidth with
  | .error _ => expect "RR7.27-01 fixture blob parses" false
  | .ok dt =>
      expect "RR7.27-01 fixture blob parses" true
      expect "RR7.27-01 one RAM region discovered"
        (decide (dt.machineConfig.memoryMap.length = 1))
      expect "RR7.27-01 three peripherals discovered"
        (decide (dt.peripherals.length = 3))

/-- WS-RR RR7.27: a board with the binding's RAM and MMIO is accepted, and the
configuration carries the device tree's machine map plus the caller's
deployment half. -/
def deviceTreeBridge_02_matching_board_accepted : IO Unit := do
  match rpi5PlatformConfigFromDtb (boardDtb 0xFC000000) [] [] none with
  | .error _ => expect "RR7.27-02 matching board accepted" false
  | .ok config =>
      expect "RR7.27-02 matching board accepted" true
      expect "RR7.27-02 config carries the device tree's map"
        (decide (config.machineConfig.memoryMap.length = 1))
      expect "RR7.27-02 config carries the caller's deployment half"
        (config.irqTable.isEmpty && config.initialObjects.isEmpty
          && config.bootVSpaceRoot.isNone)

/-- WS-RR RR7.27: a board with less RAM than the **smallest** variant the
binding declares is refused.  The mutation that finds a vacuous check: the blob
is well formed, the peripherals are all there, and only the RAM extent differs.
PR #892 review round 2 moved the bar from the fixed 4 GiB map to the family's
smallest member — 512 MiB is short of every Raspberry Pi 5 ever shipped, where
1 GiB (the old fixture) is a board this image is built for. -/
def deviceTreeBridge_03_short_ram_refused : IO Unit := do
  match rpi5PlatformConfigFromDtb (boardDtb 0x20000000) [] [] none with
  | .error .boardDoesNotMatchBinding =>
      expect "RR7.27-03 short-RAM board refused" true
  | _ => expect "RR7.27-03 short-RAM board refused" false

/-- WS-RR RR7.27: a board whose device tree discovered none of the MMIO the
binding programs is refused — the half a RAM-only check would miss.  Same RAM,
same header; only the peripheral nodes are gone. -/
def deviceTreeBridge_04_missing_mmio_refused : IO Unit := do
  match rpi5PlatformConfigFromDtb (boardDtb 0xFC000000 (withMmio := false)) [] [] none with
  | .error .boardDoesNotMatchBinding =>
      expect "RR7.27-04 board without the binding's MMIO refused" true
  | _ => expect "RR7.27-04 board without the binding's MMIO refused" false

/-- WS-RR RR7.27: an unparseable blob is refused as such, not as a mismatched
board — the two refusals mean different things to an operator. -/
def deviceTreeBridge_05_unparseable_blob_refused : IO Unit := do
  match rpi5PlatformConfigFromDtb (ByteArray.mk #[0x00, 0x01, 0x02, 0x03]) [] [] none with
  | .error (.unparseableBlob _) =>
      expect "RR7.27-05 unparseable blob refused as unparseable" true
  | _ => expect "RR7.27-05 unparseable blob refused as unparseable" false

/-- WS-RR RR7.27: the coverage predicate is not vacuously true — an empty
peripheral list fails a non-empty MMIO demand, which is what a truncated blob
produces. -/
def deviceTreeBridge_06_coverage_is_refusable : IO Unit := do
  match DeviceTree.fromDtbFull (boardDtb 0xFC000000 (withMmio := false))
      rpi5MachineConfig.physicalAddressWidth with
  | .error _ => expect "RR7.27-06 no-peripheral blob parses" false
  | .ok dt =>
      expect "RR7.27-06 RAM half still holds"
        (deviceTreeCoversMachineConfig dt rpi5MachineConfig)
      expect "RR7.27-06 MMIO half refuses"
        (!deviceTreeCoversMmioRegions dt mmioRegions)
      expect "RR7.27-06 MMIO demand is non-empty"
        (!mmioRegions.isEmpty)

/-- PR #892 review round 2 — the finding's own boards: a 1 GiB and a 2 GiB
Raspberry Pi 5 are accepted, and the hardware boot binds each board's **own**
variant, not the 4 GiB map the bridge used to demand of every board. -/
def deviceTreeBridge_07_small_variants_bind_their_own_map : IO Unit := do
  match rpi5PlatformConfigFromDtb (boardDtb 0x40000000) [] [] none with
  | .error _ => expect "PR892-07 1 GiB board accepted" false
  | .ok config =>
      expect "PR892-07 1 GiB board accepted" true
      expect "PR892-07 1 GiB board binds the 1 GiB variant"
        (decide (boundMapOf config = variantMap 1))
  match rpi5PlatformConfigFromDtb (boardDtb 0x80000000) [] [] none with
  | .error _ => expect "PR892-07 2 GiB board accepted" false
  | .ok config =>
      expect "PR892-07 2 GiB board accepted" true
      expect "PR892-07 2 GiB board binds the 2 GiB variant"
        (decide (boundMapOf config = variantMap 2))
      expect "PR892-07 NEGATIVE: the 2 GiB board is not bound the canonical 4 GiB map"
        (decide (boundMapOf config ≠ rpi5MachineConfig.memoryMap))

/-- PR #892 review round 2: the canonical 4 GiB board still binds the canonical
configuration — the selection is the largest covered variant, and the 8 GiB
member needs RAM above 4 GiB this board does not report. -/
def deviceTreeBridge_08_canonical_board_binds_canonical_map : IO Unit := do
  match rpi5PlatformConfigFromDtb (boardDtb 0xFC000000) [] [] none with
  | .error _ => expect "PR892-08 4 GiB board accepted" false
  | .ok config =>
      expect "PR892-08 4 GiB board binds the canonical map"
        (decide (boundMapOf config = rpi5MachineConfig.memoryMap))

/-- PR #892 review round 2: an 8 GiB board as its firmware reports it — the low
aperture and the remainder relocated above the 4 GiB boundary, 64 MiB more than
the model's high region — binds the 8 GiB variant, whose map is contained in
the report.  Two `reg` pairs, so the fixture is the shape a real blob has. -/
def deviceTreeBridge_09_eight_gib_as_reported : IO Unit := do
  let blob := boardDtbRegions [(0, 0xFC000000), (0x100000000, 0x104000000)]
  match rpi5PlatformConfigFromDtb blob [] [] none with
  | .error _ => expect "PR892-09 8 GiB board accepted" false
  | .ok config =>
      expect "PR892-09 config carries both reported regions"
        (decide (config.machineConfig.memoryMap.length = 2))
      expect "PR892-09 8 GiB board binds the 8 GiB variant"
        (decide (boundMapOf config = variantMap 8))

/-- PR #892 review round 2: a board between two variants binds the largest it
covers — 3 GiB is accepted and runs on the 2 GiB map.  The lost-resource
direction: the boot declares less RAM than the board has and never more. -/
def deviceTreeBridge_10_between_variants_binds_largest_covered : IO Unit := do
  match rpi5PlatformConfigFromDtb (boardDtb 0xC0000000) [] [] none with
  | .error _ => expect "PR892-10 3 GiB board accepted" false
  | .ok config =>
      expect "PR892-10 3 GiB board binds the 2 GiB variant"
        (decide (boundMapOf config = variantMap 2))

/-- PR #892 review round 2 (the negative a size derivation would miss): 4 GiB
of RAM at a foreign base covers no variant — the binding checks *where* the
RAM is, not how much — so the board is refused, not bound the 4 GiB map over
memory the BCM2712 does not put there. -/
def deviceTreeBridge_11_foreign_base_refused : IO Unit := do
  match rpi5PlatformConfigFromDtb (boardDtbRegions [(0x40000000, 0x100000000)]) [] [] none with
  | .error .boardDoesNotMatchBinding =>
      expect "PR892-11 RAM at a foreign base refused" true
  | _ => expect "PR892-11 RAM at a foreign base refused" false

/-- PR #892 review round 2: the union coverage reaches the bridge end to end —
a 4 GiB board reported as two adjacent halves binds the canonical map, where
the single-entry reading refused it. -/
def deviceTreeBridge_12_split_aperture_binds_canonical_map : IO Unit := do
  let blob := boardDtbRegions [(0, 0x80000000), (0x80000000, 0x7C000000)]
  match rpi5PlatformConfigFromDtb blob [] [] none with
  | .error _ => expect "PR892-12 split-aperture board accepted" false
  | .ok config =>
      expect "PR892-12 split-aperture board binds the canonical map"
        (decide (boundMapOf config = rpi5MachineConfig.memoryMap))
  -- The gap variant of the same board: the halves do not meet, so the 4 GiB
  -- member is NOT covered and the board binds the largest member it does
  -- cover — the 2 GiB one, whose aperture lies entirely in the first half.
  -- The walk stops at the gap (`memoryRegionCovered_gap_refused`); what the
  -- boot does with that is the lost-resource direction, never a false claim.
  let gapped := boardDtbRegions [(0, 0x80000000), (0x80200000, 0x7BE00000)]
  match rpi5PlatformConfigFromDtb gapped [] [] none with
  | .error _ => expect "PR892-12 NEGATIVE: a gapped board still boots on what it covers" false
  | .ok config =>
      expect "PR892-12 NEGATIVE: a gap between the halves refuses the 4 GiB member"
        (decide (boundMapOf config ≠ rpi5MachineConfig.memoryMap))
      expect "PR892-12 NEGATIVE: a gapped 4 GiB board binds the 2 GiB variant"
        (decide (boundMapOf config = variantMap 2))

/-- PR #892 review round 2: the direct entry's fallback — a caller describing no
memory at all (the model default) is bound the **smallest** variant, never the
4 GiB default: a configuration that claims no RAM a Raspberry Pi 5 lacks. -/
def deviceTreeBridge_13_direct_path_fallback_is_smallest : IO Unit := do
  let bare : PlatformConfig :=
    { irqTable := [], initialObjects := [],
      machineConfig := defaultMachineConfig, bootVSpaceRoot := none }
  expect "PR892-13 an empty account binds the smallest variant"
    (decide (boundMapOf bare = rpi5MemoryMapForConfig rpi5SmallestVariant))
  expect "PR892-13 NEGATIVE: an empty account is not bound the 4 GiB default"
    (decide (boundMapOf bare ≠ rpi5MachineConfig.memoryMap))
  let canonical : PlatformConfig := { bare with machineConfig := rpi5MachineConfig }
  expect "PR892-13 the canonical account binds the canonical map"
    (decide (boundMapOf canonical = rpi5MachineConfig.memoryMap))
  expect "PR892-13 every variant is well formed"
    (rpi5Variants.all (fun v => (rpi5MachineConfigForVariant v).wellFormed))
  expect "PR892-13 the family is ascending"
    (decide (rpi5Variants.Pairwise (fun a b => a.ramSize ≤ b.ramSize)))

/-- **PR #892 review round 5 audit**: every available top-level `/memory` node
contributes, not the first.

Found by auditing the pairs WS-XV registers rather than by review: the Rust
walker folds each node's extents into one store as it passes them, so a board
reporting its low aperture and its high bank as two nodes was read whole there
and truncated to its first node here — the two implementations answering "which
memory does this blob declare" differently. -/
def deviceTreeBridge_18_every_memory_node_contributes : IO Unit := do
  match DeviceTree.fromDtbFull twoMemoryNodeDtb rpi5MachineConfig.physicalAddressWidth with
  | .error _ => expect "RR892-18 the two-node board parses" false
  | .ok dt =>
    let ram := dt.machineConfig.memoryMap.filter (fun r => r.kind == MemoryKind.ram)
    expect "RR892-18 both memory nodes contribute" (decide (ram.length = 2))
    expect "RR892-18 the high bank is present"
      (ram.any (fun r => r.base.toNat == 0x100000000))
  -- And the bridge binds the variant the two nodes together cover, not the one
  -- the first node alone would: 8 GiB, whose map the binding installs.
  match rpi5PlatformConfigFromDtb twoMemoryNodeDtb [] [] none with
  | .error _ => expect "RR892-18 the two-node board is accepted" false
  | .ok config =>
    expect "RR892-18 the bound map is the 8 GiB variant's"
      (decide (boundMapOf config = variantMap 8))

/-- **PR #892 review round 5 audit**: the root's declared cell widths govern the
`reg`, as they do on the Rust side; the Lean path read a fixed two-cell stride
and would have mis-parsed a one-cell board entirely. -/
def deviceTreeBridge_19_root_cell_widths_are_honoured : IO Unit := do
  match DeviceTree.fromDtbFull singleCellBoardDtb rpi5MachineConfig.physicalAddressWidth with
  | .error _ => expect "RR892-19 a one-cell board parses" false
  | .ok dt =>
    let ram := dt.machineConfig.memoryMap.filter (fun r => r.kind == MemoryKind.ram)
    expect "RR892-19 the one-cell reg reads as one region" (decide (ram.length = 1))
    expect "RR892-19 …at the declared base and size"
      (ram.any (fun r => r.base.toNat == 0 && r.size == 0xFC000000))

/-- **PR #892 review round 5 audit**: a `reg` that is not a whole number of
pairs fails the whole query closed, as `fold_memory_reg` does — rather than
contributing the entries before the partial one. -/
def deviceTreeBridge_20_partial_reg_pair_refused : IO Unit := do
  match DeviceTree.fromDtbFull truncatedRegBoardDtb rpi5MachineConfig.physicalAddressWidth with
  | .ok _ => expect "RR892-20 a partial reg pair is refused" false
  | .error _ => expect "RR892-20 a partial reg pair is refused" true

/-- **PR #892 review round 5 audit**: `memory@` with no unit address is not a
memory node, matching `is_memory_node_name`. -/
def deviceTreeBridge_21_empty_unit_address_is_not_memory : IO Unit := do
  match DeviceTree.fromDtbFull emptyUnitAddressDtb rpi5MachineConfig.physicalAddressWidth with
  | .ok _ => expect "RR892-21 memory@ with no unit address is not memory" false
  | .error _ => expect "RR892-21 memory@ with no unit address is not memory" true

/-- **PR #892 review round 5**: a structure block that simply stops is refused.

The intact fixture parses and the truncated one does not — the mutation keeps
the `/memory` node and the peripherals intact and breaks only the *walk*, which
is the relation.  Before this cut `parseFdtNodes` returned the nodes it had
collected and `fromDtbFull` reported `.ok`, so the bridge decided RAM and MMIO
coverage from a prefix nothing had validated. -/
def deviceTreeBridge_14_unterminated_blob_refused : IO Unit := do
  match DeviceTree.fromDtbFull (boardDtb 0xFC000000) rpi5MachineConfig.physicalAddressWidth with
  | .ok _ => pure ()
  | .error _ => expect "RR892-14 the intact fixture still parses" false
  match DeviceTree.fromDtbFull unterminatedBoardDtb rpi5MachineConfig.physicalAddressWidth with
  | .ok _ => expect "RR892-14 an unterminated structure block is refused" false
  | .error _ => expect "RR892-14 an unterminated structure block is refused" true
  match rpi5PlatformConfigFromDtb unterminatedBoardDtb [] [] none with
  | .ok _ => expect "RR892-14 the bridge refuses it too" false
  | .error _ => expect "RR892-14 the bridge refuses it too" true

/-- **PR #892 review round 5**: an unknown token is refused rather than read as
the end of the tree. -/
def deviceTreeBridge_15_unknown_token_refused : IO Unit := do
  match DeviceTree.fromDtbFull unknownTokenBoardDtb rpi5MachineConfig.physicalAddressWidth with
  | .ok _ => expect "RR892-15 an unknown token is refused" false
  | .error _ => expect "RR892-15 an unknown token is refused" true

/-- **PR #892 review round 5**: a `/memory` node the firmware marked unavailable
is not the machine's RAM, so a board whose only memory is withheld does not
boot — the Lean twin of round 4's Rust `status` filter, on the parser the bridge
actually reads. -/
def deviceTreeBridge_16_disabled_memory_refused : IO Unit := do
  for status in ["disabled", "reserved", "fail", "fail-ecc"] do
    match DeviceTree.fromDtbFull (boardDtbWithMemoryStatus status)
        rpi5MachineConfig.physicalAddressWidth with
    | .ok _ => expect "RR892-16 a withheld memory node is refused" false
    | .error _ => expect "RR892-16 a withheld memory node is refused" true
  for status in ["okay", "ok"] do
    match rpi5PlatformConfigFromDtb (boardDtbWithMemoryStatus status) [] [] none with
    | .ok _ => expect "RR892-16 an operational memory node is accepted" true
    | .error _ => expect "RR892-16 an operational memory node is accepted" false

/-- **PR #892 review round 5**: a `memory@…` under `/reserved-memory` is a
carve-out at depth 2, not an aperture, and is not read as the machine's RAM —
the depth restriction `cmdline::find_ram_top_in_dtb` has always applied and the
Lean selector did not. -/
def deviceTreeBridge_17_reserved_memory_child_is_not_ram : IO Unit := do
  match DeviceTree.fromDtbFull reservedMemoryOnlyDtb rpi5MachineConfig.physicalAddressWidth with
  | .ok _ => expect "RR892-17 a reserved-memory child is not the machine's RAM" false
  | .error _ => expect "RR892-17 a reserved-memory child is not the machine's RAM" true

end SeLe4n.Testing.Ak9PlatformSuite

open SeLe4n.Testing.Ak9PlatformSuite in
def main : IO Unit := do
  IO.println "=== AK9 Platform Regression Suite ==="
  ak9a_01_mmioRead32_rejects_unaligned
  ak9a_02_mmioRead64_rejects_unaligned
  ak9a_03_mmioRead32_rejects_ram
  ak9a_04_mmioRead32_accepts_gic
  ak9d_01_range_within_gic_dist
  ak9d_02_range_crosses_boundary
  ak9b_01_sim_objectStoreEmptyAtBoot
  ak9b_02_rpi5_objectStoreEmptyAtBoot
  ak9c_01_empty_irqs_accepted
  ak9c_02_missing_handler_rejected
  ak9c_03_non_notification_rejected
  ak9c_04_notification_accepted
  ak9f_01_classify_empty_map
  ak9f_02_classify_unmapped
  ak9f_03_classify_mapped
  ak9f_04_applyMachineConfigChecked_rejects_zero_pa
  ak9f_05_applyMachineConfigChecked_rejects_pa_over_52
  ak9f_06_applyMachineConfigChecked_accepts_default
  ak9g_01_enables_interrupts
  ak9g_02_default_disabled
  ak9g_03_withInterrupts_enables
  -- End-to-end bootFromPlatformChecked chain
  ak9ce_01_checked_boot_rejects_bad_irq
  ak9ce_02_checked_boot_rejects_tcb_handler
  ak9fe_01_checked_boot_rejects_pa_over_52
  ak9fe_02_checked_boot_rejects_malformed_machine_config
  ak9ge_01_checked_boot_enables_interrupts
  -- AK9-A rename + positive correctness
  ak9a_05_mmioReadByte_accepts_uart
  ak9a_06_mmioRead_alias_matches_byte
  ak9a_07_mmioRead32_positive_success
  ak9a_08_mmioRead64_positive_success
  -- AK9-H readCStringChecked
  ak9h_01_readCStringChecked_rejects_oob
  ak9h_02_readCStringChecked_rejects_fuel_zero
  ak9h_03_readCStringChecked_ok
  ak9h_04_readCStringChecked_fuel_exhausted_on_unterminated
  -- AN7-D.2 RPi5 boot VSpaceRoot (DEF-P-L9 closure)
  an7d2_01_rpi5BootVSpaceRoot_wellFormed
  an7d2_02_rpi5BootVSpaceRoot_wxCompliant
  an7d2_03_rpi5BootVSpaceRoot_covers_mmio_regions
  an7d2_04_rpi5BootVSpaceRoot_paddrBounded
  -- AN7-D.5 extractPeripherals recursive walk
  an7d5_01_extractPeripherals_depth3_discovery
  review5_bus_without_ranges_hides_its_children
  review5_empty_ranges_is_the_identity
  review5_untranslatable_address_is_refused
  review5_disabled_peripheral_is_not_discovered
  an7d5_02_extractPeripherals_zero_fuel_collapses
  an7d5_03_extractPeripherals_skips_incomplete_nodes
  an7d5_04_extractPeripherals_excludes_reserved_names
  -- WS-RR RR7.27 DeviceTree → PlatformConfig bridge, end to end
  deviceTreeBridge_01_fixture_blob_parses
  deviceTreeBridge_02_matching_board_accepted
  deviceTreeBridge_03_short_ram_refused
  deviceTreeBridge_04_missing_mmio_refused
  deviceTreeBridge_05_unparseable_blob_refused
  deviceTreeBridge_06_coverage_is_refusable
  -- PR #892 review round 2: the binding installs the board's own RAM variant
  deviceTreeBridge_07_small_variants_bind_their_own_map
  deviceTreeBridge_08_canonical_board_binds_canonical_map
  deviceTreeBridge_09_eight_gib_as_reported
  deviceTreeBridge_10_between_variants_binds_largest_covered
  deviceTreeBridge_11_foreign_base_refused
  deviceTreeBridge_12_split_aperture_binds_canonical_map
  deviceTreeBridge_13_direct_path_fallback_is_smallest
  deviceTreeBridge_14_unterminated_blob_refused
  deviceTreeBridge_15_unknown_token_refused
  deviceTreeBridge_16_disabled_memory_refused
  deviceTreeBridge_17_reserved_memory_child_is_not_ram
  deviceTreeBridge_18_every_memory_node_contributes
  deviceTreeBridge_19_root_cell_widths_are_honoured
  deviceTreeBridge_20_partial_reg_pair_refused
  deviceTreeBridge_21_empty_unit_address_is_not_memory
  IO.println ""
  IO.println "=== All AK9 platform tests passed ==="
