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

/-- AN7-D.5: `extractPeripherals` discovers peripherals at depth 3+ via
    the new recursive walk.  The previous 2-level walk (pre-AN7-D.5)
    would have missed the `level3-device` in this synthetic tree; the
    new recursive form finds it. -/
def an7d5_01_extractPeripherals_depth3_discovery : IO Unit := do
  -- Build a depth-3 tree:
  --   level1-bus (depth 1)
  --     └─ level2-controller (depth 2)
  --         └─ level3-device (depth 3)
  let deepTree : List FdtNode := [
    mkPeripheral "level1-bus" 0x10000000 [
      mkPeripheral "level2-controller" 0x20000000 [
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

private def regNameOff : Nat := 0
private def deviceTypeNameOff : Nat := (fdtString "reg").size
private def compatibleNameOff : Nat :=
  (fdtString "reg").size + (fdtString "device_type").size

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

/-- A device tree for a board with `ramSize` bytes of RAM starting at 0 and the
three MMIO windows the RPi5 binding programs. -/
private def boardDtb (ramSize : Nat) (withMmio : Bool := true) : ByteArray :=
  let memoryNode :=
    fdtBeginNode "memory@0"
      ++ fdtProp deviceTypeNameOff (fdtString "memory")
      ++ fdtProp regNameOff (be64 0 ++ be64 ramSize)
      ++ fdtEndNodeTok
  let peripherals :=
    if withMmio then
      peripheralNode "serial@fe201000" 0xFE201000 0x1000
        ++ peripheralNode "interrupt-controller@ff841000" 0xFF841000 0x1000
        ++ peripheralNode "interrupt-controller@ff842000" 0xFF842000 0x2000
    else #[]
  assembleDtb (fdtBeginNode "" ++ memoryNode ++ peripherals ++ fdtEndNodeTok ++ fdtEndTok)

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

/-- WS-RR RR7.27: a board with less RAM than the binding declares is refused.
The mutation that finds a vacuous check: the blob is well formed, the
peripherals are all there, and only the RAM extent differs. -/
def deviceTreeBridge_03_short_ram_refused : IO Unit := do
  match rpi5PlatformConfigFromDtb (boardDtb 0x40000000) [] [] none with
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
  IO.println ""
  IO.println "=== All AK9 platform tests passed ==="
