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
import SeLe4n.Platform.Sim.BootContract
import SeLe4n.Platform.DeviceTree
import SeLe4n.Testing.Helpers

/-! # AK9 Platform Regression Suite — Phase AK9 audit remediation

Runtime regression checks for the AK9 Platform / Boot / DTB / MMIO
audit findings (`docs/dev_history/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` §12):

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
  { state := .idle, waitingThreads := [] }

private def minimalTcb (tid : ThreadId) : TCB :=
  { tid := tid
    priority := ⟨0⟩
    domain := ⟨0⟩
    cspaceRoot := ⟨0⟩
    vspaceRoot := ⟨0⟩
    ipcBuffer := (SeLe4n.VAddr.ofNat (0)) }

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
    [{ base := (SeLe4n.PAddr.ofNat (0x0)), size := 0x1000, kind := .ram }]
  expect "AK9-F-02 classifyChecked unmapped rejected"
    (classifyMemoryRegionChecked fdtRegion pm = none)

/-- AK9-F (P-M04): Non-empty map with address in region → some kind. -/
def ak9f_03_classify_mapped : IO Unit := do
  let fdtRegion : FdtMemoryRegion := { base := 0x500, size := 0x100 }
  let pm : List MemoryRegion :=
    [{ base := (SeLe4n.PAddr.ofNat (0x0)), size := 0x1000, kind := .ram }]
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
-- Entry point
-- ============================================================================

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
  IO.println ""
  IO.println "=== All AK9 platform tests passed ==="
