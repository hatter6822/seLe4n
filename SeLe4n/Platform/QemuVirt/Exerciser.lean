-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- The whole kernel, not only the `virt` boot: the exerciser image calls this
-- module's initializer in place of the library root's
-- (`rust/sele4n-hal/src/lean_entry.rs`), so it must initialize everything the
-- root does.
import SeLe4n

/-!
# QEMU `virt` — the allocation exerciser's boot (WS-ZA ZA5.13)

The QEMU test image that carries the in-image drivers (`smp_exercisers`)
measures the heap allocations of every syscall round trip
(`rust/sele4n-hal/src/smp_exercisers.rs`).  Four of them — the declassification,
the declassified signal, the audit read and the audit drain — are refused by
the shipped labeling before they do anything: its declassification policy
denies every downgrade and it configures no audit monitor
(`qemuVirt_shippedLabeling_denies`).  A refusal measures nothing, so the test
image boots this deployment instead: the shipped one with three differences,
each the least the four calls need, a fourth for the interrupt entry's
scenarios (WS-ZA ZA6.32), and a fifth for the declassified signal's second hop
(WS-ZA ZA6.35), and nothing else.

* **The labeling** (`qemuVirtExerciserDeploymentLabeling`): the same partition
  at the same boundary with the same witnesses, its lower half labeled
  `kernelTrusted` rather than `lowTrusted`.  The audit monitor's clearance
  must be a top of the lattice (`validatedAuditMonitorClearance`), and a monitor
  must dominate it, so the boot domain's threads must be at the top; the upper
  half stays `highUntrusted`, so the two halves still carry different labels
  (the boot guard's `verifiesDeclaredSeparation`).  Information may now flow up
  into the boot domain, which the shipped confinement forbids — this image is a
  test image, and the shipped image keeps the confinement.
* **Two downgrades** (`qemuVirtExerciserDeclassificationPolicy`): from the boot
  domain to the upper one, the one pair the base lattice refuses that a boot
  thread can reach, and from the upper one to the low band below, so a
  declassified signal can owe two records (WS-ZA ZA6.35).
* **A low band** (`qemuVirtExerciserInLowBand`, WS-ZA ZA6.35): the ids from
  `qemuVirtExerciserLowBandBase`, which no boot object holds, labeled
  `lowTrusted`, entity and endpoint alike.  The exerciser carves a thread and
  an endpoint there, so a declassified signal's second hop can be a downgrade
  the policy permits (the upper domain into the band) or one it refuses (the
  boot domain into the band), which no boot thread's label can be.
* **The audit monitor**: the clearance is the top, so the boot domain's threads
  qualify, and the root task holds the boot audit capability in slot 10
  (`qemuVirtExerciserAuditSlot`, the exerciser's copy slot), which the
  exerciser deletes before the invocation scenarios copy into it.
* **Interrupt handlers at run time** (WS-ZA ZA6.32): the boot binds no line,
  as seL4's does not.  The exerciser issues the handler capabilities of two
  shared peripheral interrupts the `virt` board wires to nothing
  (250 and 251, `IRQ_BOUND_LINE` / `IRQ_UNBOUND_LINE` in the HAL) from the root
  task's IRQControl capability (`seL4_IRQControl_Get`) into slots 24 and 25,
  and binds the first to the interrupt notification
  (`seL4_IRQHandler_SetNotification`), so the interrupt entry's bound and
  unbound branches each have a line the exerciser raises at the distributor.

The shipped `virt` entry (`QemuVirt.kernelMain`, `lean_kernel_main_qemu_virt`)
is untouched: it boots `QemuVirtPlatform`, whose labeling is the confined
production context (`qemuVirt_deploymentLabeling`), and
`SeLe4n/Testing/BootEntryContract.lean` holds it to that call and refuses this
image's call under it.  The HAL calls this entry only on an image built with
both `board_qemu_virt` and `smp_exercisers` (`rust/sele4n-hal/src/lean_entry.rs`),
and the Raspberry Pi 5 image never carries `smp_exercisers`.

**Not in the shipped images.**  This module is its own library
(`SeLe4nQemuVirtExerciser` in `lakefile.toml`), outside `SeLe4n.lean`'s import
closure, so the kernel's archive (`libsele4n.a`) holds none of it.  The archive
builder compiles it into a second archive (`libsele4n_exerciser.a`) with its own
link roots, and only the exerciser image links them (`rust/sele4n-hal/build.rs`)
and runs its initializer.  `scripts/check_kernel_image.py --excludes` refuses
a shipped image that defines any symbol of that archive.
-/

namespace SeLe4n.Platform.QemuVirt

open SeLe4n.Model
open SeLe4n.Platform.Boot
open SeLe4n.Platform.FFI

/-- The allocation exerciser's `virt` deployment. -/
structure QemuVirtExerciserPlatform where

/-- The exerciser's two authorized downgrades: from the boot domain
    (`kernelTrusted`, domain 3) to the upper one (`highUntrusted`, domain 2),
    and from the upper one to the low band (`lowTrusted`, domain 1). -/
def qemuVirtExerciserDeclassificationPolicy : SeLe4n.Kernel.DeclassificationPolicy :=
  { canDeclassify := fun src dst =>
      (src.id == (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted).id &&
        dst.id == (SeLe4n.Kernel.embedLegacyLabel .highUntrusted).id) ||
      (src.id == (SeLe4n.Kernel.embedLegacyLabel .highUntrusted).id &&
        dst.id == (SeLe4n.Kernel.embedLegacyLabel .lowTrusted).id) }

/-- The first id of the exerciser's low band: below the upper domain's base and
    above every boot object, so the band holds only what the exerciser carves
    there. -/
def qemuVirtExerciserLowBandBase : Nat := 0x8_0000

/-- The number of ids in the exerciser's low band. -/
def qemuVirtExerciserLowBandSize : Nat := 0x100

/-- Whether an entity index is in the exerciser's low band. -/
def qemuVirtExerciserInLowBand (index : Nat) : Bool :=
  qemuVirtExerciserLowBandBase ≤ index && index < qemuVirtExerciserLowBandBase + qemuVirtExerciserLowBandSize

/-- The exerciser's entity labels: the shipped partition, its lower half at the
    top of the lattice, and the low band at `lowTrusted`. -/
def qemuVirtExerciserEntityLabel (index : Nat) : SeLe4n.Kernel.SecurityLabel :=
  if qemuVirtExerciserInLowBand index then .lowTrusted
  else SeLe4n.Kernel.indexPartitionedLabel qemuVirtUpperDomainBase .kernelTrusted .highUntrusted index

/-- The exerciser's labeling: the shipped partition at the shipped boundary and
    witnesses, its lower half at the top of the lattice, a low band, two
    downgrades and the top as the audit monitor's clearance.  An endpoint's flow
    label is its entity label, so the two agree everywhere. -/
def qemuVirtExerciserDeploymentLabeling : SeLe4n.Kernel.DeploymentLabeling :=
  { SeLe4n.Kernel.indexPartitionedDeploymentLabeling qemuVirtUpperDomainBase
      qemuVirtLowerWitnessIndex .kernelTrusted .highUntrusted (by decide)
      qemuVirtLowerWitnessIndex_admissible qemuVirtLowerWitnessIndex_below_boundary with
    entityLabelOf := qemuVirtExerciserEntityLabel
    endpointLabelOf := fun oid => qemuVirtExerciserEntityLabel oid.toNat
    hSeparated := by decide
    hEndpointObjectCoherence := fun _ => SeLe4n.Kernel.securityFlowsTo_refl _
    declassificationPolicy := qemuVirtExerciserDeclassificationPolicy
    auditMonitorClearance := some (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted) }

/-- The exerciser's binding: the `virt` binding with the exerciser's labeling. -/
instance qemuVirtExerciserPlatformBinding : PlatformBinding QemuVirtExerciserPlatform :=
  { (qemuVirtPlatformBinding : PlatformBinding QemuVirtPlatform) with
    name := "QEMU virt allocation exerciser (GICv2 / Cortex-A76 / ARM64)"
    deploymentLabeling := qemuVirtExerciserDeploymentLabeling
    witnessesOffBootVSpaceRoot := by decide }

/-- The root task's CNode slot holding the exerciser's boot audit capability:
    the exerciser's copy slot, which no scenario fills before the audit
    scenarios end, and whose next use is a copy rather than a carve. -/
def qemuVirtExerciserAuditSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 10

/-- The root task's IPC buffer's pages: the buffer frame and the three tables
    that complete the walk to it, carved at boot from their own untyped
    (`qemuVirtExerciserRootIpcBufferUntyped`), so the root task's untyped keeps
    no child the boot made and its reset scenarios still find it empty. -/
def qemuVirtExerciserRootIpcBufferPages : Nat := 4

/-- The root task's IPC-buffer untyped: the last
    `qemuVirtExerciserRootIpcBufferPages` pages of the shipped root untyped,
    which the root task's own untyped gives up
    (`qemuVirtExerciserRootTaskUntyped`).  The shipped root untyped ends where
    the region map's reservation begins (`qemuVirtRegionMap_layout`), so these
    pages lie directly below the map, never in it. -/
def qemuVirtExerciserRootIpcBufferUntyped : UntypedObject :=
  SeLe4n.Platform.RPi5.rpi5InitialUntyped
    (qemuVirtRootTaskUntyped.regionBase.toNat + qemuVirtRootTaskUntyped.regionSize -
      qemuVirtExerciserRootIpcBufferPages * 4096)
    (qemuVirtExerciserRootIpcBufferPages * 4096)

/-- The root task's untyped in the exerciser: the shipped one less the IPC
    buffer untyped's pages at its top. -/
def qemuVirtExerciserRootTaskUntyped : UntypedObject :=
  SeLe4n.Platform.RPi5.rpi5InitialUntyped qemuVirtKernelReservedEnd
    (qemuVirtRootTaskUntyped.regionSize - qemuVirtExerciserRootIpcBufferPages * 4096)

/-- The IPC-buffer untyped's object id, the first above the boot objects. -/
def qemuVirtExerciserRootIpcBufferUntypedId : SeLe4n.ObjId := ⟨11⟩

/-- The root CNode slot of the IPC-buffer untyped's capability; the three
    tables' capabilities follow it, and then the buffer frame's
    (`qemuVirtExerciserRootIpcBufferFrameSlot`).  Past the 32 slots the
    shipped root CNode has, which the exerciser fills. -/
def qemuVirtExerciserRootIpcBufferUntypedSlot : Nat := 32

/-- The root CNode slot of the IPC buffer frame's capability, seL4's
    `seL4_CapInitThreadIPCBuffer`. -/
def qemuVirtExerciserRootIpcBufferFrameSlot : Nat :=
  qemuVirtExerciserRootIpcBufferUntypedSlot + 4

/-- **The root task's IPC buffer address**: the first page of the 512 GiB
    window under level-0 index 2 of its address space, a window no exerciser
    scenario maps into (the scenarios' window is index 1, the HAL's
    `FRAME_VADDR`).  `rust/sele4n-hal/src/smp_exercisers.rs` names it
    `ROOT_IPC_BUFFER`. -/
def qemuVirtExerciserRootIpcBufferVAddr : Nat := 2 <<< 39

/-- The exerciser's root CNode geometry: one level resolving a whole 64-bit
    CPtr, a 58-bit guard over 64 slots.  The guard's value is the shipped
    root's shifted by one, so a slot's capability address is `2^63 + n`, as in
    the shipped geometry (`qemuVirtRootCNodeOf`), and the 32 slots past the
    shipped ones hold what the boot gives the root task. -/
def qemuVirtExerciserRootCNodeOf (slots : List (SeLe4n.Slot × Capability)) : CNode :=
  CNode.ofList 64 58 (qemuVirtRootTaskCNodeGuard / 2) 6 slots

/-- The exerciser's root CNode: the shipped root CNode's capabilities, the
    audit trail's, with read and write (`Capability.auditTrailManage`), in
    `qemuVirtExerciserAuditSlot`, and the IPC-buffer untyped's in
    `qemuVirtExerciserRootIpcBufferUntypedSlot`. -/
def qemuVirtExerciserRootTaskCNode : CNode :=
  qemuVirtExerciserRootCNodeOf
    (qemuVirtRootTaskCNodeSlots ++
      [ (qemuVirtExerciserAuditSlot, Capability.auditTrailManage)
      , (SeLe4n.Slot.ofNat qemuVirtExerciserRootIpcBufferUntypedSlot,
          SeLe4n.Platform.RPi5.rpi5InitialCap qemuVirtExerciserRootIpcBufferUntypedId
            [.read, .write, .retype]) ])

set_option maxRecDepth 8192 in
/-- The exerciser's initial objects: the shipped deployment's, its root CNode
    (the second entry) replaced by the exerciser's and its root untyped (the
    fifth) by the exerciser's, and the IPC-buffer untyped after them. -/
def qemuVirtExerciserInitialObjects : List ObjectEntry :=
  ((qemuVirtInitialObjects.set 1
    { id := qemuVirtRootTaskCNodeId, obj := .cnode qemuVirtExerciserRootTaskCNode
      hSlots := fun _ h => by cases h; exact CNode.slotsUnique_holds _
      hMappings := fun _ h => nomatch h }).set 4
    { id := qemuVirtRootTaskUntypedId, obj := .untyped qemuVirtExerciserRootTaskUntyped
      hSlots := fun _ h => nomatch h
      hMappings := fun _ h => nomatch h }) ++
  [ { id := qemuVirtExerciserRootIpcBufferUntypedId
      obj := .untyped qemuVirtExerciserRootIpcBufferUntyped
      hSlots := fun _ h => nomatch h
      hMappings := fun _ h => nomatch h } ]

/-- The configuration the exerciser's boot checks, whatever the account. -/
def qemuVirtExerciserBoundPlatformConfig : PlatformConfig :=
  { initialObjects := qemuVirtExerciserInitialObjects
    machineConfig := qemuVirtMachineConfig
    bootVSpaceRoot := PlatformBinding.bootVSpaceRoot (platform := QemuVirtExerciserPlatform)
    initialThreads := PlatformBinding.initialThreads (platform := QemuVirtExerciserPlatform)
    initialInterfaces := PlatformBinding.serviceInterfaces (platform := QemuVirtExerciserPlatform) }

-- ============================================================================
-- The root task's IPC buffer
-- ============================================================================

/-- The root task's capability address for root CNode slot `slot`: the guard's
    top bit and the slot (`qemuVirtExerciserRootCNodeOf`). -/
def qemuVirtExerciserRootCapAddress (slot : Nat) : SeLe4n.CPtr :=
  SeLe4n.CPtr.ofNat (2 ^ 63 + slot)

/-- One invocation the boot makes for the root task: four message words, no
    extra capability. -/
def qemuVirtExerciserRootInvocation (syscallId : SyscallId) (slot : Nat)
    (words : List Nat) : SyscallDecodeResult :=
  { capAddr := qemuVirtExerciserRootCapAddress slot
    msgInfo := { length := 4, extraCaps := 0, label := 0 }
    syscallId := syscallId
    msgRegs := (words.map SeLe4n.RegValue.ofNat).toArray
    inlineCount := 4 }

/-- **The invocations that give the root task its IPC buffer**, as seL4's boot
    gives its initial thread one (`create_ipcbuf_frame_cap`, with the tables of
    `create_it_address_space`): three page tables and a frame carved from the
    IPC-buffer untyped into the slots after its own (`untypedRetype`, the tag
    words 9 and 8), each table installed on the walk to
    `qemuVirtExerciserRootIpcBufferVAddr` (`pageTableMap`), the frame mapped
    there read-write, user and cacheable (`vspaceMap`, `PagePermissions` word
    `0b11011`), and the address set as the root TCB's buffer
    (`tcbSetIPCBuffer`).  They are the kernel's own transitions, invoked on the
    root task's capabilities: the untyped's (slot 32), the root CNode's
    (slot 2), the address space's (slot 3) and the TCB's (slot 1). -/
def qemuVirtExerciserRootIpcBufferInvocations : List SyscallDecodeResult :=
  let utSlot := qemuVirtExerciserRootIpcBufferUntypedSlot
  let ut := qemuVirtExerciserRootIpcBufferUntypedId.toNat
  let va := qemuVirtExerciserRootIpcBufferVAddr
  let cnode := (qemuVirtExerciserRootCapAddress 2).toNat
  let vspace := (qemuVirtExerciserRootCapAddress 3).toNat
  let table (i : Nat) : List SyscallDecodeResult :=
    [ qemuVirtExerciserRootInvocation .untypedRetype utSlot [9, ut + 1 + i, cnode, utSlot + 1 + i]
    , qemuVirtExerciserRootInvocation .pageTableMap (utSlot + 1 + i) [vspace, va, 0, 0] ]
  table 0 ++ table 1 ++ table 2 ++
  [ qemuVirtExerciserRootInvocation .untypedRetype utSlot
      [8, ut + 4, cnode, qemuVirtExerciserRootIpcBufferFrameSlot]
  , qemuVirtExerciserRootInvocation .vspaceMap 3
      [1, va, (qemuVirtExerciserRootCapAddress qemuVirtExerciserRootIpcBufferFrameSlot).toNat,
        0b11011]
  , qemuVirtExerciserRootInvocation .tcbSetIPCBuffer 1 [va, 0, 0, 0] ]

/-- **One invocation by the root task, made by the boot**: the checked
    dispatcher's capability path for the root thread on the boot core, as the
    compiled dispatcher runs it (`SeLe4n.Kernel.dispatchSyscallCheckedImpl`) —
    its CSpace root, then the capability resolved there with the syscall's
    right, the checked arm and the taint step in one
    (`dispatchCheckedArmThenTaintFused`) — without that dispatcher's first test, that the caller is the thread current
    on the trapping core.  That test ties a trap to its caller; the boot is not
    a trap, and no thread is current on any core until the first schedule. -/
def qemuVirtExerciserRootInvoke (decoded : SyscallDecodeResult) :
    SeLe4n.Model.Kernel Unit := fun st =>
  let tid := SeLe4n.ThreadId.mk qemuVirtLowerWitnessIndex
  let ctx := PlatformBinding.labeling (platform := QemuVirtExerciserPlatform)
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    match st.getObject? tcb.cspaceRoot with
    | some (.cnode rootCn) =>
      let gate : SeLe4n.Kernel.SyscallGate :=
        { callerId := tid, cspaceRoot := tcb.cspaceRoot, capAddr := decoded.capAddr
          capDepth := rootCn.depth
          requiredRight := SeLe4n.Kernel.syscallRequiredRight decoded.syscallId }
      SeLe4n.Kernel.dispatchCheckedArmThenTaintFused ctx decoded tid
        SeLe4n.Kernel.Concurrency.bootCoreId gate st
    | some _ => .error (.invalidCapability 0)
    | none => .error .objectNotFound
  | some _ => .error .illegalState
  | none => .error .objectNotFound

/-- **The boot's last step**: each of `qemuVirtExerciserRootIpcBufferInvocations`
    made in turn for the root task (`qemuVirtExerciserRootInvoke`) on the
    state the boot installed.  The first refusal stops it. -/
def qemuVirtExerciserGiveRootIpcBuffer (st : SystemState) : Except KernelError SystemState :=
  qemuVirtExerciserRootIpcBufferInvocations.foldlM
    (fun st decoded =>
      match qemuVirtExerciserRootInvoke decoded st with
      | .ok ((), st') => .ok st'
      | .error e => .error e)
    st

/-- The step on the live kernel state, as a syscall seam commits one: the
    state the dispatches leave, its physical-write and instruction-cache
    ledgers read and cleared in the same step and then performed (the buffer
    page and the tables scrubbed, the four descriptors stored).  A refusal
    changes nothing and halts every PE. -/
def qemuVirtExerciserGiveRootIpcBufferOrHalt : BaseIO Unit := do
  let owed ← Platform.FFI.modifyGetKernelState (fun st =>
    match qemuVirtExerciserGiveRootIpcBuffer st with
    | .ok post =>
        (some (post.drainedPhysicalWrites, post.pendingIcacheMaintenance),
          SeLe4n.Kernel.Architecture.clearIcacheMaintenance
            (SeLe4n.Kernel.Architecture.clearPhysicalWrites post))
    | .error _ => (none, st))
  match owed with
  | none => ffiFatalHaltAll
  | some (writes, icache) => do
      Platform.FFI.completePhysicalWrites writes
      Platform.FFI.completeIcacheMaintenance icache

-- ============================================================================
-- The boot, and the entry
-- ============================================================================

/-- The checked platform boot at the exerciser's binding. -/
def bootAndInitialiseQemuVirtExerciser (config : PlatformConfig) :
    BaseIO (Except String SeLe4n.Model.SystemState) :=
  bootAndInitialisePlatform QemuVirtExerciserPlatform config

/-- The exerciser's boot with its failure handled: a refused boot halts every
    PE.  An accepted one ends by giving the root task its IPC buffer
    (`qemuVirtExerciserGiveRootIpcBufferOrHalt`), so the root task's first
    syscall finds it mapped, as seL4's initial thread does. -/
def bootAndInitialiseQemuVirtExerciserOrHalt (config : PlatformConfig) : BaseIO Unit := do
  match ← bootAndInitialiseQemuVirtExerciser config with
  | .ok _ => qemuVirtExerciserGiveRootIpcBufferOrHalt
  | .error _ => ffiFatalHaltAll

/-- **The exerciser image's only correct boot call** — the `virt` device-tree
    boot (`qemuVirtPlatformConfigFromDtb`, the shipped entry's own check of the
    board) at the exerciser's binding, its failure handled.  What
    `lean_kernel_main_qemu_virt_exerciser` is, and what
    `SeLe4n/Testing/BootEntryContract.lean` holds that entry to. -/
def bootAndInitialiseQemuVirtExerciserFromDtbOrHalt (blob : ByteArray)
    (initialObjects : List ObjectEntry)
    (bootVSpaceRoot : Option BootVSpaceRootEntry) : BaseIO Unit :=
  match qemuVirtPlatformConfigFromDtb blob initialObjects bootVSpaceRoot with
  | .error _ => ffiFatalHaltAll
  | .ok config => do
      extendBootRamMap qemuVirtBootRamExtensions
      bootAndInitialiseQemuVirtExerciserOrHalt config

/-- The exerciser image's boot entry: `lean_kernel_main_qemu_virt_exerciser`,
    which `rust/sele4n-hal/src/lean_entry.rs` calls in place of
    `lean_kernel_main_qemu_virt` on an image built with `smp_exercisers`. -/
@[export lean_kernel_main_qemu_virt_exerciser]
def exerciserKernelMain (dtb : ByteArray) : BaseIO Unit :=
  bootAndInitialiseQemuVirtExerciserFromDtbOrHalt dtb qemuVirtExerciserInitialObjects none

-- ============================================================================
-- What differs, and what does not
-- ============================================================================

/-- **The shipped `virt` labeling refuses all four calls**: its declassification
    policy denies every pair and it configures no audit monitor, so the shipped
    image's `.declassify` and `.declassifySignal` are `.declassificationDenied`
    and its `.auditRead` and `.auditDrain` `.illegalAuthority`
    (`auditRead_unconfigured_denied`, `auditDrain_unconfigured_denied`). -/
theorem qemuVirt_shippedLabeling_denies :
    (∀ src dst, (PlatformBinding.labeling (platform := QemuVirtPlatform)).declassificationPolicy.canDeclassify
        src dst = false) ∧
    (PlatformBinding.labeling (platform := QemuVirtPlatform)).auditMonitorClearance = none ∧
    SeLe4n.Kernel.validatedAuditMonitorClearance
        (PlatformBinding.labeling (platform := QemuVirtPlatform)) = none :=
  ⟨fun _ _ => rfl, rfl, rfl⟩

/-- The exerciser's policy authorizes exactly two pairs: the boot domain to the
    upper one, and the upper one to the low band. -/
theorem qemuVirtExerciserDeclassificationPolicy_canDeclassify_iff
    (src dst : SeLe4n.Kernel.SecurityDomain) :
    qemuVirtExerciserDeclassificationPolicy.canDeclassify src dst = true ↔
      (src = SeLe4n.Kernel.embedLegacyLabel .kernelTrusted ∧
        dst = SeLe4n.Kernel.embedLegacyLabel .highUntrusted) ∨
      (src = SeLe4n.Kernel.embedLegacyLabel .highUntrusted ∧
        dst = SeLe4n.Kernel.embedLegacyLabel .lowTrusted) := by
  obtain ⟨s⟩ := src
  obtain ⟨d⟩ := dst
  simp [qemuVirtExerciserDeclassificationPolicy, SeLe4n.Kernel.embedLegacyLabel,
    SeLe4n.Kernel.SecurityLabel.kernelTrusted, SeLe4n.Kernel.SecurityLabel.highUntrusted,
    SeLe4n.Kernel.SecurityLabel.lowTrusted]

/-- The exerciser's monitor clearance validates — it is the top — so its audit
    calls are not refused for want of a monitor. -/
theorem qemuVirtExerciser_validatedAuditMonitorClearance :
    SeLe4n.Kernel.validatedAuditMonitorClearance
        (PlatformBinding.labeling (platform := QemuVirtExerciserPlatform)) =
      some (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted) := by
  decide

/-- The exerciser's labeling declares the shipped witnesses, so its boot starts
    the shipped initial threads. -/
theorem qemuVirtExerciser_initialThreads :
    PlatformBinding.initialThreads (platform := QemuVirtExerciserPlatform) =
      PlatformBinding.initialThreads (platform := QemuVirtPlatform) := rfl

/-- The exerciser's boot binds the shipped machine and boot root. -/
theorem qemuVirtExerciser_bindMachineConfig (board : SeLe4n.MachineConfig) :
    PlatformBinding.bindMachineConfig (platform := QemuVirtExerciserPlatform) board =
      qemuVirtMachineConfig := rfl

/-- WS-ZA ZA6.32: the exerciser's bound configuration serves `virt`'s lines,
    `qemuVirtGicSpiCount + 32`, the count the interrupt entry and the
    acknowledge refuse a line outside of. -/
theorem qemuVirtExerciser_bound_interruptLineCount (board : SeLe4n.MachineConfig) :
    (PlatformBinding.bindMachineConfig (platform := QemuVirtExerciserPlatform)
      board).interruptLineCount = qemuVirtGicSpiCount + 32 := rfl

-- ============================================================================
-- Every gate of the exerciser's checked boot, decided
-- ============================================================================

set_option maxRecDepth 8192 in
theorem qemuVirtExerciserBoundPlatformConfig_wellFormed :
    qemuVirtExerciserBoundPlatformConfig.wellFormed = true := by
  unfold PlatformConfig.wellFormed
  rw [objectIdsUnique_eq_transparent]
  decide

-- WS-ZA ZA6.4: the root CNode's cells: the shipped deployment's, the audit trail's and
-- the IPC-buffer untyped's, in a 64-slot geometry.
set_option maxRecDepth 8192 in
theorem qemuVirtExerciserBoundPlatformConfig_bootSafe :
    qemuVirtExerciserBoundPlatformConfig.initialObjects.all
      (fun entry => bootSafeObjectCheck entry.obj) = true := by
  decide

theorem qemuVirtExerciserBoundPlatformConfig_asidsDistinct :
    bootVSpaceAsidsDistinct qemuVirtExerciserBoundPlatformConfig = true := by
  decide

theorem qemuVirtExerciserBoundPlatformConfig_rootDistinct :
    bootVSpaceRootObjIdDistinct qemuVirtExerciserBoundPlatformConfig = true := by
  decide

theorem qemuVirtExerciserBoundPlatformConfig_rootNonSentinel :
    bootVSpaceRootObjIdNonSentinel qemuVirtExerciserBoundPlatformConfig = true := by
  decide

theorem qemuVirtExerciserBoundPlatformConfig_rootSafe :
    bootVSpaceRootSafe qemuVirtExerciserBoundPlatformConfig = true := by
  unfold bootVSpaceRootSafe
  decide

/-- The exerciser's checked boot takes its success arm — none of its refusals
    is reachable. -/
theorem qemuVirtExerciserBoundPlatformConfig_checked :
    bootFromPlatformChecked qemuVirtExerciserBoundPlatformConfig =
      .ok (bootEnableInterruptsOp
        (installBootVSpaceRoot (bootFromPlatform qemuVirtExerciserBoundPlatformConfig)
          qemuVirtBootVSpaceRootEntry.id qemuVirtBootVSpaceRootEntry.root
          qemuVirtBootVSpaceRootEntry.hMappings)) :=
  bootFromPlatformChecked_admits_bootVSpace _ qemuVirtExerciserBoundPlatformConfig_wellFormed
    qemuVirtExerciserBoundPlatformConfig_bootSafe
    qemuVirtExerciserBoundPlatformConfig_asidsDistinct
    qemuVirtMachineConfig_wellFormed
    (by decide)
    qemuVirtExerciserBoundPlatformConfig_rootDistinct
    qemuVirtExerciserBoundPlatformConfig_rootNonSentinel
    qemuVirtExerciserBoundPlatformConfig_rootSafe qemuVirtBootVSpaceRootEntry rfl

/-- The root task's two untypeds tile the shipped root untyped's region: the
    root task's from the kernel's extent up, the IPC buffer's directly above it
    to the shipped untyped's top, which is the region map's base
    (`regionMapBaseOf`), so the exerciser hands the root task the same memory
    as the shipped deployment, one IPC buffer's pages set aside, and none of
    the map's reserved pages. -/
theorem qemuVirtExerciserRootUntypeds_tile :
    qemuVirtExerciserRootTaskUntyped.regionBase = qemuVirtRootTaskUntyped.regionBase ∧
    qemuVirtExerciserRootTaskUntyped.regionBase.toNat +
        qemuVirtExerciserRootTaskUntyped.regionSize =
      qemuVirtExerciserRootIpcBufferUntyped.regionBase.toNat ∧
    qemuVirtExerciserRootIpcBufferUntyped.regionBase.toNat +
        qemuVirtExerciserRootIpcBufferUntyped.regionSize =
      qemuVirtRootTaskUntyped.regionBase.toNat + qemuVirtRootTaskUntyped.regionSize ∧
    [qemuVirtExerciserRootIpcBufferUntyped.regionBase.toNat +
        qemuVirtExerciserRootIpcBufferUntyped.regionSize] =
      qemuVirtBootRamExtensions.map regionMapBaseOf := by
  decide

/-- The root task's IPC buffer is page aligned, canonical, and under a level-0
    entry of its own: not the scenarios' window (level-0 index 1). -/
theorem qemuVirtExerciserRootIpcBufferVAddr_placed :
    qemuVirtExerciserRootIpcBufferVAddr % 4096 = 0 ∧
    qemuVirtExerciserRootIpcBufferVAddr < 2 ^ 48 ∧
    qemuVirtExerciserRootIpcBufferVAddr >>> 39 = 2 := by
  decide

end SeLe4n.Platform.QemuVirt
