-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- The whole kernel: the exerciser image calls its library root's initializer
-- in place of the kernel's (`rust/sele4n-hal/src/lean_entry.rs`), so the
-- exerciser's modules must reach everything the kernel's root does.
import SeLe4n

/-!
# The allocation exerciser's deployment, on any board (WS-ZA ZA5.13, WS-RB RB3)

The test image that carries the in-image drivers (`smp_exercisers`) measures
the heap allocations of every syscall round trip
(`rust/sele4n-hal/src/smp_exercisers.rs`).  It boots this deployment instead of
the shipped one, on the Raspberry Pi 5 (`SeLe4n/Platform/RPi5/Exerciser.lean`,
on rpi5_machine's `raspi5b`) and on QEMU `virt`
(`SeLe4n/Platform/QemuVirt/Exerciser.lean`).  Everything the exerciser's
scenarios name is here, once: the objects and their ids, the root CNode's
slots, the labeling, and the boot's last step that gives the root task its IPC
buffer.  A board supplies only its memory: the page its boot table pool
starts each address space's top-level table at (`tablePage`) and the RAM the
boot maps outside the kernel's extent (`extensions`).  So the HAL drives one
layout on both boards, and a count that differs between them is a finding
about the kernel, not about the deployment.

The shipped deployments refuse four of the calls the exerciser measures — the
declassification, the declassified signal, the audit read and the audit drain
— before they do anything: their declassification policy denies every
downgrade and they configure no audit monitor.  A refusal measures nothing, so
this deployment differs from the shipped labeling in five ways, each the least
its scenarios need, and in nothing else.

* **The labeling** (`deploymentLabeling`): the shipped partition at the shipped
  boundary (`upperDomainBase`) with the shipped witnesses, its lower half
  labeled `kernelTrusted` rather than `lowTrusted`.  The audit monitor's
  clearance must be a top of the lattice (`validatedAuditMonitorClearance`), and
  a monitor must dominate it, so the boot domain's threads must be at the top;
  the upper half stays `highUntrusted`, so the two halves still carry
  different labels (the boot guard's `verifiesDeclaredSeparation`).
  Information may now flow up into the boot domain, which the shipped
  confinement forbids: this image is a test image, and the shipped images keep
  the confinement.
* **Two downgrades** (`declassificationPolicy`): from the boot domain to the
  upper one, the one pair the base lattice refuses that a boot thread can
  reach, and from the upper one to the low band below, so a declassified
  signal can owe two records (WS-ZA ZA6.35).
* **A low band** (`inLowBand`, WS-ZA ZA6.35): the ids from `lowBandBase`, which
  no boot object holds, labeled `lowTrusted`, entity and endpoint alike.  The
  exerciser carves a thread and an endpoint there, so a declassified signal's
  second hop can be a downgrade the policy permits (the upper domain into the
  band) or one it refuses (the boot domain into the band).
* **The audit monitor**: the clearance is the top, so the boot domain's
  threads qualify, and the root task holds the boot audit capability in slot
  10 (`auditSlot`, the exerciser's copy slot), which the exerciser deletes
  before the invocation scenarios copy into it.
* **Interrupt handlers at run time** (WS-ZA ZA6.32): the boot binds no line,
  as seL4's does not.  The exerciser issues the handler capabilities of two
  shared peripheral interrupts its board wires to nothing (the HAL's
  `IRQ_BOUND_LINE` / `IRQ_UNBOUND_LINE`, per board) from the root task's
  IRQControl capability (`seL4_IRQControl_Get`) into slots 24 and 25, and binds
  the first to the interrupt notification, so the interrupt entry's bound and
  unbound branches each have a line the exerciser raises at the distributor.

| Object | Id |
|---|---|
| root task TCB (the lower separation witness) | `2` |
| root task CNode (64 slots, 58-bit guard) | `3` |
| root task VSpace (ASID 1, pool page 0) | `4` |
| interrupt notification | `5` |
| root task untyped: the first extension's untyped part, its top four pages set aside | `6` |
| partner TCB (`.Inactive` until resumed) | `7` |
| endpoint | `8` |
| reply object | `9` |
| scheduling context (unconfigured, unbound) | `10` |
| the root task's IPC-buffer untyped: those four pages | `11` |
| one untyped per further extension (boards past their first gigabyte) | `0x4_0000`, … |
| untrusted initial TCB (the upper witness, pinned to core 1) | `0x10_0000` |
| its CNode | `0x10_0001` |
| its VSpace (ASID 2, pool page 1) | `0x10_0002` |

**Not in the shipped images.**  These modules are their own library
(`SeLe4nExerciser` in `lakefile.toml`, rooted at `SeLe4n.Platform.Exerciser`),
outside `SeLe4n.lean`'s import closure, so the kernel's archive
(`libsele4n.a`) holds none of it.  The archive builder compiles them into a
second archive (`libsele4n_exerciser.a`) with its own link roots, and only an
exerciser image links them (`rust/sele4n-hal/build.rs`) and runs their
initializer.  `scripts/check_kernel_image.py --excludes` refuses a shipped
image that defines any symbol of that archive.
-/

namespace SeLe4n.Platform.Exerciser

open SeLe4n.Model
open SeLe4n.Platform.Boot
open SeLe4n.Platform.FFI
open SeLe4n.Platform.RPi5 (rpi5InitialThread rpi5InitialCap rpi5InitialCNode rpi5InitialUntyped
  schedControlBootSlots)

-- ============================================================================
-- The labeling
-- ============================================================================

/-- The index the untrusted domain begins at: the boundary both boards' shipped
    deployments draw (`rpi5UpperDomainBase`, `qemuVirtUpperDomainBase`). -/
def upperDomainBase : Nat := 0x10_0000

/-- The lower separation witness, the root task's TCB: the shipped one on both
    boards (`rpi5LowerWitnessIndex`, `qemuVirtLowerWitnessIndex`). -/
def lowerWitnessIndex : Nat := 2

theorem lowerWitnessIndex_admissible :
    SeLe4n.Kernel.separationWitnessAdmissible ⟨lowerWitnessIndex⟩ = true := by
  decide

theorem lowerWitnessIndex_below_boundary :
    lowerWitnessIndex < SeLe4n.Kernel.separationBoundary upperDomainBase := by
  decide

/-- The exerciser's two authorized downgrades: from the boot domain
    (`kernelTrusted`, domain 3) to the upper one (`highUntrusted`, domain 2),
    and from the upper one to the low band (`lowTrusted`, domain 1). -/
def declassificationPolicy : SeLe4n.Kernel.DeclassificationPolicy :=
  { canDeclassify := fun src dst =>
      (src.id == (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted).id &&
        dst.id == (SeLe4n.Kernel.embedLegacyLabel .highUntrusted).id) ||
      (src.id == (SeLe4n.Kernel.embedLegacyLabel .highUntrusted).id &&
        dst.id == (SeLe4n.Kernel.embedLegacyLabel .lowTrusted).id) }

/-- The first id of the exerciser's low band: below the upper domain's base and
    above every boot object, so the band holds only what the exerciser carves
    there. -/
def lowBandBase : Nat := 0x8_0000

/-- The number of ids in the exerciser's low band. -/
def lowBandSize : Nat := 0x100

/-- Whether an entity index is in the exerciser's low band. -/
def inLowBand (index : Nat) : Bool :=
  lowBandBase ≤ index && index < lowBandBase + lowBandSize

/-- The exerciser's entity labels: the shipped partition, its lower half at the
    top of the lattice, and the low band at `lowTrusted`. -/
def entityLabel (index : Nat) : SeLe4n.Kernel.SecurityLabel :=
  if inLowBand index then .lowTrusted
  else SeLe4n.Kernel.indexPartitionedLabel upperDomainBase .kernelTrusted .highUntrusted index

/-- The exerciser's labeling: the shipped partition at the shipped boundary and
    witnesses, its lower half at the top of the lattice, a low band, two
    downgrades and the top as the audit monitor's clearance.  An endpoint's flow
    label is its entity label, so the two agree everywhere. -/
def deploymentLabeling : SeLe4n.Kernel.DeploymentLabeling :=
  { SeLe4n.Kernel.indexPartitionedDeploymentLabeling upperDomainBase
      lowerWitnessIndex .kernelTrusted .highUntrusted (by decide)
      lowerWitnessIndex_admissible lowerWitnessIndex_below_boundary with
    entityLabelOf := entityLabel
    endpointLabelOf := fun oid => entityLabel oid.toNat
    hSeparated := by decide
    hEndpointObjectCoherence := fun _ => SeLe4n.Kernel.securityFlowsTo_refl _
    declassificationPolicy := declassificationPolicy
    auditMonitorClearance := some (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted) }

/-- The exerciser's policy authorizes exactly two pairs: the boot domain to the
    upper one, and the upper one to the low band. -/
theorem declassificationPolicy_canDeclassify_iff (src dst : SeLe4n.Kernel.SecurityDomain) :
    declassificationPolicy.canDeclassify src dst = true ↔
      (src = SeLe4n.Kernel.embedLegacyLabel .kernelTrusted ∧
        dst = SeLe4n.Kernel.embedLegacyLabel .highUntrusted) ∨
      (src = SeLe4n.Kernel.embedLegacyLabel .highUntrusted ∧
        dst = SeLe4n.Kernel.embedLegacyLabel .lowTrusted) := by
  obtain ⟨s⟩ := src
  obtain ⟨d⟩ := dst
  simp [declassificationPolicy, SeLe4n.Kernel.embedLegacyLabel,
    SeLe4n.Kernel.SecurityLabel.kernelTrusted, SeLe4n.Kernel.SecurityLabel.highUntrusted,
    SeLe4n.Kernel.SecurityLabel.lowTrusted]

/-- The exerciser's monitor clearance validates — it is the top — so its audit
    calls are not refused for want of a monitor. -/
theorem validatedAuditMonitorClearance_eq :
    SeLe4n.Kernel.validatedAuditMonitorClearance
        (SeLe4n.Kernel.deploymentLabelingContext deploymentLabeling) =
      some (SeLe4n.Kernel.embedLegacyLabel .kernelTrusted) := by
  decide

-- ============================================================================
-- Object ids and the root CNode's slots
-- ============================================================================

/-- The root task's TCB — the lower separation witness. -/
def rootTaskTcbId : SeLe4n.ObjId := ⟨lowerWitnessIndex⟩
/-- The root task's CNode. -/
def rootTaskCNodeId : SeLe4n.ObjId := ⟨3⟩
/-- The root task's VSpace. -/
def rootTaskVSpaceId : SeLe4n.ObjId := ⟨4⟩
/-- The notification the root task binds its interrupt handlers to. -/
def interruptNotificationId : SeLe4n.ObjId := ⟨5⟩
/-- The root task's untyped, over its board's first extension. -/
def rootTaskUntypedId : SeLe4n.ObjId := ⟨6⟩
/-- **WS-ZA ZA4.1**: a second boot-domain thread.  The root task cannot make a
    thread, an endpoint or a reply object itself (untyped retype carves frames,
    page tables, untypeds and address spaces only), so the scenarios that need
    a partner — a send that finds a receiver waiting, a call answered by a
    reply, a wait woken by a signal — have their objects configured here.  The
    thread shares the root task's CSpace and address space and stays
    `.Inactive` until the exerciser resumes it. -/
def partnerTcbId : SeLe4n.ObjId := ⟨7⟩
/-- The endpoint the partner scenarios rendezvous on. -/
def endpointId : SeLe4n.ObjId := ⟨8⟩
/-- The reply object a call's receiver answers through. -/
def replyId : SeLe4n.ObjId := ⟨9⟩
/-- **WS-ZA ZA5.2**: the scheduling context the exerciser configures, binds to
    the partner and unbinds, configured here because the root task cannot make
    one. -/
def schedContextId : SeLe4n.ObjId := ⟨10⟩
/-- The root task's IPC-buffer untyped, the first id above the boot objects. -/
def rootIpcBufferUntypedId : SeLe4n.ObjId := ⟨11⟩
/-- The first id of the untypeds over a board's further extensions: in the boot
    domain, below the low band, and clear of every id the exerciser carves. -/
def extraUntypedIdBase : Nat := 0x4_0000
/-- The untrusted domain's initial TCB — the upper separation witness. -/
def untrustedTcbId : SeLe4n.ObjId := ⟨upperDomainBase⟩
/-- Its CNode. -/
def untrustedCNodeId : SeLe4n.ObjId := ⟨upperDomainBase + 1⟩
/-- Its VSpace. -/
def untrustedVSpaceId : SeLe4n.ObjId := ⟨upperDomainBase + 2⟩

/-- The core the untrusted thread is pinned to — core 1, so the two domains'
    threads start on two cores. -/
def untrustedCore : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩

/-- The root CNode's guard: its top bit set, so a slot's capability address is
    `2^63 + n`.  WS-ZA ZA4.8: every capability address the exerciser resolves is
    then a word that does not fit a scalar `Nat`, and its guard and slot are
    read from that word on every lookup the gate measures. -/
def rootTaskCNodeGuard : UInt64 := 2 ^ 57

/-- The root guard's width: 58 bits above the 6-bit radix, so one level
    resolves a whole 64-bit CPtr.  Carried by the capabilities naming the root
    CNode (each root thread's CSpace root and the CNode's own slot 2), as seL4
    keeps a CNode's guard in `cap_cnode_cap`. -/
def rootTaskCNodeGuardSize : UInt8 := 58

/-- **WS-ZA ZA6.4**: the first of the root task's scheduling-control slots, core
    `c`'s at `16 + c`. -/
def schedControlSlotBase : Nat := 16

/-- **WS-ZA ZA6.32**: the root task's interrupt-control slot, above the
    scheduling controls — seL4's boot info `seL4_CapIRQControl`. -/
def irqControlSlot : Nat := 20

/-- The root CNode slot holding the boot audit capability: the exerciser's copy
    slot, which no scenario fills before the audit scenarios end, and whose
    next use is a copy rather than a carve. -/
def auditSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 10

/-- The root CNode slot of the IPC-buffer untyped's capability; the three
    tables' capabilities follow it, and then the buffer frame's
    (`rootIpcBufferFrameSlot`). -/
def rootIpcBufferUntypedSlot : Nat := 32

/-- The root CNode slot of the IPC buffer frame's capability, seL4's
    `seL4_CapInitThreadIPCBuffer`. -/
def rootIpcBufferFrameSlot : Nat := rootIpcBufferUntypedSlot + 4

/-- The first root CNode slot of the further extensions' untypeds: the top
    three, above every slot a scenario names. -/
def extraUntypedSlotBase : Nat := 61

/-- The root task's IPC buffer's pages: the buffer frame and the three tables
    that complete the walk to it, carved at boot from their own untyped, so the
    root task's untyped keeps no child the boot made and its reset scenarios
    still find it empty. -/
def rootIpcBufferPages : Nat := 4

/-- **The root task's IPC buffer address**: the first page of the 512 GiB
    window under level-0 index 2 of its address space, a window no exerciser
    scenario maps into (the scenarios' window is index 1, the HAL's
    `FRAME_VADDR`).  `rust/sele4n-hal/src/smp_exercisers.rs` names it
    `ROOT_IPC_BUFFER`. -/
def rootIpcBufferVAddr : Nat := 2 <<< 39

/-- The root task's boot capabilities, by slot: its own TCB, CNode (with the
    exerciser's guard) and VSpace, the interrupt notification, the untyped,
    the partner thread, endpoint and reply object, and in slot 0 the scheduling
    context (slot 9 is left free for the reply capability the exerciser mints
    from slot 8, and slots 10 to 15 for what it copies and carves), the
    interrupt control, each core's scheduling control, the audit trail's
    capability with read and write (`Capability.auditTrailManage`), the
    IPC-buffer untyped's, and one per further extension's untyped
    (`extraUntypeds`, `count` of them). -/
def rootTaskCNodeSlots (count : Nat) : List (SeLe4n.Slot × Capability) :=
  [ (SeLe4n.Slot.ofNat 1, rpi5InitialCap rootTaskTcbId [.read, .write, .grant, .grantReply])
  , (SeLe4n.Slot.ofNat 2, rpi5InitialCap rootTaskCNodeId [.read, .write, .grant, .grantReply]
      rootTaskCNodeGuard rootTaskCNodeGuardSize)
  , (SeLe4n.Slot.ofNat 3, rpi5InitialCap rootTaskVSpaceId [.read, .write])
  , (SeLe4n.Slot.ofNat 4, rpi5InitialCap interruptNotificationId [.read, .write])
  , (SeLe4n.Slot.ofNat 5, rpi5InitialCap rootTaskUntypedId [.read, .write, .retype])
  , (SeLe4n.Slot.ofNat 6, rpi5InitialCap partnerTcbId [.read, .write, .grant, .grantReply])
  , (SeLe4n.Slot.ofNat 7, rpi5InitialCap endpointId [.read, .write, .grant, .grantReply])
  , (SeLe4n.Slot.ofNat 8, rpi5InitialCap replyId [.read, .write, .grant])
  , (SeLe4n.Slot.ofNat 0, rpi5InitialCap schedContextId [.read, .write])
  , (SeLe4n.Slot.ofNat irqControlSlot, Capability.irqControl) ] ++
  schedControlBootSlots schedControlSlotBase ++
  [ (auditSlot, Capability.auditTrailManage)
  , (SeLe4n.Slot.ofNat rootIpcBufferUntypedSlot,
      rpi5InitialCap rootIpcBufferUntypedId [.read, .write, .retype]) ] ++
  (List.range count).map fun i =>
    (SeLe4n.Slot.ofNat (extraUntypedSlotBase + i),
      rpi5InitialCap ⟨extraUntypedIdBase + i⟩ [.read, .write, .retype])

/-- The root CNode: 64 slots, one level resolving a whole 64-bit CPtr through
    the 58-bit guard its capabilities carry. -/
def rootTaskCNode (count : Nat) : CNode :=
  CNode.ofList 6 (rootTaskCNodeSlots count)

/-- The untrusted thread's CNode: its own objects and nothing of the boot
    domain's. -/
def untrustedCNode : CNode :=
  rpi5InitialCNode
    [ (SeLe4n.Slot.ofNat 1, rpi5InitialCap untrustedTcbId [.read, .write, .grant, .grantReply])
    , (SeLe4n.Slot.ofNat 2, rpi5InitialCap untrustedCNodeId [.read, .write, .grant, .grantReply]
      (guardSize := 60))
    , (SeLe4n.Slot.ofNat 3, rpi5InitialCap untrustedVSpaceId [.read, .write]) ]

-- ============================================================================
-- Objects, over a board's memory
-- ============================================================================

/-- An empty user address space on `asid` whose top-level table is the
    `page`-th page of the board's table-page pool. -/
def initialVSpace (tablePage : Nat → SeLe4n.PAddr) (asid : SeLe4n.ASID) (page : Nat) :
    VSpaceRoot :=
  { asid := asid, mappings := SeLe4n.Kernel.RobinHood.RHTable.empty 16
    tableBase := some (tablePage page) }

/-- The first extension the board's boot maps: the one the root task's two
    untypeds tile. -/
def firstExtension (extensions : List (Nat × Nat)) : Nat × Nat :=
  extensions.headD (0, 0)

/-- The root task's untyped: the first extension's untyped part
    (`untypedExtentOf`, below the region map's reservation) less the IPC
    buffer's pages at its top. -/
def rootTaskUntyped (extensions : List (Nat × Nat)) : UntypedObject :=
  rpi5InitialUntyped (firstExtension extensions).1
    (untypedSizeOf (firstExtension extensions).2 - rootIpcBufferPages * 4096)

/-- The root task's IPC-buffer untyped: the last `rootIpcBufferPages` pages of
    the first extension's untyped part, directly below the region map. -/
def rootIpcBufferUntyped (extensions : List (Nat × Nat)) : UntypedObject :=
  rpi5InitialUntyped
    (regionMapBaseOf (firstExtension extensions) - rootIpcBufferPages * 4096)
    (rootIpcBufferPages * 4096)

/-- One untyped per further extension, each over its untyped part, the `i`-th
    at id `extraUntypedIdBase + i`. -/
def extraUntypeds (extensions : List (Nat × Nat)) : List (SeLe4n.ObjId × UntypedObject) :=
  extensions.tail.mapIdx fun i e =>
    (⟨extraUntypedIdBase + i⟩, rpi5InitialUntyped e.1 (untypedSizeOf e.2))

private def tcbEntry (id : SeLe4n.ObjId) (tcb : TCB) : ObjectEntry :=
  { id := id, obj := .tcb tcb
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

private def cnodeEntry (id : SeLe4n.ObjId) (cn : CNode) : ObjectEntry :=
  { id := id, obj := .cnode cn
    hSlots := fun _ h => by cases h; exact CNode.slotsUnique_holds _
    hMappings := fun _ h => nomatch h }

private def vspaceEntry (tablePage : Nat → SeLe4n.PAddr) (id : SeLe4n.ObjId)
    (asid : SeLe4n.ASID) (page : Nat) : ObjectEntry :=
  { id := id, obj := .vspaceRoot (initialVSpace tablePage asid page)
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => by
      cases h; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExt 16 (by omega) }

private def untypedEntry (id : SeLe4n.ObjId) (ut : UntypedObject) : ObjectEntry :=
  { id := id, obj := .untyped ut
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

private def notificationEntry (id : SeLe4n.ObjId) : ObjectEntry :=
  { id := id
    obj := .notification
      { state := .idle, hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero }
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

private def endpointEntry (id : SeLe4n.ObjId) : ObjectEntry :=
  { id := id, obj := .endpoint {}
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

private def replyEntry (id : SeLe4n.ObjId) : ObjectEntry :=
  { id := id, obj := .reply (SeLe4n.Kernel.Reply.empty (SeLe4n.ReplyId.ofObjId id))
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

private def schedContextEntry (id : SeLe4n.ObjId) : ObjectEntry :=
  { id := id
    obj := .schedContext
      (SeLe4n.Kernel.SchedContext.empty (SeLe4n.SchedContextId.ofObjId id))
    hSlots := fun _ h => nomatch h
    hMappings := fun _ h => nomatch h }

/-- The root thread and the partner: both in the root task's CSpace, through
    the exerciser's guard, and its address space. -/
def rootThread (id : SeLe4n.ObjId) : TCB :=
  rpi5InitialThread id rootTaskCNodeId rootTaskVSpaceId rootTaskCNodeGuard rootTaskCNodeGuardSize

/-- The untrusted domain's initial thread, pinned to `untrustedCore`. -/
def untrustedThread : TCB :=
  { rpi5InitialThread untrustedTcbId untrustedCNodeId untrustedVSpaceId with
    cpuAffinity := some untrustedCore }

/-- **The exerciser's initial objects on a board**: whose boot table pool
    starts at `tablePage` and whose boot maps `extensions` outside the
    kernel's extent (`Platform.FFI.extendBootRamMap`'s argument). -/
def initialObjects (tablePage : Nat → SeLe4n.PAddr) (extensions : List (Nat × Nat)) :
    List ObjectEntry :=
  [ tcbEntry rootTaskTcbId (rootThread rootTaskTcbId)
  , cnodeEntry rootTaskCNodeId (rootTaskCNode extensions.tail.length)
  , vspaceEntry tablePage rootTaskVSpaceId (SeLe4n.ASID.ofNat 1) 0
  , notificationEntry interruptNotificationId
  , untypedEntry rootTaskUntypedId (rootTaskUntyped extensions)
  , tcbEntry partnerTcbId (rootThread partnerTcbId)
  , endpointEntry endpointId
  , replyEntry replyId
  , schedContextEntry schedContextId
  , tcbEntry untrustedTcbId untrustedThread
  , cnodeEntry untrustedCNodeId untrustedCNode
  , vspaceEntry tablePage untrustedVSpaceId (SeLe4n.ASID.ofNat 2) 1
  , untypedEntry rootIpcBufferUntypedId (rootIpcBufferUntyped extensions) ] ++
  (extraUntypeds extensions).map fun u => untypedEntry u.1 u.2

/-- The root task's two untypeds tile the first extension's untyped part: the
    root task's from the extension's base up, the IPC buffer's directly above
    it to the region map's base, so the exerciser hands the root task the
    memory the shipped deployment does, one IPC buffer's pages set aside, and
    none of the map's reserved pages. -/
theorem rootUntypeds_tile (extensions : List (Nat × Nat))
    (h : rootIpcBufferPages * 4096 ≤ untypedSizeOf (firstExtension extensions).2) :
    (rootTaskUntyped extensions).regionBase.toNat = (firstExtension extensions).1 ∧
    (rootTaskUntyped extensions).regionBase.toNat + (rootTaskUntyped extensions).regionSize =
      (rootIpcBufferUntyped extensions).regionBase.toNat ∧
    (rootIpcBufferUntyped extensions).regionBase.toNat +
        (rootIpcBufferUntyped extensions).regionSize =
      regionMapBaseOf (firstExtension extensions) := by
  have hBase (b s : Nat) : (rpi5InitialUntyped b s).regionBase.toNat = b := rfl
  have hSize (b s : Nat) : (rpi5InitialUntyped b s).regionSize = s := rfl
  unfold rootTaskUntyped rootIpcBufferUntyped regionMapBaseOf
  rw [hBase, hBase, hSize, hSize]
  exact ⟨rfl, by omega, by omega⟩

/-- The root task's IPC buffer is page aligned, canonical, and under a level-0
    entry of its own: not the scenarios' window (level-0 index 1). -/
theorem rootIpcBufferVAddr_placed :
    rootIpcBufferVAddr % 4096 = 0 ∧ rootIpcBufferVAddr < 2 ^ 48 ∧
    rootIpcBufferVAddr >>> 39 = 2 := by
  decide

-- ============================================================================
-- The root task's IPC buffer
-- ============================================================================

/-- The root task's capability address for root CNode slot `slot`: the guard's
    top bit and the slot (`rootTaskCNodeGuard`). -/
def rootCapAddress (slot : Nat) : SeLe4n.CPtr :=
  SeLe4n.CPtr.ofNat (2 ^ 63 + slot)

/-- One invocation the boot makes for the root task: four message words, no
    extra capability. -/
def rootInvocation (syscallId : SyscallId) (slot : Nat) (words : List Nat) :
    SyscallDecodeResult :=
  { capAddr := rootCapAddress slot
    msgInfo := { length := 4, extraCaps := 0, label := 0 }
    syscallId := syscallId
    msgRegs := (words.map SeLe4n.RegValue.ofNat).toArray
    inlineCount := 4 }

/-- **The invocations that give the root task its IPC buffer**, as seL4's boot
    gives its initial thread one (`create_ipcbuf_frame_cap`, with the tables of
    `create_it_address_space`): three page tables and a frame carved from the
    IPC-buffer untyped into the slots after its own (`untypedRetype`, the tag
    words 9 and 8), each table installed on the walk to `rootIpcBufferVAddr`
    (`pageTableMap`), the frame mapped there read-write, user and cacheable
    (`vspaceMap`, `PagePermissions` word `0b11011`), and the address set as the
    root TCB's buffer (`tcbSetIPCBuffer`).  They are the kernel's own
    transitions, invoked on the root task's capabilities: the untyped's
    (slot 32), the root CNode's (slot 2), the address space's (slot 3) and the
    TCB's (slot 1). -/
def rootIpcBufferInvocations : List SyscallDecodeResult :=
  let utSlot := rootIpcBufferUntypedSlot
  let ut := rootIpcBufferUntypedId.toNat
  let va := rootIpcBufferVAddr
  let cnode := (rootCapAddress 2).toNat
  let vspace := (rootCapAddress 3).toNat
  let table (i : Nat) : List SyscallDecodeResult :=
    [ rootInvocation .untypedRetype utSlot [9, ut + 1 + i, cnode, utSlot + 1 + i]
    , rootInvocation .pageTableMap (utSlot + 1 + i) [vspace, va, 0, 0] ]
  table 0 ++ table 1 ++ table 2 ++
  [ rootInvocation .untypedRetype utSlot [8, ut + 4, cnode, rootIpcBufferFrameSlot]
  , rootInvocation .vspaceMap 3
      [1, va, (rootCapAddress rootIpcBufferFrameSlot).toNat, 0b11011]
  , rootInvocation .tcbSetIPCBuffer 1 [va, 0, 0, 0] ]

/-- **One invocation by the root task, made by the boot**, under platform
    `P`'s labeling: the checked dispatcher's capability path for the root
    thread on the boot core, as the compiled dispatcher runs it
    (`SeLe4n.Kernel.dispatchSyscallCheckedImpl`) — its CSpace root, then the
    capability resolved there with the syscall's right, the checked arm and
    the taint step in one (`dispatchCheckedArmThenTaintFused`) — without that
    dispatcher's first test, that the caller is the thread current on the
    trapping core.  That test ties a trap to its caller; the boot is not a
    trap, and no thread is current on any core until the first schedule. -/
def rootInvoke (P : Type) [PlatformBinding P] (decoded : SyscallDecodeResult) :
    SeLe4n.Model.Kernel Unit := fun st =>
  let tid := SeLe4n.ThreadId.mk lowerWitnessIndex
  let ctx := PlatformBinding.labeling (platform := P)
  match st.getObject? tid.toObjId with
  | some (.tcb tcb) =>
    let gate : SeLe4n.Kernel.SyscallGate :=
      { callerId := tid, cspaceRootCap := tcb.spaceCells[0], capAddr := decoded.capAddr
        requiredRight := SeLe4n.Kernel.syscallRequiredRight decoded.syscallId }
    SeLe4n.Kernel.dispatchCheckedArmThenTaintFused ctx decoded tid
      SeLe4n.Kernel.Concurrency.bootCoreId gate st
  | some _ => .error .illegalState
  | none => .error .objectNotFound

/-- **The boot's last step**: each of `rootIpcBufferInvocations` made in turn
    for the root task (`rootInvoke`) on the state the boot installed.  The
    first refusal stops it. -/
def giveRootIpcBuffer (P : Type) [PlatformBinding P] (st : SystemState) :
    Except KernelError SystemState :=
  rootIpcBufferInvocations.foldlM
    (fun st decoded =>
      match rootInvoke P decoded st with
      | .ok ((), st') => .ok st'
      | .error e => .error e)
    st

/-- The step on the live kernel state, as a syscall seam commits one: the
    state the dispatches leave, its physical-write and instruction-cache
    ledgers read and cleared in the same step and then performed (the buffer
    page and the tables scrubbed, the four descriptors stored).  A refusal
    changes nothing and halts every PE. -/
def giveRootIpcBufferOrHalt (P : Type) [PlatformBinding P] : BaseIO Unit := do
  let owed ← Platform.FFI.modifyGetKernelState (fun st =>
    match giveRootIpcBuffer P st with
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

/-- **The exerciser's boot at platform `P`**, its failure handled: the checked
    platform boot of `config` at `P`'s binding, a refusal halting every PE.
    An accepted boot ends by giving the root task its IPC buffer
    (`giveRootIpcBufferOrHalt`), so the root task's first syscall finds it
    mapped, as seL4's initial thread does. -/
def bootAndInitialiseOrHalt (P : Type) [PlatformBinding P] (config : PlatformConfig) :
    BaseIO Unit := do
  match ← bootAndInitialisePlatform P config with
  | .ok _ => giveRootIpcBufferOrHalt P
  | .error _ => ffiFatalHaltAll

end SeLe4n.Platform.Exerciser
