-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.Policy
import Std.Data.HashSet

/-!
WS-C3 proof-surface note:

Determinism of pure Lean definitions is a meta-property, so tautological equalities
such as `f x = f x` do not constitute security evidence.
Tracked replacement obligations for the information-flow projection surface live in
TPI-002 (the TPI registry has been absorbed into closed workstreams).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (bootCoreId)

/-- Observer descriptor for IF-M1 projections. -/
structure IfObserver where
  clearance : SecurityLabel
  deriving Repr, DecidableEq

/-- Projection result used by IF-M1 low-equivalence statements.

WS-F3/CRIT-02: Extended with `activeDomain`, `irqHandlers`, and `objectIndex`
to cover all security-relevant scheduler, interrupt, and identity fields.

WS-H8/A-36/H-11: Extended with `domainTimeRemaining`, `domainSchedule`, and
`domainScheduleIndex` to prevent timing-channel attacks via domain scheduling
metadata. All three are visible under scheduling transparency (same rationale
as `activeDomain`).

WS-H10/C-05/A-38: Extended with `machineRegs` (domain-gated register file
projection). Machine timer is deliberately excluded — it is a kernel-internal
monotonic counter; projecting it unconditionally would create a covert timing
channel. Memory projection deferred to WS-H11 (VSpace domain ownership). -/
structure ObservableState where
  objects : SeLe4n.ObjId → Option KernelObject
  runnable : List SeLe4n.ThreadId
  current : Option SeLe4n.ThreadId
  /-- WS-F3: Active scheduling domain — visible to all observers (scheduling
      transparency: all threads need to know which domain is active).
      WS-H8/A-36: Documented as deliberate security assumption — scheduling
      transparency requires all threads to observe the active domain for
      deterministic scheduling behavior. This matches seL4's domain scheduler
      design where domain identity is not a secret. -/
  activeDomain : SeLe4n.DomainId
  /-- WS-F3: IRQ handler mappings filtered to only those targeting observable
      notification objects. Prevents leaking high-domain IRQ routing. -/
  irqHandlers : SeLe4n.Irq → Option SeLe4n.ObjId
  /-- WS-F3: Object index filtered to observable IDs. Prevents leaking the
      existence of high-domain objects through the identity registry. -/
  objectIndex : List SeLe4n.ObjId
  /-- WS-H8/A-36/H-11: Remaining ticks in current domain schedule entry.
      Visible under scheduling transparency — allows NI proofs to cover
      domain timing state, preventing timing-channel information leaks. -/
  domainTimeRemaining : Nat
  /-- WS-H8/A-36/H-11: Domain schedule table. Visible under scheduling
      transparency — the schedule is system-wide configuration, not per-domain
      secret state. -/
  domainSchedule : List DomainScheduleEntry
  /-- WS-H8/A-36/H-11: Current index into domain schedule. Visible under
      scheduling transparency. -/
  domainScheduleIndex : Nat
  /-- WS-H10/C-05/A-38: Machine register file, filtered by current thread
      observability. The register file represents the currently-executing
      thread's architectural context. Visible only when the current thread
      is observable to the observer; `none` otherwise.
      Note: Memory projection (`Memory = PAddr → UInt8`) is deferred to
      WS-H11 (VSpace domain ownership model required for meaningful per-domain
      memory partitioning in the abstract model). -/
  machineRegs : Option RegisterFile
  /-- WS-I2/R-16: Optional memory projection, filtered by domain ownership.
      When `ctx.memoryOwnership = none`, this projection is empty (`none` at
      all addresses) for backward compatibility. -/
  memory : SeLe4n.PAddr → Option UInt8
  -- The service registry has no field of its own (WS-ZA ZA5.9): it is read off
  -- the endpoints, which `objects` shows with their service records, so an
  -- observer sees exactly the registrations of the endpoints it can see
  -- (`serviceRegistry_eq_of_projectObjects_eq`).

/-- Object observability gate under a labeling context. -/
def objectObservable (ctx : LabelingContext) (observer : IfObserver) (oid : SeLe4n.ObjId) : Bool :=
  securityFlowsTo (ctx.objectLabelOf oid) observer.clearance

/-- Thread observability gate under a labeling context. -/
def threadObservable (ctx : LabelingContext) (observer : IfObserver) (tid : SeLe4n.ThreadId) : Bool :=
  securityFlowsTo (ctx.threadLabelOf tid) observer.clearance

-- ============================================================================
-- WS-F3/F-22: CNode slot filtering to prevent capability target leakage
-- ============================================================================

/-- WS-F3/F-22: Observability gate for capability targets. A capability target
is observable iff the referenced entity is within the observer's clearance.
This prevents CNode projections from leaking the identity of high-domain
objects through capability slot contents. -/
def capTargetObservable (ctx : LabelingContext) (observer : IfObserver) (target : CapTarget) : Bool :=
  match target with
  | .object oid => objectObservable ctx observer oid
  | .cnodeSlot cnode _ => objectObservable ctx observer cnode
  -- WS-SM SM6.D: a reply cap now references a `Reply` object by `ReplyId`; the
  -- slot reveals that object's identity, so it is observable iff the reply
  -- object is — consistent with the `.object`/`.cnodeSlot` arms above.
  | .replyCap rid => objectObservable ctx observer rid.toObjId
  -- WS-SM SM9.A.9: an audit-trail capability names no object, so there is no
  -- entity whose identity a slot holding it could leak.  Observable to every
  -- observer, exactly as a fieldless authority should be: the *content* it
  -- unlocks is gated by the reader's clearance at the read
  -- (`auditLogVisibleTo`), never by whether the capability is visible.
  | .auditTrail => true
  -- WS-ZA ZA6.4: a scheduling-control capability names a core, which every
  -- observer knows; the authority it carries is the configure's, whose writes
  -- are the context's.
  | .schedControl _ => true

/-- WS-F3/F-22: Filter a KernelObject to redact high-domain information.
For CNode objects, removes capability slots whose targets are not observable
by the given observer. All other object types pass through unchanged.

WS-G5: Uses `HashMap.filter` for O(m) filtering on HashMap-backed CNode slots. -/
def projectKernelObject (ctx : LabelingContext) (observer : IfObserver) (obj : KernelObject) : KernelObject :=
  match obj with
  | .cnode cn =>
      -- WS-ZA ZA5.3 part 4: the derivation links are cleared, as the tree they
      -- encode is not projected.
      .cnode (cn.filterSlots (fun _ cap =>
        capTargetObservable ctx observer cap.target)).withoutLinks
  | .tcb tcb =>
      -- WS-H12c: Strip registerContext from projected TCBs. Register context
      -- is saved/restored by schedule's inline context switch and is an
      -- implementation detail of the scheduler, not a security-relevant
      -- kernel object property. Projecting it away ensures that
      -- saveOutgoingContext/restoreIncomingContext do not affect the
      -- information-flow projection.
      -- X5-I (L-6): Confirmed v0.22.17 audit — register stripping is sound at
      -- the logical level. The projection model intentionally abstracts away
      -- architectural register state for NI purposes.
      -- AK6-G (NI-M01): Strip `pendingMessage` and `timedOut`.
      -- Historically these two fields survived projection (see commentary
      -- below) because the NI invariants `runnableThreadIpcReady`,
      -- `currentNotEndpointQueueHead`, and domain scheduling together made
      -- cross-domain exposure "unreachable under the live invariants" —
      -- but the projection itself is defined as a pure function of the
      -- state and must not depend on a deployment-time invariant witness.
      -- A malformed state or any path that bypasses the invariants would
      -- expose cross-domain IPC and timeout signal to non-current
      -- observers. AK6-G closes the covert channel by stripping both
      -- fields structurally at projection time.
      --
      -- M-07/AH5-A (historical rationale — now preserved as defense-in-
      -- depth): `pendingMessage` leakage is unreachable under the NI
      -- invariant conjunction:
      --
      -- 1. `runnableThreadIpcReady`: observable threads are in `.ready` IPC state,
      --    meaning they have no pending message from a cross-domain sender.
      -- 2. `currentNotEndpointQueueHead`: the current thread is not in any endpoint
      --    queue, preventing it from receiving cross-domain messages while observable.
      -- 3. Domain scheduling: only threads in the current domain are observable,
      --    and IPC messages across domains require a domain switch.
      --
      -- `timedOut` is set by `timeoutThread` on budget exhaustion during
      -- cross-domain IPC — propagating its value across projection would
      -- leak the fact that a different domain's budget expired. The flag
      -- is purely internal scheduling plumbing (cleared by
      -- `timeoutAwareReceive`), not a security-relevant property.
      --
      -- AI4-A: Also strip schedContextBinding — internal scheduling plumbing
      -- (donation chain state), not security-relevant observable state. Donation
      -- chain changes (returnDonatedSchedContext) modify only this field and must
      -- not leak through the NI projection.
      -- AJ2-B (M-11): Strip pipBoost — cross-domain PIP boost reflects blocking
      -- relationships and could leak timing information across security domains.
      -- A thread's effective priority boost is an internal scheduling detail,
      -- not a security-relevant observable property.
      -- WS-SM SM5.B (NI-M01 lineage, PR #805 review P2-4): Strip cpuAffinity —
      -- per-thread CPU *placement* is a scheduler resource-management decision
      -- (which physical core runs the thread), structurally the same class as
      -- schedContextBinding and pipBoost above, not part of the thread's
      -- observable logical identity for IPC/capability purposes.  Two states
      -- differing only by a (high/scheduler-driven) affinity change must project
      -- to the *same* low object, or the NI projection would leak cross-domain
      -- placement decisions once setThreadCpuAffinity (SM5.C) can change it.
      -- Stripped structurally (not by a "no operation sets it yet" invariant
      -- witness) per the projection's pure-function discipline — mirrors AK6-G's
      -- structural stripping of pendingMessage/timedOut.
      -- WS-SM SM6.D (PR #822 review, Reply objects): Strip `replyObject` — the
      -- forward TCB→Reply link (seL4's `tcb->tcbReply`) names which first-class
      -- Reply object a blocked caller is waiting on.  Linking a high caller to a
      -- low-visible thread (or the cross-domain Call→Reply rendezvous) would
      -- otherwise change the low projection and leak the reply-object identity.
      -- Structurally erased — same class as `schedContextBinding`/`pipBoost`
      -- above (internal IPC/donation plumbing, not the thread's observable
      -- logical identity).  The matching `Reply.caller` back-link is erased by
      -- the `.reply` arm below.
      .tcb { tcb with registerContext := default, scBindingScCode := 0, scBindingOwnerCode := 0,
                       pipBoostCode := SeLe4n.Priority.optCode none, pendingMessage := none, timedOut := false,
                       cpuAffinity := none, replyObjectCode := 0,
                       pendingReceiveReplyCode := 0,
                       -- WS-BP BP7.9: the saved FP/SIMD context is the thread's
                       -- own register state, erased exactly as `registerContext`
                       -- is; the lazy switch (`Architecture.fpAccessOnCore` /
                       -- `fpReleaseOnCore`) writes it, and an observer that saw
                       -- it would see every value the thread computed in FP.
                       fpContext := default,
                       -- WS-ZA ZA4.5: the run-queue links (seL4's
                       -- `tcbSchedNext`/`tcbSchedPrev`) name the threads
                       -- queued beside this one on its core, whatever their
                       -- domain; erased as `cpuAffinity` is — the scheduler's
                       -- own projection carries what an observer may see of
                       -- the run queue.
                       runCoreCode := 0, runPrio := ⟨0⟩, runPrevCode := 0,
                       runNextCode := 0, runBucketPrevCode := 0,
                       runBucketNextCode := 0,
                       -- WS-ZA ZA4.6: the reply-waiter links and ends name the
                       -- callers reply-blocked on the same server, whatever
                       -- their domain; erased as `pipBoost`, which they feed,
                       -- and `replyObject` are.
                       replyWaiterPrevCode := 0, replyWaiterNextCode := 0,
                       replyWaitersHeadCode := 0, replyWaitersCount := 0,
                       -- WS-ZA ZA4.7: a blocked sender's badge, grant bit and
                       -- fault flag are the parked half of its message (seL4's
                       -- `blockingIPCBadge`/`blockingIPCCanGrant`/`blockingIPCIsCall`);
                       -- erased as `pendingMessage`, the field they replace, is.
                       ipcBadge := 0, ipcBadged := false, ipcCanGrant := false,
                       ipcFaultSend := false,
                       -- The context the thread is the recorded origin of is
                       -- erased, as the context's own `donationOrigin` is.
                       originScCode := 0,
                       -- The derivation links of the thread's two space slots
                       -- are cleared, as a CNode's are: the tree they encode is
                       -- not projected.  The space capabilities stay visible.
                       spaceLinks := Vector.replicate _ 0,
                       -- WS-ZA ZA5.11: the taint words are provenance about
                       -- the content the thread holds, recorded for the
                       -- downgrade detector, not observable state — erased as
                       -- the table they mirror is never projected.
                       taintTag0 := 0, taintTag1 := 0, taintTag2 := 0, taintTag3 := 0,
                       taintTag4 := 0, taintTag5 := 0, taintTag6 := 0, taintTag7 := 0,
                       taintCount := 0, taintSaturated := false,
                       -- WS-ZA ZA6.6: the yield link (seL4-MCS's `tcbYieldTo`)
                       -- names the context the thread yielded to, whatever its
                       -- domain; erased as the binding codes are, and the
                       -- context's own end (`yieldFromCode`) below.
                       yieldToCode := 0 }
  | .schedContext sc =>
      -- AI4-A: Strip boundThread — internal scheduling plumbing binding a
      -- SchedContext to its owning thread. Donation chain changes modify only
      -- this field and must not leak through the NI projection.
      --
      -- WS-OD OD2.2: strip `scReply` for the same reason, and in the same cut
      -- as the field itself.  It is the head of this context's MCS reply stack
      -- — a **ReplyId**, so it names the innermost Call the context was donated
      -- through, and with it the caller that Call blocked.  That is the same
      -- class of cross-domain linkage the `.reply` arm below erases
      -- (`caller` / `prev` / `next`) and the TCB arm erases
      -- (`schedContextBinding` / `replyObject`): internal donation plumbing,
      -- not part of the context's observable logical identity.  Landing the
      -- erasure with the field is what keeps the OD4 push *unobservable* — a
      -- push writes this head, and an un-erased head would make a high caller's
      -- Call visible through a low-visible scheduling context.
      --
      -- **WS-HP HP10.3**: strip `donationOrigin` for the third time over the same
      -- reason, and again in the cut that adds the field.  It is a **ThreadId** —
      -- the thread that owned this reservation when it first left — so it names a
      -- possibly-high caller directly, which is the linkage `boundThread` above
      -- and the `.reply` arm's `caller` below are erased for.  Landing the
      -- erasure with the field is what keeps the HP10 write unobservable: the
      -- origin is recorded by a `Call` that donates and cleared when the loan
      -- ends, so an un-erased origin would make a high client's Call visible
      -- through a low-visible scheduling context for as long as the loan lasts —
      -- strictly longer than the `scReply` head, which moves with every push.
      --
      -- **WS-ZA ZA6.3**: strip the release-queue links — `releaseNextCode`
      -- (seL4-MCS's intrusive release-queue successor), `releaseCoreCode` (the
      -- core whose queue holds the context) and `releaseAt` (its place in that
      -- queue).  One core's release queue interleaves contexts of every domain,
      -- so a low context's successor link can name a high context, and its
      -- place moves when a high context is inserted ahead of it or drained.
      -- Erased as the run-queue links are on the TCB arm (WS-ZA ZA4.5), and in
      -- the cut that adds them: the queue is the scheduler's, and an observer
      -- sees of it only what the scheduler's own projection carries.
      .schedContext { sc with boundThreadCode := 0, scReply := none,
                              donationOrigin := none,
                              releaseNextCode := 0, releaseCoreCode := 0, releaseAt := 0,
                              -- WS-ZA ZA6.6: the yield link's context end
                              -- (seL4-MCS's `scYieldFrom`) names the thread that
                              -- yielded to this context — a possibly-high
                              -- thread, as `boundThread` is — so it is erased
                              -- with the thread's end, in the cut that adds both.
                              yieldFromCode := 0 }
  | .reply r =>
      -- WS-SM SM6.D (PR #822 review, Reply objects): Strip the Reply object's
      -- cross-domain linkage — `caller` (the back-link to the blocked caller
      -- TCB), `prev` (the reply-stack link to the enclosing call's reply) and
      -- `next` (the link to the frame above, or — on the head — to the donated
      -- SchedContext; WS-OD `v0.35.4`, seL4's `replyNext`).  These three fields
      -- name high-domain thread / SchedContext / reply-stack identities; leaving them in the
      -- low projection would leak who is blocked on (or donating to) a
      -- low-visible reply object once the receive-path links it.  Mirrors the
      -- `.schedContext` `boundThread := none` stripping and the TCB
      -- `schedContextBinding`/`replyObject` stripping above — structural, per
      -- the projection's pure-function discipline.
      --
      -- PR #822 review (Codex): also **normalize `replyId`** to the sentinel.  The
      -- *outer* object key is gated by `objectObservable`, but the Reply's *internal*
      -- `replyId` field need not equal that key (`wellFormed` does not enforce it,
      -- and a retyped Reply is built with `ReplyId.sentinel`), so an un-normalized
      -- internal id would leak a hidden ReplyId through a low-visible Reply object.
      -- Erasing it to the canonical sentinel removes the channel.
      --
      -- The recorded stasher (`stasherCode`) is erased with the caller link: it
      -- names a receiving thread exactly as `callerCode` names a calling one, and
      -- a stash records it only on its own write, so no wake or clear on the
      -- thread's side changes this projection.
      .reply { r with replyId := SeLe4n.ReplyId.sentinel,
                      callerCode := 0, prev := none, next := none, stasherCode := 0,
                      capTarget := .replyCap SeLe4n.ReplyId.sentinel, capTarget_eq := rfl }
  -- WS-SM SM8.B.4 stripped the per-object lock word here, because `RwLockState`
  -- carries core identities (`writerHeld`, `readers`, `waiters`) and an
  -- observer that could see an object would otherwise see the cores operating
  -- on it.  Since WS-LS LS3.1 no kernel object carries a lock word: the lock
  -- state is the ghost table beside the kernel state
  -- (`Concurrency/Locks/LockState.lean`), which no projection reads, so the
  -- lock-contention channel CC-5 is a hardware **timing** channel only, exactly
  -- as the SM8 plan's Definition 3.4.1 describes it — there is no model-level
  -- state to erase.  The remaining kinds carry only their observable identity,
  -- gated by `objectObservable` on the object's own key: an endpoint's and a
  -- notification's queues, an address space's mappings, an untyped's extent, a
  -- frame's `base` and `isDevice` (WS-BP BP7.1: *which* physical memory the
  -- object is), and a page table's `base` and `installedIn`.
  -- An endpoint's service record (`Endpoint.service`, its flag and the
  -- registration's words) is the service registered on it (seL4 has no such
  -- registry); since WS-ZA ZA5.9 it is the registry itself.  It is kept: a
  -- registration is labelled with the endpoint it names (`serviceObservable`),
  -- so an observer sees exactly the registrations of visible endpoints.  A
  -- notification's `irqBound` is kept for the same reason: it is true exactly
  -- when an IRQ names the notification, which `projectIrqHandlers` already
  -- shows for every visible notification.
  | .endpoint e => .endpoint e
  -- WS-ZA ZA5.11: a notification's taint words are erased as a thread's are.
  | .notification n => .notification (n.withTaintWords {})
  | .vspaceRoot v => .vspaceRoot v
  | .untyped u => .untyped u
  | .frame f => .frame f
  | .pageTable p => .pageTable p

/-- WS-ZA ZA5.11 (**the projection strips the taint words, on every kind**):
an object projects as its erasure does, so a write of nothing but taint words
moves no observer's view. -/
theorem projectKernelObject_eraseTaint (ctx : LabelingContext) (observer : IfObserver)
    (o : KernelObject) :
    projectKernelObject ctx observer o.eraseTaint = projectKernelObject ctx observer o := by
  cases o <;> rfl

/-- ...and so does the object with any words written. -/
theorem projectKernelObject_withTaintWords (ctx : LabelingContext) (observer : IfObserver)
    (o : KernelObject) (w : SeLe4n.Kernel.TaintWords) :
    projectKernelObject ctx observer (o.withTaintWords w) = projectKernelObject ctx observer o := by
  rw [← projectKernelObject_eraseTaint ctx observer (o.withTaintWords w),
    KernelObject.eraseTaint_withTaintWords, projectKernelObject_eraseTaint]

/-- WS-F3/F-22: `projectKernelObject` is idempotent — filtering twice yields
observationally equivalent results to filtering once.

WS-G5: With RHTable-backed CNode slots, idempotency is stated at the slot
lookup level rather than structural equality, because `RHTable.filter`
may reorder internal entries, making
`(m.filter f).filter f ≠ m.filter f` structurally despite identical entries.
For all non-CNode variants, structural equality holds directly. -/
theorem projectKernelObject_idempotent
    (ctx : LabelingContext) (observer : IfObserver) (obj : KernelObject)
    (slot : SeLe4n.Slot)
    (hUniq : ∀ cn, obj = .cnode cn → cn.slotsUnique) :
    match projectKernelObject ctx observer (projectKernelObject ctx observer obj),
          projectKernelObject ctx observer obj with
    | .cnode cn1, .cnode cn2 => cn1.lookup slot = cn2.lookup slot
    | _, _ => True := by
  cases obj with
  | cnode cn =>
    simp only [projectKernelObject, CNode.lookup, CNode.slots_withoutLinks, CNode.slots_filterSlots,
      SeLe4n.UniqueSlotMap.get?, SeLe4n.UniqueSlotMap.filter]
    -- WS-RC R4.A: project to `.table` for the underlying RHTable lemma.
    exact SeLe4n.Kernel.RobinHood.RHTable.filter_filter_getElem? cn.slots.table _ slot (hUniq cn rfl).1
  | _ => trivial

/-- WS-F3/F-22: `projectKernelObject` preserves object type. -/
theorem projectKernelObject_objectType
    (ctx : LabelingContext) (observer : IfObserver) (obj : KernelObject) :
    (projectKernelObject ctx observer obj).objectType = obj.objectType := by
  cases obj <;> rfl

/-- AK6-G (NI-M01): `projectKernelObject` strips cross-domain IPC from
    projected TCBs. The projection erases `pendingMessage` regardless of the
    source state — whatever inter-domain message is latched on the TCB, the
    projection shows `none`. Combined with `projectObjects` gating by
    `objectObservable`, this closes the covert channel through which an
    observer could distinguish two states that differ only in a
    cross-domain sender's message content. -/
theorem projectKernelObject_erases_cross_domain_ipc
    (ctx : LabelingContext) (observer : IfObserver) (tcb : TCB) :
    match projectKernelObject ctx observer (.tcb tcb) with
    | .tcb tcb' => tcb'.pendingMessage = none
    | _ => True := by
  simp [projectKernelObject]

/-- AK6-G (NI-M01): `projectKernelObject` strips the IPC timeout flag from
    projected TCBs. `timedOut` is set by `timeoutThread` when a
    SchedContext budget expires during cross-domain IPC; leaking that
    value across projection would expose another domain's scheduling
    state. The projection always shows `false`. -/
theorem projectKernelObject_erases_timeout_signal
    (ctx : LabelingContext) (observer : IfObserver) (tcb : TCB) :
    match projectKernelObject ctx observer (.tcb tcb) with
    | .tcb tcb' => tcb'.timedOut = false
    | _ => True := by
  simp [projectKernelObject]

/-- WS-SM SM5.B (NI-M01 lineage, PR #805 review P2-4): `projectKernelObject`
    strips the per-thread CPU-affinity field from projected TCBs (resets it to
    `none`). Per-thread CPU *placement* is a scheduler resource-management
    decision — the same class as `schedContextBinding`, `pipBoost`, and register
    state, all of which the projection already erases. Two states differing only
    by a (high/scheduler-driven) affinity change therefore project to the *same*
    low object, so the information-flow projection cannot leak cross-domain
    placement decisions once `setThreadCpuAffinity` (SM5.C) can change it.
    Mirrors `projectKernelObject_erases_timeout_signal`. -/
theorem projectKernelObject_erases_cpuAffinity
    (ctx : LabelingContext) (observer : IfObserver) (tcb : TCB) :
    match projectKernelObject ctx observer (.tcb tcb) with
    | .tcb tcb' => tcb'.cpuAffinity = none
    | _ => True := by
  simp [projectKernelObject]

/-- WS-SM SM6.D (PR #822 review, Reply objects): `projectKernelObject` strips the
    forward TCB→Reply link (`replyObject`) from projected TCBs (resets it to
    `none`).  The link names which first-class Reply object a blocked caller is
    waiting on; leaking it would expose the cross-domain Call→Reply rendezvous.
    Mirrors `projectKernelObject_erases_cpuAffinity`. -/
theorem projectKernelObject_erases_replyObject
    (ctx : LabelingContext) (observer : IfObserver) (tcb : TCB) :
    match projectKernelObject ctx observer (.tcb tcb) with
    | .tcb tcb' => tcb'.replyObject = none
    | _ => True := by
  simp [projectKernelObject]

/-- WS-SM SM6.D (PR #822 review, server-first receive): `projectKernelObject`
    strips the server's stashed `pendingReceiveReply` link from projected TCBs
    (resets it to `none`).  Like `replyObject`, it names a Reply object identity
    (the reply a server will hand to its next caller); leaking it would expose the
    server's outstanding-receive reply provisioning.  Mirrors
    `projectKernelObject_erases_replyObject`. -/
theorem projectKernelObject_erases_pendingReceiveReply
    (ctx : LabelingContext) (observer : IfObserver) (tcb : TCB) :
    match projectKernelObject ctx observer (.tcb tcb) with
    | .tcb tcb' => tcb'.pendingReceiveReply = none
    | _ => True := by
  simp [projectKernelObject]

/-- WS-SM SM6.D (PR #822 review, Reply objects): `projectKernelObject` strips the
    Reply object's `caller` back-link (resets it to `none`).  The link names the
    high-domain caller TCB blocked on this reply; leaking it through a
    low-visible reply object would reveal who is awaiting a reply.  Mirrors the
    `.schedContext` `boundThread` stripping. -/
theorem projectKernelObject_erases_reply_caller
    (ctx : LabelingContext) (observer : IfObserver) (r : SeLe4n.Kernel.Reply) :
    match projectKernelObject ctx observer (.reply r) with
    | .reply r' => r'.caller = none
    | _ => True := by
  simp [projectKernelObject]

/-- WS-OD (`v0.35.4`): `projectKernelObject` strips the Reply object's `next`
    reply-stack link (resets it to `none`).  On the head frame that link names the
    donated SchedContext — seL4's `replyNext` with the `isHead` bit set — and below
    the head it names the frame above; either is cross-domain donation plumbing,
    erased for the reason the SM6.D arm erased the per-frame context field it
    replaces. -/
theorem projectKernelObject_erases_reply_next
    (ctx : LabelingContext) (observer : IfObserver) (r : SeLe4n.Kernel.Reply) :
    match projectKernelObject ctx observer (.reply r) with
    | .reply r' => r'.next = none
    | _ => True := by
  simp [projectKernelObject]

/-- WS-SM SM6.D (PR #822 review, Reply objects): `projectKernelObject` strips the
    Reply object's `prev` reply-stack link (resets it to `none`).  The nested-call
    reply stack is internal IPC plumbing and names another reply object's
    identity. -/
theorem projectKernelObject_erases_reply_prev
    (ctx : LabelingContext) (observer : IfObserver) (r : SeLe4n.Kernel.Reply) :
    match projectKernelObject ctx observer (.reply r) with
    | .reply r' => r'.prev = none
    | _ => True := by
  simp [projectKernelObject]

/-- WS-SM SM6.D (PR #822 review, Codex): `projectKernelObject` **normalizes** the
    Reply object's internal `replyId` to `ReplyId.sentinel`.  The internal field
    need not equal the object-store key (`wellFormed` does not enforce it; a
    retyped Reply is built with the sentinel id), so without normalization a hidden
    ReplyId stored inside a low-visible Reply would leak through `projectObjects`. -/
theorem projectKernelObject_normalizes_reply_replyId
    (ctx : LabelingContext) (observer : IfObserver) (r : SeLe4n.Kernel.Reply) :
    match projectKernelObject ctx observer (.reply r) with
    | .reply r' => r'.replyId = SeLe4n.ReplyId.sentinel
    | _ => True := by
  simp [projectKernelObject]

/-- WS-SM SM6.D (#7.1 fold): the projection of a Reply object is **invariant under
    its `caller` field** — `projectKernelObject` overwrites `caller` to `none`
    regardless of its actual value (and leaves every other field that differs
    between `r` and `{ r with caller := c }` untouched — there are none).  This is
    the projection-blindness the fold's atomic `linkCallerReply` reply-write
    (`reply.caller := some caller`) relies on for non-interference: writing the
    caller back-link is invisible to any observer, high- or low-domain. -/
theorem projectKernelObject_reply_caller_invariant
    (ctx : LabelingContext) (observer : IfObserver) (r : SeLe4n.Kernel.Reply)
    (c : Option SeLe4n.ThreadId) :
    projectKernelObject ctx observer (.reply { r with callerCode := SeLe4n.ThreadId.optCode c })
      = projectKernelObject ctx observer (.reply r) := by
  simp [projectKernelObject]

/-- **WS-OD OD2.2 / `v0.35.4`**: the projection is invariant under a Reply's
`next` link — the `.reply` arm strips it, so a push that writes the head link (or
a splice that rewrites the links either side of a cut) is unobservable through a
low-visible Reply.  Stated per field beside `_caller_invariant` and `_prev_invariant`, because
an erasure with no theorem is one nothing consumes: the OD2.2 sweep found the
arm had erased every link field from the day it was written while only `caller`
had a statement. -/
theorem projectKernelObject_reply_next_invariant
    (ctx : LabelingContext) (observer : IfObserver) (r : SeLe4n.Kernel.Reply)
    (n : Option SeLe4n.Kernel.ReplyStackLink) :
    projectKernelObject ctx observer (.reply { r with next := n })
      = projectKernelObject ctx observer (.reply r) := by
  simp [projectKernelObject]

/-- **WS-OD OD2.2**: the projection is invariant under a Reply's link to the
reply below it on the stack — the third of the three fields the `.reply` arm
erases, and the one the donation pop rewrites. -/
theorem projectKernelObject_reply_prev_invariant
    (ctx : LabelingContext) (observer : IfObserver) (r : SeLe4n.Kernel.Reply)
    (p : Option SeLe4n.ReplyId) :
    projectKernelObject ctx observer (.reply { r with prev := p })
      = projectKernelObject ctx observer (.reply r) := by
  simp [projectKernelObject]

/-- **WS-OD OD3.2**: the projection is invariant under a Reply's whole reply-stack
frame — the two links the donation return's head clear resets together.  Stated as
one lemma so a projection hop over that write is one rewrite rather than two. -/
theorem projectKernelObject_reply_stackLinks_invariant
    (ctx : LabelingContext) (observer : IfObserver) (r : SeLe4n.Kernel.Reply)
    (prev : Option SeLe4n.ReplyId) (next : Option SeLe4n.Kernel.ReplyStackLink) :
    projectKernelObject ctx observer (.reply { r with prev := prev, next := next })
      = projectKernelObject ctx observer (.reply r) := by
  simp [projectKernelObject]

/-- The projection is invariant under recording a Reply's stasher: the `.reply`
arm erases `stasherCode`, so the stash's record on the Reply is unobservable
through it whatever the Reply's label. -/
theorem projectKernelObject_reply_stasher_invariant
    (ctx : LabelingContext) (observer : IfObserver) (r : SeLe4n.Kernel.Reply) (k : Nat) :
    projectKernelObject ctx observer (.reply { r with stasherCode := k })
      = projectKernelObject ctx observer (.reply r) := by
  simp [projectKernelObject]

/-- `v0.35.4`: the projection is invariant under **consuming** a Reply —
`Reply.consumed` clears `caller` and, off a stack head, both stack links, all
three of which the `.reply` arm strips, and keeps `replyId`, which the arm
normalises.  The consume is therefore unobservable through a
low-visible Reply whether or not the frame headed a context. -/
theorem projectKernelObject_reply_consumed_invariant
    (ctx : LabelingContext) (observer : IfObserver) (r : SeLe4n.Kernel.Reply) :
    projectKernelObject ctx observer (.reply r.consumed)
      = projectKernelObject ctx observer (.reply r) := by
  unfold SeLe4n.Kernel.Reply.consumed
  split <;> simp [projectKernelObject]

/-- **WS-RR RR7.22 (residual, remediation)**: the projection is invariant under a
TCB's SchedContext binding — `projectKernelObject` strips the field (AI4-A), so a
donation hand-off is invisible to any observer, not merely to a high one. -/
theorem projectKernelObject_tcb_schedContextBinding_invariant
    (ctx : LabelingContext) (observer : IfObserver) (t : TCB)
    (c o : Nat) :
    projectKernelObject ctx observer (.tcb { t with scBindingScCode := c, scBindingOwnerCode := o })
      = projectKernelObject ctx observer (.tcb t) := by
  simp [projectKernelObject]

/-- The projection is likewise invariant under the donor's origin back-link
(`TCB.originScCode`), the third field the donation's donor store writes: the
`.tcb` arm strips it with the binding. -/
theorem projectKernelObject_tcb_donorStore_invariant
    (ctx : LabelingContext) (observer : IfObserver) (t : TCB)
    (c o g : Nat) :
    projectKernelObject ctx observer
        (.tcb { t with scBindingScCode := c, scBindingOwnerCode := o, originScCode := g })
      = projectKernelObject ctx observer (.tcb t) := by
  simp [projectKernelObject]

/-- **WS-RR RR7.22 (residual, remediation)**: the projection is invariant under a
SchedContext's bound thread — the other half of the donation hand-off's write
set, stripped for the same reason. -/
theorem projectKernelObject_schedContext_boundThread_invariant
    (ctx : LabelingContext) (observer : IfObserver) (sc : SchedContext)
    (bt : Option SeLe4n.ThreadId) :
    projectKernelObject ctx observer (.schedContext { sc with boundThreadCode := SeLe4n.ThreadId.optCode (bt) })
      = projectKernelObject ctx observer (.schedContext sc) := by
  simp [projectKernelObject]

/-- **WS-OD OD2.2**: the projection is invariant under a SchedContext's
reply-stack head — `projectKernelObject` strips `scReply` (OD2.2), so pushing a
donation onto the stack, or popping it off, is invisible to any observer rather
than only to a high one.

Stated beside `projectKernelObject_schedContext_boundThread_invariant` and in
the same cut as the field, because the two are the write set of a donation
hand-off: the binding moves (`boundThread`) and the stack moves (`scReply`).
An erasure that landed a cut later would make the OD4 push observable in the
interval. -/
theorem projectKernelObject_schedContext_scReply_invariant
    (ctx : LabelingContext) (observer : IfObserver) (sc : SchedContext)
    (rid : Option SeLe4n.ReplyId) :
    projectKernelObject ctx observer (.schedContext { sc with scReply := rid })
      = projectKernelObject ctx observer (.schedContext sc) := by
  simp [projectKernelObject]

/-- **WS-OD OD3.2**: the projection is invariant under the whole of a donation
step's SchedContext write — the rebind, the reply-stack link and the recorded
origin together.  The grouping is the operation's actual write set, so a projection
hop over it is one rewrite rather than three, and a hop stated over fewer fields
than the store writes does not apply at all.

**WS-HP HP10.4** widened it from two fields to three rather than adding a second,
push-specific lemma: the *push* and the *pop* write the same three fields — the
push records the origin on a first donation and the pop clears it when the loan
ends — so this is one question with one answer, and a `…PushWrite…` sibling beside
it would be the duplicate this project retires.  The name does not promise an
arity; it names the operation class whose write set this is. -/
theorem projectKernelObject_schedContext_donationWrite_invariant
    (ctx : LabelingContext) (observer : IfObserver) (sc : SchedContext)
    (bt : Option SeLe4n.ThreadId) (rid : Option SeLe4n.ReplyId)
    (origin : Option SeLe4n.ThreadId) :
    projectKernelObject ctx observer
        (.schedContext { sc with boundThreadCode := SeLe4n.ThreadId.optCode (bt), scReply := rid,
                                 donationOrigin := origin })
      = projectKernelObject ctx observer (.schedContext sc) := by
  simp [projectKernelObject]

/-- **WS-HP HP10.3**: the projection is invariant under the recorded origin.

Stated on its own account beside the two above, because the origin is written and
cleared by steps whose write sets are not the donation return's: the `Call` that
first donates records it, and `schedContextBind` / `schedContextUnbind` /
`lifecyclePreRetypeCleanup` clear it.  A hop over the donation return's pair would
not cover any of those. -/
theorem projectKernelObject_schedContext_donationOrigin_invariant
    (ctx : LabelingContext) (observer : IfObserver) (sc : SchedContext)
    (origin : Option SeLe4n.ThreadId) :
    projectKernelObject ctx observer (.schedContext { sc with donationOrigin := origin })
      = projectKernelObject ctx observer (.schedContext sc) := by
  simp [projectKernelObject]

/-- Project object store to observer-visible subset.

WS-F3/F-22: Objects are now filtered through `projectKernelObject` to redact
CNode slot contents that reference high-domain targets. -/
def projectObjects (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    SeLe4n.ObjId → Option KernelObject :=
  fun oid =>
    if objectObservable ctx observer oid then
      (st.getObject? oid).map (projectKernelObject ctx observer)
    else
      none

/-- Project runnable queue to observer-visible threads only. -/
noncomputable def projectRunnable (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    List SeLe4n.ThreadId :=
  st.scheduler.runnable.filter (threadObservable ctx observer)

/-- Project current thread to observer-visible identity. -/
def projectCurrent (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    Option SeLe4n.ThreadId :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | some tid => if threadObservable ctx observer tid then some tid else none
  | none => none

/-- WS-F3: Project active scheduling domain (always visible — scheduling transparency). -/
def projectActiveDomain (_ctx : LabelingContext) (_observer : IfObserver) (st : SystemState) :
    SeLe4n.DomainId :=
  (st.scheduler.activeDomainOnCore bootCoreId)

/-- WS-F3: Project IRQ handler mappings, filtering to only those whose target
notification object is observable by the observer. -/
def projectIrqHandlers (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    SeLe4n.Irq → Option SeLe4n.ObjId :=
  fun irq =>
    match st.irqHandlers[irq]? with
    | some oid => if objectObservable ctx observer oid then some oid else none
    | none => none

/-- WS-F3: Project object index, filtering to only observable object IDs. -/
def projectObjectIndex (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    List SeLe4n.ObjId :=
  st.objectIndex.filter (objectObservable ctx observer)

/-- **A service registration carries the label of the endpoint it names.**  The
registry is reached only through an endpoint: the register writes the
registration of the endpoint the invoked capability names, and the query and
the revoke read and remove the registration that endpoint records
(`Endpoint.serviceRegistered`).  So a registration is observable exactly when its
endpoint is, and a registration naming no object (which `registerService`
never builds) is observable to no one. -/
def serviceObservable (ctx : LabelingContext) (observer : IfObserver)
    (reg : ServiceRegistration) : Bool :=
  match reg.endpointCap.target with
  | .object epId => objectObservable ctx observer epId
  | _ => false

/-- **An observer sees a service exactly through its endpoint** (WS-ZA ZA5.9):
the registration under `sid` is read off the endpoint with that id, and the
projection keeps a visible endpoint whole, service record included — so for a
visible endpoint the observer reads the registry off its projected objects. -/
theorem serviceRegistry_of_projectObjects
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) (sid : ServiceId)
    (hObs : objectObservable ctx observer (SeLe4n.ObjId.ofNat sid.toNat) = true) :
    st.serviceRegistry[sid]? =
      match projectObjects ctx observer st (SeLe4n.ObjId.ofNat sid.toNat) with
      | some (.endpoint ep) =>
        if ep.serviceRegistered then some (ep.service.registrationAt (SeLe4n.ObjId.ofNat sid.toNat))
        else none
      | _ => none := by
  rw [SystemState.serviceRegistry_getElem?]
  unfold projectObjects SystemState.getObject?
  rw [if_pos hObs]
  cases st.objects[SeLe4n.ObjId.ofNat sid.toNat]? with
  | none => rfl
  | some o => cases o <;> rfl

/-- **Low-equivalent objects agree on every observable registration**: the
registry needs no projection of its own. -/
theorem serviceRegistry_eq_of_projectObjects_eq
    (ctx : LabelingContext) (observer : IfObserver) {s₁ s₂ : SystemState}
    (h : projectObjects ctx observer s₁ = projectObjects ctx observer s₂) (sid : ServiceId)
    (hObs : objectObservable ctx observer (SeLe4n.ObjId.ofNat sid.toNat) = true) :
    s₁.serviceRegistry[sid]? = s₂.serviceRegistry[sid]? := by
  rw [serviceRegistry_of_projectObjects ctx observer s₁ sid hObs,
    serviceRegistry_of_projectObjects ctx observer s₂ sid hObs, h]

/-- WS-H8/A-36: Project domain time remaining (scheduling transparency — always visible). -/
def projectDomainTimeRemaining (_ctx : LabelingContext) (_observer : IfObserver) (st : SystemState) :
    Nat :=
  (st.scheduler.domainTimeRemainingOnCore bootCoreId)

/-- WS-H8/A-36: Project domain schedule (scheduling transparency — always visible). -/
def projectDomainSchedule (_ctx : LabelingContext) (_observer : IfObserver) (st : SystemState) :
    List DomainScheduleEntry :=
  st.scheduler.domainSchedule

/-- WS-H8/A-36: Project domain schedule index (scheduling transparency — always visible). -/
def projectDomainScheduleIndex (_ctx : LabelingContext) (_observer : IfObserver) (st : SystemState) :
    Nat :=
  (st.scheduler.domainScheduleIndexOnCore bootCoreId)

/-- WS-H10/C-05 + WS-H12c/H-03: Project machine register file, filtered by
current thread observability. The register file is the architectural context
of the currently-executing thread. Only visible when the current thread is
observable.

Under `contextMatchesCurrent` (established by `schedule`), the machine
register file is guaranteed to equal `currentThread.registerContext` when
a thread is dispatched. The projection reads `st.machine.regs` which is
synchronized with the current TCB's `registerContext` by the inline
context switch in `schedule`. -/
def projectMachineRegs (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    Option RegisterFile :=
  match (st.scheduler.currentOnCore bootCoreId) with
  | some tid => if threadObservable ctx observer tid then some st.machine.regs else none
  | none => none

/-- WS-I2/R-16: Address observability under optional memory-ownership metadata. -/
def memoryAddressObservable (ctx : LabelingContext) (observer : IfObserver)
    (paddr : SeLe4n.PAddr) : Bool :=
  match ctx.memoryOwnership with
  | none => false
  | some ownership =>
      match ownership.regionOwner paddr with
      | none => false
      | some dom => securityFlowsTo (ownership.domainLabelOf dom) observer.clearance

/-- R5-C.1/M-03: Project machine memory using actual content lookup.

When a memory address is observable (domain ownership model assigns it to a
domain that flows to the observer), the projection returns the actual byte
value from `st.machine.memory`. When no ownership model is configured
(`ctx.memoryOwnership = none`), `memoryAddressObservable` returns `false` for
all addresses, preserving backward compatibility.

This replaces the prior dummy-byte projection (`some 0`) that was flagged in
audit finding M-03 as failing to verify content isolation. -/
def projectMemory (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    SeLe4n.PAddr → Option UInt8 :=
  fun paddr => if memoryAddressObservable ctx observer paddr then some (st.machine.memory paddr) else none

/-- R5-C.1: When no memory ownership model is configured, projectMemory returns
none for all addresses regardless of state, preserving state-irrelevance. -/
theorem projectMemory_no_ownership
    (ctx : LabelingContext) (observer : IfObserver)
    (hNone : ctx.memoryOwnership = none) (s₁ s₂ : SystemState) :
    projectMemory ctx observer s₁ = projectMemory ctx observer s₂ := by
  funext paddr
  simp only [projectMemory, memoryAddressObservable, hNone]
  rfl

/-- R5-C.1: When memory is unmodified between two states, projectMemory agrees. -/
theorem projectMemory_eq_of_memory_eq
    (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState)
    (hMem : s₁.machine.memory = s₂.machine.memory) :
    projectMemory ctx observer s₁ = projectMemory ctx observer s₂ := by
  funext paddr
  simp only [projectMemory, hMem]

/-! ### U6-K (U-M23): Accepted Covert Channels

The following covert channels are known and accepted in the seLe4n NI model:

1. **Scheduling state (domain schedule)**: `activeDomain`, `domainSchedule`,
   `domainScheduleIndex`, and `domainTimeRemaining` are visible to all
   observers under the scheduling transparency assumption. This means any
   observer can infer the global scheduling state, including which domain is
   active and how much time remains. This is a deliberate design choice
   matching seL4's domain scheduler visibility.

2. **TCB metadata (priority, IPC state)**: Thread priority and IPC state
   are visible to any observer that can observe the thread (via
   `threadObservable`). This means an observer in one domain can infer
   another domain's thread priorities if those threads are observable to it.
   In seL4, thread priority is not considered confidential — it is visible
   through capability lookup and scheduling behavior.

3. **Machine timer (excluded)**: The machine timer (`st.machine.timer`) is
   deliberately excluded from `ObservableState` to prevent a timing covert
   channel. If projected, observers could infer other domains' execution
   duration by watching timer increments.

4. **Object store metadata**: Object IDs and types are visible through
   `objectIndex` projection. An observer can determine which objects exist
   (filtered by label), which reveals the system's object population
   indirectly.

These covert channels are consistent with seL4's information flow model
(Murray et al., CCS 2013) and are documented for auditor awareness.
Mitigation requires hardware-level isolation (e.g., partitioned caches,
separate timer domains) beyond the kernel model's scope.
-/

/-- V6-J (L-IF-1): Accepted scheduling covert channel — explicit bound theorem.

    The domain scheduling state (`activeDomain`, `domainSchedule`,
    `domainScheduleIndex`, `domainTimeRemaining`) is unconditionally visible
    to ALL observers. This creates a covert channel: a high-security domain
    can influence the scheduling state observable by a low-security domain.

    **Explicit bound**: The scheduling covert channel is bounded to at most
    4 scalar values per observation (the 4 scheduling-related fields in
    `ObservableState`). The bandwidth is limited by the domain schedule
    switching frequency (typically 1-100 Hz in seL4 configurations).

    This theorem witnesses the covert channel by showing that two observers
    with different clearances see identical scheduling projections, confirming
    that scheduling state is not filtered by security labels. -/
theorem acceptedCovertChannel_scheduling
    (ctx : LabelingContext)
    (obs₁ obs₂ : IfObserver)
    (st : SystemState) :
    projectActiveDomain ctx obs₁ st = projectActiveDomain ctx obs₂ st ∧
    projectDomainTimeRemaining ctx obs₁ st = projectDomainTimeRemaining ctx obs₂ st ∧
    projectDomainSchedule ctx obs₁ st = projectDomainSchedule ctx obs₂ st ∧
    projectDomainScheduleIndex ctx obs₁ st = projectDomainScheduleIndex ctx obs₂ st := by
  exact ⟨rfl, rfl, rfl, rfl⟩

/-- X5-C (M-3): Formal covert channel bandwidth analysis.

    **Channel characteristics**:
    - **Source**: 4 scheduling scalar values (`activeDomain`, `domainSchedule`,
      `domainScheduleIndex`, `domainTimeRemaining`)
    - **Capacity**: ≤ log₂(N × (Q + 1)) × tickFreq bits/second, where N =
      |domainSchedule| and Q bounds `domainTimeRemaining`.  The second factor
      is the **timer-tick** rate, not the domain-switch rate — see below.
    - **Realizable rate**: not bounded by this analysis.  Earlier revisions
      claimed "sub-bit per second" at the same configurations costed below at
      thousands of bits/second — two figures orders of magnitude apart for one
      configuration, the smaller with no derivation.  Removed rather than
      re-justified: a realizable rate needs a model of how much of the alphabet
      a sender controls and a receiver resolves, and this model has neither.
    - **Theoretical maximum**: With |domainSchedule| = N entries, a countdown
      capped at Q, and **tick** frequency F Hz, an observer can extract at most
      log₂(N × (Q + 1)) × F bits/second. For typical configurations (N ≤ 16,
      Q ≤ 255) each observation is ≤ 12 bits, and at the canonical RPi5 1 ms
      tick (F = 1000 Hz) that is ≤ 12 000 bits/second — the figure a deployment
      should compare against its own policy.

      **The rate factor is the tick rate, and earlier revisions used the
      domain-switch rate** (WS-SM SM8.B, PR #861 review round 12), quoting
      ≤ 1200 bits/second at F ≤ 100 Hz.  That understates the channel by an
      order of magnitude on the canonical configuration, because
      `domainTimeRemaining` is one of the observed components and an ordinary
      tick decrements it: consecutive observations differ *between* switches, so
      the observer is paced by ticks.  `schedulingObservation_changes_on_domain_tick`
      is that fact as a theorem, and `schedulingChannel_trace_capacity` states
      the run-length bound per observation — over n observations the whole trace
      is one of `alphabet ^ n` possibilities (`boundedCodeTraces`, whose length
      is exactly that) — so the two factors cannot drift apart again.

      **The Q factor is load-bearing, and the earlier form of this note omitted
      it** (WS-SM SM8.B, PR #861 review): the claim used to read log₂(N) × F,
      which is false as stated, because `domainTimeRemaining` is projected
      unfiltered and ranges over all of `Nat` — `schedulingChannel_not_bounded_by_scheduleLength`
      proves exactly that N alone bounds nothing.  The corrected figure is
      **proven**, not asserted: `schedulingChannel_alphabet_bounded` injects the
      per-core observation alphabet into `Fin (N × (Q + 1))`, and
      `schedulingObservationCode_injective` is why that injection loses nothing.
      The third observable component, `activeDomain`, is covered rather than
      ignored: `schedulingChannel_full_observation_determined` shows two states
      the encoding identifies expose the same active domain — under
      `domainConsistentOnCore`, the invariant that actually ties it to
      `domainSchedule[index]`.  A deployment that does not cap the countdown —
      or that runs the empty single-domain schedule, which makes the
      index-bounds invariant vacuous and so leaves the observed index unbounded
      — does not get this bound.  The complete premise list is
      `schedulingCapacityPreconditions` (per state) and
      `schedulingCapacityComparable` (across two states, adding that
      `domainSchedule` is itself unchanged: it is projected unfiltered, so a
      mutable schedule is its own channel).  `docs/SECURITY_ADVISORY.md` §SA-3
      tabulates which premises the kernel discharges and which the deployment
      must.

    **Mitigation status**: Temporal partitioning via domain scheduling bounds
    the channel bandwidth. Each domain receives guaranteed time quanta regardless
    of other domains' behavior. This is the same mitigation used by seL4
    (Murray et al., "seL4: From General Purpose to a Proof of Information Flow
    Enforcement", IEEE S&P 2013).

    **Acceptance rationale**: This covert channel is accepted per seL4 design
    precedent. Full elimination would require hardware-level temporal isolation
    (partitioned caches, separate timer domains) beyond the kernel model's scope.
    The `acceptedCovertChannel_scheduling` theorem above formally witnesses the
    channel's existence and confirms it is not accidentally introduced by the
    information-flow enforcement layer.

    **What this theorem proves, precisely** (corrected WS-SM SM8.B, PR #861
    review): that the three scheduling projections are the raw scheduler reads —
    the channel is transparent, and the information-flow layer does not
    accidentally add to it. It is *not* a capacity result: there is no
    cardinality, frequency or bandwidth argument here, and the "4" below counts
    projected **components**, not values (`domainTimeRemaining` alone ranges
    over all of `Nat`). An earlier form of this docstring read the count as a
    value bound and cited it as an upper bound on the channel; that reading was
    wrong.

    For the part that genuinely is bounded — the schedule-index alphabet, under
    the scheduler's index-bounds invariant — see
    `schedulingChannelIndex_alphabet_bounded`, and for the statement that
    schedule length does *not* bound the rest, its companion
    `schedulingChannel_not_bounded_by_scheduleLength`. -/
theorem schedulingCovertChannel_bounded_width
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    -- The scheduling covert channel consists of exactly 4 scalar projections:
    -- activeDomain, domainTimeRemaining, domainSchedule, domainScheduleIndex
    projectActiveDomain ctx observer st = (st.scheduler.activeDomainOnCore bootCoreId) ∧
    projectDomainTimeRemaining ctx observer st = (st.scheduler.domainTimeRemainingOnCore bootCoreId) ∧
    projectDomainScheduleIndex ctx observer st = (st.scheduler.domainScheduleIndexOnCore bootCoreId) := by
  exact ⟨rfl, rfl, rfl⟩

/-- Canonical IF-M1 state projection helper used by theorem targets.

WS-F3/CRIT-02: Extended with activeDomain, irqHandlers, and objectIndex
projections for complete security-relevant state coverage.

WS-H8/A-36/H-11: Extended with domainTimeRemaining, domainSchedule, and
domainScheduleIndex projections for timing-channel coverage.

WS-H10/C-05/A-38: Extended with machineRegs projection for MachineState
coverage. Machine timer is excluded from ObservableState because it is a
kernel-internal monotonic counter — projecting it unconditionally would
create a covert timing channel (observers could infer other domains'
execution by watching timer increments). Memory projection deferred to
WS-H11 (VSpace domain ownership model required). -/
noncomputable def projectState (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) : ObservableState :=
  {
    objects := projectObjects ctx observer st
    runnable := projectRunnable ctx observer st
    current := projectCurrent ctx observer st
    activeDomain := projectActiveDomain ctx observer st
    irqHandlers := projectIrqHandlers ctx observer st
    objectIndex := projectObjectIndex ctx observer st
    domainTimeRemaining := projectDomainTimeRemaining ctx observer st
    domainSchedule := projectDomainSchedule ctx observer st
    domainScheduleIndex := projectDomainScheduleIndex ctx observer st
    machineRegs := projectMachineRegs ctx observer st
    memory := projectMemory ctx observer st
  }

/-- WS-ZA ZA5.11: **a step that writes only taint words is invisible to every
observer** — the projection reads the store through `projectKernelObject`,
which strips the words on every kind (`projectKernelObject_eraseTaint`). -/
theorem projectState_of_objectsAgreeOffTaint (ctx : LabelingContext) (observer : IfObserver)
    {st st' : SystemState} (h : SystemState.objectsAgreeOffTaint st st')
    (hF : st' = { st with objects := st'.objects }) :
    projectState ctx observer st' = projectState ctx observer st := by
  have hO : projectObjects ctx observer st' = projectObjects ctx observer st := by
    funext oid
    unfold projectObjects SystemState.getObject?
    split
    · have hk := congrArg (Option.map (projectKernelObject ctx observer)) (h oid)
      simpa only [Option.map_map, Function.comp_def, projectKernelObject_eraseTaint] using hk
    · rfl
  rw [hF]
  simp only [projectState]
  congr 1

/-- AK6-F.2a: Modifying `scheduler.replenishQueue` does not affect
`projectState`. The CBS replenishment queue is a scheduler-internal
ordering structure NOT included in the observable state projection, so
mutations to it (including `ReplenishQueue.remove`, `popDue`, `insert`)
are invisible to information-flow analysis. Used by
`schedContextConfigure/Unbind` preservation. -/
theorem projectState_replenishQueue_eq (ctx : LabelingContext) (observer : IfObserver)
    (st : SystemState) (rq : SeLe4n.Kernel.ReplenishQueue) :
    projectState ctx observer
      { st with scheduler := st.scheduler.setReplenishQueueOnCore bootCoreId rq } =
    projectState ctx observer st := by rfl

/-- AK6-F.2a: Clearing `scheduler.current` when the previous current was
non-observable preserves `projectCurrent`. `projectCurrent` returns
`none` for non-observable current threads, and also `none` when
`scheduler.current = none`. So when the previous current was already
being projected as `none`, clearing it leaves the projection unchanged.

This is the helper used by `schedContextUnbind` and `suspendThread` when
they clear `current` before rescheduling. Only `projectCurrent` and
`projectMachineRegs` read `scheduler.current`; both produce `none` when
current is high or absent. -/
theorem projectState_scheduler_current_cleared_when_high
    (ctx : LabelingContext) (observer : IfObserver) (st : SystemState)
    (hCurrHigh : ∀ t, (st.scheduler.currentOnCore bootCoreId) = some t →
                       threadObservable ctx observer t = false) :
    projectState ctx observer
      { st with scheduler := st.scheduler.setCurrentOnCore bootCoreId none } =
    projectState ctx observer st := by
  -- Only projectCurrent and projectMachineRegs read scheduler.current.
  have hCur : projectCurrent ctx observer
                { st with scheduler := st.scheduler.setCurrentOnCore bootCoreId none } =
              projectCurrent ctx observer st := by
    have hLHS : projectCurrent ctx observer
        { st with scheduler := st.scheduler.setCurrentOnCore bootCoreId none } = none := by
      simp only [projectCurrent, SchedulerState.setCurrentOnCore, SchedulerState.currentOnCore,
        PerCoreVector.get_set_eq, SeLe4n.ThreadId.ofOptCode_optCode]
    rw [hLHS]; unfold projectCurrent
    cases hSome : (st.scheduler.currentOnCore bootCoreId) with
    | none => rfl
    | some tid => have := hCurrHigh tid hSome; simp [this]
  have hMachine : projectMachineRegs ctx observer
                    { st with scheduler := st.scheduler.setCurrentOnCore bootCoreId none } =
                  projectMachineRegs ctx observer st := by
    have hLHS : projectMachineRegs ctx observer
        { st with scheduler := st.scheduler.setCurrentOnCore bootCoreId none } = none := by
      simp only [projectMachineRegs, SchedulerState.setCurrentOnCore, SchedulerState.currentOnCore,
        PerCoreVector.get_set_eq, SeLe4n.ThreadId.ofOptCode_optCode]
    rw [hLHS]; unfold projectMachineRegs
    cases hSome : (st.scheduler.currentOnCore bootCoreId) with
    | none => rfl
    | some tid => have := hCurrHigh tid hSome; simp [this]
  simp only [projectState]
  congr 1 <;> first | rfl | exact hCur | exact hMachine

/-- Two states are low-equivalent when their observer projections are equal. -/
def lowEquivalent (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState) : Prop :=
  projectState ctx observer s₁ = projectState ctx observer s₂

theorem lowEquivalent_refl
    (ctx : LabelingContext)
    (observer : IfObserver)
    (st : SystemState) :
    lowEquivalent ctx observer st st := by
  rfl

theorem lowEquivalent_symm
    (ctx : LabelingContext)
    (observer : IfObserver)
    (s₁ s₂ : SystemState)
    (hEq : lowEquivalent ctx observer s₁ s₂) :
    lowEquivalent ctx observer s₂ s₁ := by
  simpa [lowEquivalent] using Eq.symm hEq

theorem lowEquivalent_trans
    (ctx : LabelingContext)
    (observer : IfObserver)
    (s₁ s₂ s₃ : SystemState)
    (h₁₂ : lowEquivalent ctx observer s₁ s₂)
    (h₂₃ : lowEquivalent ctx observer s₂ s₃) :
    lowEquivalent ctx observer s₁ s₃ := by
  simpa [lowEquivalent] using Eq.trans h₁₂ h₂₃

-- ============================================================================
-- §14 What the endpoint admission gate admits onto a single queue
-- ============================================================================

/-- **WS-RR RR8.8**: the live endpoint admission gate puts an **observable** and a
**non-observable** thread on the *same* endpoint queue.

This decides how the cancellation path's two standing projection obligations
(`abortHolderProjectionStable`, retired at `v0.36.136` with the abort it
covered, and `descheduledHolderHigh` — `abortHolderWakeHigh` until
`v0.35.158`) and the three queue arms'
`hTeardownProj` can be closed — and it **refutes the remedy all three were
registered with**.

The live send / call gate is
`endpointFlowGate ctx ep (threadLabelOf sender) (endpointLabelOf ep)`
(`endpointSendCrossCoreDispatchChecked`, `endpointCallCrossCoreDispatchChecked`;
the receive side is its mirror, `endpointReceiveDualChecked`): a thread is
admitted onto an endpoint's queue when its own label **flows to** the endpoint's,
not when it *equals* it.  `securityFlowsTo` is a genuine order rather than
equality — `publicLabel → kernelTrusted` is permitted *by design*, which
`securityFlowsTo_prevents_label_escalation` states in as many words — so two
senders with different labels are both admitted onto one endpoint, and an
observer cleared for the lower one sees exactly one of them.

Two consequences, both load-bearing.

**An endpoint/notification queue label-uniformity invariant cannot be
established.**  It was registered as the closure for all three obligations, and
the enqueue's own admission predicate admits a non-uniform queue, so no enqueue
path can establish it.  Establishing it would mean narrowing the gate to label
*equality*, which refuses the canonical one-way flow this lattice exists to
permit — a lower-labelled client sending to a higher-labelled server.  The
remedy is retracted; see `docs/REGISTERED_DEBT.md`.

**What the gate does give is the other direction, and with one conjunct it
closes two of the three write classes.**  Every thread on an endpoint's queue
satisfies `label thread ⊑ endpointLabelOf endpoint`
(`endpointFlowGate_implies_securityFlowsTo`, which takes no hypothesis at all),
and `LabelingContextValid.endpointObjectCoherence` (WS-RR RR8.8) carries that on
to `objectLabelOf endpoint`, which is what `objectObservable` decides visibility
from — two independent `LabelingContext` fields that nothing related until that
conjunct.  So an *observable* endpoint has only observable waiters and —
contrapositively — the endpoint object is non-observable whenever any of its
waiters is (`endpointObjectHigh_of_admittedThreadHigh`).  That covers the endpoint's own
`sendQueue` / `recvQueue` boundaries, and the aborted holder's own TCB is
covered by the same order run through the donating `Call` and the server's
receive.  What is left is the **queue neighbours**: their labels are constrained
only against the *endpoint's*, so nothing relates a neighbour to the thread being
spliced out, and this theorem exhibits the admission in which they differ.
`queuePrev` / `queuePPrev` / `queueNext` survive `projectKernelObject`, so the
splice writes an observable field — which is why the remaining closure is to take
the queue links **out of the TCB** rather than to constrain labels.

The admission is a first-class member of the production labelling family:
`indexPartitionedLabelingContext base w publicLabel kernelTrusted` differs from
the shipped `confinedLabelingContext` only in the two labels applied to it, and
its label obligation is distinctness (`lowerLabel ≠ upperLabel`), not mutual
non-flow.  The RPi5 binding passes `lowTrusted` / `highUntrusted`, which are
mutually non-flowing (`lowTrusted_highUntrusted_mutually_isolated`), so *that*
deployment admits no cross-label endpoint flow and its queues are uniform by
construction: the gap is in the general claim, not in the shipped
configuration. -/
theorem endpointAdmissionAdmitsMixedObservability
    (ctx : LabelingContext) (observer : IfObserver) (epId : SeLe4n.ObjId)
    (lowerTid upperTid : SeLe4n.ThreadId)
    (hNoOverride : ctx.endpointPolicy.endpointPolicy epId = none)
    (hEndpoint : ctx.endpointLabelOf epId = SecurityLabel.kernelTrusted)
    (hClearance : observer.clearance = SecurityLabel.publicLabel)
    (hLower : ctx.threadLabelOf lowerTid = SecurityLabel.publicLabel)
    (hUpper : ctx.threadLabelOf upperTid = SecurityLabel.kernelTrusted) :
    endpointFlowGate ctx epId (ctx.threadLabelOf lowerTid) (ctx.endpointLabelOf epId) = true
      ∧ endpointFlowGate ctx epId (ctx.threadLabelOf upperTid) (ctx.endpointLabelOf epId) = true
      ∧ threadObservable ctx observer lowerTid = true
      ∧ threadObservable ctx observer upperTid = false
      ∧ ctx.threadLabelOf lowerTid ≠ ctx.threadLabelOf upperTid := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;>
    simp only [endpointFlowGate, endpointOverrideAllows, threadObservable,
      hNoOverride, hEndpoint, hClearance, hLower, hUpper] <;> decide

end SeLe4n.Kernel
