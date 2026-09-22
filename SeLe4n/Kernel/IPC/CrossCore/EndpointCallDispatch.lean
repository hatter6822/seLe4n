-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.A: PRODUCTION (LANDED). The pure `.call` dispatch ops below the API
-- layer; the live `API.dispatchWithCap{,Checked}` `.call` arm routes through
-- `endpointCallCrossCoreDispatch{,Checked}` here, deriving the executing core
-- from the live state (`determineExecutingCore`). (Former "STATUS: staged"
-- marker replaced with this landing note per the implement-the-improvement rule;
-- see docs/planning/SMP_CROSS_CORE_IPC_PLAN.md.)

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.DualQueue.WithCaps
import SeLe4n.Kernel.IPC.Operations.Donation
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers

/-!
# WS-SM SM6.A — Cross-core `.call` dispatch (pure; below the API layer)

The pure cross-core `.call` dispatch operations — `endpointCallWithCapsOnCore`,
`endpointCallCrossCoreDispatch`, and the information-flow-checked
`endpointCallCrossCoreDispatchChecked`. These live *below* `SeLe4n.Kernel.API`
(no `Platform.FFI` dependency) so the live `.call` dispatch arm can route through
them. The BaseIO live driver (`endpointCallCrossCoreEntry`, which reads the
hardware core and fires the SGI) layers on top of these in
`EndpointCallEntry.lean`, which imports `Platform.FFI`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind)

-- ============================================================================
-- §0 Executing-core derivation (per-core dispatch without a parameter)
-- ============================================================================

/-- WS-SM SM6.A: the core a syscall is executing on, derived from the live state.
A thread issuing a syscall is the *current* thread on its core, so the executing
core is the unique `c` with `currentOnCore c = some tid` — found by scanning
`Concurrency.allCores`, defaulting to `bootCoreId` (the boot-pinned fallback, and
the single-core answer). This lets the live `.call` dispatch identify and
deschedule the caller on its *own* core without threading a hardware-core
parameter through the `Kernel`-monad dispatch chain (which returns `Kernel Unit`,
applying its state positionally). -/
def determineExecutingCore (st : SystemState) (tid : SeLe4n.ThreadId) : CoreId :=
  (Concurrency.allCores.find? (fun c => st.scheduler.currentOnCore c == some tid)).getD
    Concurrency.bootCoreId

/-- `determineExecutingCore` always returns a core on which the caller is the
current thread, *or* the `bootCoreId` fallback — it never invents a core that
isn't running the caller. (Either `find?` succeeds, witnessing `currentOnCore c
= some tid`, or it falls back to the boot core.) -/
theorem determineExecutingCore_sound (st : SystemState) (tid : SeLe4n.ThreadId) :
    determineExecutingCore st tid = Concurrency.bootCoreId
      ∨ st.scheduler.currentOnCore (determineExecutingCore st tid) = some tid := by
  unfold determineExecutingCore
  cases hf : Concurrency.allCores.find? (fun c => st.scheduler.currentOnCore c == some tid) with
  | none => exact Or.inl (by simp)
  | some c =>
    have hc := List.find?_some hf
    exact Or.inr (by simpa using hc)

-- ============================================================================
-- §1 Cross-core `endpointCallWithCaps`
-- ============================================================================

/-- WS-SM SM6.A.8 (operation): endpoint call with capability transfer, across
cores. The cross-core `endpointCallOnCore` rendezvous (which surfaces the
receiver-wake SGI), then — on an immediate rendezvous carrying caps —
`ipcUnwrapCaps` installs the transferred capabilities into the receiver's
CSpace (gated on the endpoint's `grant` right). Returns the post-state, the
capability-transfer summary, and the optional cross-core SGI. -/
def endpointCallWithCapsOnCore
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  -- PR #873 round 13: stamp the endpoint's grant right into the message, so the
  -- queued ordering and the immediate rendezvous read the same authority from the
  -- same place. See `endpointSendDualWithCaps` for the ordering this removes.
  let hasReceiver := match st.getEndpoint? endpointId with
    | some ep => ep.receiveQ.head.isSome
    | none => false
  match endpointCallOnCore endpointId caller { msg with capsGranted := endpointRights.mem .grant } executingCore st with
  | (st', .error e) => (st', .error e)
  | (st', .ok sgi) =>
      if !hasReceiver || msg.caps.isEmpty then (st', .ok ({ results := #[] }, sgi))
      else
        match st.getEndpoint? endpointId with
        | some ep =>
          match ep.receiveQ.head with
          | some receiverId =>
            match lookupCspaceRoot st' receiverId with
            | some recvRoot =>
              match ipcUnwrapCaps { msg with capsGranted := endpointRights.mem .grant } recvRoot
                  receiverSlotBase (endpointRights.mem .grant) st' with
              | .error e => (st', .error e)
              | .ok (summary, st'') => (st'', .ok (summary, sgi))
            | none => (st', .error .invalidCapability)
          | none => (st', .ok ({ results := #[] }, sgi))
        | none => (st', .ok ({ results := #[] }, sgi))

-- ============================================================================
-- §2 Full cross-core `.call` dispatch (WithCaps + donation + PIP)
-- ============================================================================

/-- WS-SM SM6.A.5 (operation): the full cross-core `Call` syscall semantics.
The cross-core WithCaps call, then — if a receiver rendezvoused — the
SchedContext **donation** to a passive server and priority-inheritance
propagation. The cross-core `.reschedule` SGI is surfaced for the runtime to
fire after the commit. Mirrors the live single-core `.call` dispatch arm
(`API.dispatchWithCap`).

**WS-RR RR2.7**: the donation is `applyCallDonationOnCore`, not the boot-pinned
`applyCallDonation`. The rebinding of the caller's SchedContext to the receiver
is an object-store-only update and is cross-core-safe on its own, but the
SchedContext's pending CBS replenishments are **not** in the object store — they
live on a per-core replenish queue, the donor's, and the SM5.H affinity
invariant `replenishQueueAffinityConsistentOnCore` says they must live on the
*bound thread's* home core. The per-core form carries them across with
`migrateSchedContextReplenishment`, exactly as the cancellation arm
`cancelDonatedDonationOnCore` has since SM6.E, and
`applyCallDonationOnCore_preserves_replenishQueueAffinityConsistent_smp` proves
the invariant holds on every core afterwards. -/
def endpointCallCrossCoreDispatch
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  let maybeReceiver := match st.getEndpoint? endpointId with
    | some ep => ep.receiveQ.head
    | none => none
  match endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st with
  | (st', .error e) => (st', .error e)
  | (st', .ok (summary, sgi)) =>
      match maybeReceiver with
      | some receiverTid =>
        match SeLe4n.ThreadId.toValid? caller, SeLe4n.ThreadId.toValid? receiverTid with
        | some callerV, some receiverV =>
          -- WS-RR RR2.7: the live `.call` arm routes through the **migrating**
          -- donation. A SchedContext donated to a server homed on another core
          -- must drag its pending CBS replenishments with it, or the SM5.H
          -- affinity invariant `replenishQueueAffinityConsistentOnCore` breaks on
          -- a reachable path and the donee's budget is refilled by a core that no
          -- longer runs it. Both endpoints are resolved from the **pre**-state
          -- `st`, which is what the `withLockSet` bracket sees when it acquires
          -- the two `SchedLockId.replenishQueue` write locks
          -- (`endpointCallCrossCoreDispatchSchedLockSet`); the intervening
          -- rendezvous writes `ipcState` / queue links / scheduler slots and the
          -- receiver's CSpace, never a `cpuAffinity`, so the pre-state reading is
          -- the reading at the donation site. Donor and donee on one core makes
          -- the migration a definitional no-op, which is every single-core
          -- configuration.
          match applyCallDonationOnCore st' callerV receiverV
              (determineTargetCore st caller) (determineTargetCore st receiverTid) with
          | .error e => (st', .error e)
          | .ok st'' =>
              -- WS-SM SM6.A: propagate the donated-priority boost with the
              -- *cross-core* chain walk (`propagatePipChainCrossCore`, SM5.F.4 — in
              -- the FFI-free `Propagate`, so no import cycle below the API layer);
              -- its `.1` is the post-walk state. Each boosted server's run-queue
              -- bucket migrates on its *home* core (via `pipBoostWithWake`'s
              -- `updatePipBoostOnCore`), so a passive server pinned to a remote core
              -- becomes schedulable at the donated priority there — and the run-queue
              -- change surfaces in the `(pre, post)` diff the syscall seam fires the
              -- cross-core SGI from. On the boot core with an unbound receiver this
              -- is state-identical to the single-core `propagatePriorityInheritance`
              -- (`pipBoostWithWake … bootCoreId` of an unbound thread = `updatePipBoost`).
              ((PriorityInheritance.propagatePipChainCrossCore st'' receiverTid executingCore).1,
               .ok (summary, sgi))
        | _, _ => (st', .error .invalidArgument)
      | none => (st', .ok (summary, sgi))

/-- WS-SM SM6.A (live `.call` enforcement): the **information-flow-checked**
cross-core call dispatch — the cross-core analogue of `endpointCallChecked`
composed with `endpointCallCrossCoreDispatch`. Mirrors the single-core checked
`.call` arm exactly: it first applies the SM-IF security guard
(`securityFlowsTo callerLabel endpointLabel`, rejecting with `.flowDenied` on a
disallowed flow), then runs the full cross-core dispatch (WithCaps +
`applyCallDonation` + PIP propagation), surfacing the cross-core `.reschedule`
SGI. This is the operation the live `dispatchWithCapChecked` `.call` arm routes
through, replacing the boot-pinned `endpointCallChecked` so the receiver is woken
on its *home* core. -/
def endpointCallCrossCoreDispatchChecked
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)) :=
  -- WS-SM SM8.C: global lattice check AND this endpoint's configured override.
  if endpointFlowGate ctx endpointId (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) then
    endpointCallCrossCoreDispatch endpointId caller msg endpointRights
      receiverSlotBase executingCore st
  else
    (st, .error .flowDenied)

/-- WS-SM SM6.A: a disallowed flow is rejected before any state change — the
checked cross-core dispatch is fail-closed (state unchanged, `.flowDenied`). -/
theorem endpointCallCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf endpointId) = false) :
    endpointCallCrossCoreDispatchChecked ctx endpointId caller msg endpointRights
        receiverSlotBase executingCore st = (st, .error .flowDenied) := by
  -- WS-SM SM8.C: a denied global flow denies the gate whatever the override says,
  -- so the hypothesis is the one this theorem always had.
  simp [endpointCallCrossCoreDispatchChecked,
    endpointFlowGate_false_of_securityFlowsTo_false ctx endpointId _ _ hDeny]

/-- WS-SM SM6.A: when the flow is permitted, the checked dispatch is exactly the
unchecked cross-core dispatch — the guard is a pure precondition. -/
theorem endpointCallCrossCoreDispatchChecked_flow_allowed
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf caller) (ctx.endpointLabelOf endpointId) = true)
    -- WS-SM SM8.C: the endpoint's override must admit the flow too.
    (hOverride : endpointOverrideAllows ctx endpointId (ctx.threadLabelOf caller)
      (ctx.endpointLabelOf endpointId) = true) :
    endpointCallCrossCoreDispatchChecked ctx endpointId caller msg endpointRights
        receiverSlotBase executingCore st
      = endpointCallCrossCoreDispatch endpointId caller msg endpointRights
          receiverSlotBase executingCore st := by
  simp [endpointCallCrossCoreDispatchChecked,
    endpointFlowGate_of ctx endpointId _ _ hAllow hOverride]

-- ============================================================================
-- §3 Characterisation theorems
-- ============================================================================

/-- WS-SM SM6.A.8: with no capabilities to transfer, the WithCaps cross-core
call is exactly the bare cross-core call (empty transfer summary), so its
surfaced SGI is the bare call's — the SM6.A.3 SGI characterisation carries to
the WithCaps path. -/
theorem endpointCallWithCapsOnCore_no_caps
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hCaps : msg.caps.isEmpty = true) :
    endpointCallWithCapsOnCore endpointId caller msg endpointRights
        receiverSlotBase executingCore st
      = ((endpointCallOnCore endpointId caller { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1,
         (endpointCallOnCore endpointId caller { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).2.map
           (fun sgi => ({ results := #[] }, sgi))) := by
  -- PR #873 round 13: against the **stamped** message, because that is what the
  -- wrapper transmits. With no capabilities the grant bit changes no behaviour,
  -- but it is part of the message the send parks, so saying otherwise would be
  -- saying something false about the state.
  unfold endpointCallWithCapsOnCore
  cases h : endpointCallOnCore endpointId caller { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk st' res => cases res with
    | error e => simp [Except.map]
    | ok sgi => simp [hCaps, Except.map]

/-- WS-SM SM6.A.5: on the no-receiver path (the caller blocks as `blockedOnCall`)
the cross-core dispatch performs no donation — it is exactly the WithCaps call.
Donation only fires on an immediate rendezvous with a passive server. -/
theorem endpointCallCrossCoreDispatch_no_receiver
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hNoRecv : (match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head | none => none) = none) :
    endpointCallCrossCoreDispatch endpointId caller msg endpointRights
        receiverSlotBase executingCore st
      = endpointCallWithCapsOnCore endpointId caller msg endpointRights
          receiverSlotBase executingCore st := by
  unfold endpointCallCrossCoreDispatch
  rw [hNoRecv]
  cases h : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st with
  | mk st' res => cases res with
    | error e => rfl
    | ok pair => rfl

-- ============================================================================
-- §3 WS-RR RR8.12 Cut C3a — the live `.call` arm's per-core write set and its
--    scheduler-domain footprint
-- ============================================================================
--
-- `lockSet_endpointCall` is an object-domain `LockSet` and cannot name a per-core
-- run-queue or replenish-queue slot at all, so
-- `UncoveredLockDomain.syscallSeamSchedulerDomain` recorded the live `.call` arm's
-- scheduler writes as outside the footprint the RR7.12 seam acquires.  This
-- section declares them, in the same cross-domain `SchedLockId` order every
-- sibling footprint uses (`object < runQueue < replenishQueue`, each same-kind
-- segment `CoreId`-ascending, so the list *is* the SM3.D acquisition sequence).
-- Inert until the bracket cut wires `schedLockSetForSyscall`.
--
-- The arm's SM8.B write set is declared here too, relocated from the staged
-- `InformationFlow/NonInterferenceCrossCore.lean` for the reason Cuts 5, 7, 8a-ii
-- and C2 each applied: a write set declared in a staged module is one the
-- production footprint cannot read.  The confinement theorem
-- (`endpointCallCrossCoreDispatch_confinedToCores`) stays there, because
-- `observableSlotsConfinedToCores` is that module's predicate.

/-- SM8.B.2: the WithCaps call leaves the bare call's run queues in place — every
arm either *is* the bare call's post-state or is that state after an
`ipcUnwrapCaps`, which preserves the scheduler.

Relocated to production at **WS-RR RR8.12 Cut C3a**: the `.call` footprint's
exactness licence composes it, and a staged frame is one a production footprint
cannot read. -/
theorem endpointCallWithCapsOnCore_scheduler_eq (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (endpointCallWithCapsOnCore endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1.scheduler
      = (endpointCallOnCore endpointId caller { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st).1.scheduler := by
  unfold endpointCallWithCapsOnCore
  cases hCall : endpointCallOnCore endpointId caller { msg with capsGranted := endpointRights.mem AccessRight.grant } executingCore st with
  | mk stCall res =>
    cases res with
    | error e => rfl
    | ok sgi =>
      simp only []
      repeat' split
      all_goals first
        | rfl
        | (rename_i h; exact ipcUnwrapCaps_preserves_scheduler _ _ _ _ _ _ _ h)

/-- **WS-RR RR8.12 Cut C3a (frame)**: so the WithCaps call writes no replenish
queue either — the bare call's frame `endpointCallOnCore_replenishQueueOnCore`
through the scheduler equality above. -/
theorem endpointCallWithCapsOnCore_replenishQueueOnCore (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (c : CoreId) :
    (endpointCallWithCapsOnCore endpointId caller msg endpointRights
        receiverSlotBase executingCore st).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  rw [endpointCallWithCapsOnCore_scheduler_eq]
  exact endpointCallOnCore_replenishQueueOnCore endpointId caller _ executingCore st c

/-- SM8.B.2: **the chain leg the live `.call` actually walks**, recovered from
the pre-state by mirroring `endpointCallCrossCoreDispatch`'s own control flow —
same receiver resolution, same WithCaps call, same `applyCallDonation` — so the
walk is keyed on the *resolved receiver* at the *post-donation* state, which is
where the dispatch keys it. Every arm on which the dispatch does not walk a
chain returns `[]`.

Relocated to production at **WS-RR RR8.12 Cut C3a**, beside the dispatch it mirrors,
so the scheduler-domain footprint `schedLockSet_endpointCallOnCore` can read it; its
confinement theorem stays in `InformationFlow/NonInterferenceCrossCore.lean`, because
`observableSlotsConfinedToCores` is that module's predicate. -/
def endpointCallDispatchChainWriteSet
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId)
    (st : SystemState) : List CoreId :=
  let maybeReceiver := match st.getEndpoint? endpointId with
    | some ep => ep.receiveQ.head
    | none => none
  match endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st with
  | (_, .error _) => []
  | (st', .ok _) =>
      match maybeReceiver with
      | some receiverTid =>
        match SeLe4n.ThreadId.toValid? caller, SeLe4n.ThreadId.toValid? receiverTid with
        | some callerV, some receiverV =>
          -- WS-RR RR2.7: mirrors the dispatch's own migrating donation, so the
          -- chain state named here is the state the dispatch really walks from.
          match applyCallDonationOnCore st' callerV receiverV
              (determineTargetCore st caller) (determineTargetCore st receiverTid) with
          | .error _ => []
          | .ok st'' =>
              pipChainWriteSet st'' receiverTid executingCore st''.objectIndex.length
        | _, _ => []
      | none => []

/-- SM8.B.2: **the cores the live cross-core `.call` may write** — the endpoint
call's own two-core set, plus the chain the dispatch really walks. A function of
the dispatch's own arguments, so it can be evaluated at a call site rather than
supplied by hand.

Relocated to production at **WS-RR RR8.12 Cut C3a**, beside the dispatch it mirrors,
so the scheduler-domain footprint `schedLockSet_endpointCallOnCore` can read it; its
confinement theorem stays in `InformationFlow/NonInterferenceCrossCore.lean`, because
`observableSlotsConfinedToCores` is that module's predicate. -/
def endpointCallDispatchWriteSet
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId)
    (st : SystemState) : List CoreId :=
  endpointCallWriteSet st endpointId executingCore
    ++ endpointCallDispatchChainWriteSet endpointId caller msg endpointRights
        receiverSlotBase executingCore st

/-- **WS-RR RR8.12 Cut C3a**: the replenish-queue cores the live `.call` dispatch's
donation migrates between — the caller's home and the receiver's — recovered from
the pre-state by mirroring `endpointCallCrossCoreDispatch`'s own control flow, as
`endpointCallDispatchChainWriteSet` mirrors it for the chain: the same WithCaps
leg, the same receiver, the same two `toValid?`s, and the donation's own guard
`callDonationSchedContext?` asked of the two threads the dispatch asks it of, **at
the WithCaps post-state**, which is where `applyCallDonationOnCore` reads it.  The
two homes are read off the pre-state because that is where the dispatch reads
them — `applyCallDonationOnCore st' callerV receiverV (determineTargetCore st
caller) (determineTargetCore st receiverTid)` — so the footprint's pair and the
migration's endpoints are the same two expressions, and no home-core frame stands
between them.

Every arm on which the dispatch migrates nothing returns `[]`: a failed leg, no
receiver, a caller or receiver that does not validate, and a guard that declines
(a bound receiver, or a caller with no context to hand on).  That last one is
exact rather than merely narrow
(`endpointCallCrossCoreDispatch_replenishQueueOnCore_of_no_donation`), and it
matters: lock contention is an observable channel (SM8.D's CC-5), so a segment
naming two cores for a migration that does not happen is a footprint wider than
its operation — the over-declaration Cut C1 removed from the `.receive` segment. -/
def endpointCallDispatchReplenishCores
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId)
    (st : SystemState) : List CoreId :=
  let maybeReceiver := match st.getEndpoint? endpointId with
    | some ep => ep.receiveQ.head
    | none => none
  match endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st with
  | (_, .error _) => []
  | (st', .ok _) =>
      match maybeReceiver with
      | some receiverTid =>
        match SeLe4n.ThreadId.toValid? caller, SeLe4n.ThreadId.toValid? receiverTid with
        | some callerV, some receiverV =>
          match callDonationSchedContext? st' callerV.val receiverV.val with
          | some _ => [determineTargetCore st caller, determineTargetCore st receiverTid]
          | none => []
        | _, _ => []
      | none => []

/-- The segment on a rendezvous whose donation resolves: the migration's own two
endpoints, read where the dispatch reads them. -/
theorem endpointCallDispatchReplenishCores_of_donation (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st stWith : SystemState)
    (receiverTid : SeLe4n.ThreadId) (callerV receiverV : SeLe4n.ValidThreadId)
    (summary : CapTransferSummary) (sgi : Option (CoreId × SgiKind))
    (scId : SeLe4n.SchedContextId)
    (hRecv : endpointCallReceiver? st endpointId = some receiverTid)
    (hWith : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st = (stWith, .ok (summary, sgi)))
    (hCallerV : SeLe4n.ThreadId.toValid? caller = some callerV)
    (hRecvV : SeLe4n.ThreadId.toValid? receiverTid = some receiverV)
    (hSc : callDonationSchedContext? stWith callerV.val receiverV.val = some scId) :
    endpointCallDispatchReplenishCores endpointId caller msg endpointRights
        receiverSlotBase executingCore st
      = [determineTargetCore st caller, determineTargetCore st receiverTid] := by
  have hRecv' : (match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head
      | none => none) = some receiverTid := hRecv
  unfold endpointCallDispatchReplenishCores
  simp only [hWith, hRecv', hCallerV, hRecvV, hSc]

/-- Where the guard declines, no core. -/
theorem endpointCallDispatchReplenishCores_of_no_donation (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st stWith : SystemState)
    (receiverTid : SeLe4n.ThreadId) (callerV receiverV : SeLe4n.ValidThreadId)
    (summary : CapTransferSummary) (sgi : Option (CoreId × SgiKind))
    (hRecv : endpointCallReceiver? st endpointId = some receiverTid)
    (hWith : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st = (stWith, .ok (summary, sgi)))
    (hCallerV : SeLe4n.ThreadId.toValid? caller = some callerV)
    (hRecvV : SeLe4n.ThreadId.toValid? receiverTid = some receiverV)
    (hNone : callDonationSchedContext? stWith callerV.val receiverV.val = none) :
    endpointCallDispatchReplenishCores endpointId caller msg endpointRights
        receiverSlotBase executingCore st = [] := by
  have hRecv' : (match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head
      | none => none) = some receiverTid := hRecv
  unfold endpointCallDispatchReplenishCores
  simp only [hWith, hRecv', hCallerV, hRecvV, hNone]

/-- And with no receiver — the block path — none either, whatever the leg did. -/
theorem endpointCallDispatchReplenishCores_of_no_receiver (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st : SystemState)
    (hRecv : endpointCallReceiver? st endpointId = none) :
    endpointCallDispatchReplenishCores endpointId caller msg endpointRights
        receiverSlotBase executingCore st = [] := by
  have hRecv' : (match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head
      | none => none) = none := hRecv
  unfold endpointCallDispatchReplenishCores
  cases endpointCallWithCapsOnCore endpointId caller msg endpointRights receiverSlotBase
      executingCore st with
  | mk st' res =>
    cases res with
    | error e => rfl
    | ok pair => simp only [hRecv']

/-- **WS-RR RR8.12 Cut C3a**: the scheduler-domain footprint of the live `.call`
arm — the object-store table write lock, the run-queue write locks of every core
the dispatch writes (the caller's own, the receiver's home on a rendezvous, and
the home of each priority-inheritance chain member the walk re-buckets), and the
replenish-queue write locks of the two cores the donation migrates between.

**Every core is derived; nothing is a parameter.**  The run segment is
`endpointCallDispatchWriteSet`, the arm's own SM8.B write set, which
`endpointCallCrossCoreDispatch_confinedToCores` is stated at — so the footprint and
the confinement claim cannot name different cores (Cut 7's rule).  The replenish
segment is `endpointCallDispatchReplenishCores`, the donation's own pair by
construction.  Both mirror the dispatch's own control flow, so the footprint's
resolution and the transition's are one computation, and a bracket resolving this
footprint has everything it needs before the transition runs.

**The chain walk is in the run segment, not left to the dynamic extension.**
`endpointCallDispatchWriteSet` appends `pipChainWriteSet` at the post-donation
state the walk really starts from, so every run queue the reversion re-buckets is a
static member here — bounded by the object count rather than by a constant, which
a `SchedLockSet` permits, carrying no cardinality bound.  What
`pipChainStart_endpointCall`'s dynamic walker still adds is the object domain's
per-member TCB write lock, which no scheduler footprint can name.  The RR2.4
parametric `endpointCallCrossCoreDispatchSchedLockSet` is the shape this refines:
on the rendezvous arm whose donation resolves, this footprint covers it at the
resolved cores (`…_covers_parametric`), and names besides the chain members the
parametric form left to the walker. -/
def schedLockSet_endpointCallOnCore
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId)
    (st : SystemState) : List (SchedLockId × Concurrency.AccessMode) :=
  schedFootprintOfCores
    (endpointCallDispatchWriteSet endpointId caller msg endpointRights receiverSlotBase
      executingCore st)
    (endpointCallDispatchReplenishCores endpointId caller msg endpointRights receiverSlotBase
      executingCore st)

-- No `_write_only` / `_pairwise_le` restatement here, and that is deliberate: both
-- are `schedFootprintOfCores_write_only` / `_pairwise_le` applied to this
-- footprint's own arguments, so a consumer reaches for the shared lemma directly.

/-- **WS-RR RR8.12 Cut C3a**: the caller's own core is a run-queue write member on
both paths — it is descheduled there whether it rendezvouses or blocks. -/
theorem schedLockSet_endpointCallOnCore_contains_executing_runQueue_write
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) :
    (SchedLockId.runQueue ⟨executingCore⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_endpointCallOnCore endpointId caller msg endpointRights
          receiverSlotBase executingCore st := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  unfold endpointCallDispatchWriteSet
  exact List.mem_append.mpr
    (Or.inl (executingCore_mem_endpointCallWriteSet st endpointId executingCore))

/-- **WS-RR RR8.12 Cut C3a**: and with a receiver waiting, that receiver's home
core — resolved through `endpointCallReceiver?`, the resolver the object-domain
footprint's own receiver member comes from. -/
theorem schedLockSet_endpointCallOnCore_contains_receiver_runQueue_write
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hRecv : endpointCallReceiver? st endpointId = some receiver) :
    (SchedLockId.runQueue ⟨determineTargetCore st receiver⟩, Concurrency.AccessMode.write)
      ∈ schedLockSet_endpointCallOnCore endpointId caller msg endpointRights
          receiverSlotBase executingCore st := by
  refine (mem_schedFootprintOfCores_runQueue_iff _ _ _).mpr ?_
  unfold endpointCallDispatchWriteSet
  rw [endpointCallWriteSet_of_receiver st endpointId executingCore receiver hRecv]
  simp

/-- **WS-RR RR8.12 Cut C3a (coverage)**: on the rendezvous arm whose donation
resolves, the footprint covers `applyCallDonationOnCoreSchedLockSet` member for
member — at the two cores the dispatch hands the migration, which are the two the
segment names — hence, through
`applyCallDonationOnCoreSchedLockSet_covers_migration`, the migration's two
replenish-queue write locks.  Conditioned on the dispatch's own readings (the
receiver it resolves, the WithCaps leg it runs, the guard it asks at that leg's
post-state), because those are the only shape on which there is a migration to
cover. -/
theorem schedLockSet_endpointCallOnCore_covers_donation (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st stWith : SystemState)
    (receiverTid : SeLe4n.ThreadId) (callerV receiverV : SeLe4n.ValidThreadId)
    (summary : CapTransferSummary) (sgi : Option (CoreId × SgiKind))
    (scId : SeLe4n.SchedContextId)
    (hRecv : endpointCallReceiver? st endpointId = some receiverTid)
    (hWith : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st = (stWith, .ok (summary, sgi)))
    (hCallerV : SeLe4n.ThreadId.toValid? caller = some callerV)
    (hRecvV : SeLe4n.ThreadId.toValid? receiverTid = some receiverV)
    (hSc : callDonationSchedContext? stWith callerV.val receiverV.val = some scId) :
    ∀ p ∈ applyCallDonationOnCoreSchedLockSet (determineTargetCore st caller)
             (determineTargetCore st receiverTid),
      p ∈ schedLockSet_endpointCallOnCore endpointId caller msg endpointRights
            receiverSlotBase executingCore st := by
  have hSeg := endpointCallDispatchReplenishCores_of_donation endpointId caller msg
    endpointRights receiverSlotBase executingCore st stWith receiverTid callerV receiverV
    summary sgi scId hRecv hWith hCallerV hRecvV hSc
  unfold applyCallDonationOnCoreSchedLockSet schedLockSet_endpointCallOnCore
  rw [hSeg]
  exact schedFootprintOfCores_subset (fun _ h => absurd h (by simp)) (fun _ h => h)

/-- **WS-RR RR8.12 Cut C3a (the RR2.4 footprint is covered)**: on the same arm the
derived footprint covers the parametric `endpointCallCrossCoreDispatchSchedLockSet`
at the resolved cores — the executing core and the receiver's home in its run
segment, the caller's and receiver's homes in its replenish segment — and names in
addition every chain member's home, which the parametric form leaves to the dynamic
extension.  The RR2.4 lemmas are stated over the parametric shape; this is what
carries them to the footprint the syscall resolver consumes. -/
theorem schedLockSet_endpointCallOnCore_covers_parametric (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage) (endpointRights : AccessRightSet)
    (receiverSlotBase : SeLe4n.Slot) (executingCore : CoreId) (st stWith : SystemState)
    (receiverTid : SeLe4n.ThreadId) (callerV receiverV : SeLe4n.ValidThreadId)
    (summary : CapTransferSummary) (sgi : Option (CoreId × SgiKind))
    (scId : SeLe4n.SchedContextId)
    (hRecv : endpointCallReceiver? st endpointId = some receiverTid)
    (hWith : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st = (stWith, .ok (summary, sgi)))
    (hCallerV : SeLe4n.ThreadId.toValid? caller = some callerV)
    (hRecvV : SeLe4n.ThreadId.toValid? receiverTid = some receiverV)
    (hSc : callDonationSchedContext? stWith callerV.val receiverV.val = some scId) :
    ∀ p ∈ endpointCallCrossCoreDispatchSchedLockSet executingCore
             (determineTargetCore st receiverTid) (determineTargetCore st caller)
             (determineTargetCore st receiverTid),
      p ∈ schedLockSet_endpointCallOnCore endpointId caller msg endpointRights
            receiverSlotBase executingCore st := by
  have hSeg := endpointCallDispatchReplenishCores_of_donation endpointId caller msg
    endpointRights receiverSlotBase executingCore st stWith receiverTid callerV receiverV
    summary sgi scId hRecv hWith hCallerV hRecvV hSc
  unfold endpointCallCrossCoreDispatchSchedLockSet schedLockSet_endpointCallOnCore
  rw [hSeg]
  refine schedFootprintOfCores_subset (fun c hc => ?_) (fun _ h => h)
  unfold endpointCallDispatchWriteSet
  rw [endpointCallWriteSet_of_receiver st endpointId executingCore receiverTid hRecv]
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  simp only [List.mem_append, List.mem_cons]
  rcases hc with h | h <;> simp [h]

/-- **WS-RR RR8.12 Cut C3a (the empty segment, footprint side)**: where the guard
declines the footprint names no replenish-queue lock — over-declaring is sound and
not free (SM8.D's CC-5), and
`endpointCallCrossCoreDispatch_replenishQueueOnCore_of_no_donation` is the licence
that the transition writes none there either. -/
theorem schedLockSet_endpointCallOnCore_no_replenishQueue_of_no_donation
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st stWith : SystemState) (receiverTid : SeLe4n.ThreadId)
    (callerV receiverV : SeLe4n.ValidThreadId) (summary : CapTransferSummary)
    (sgi : Option (CoreId × SgiKind))
    (hRecv : endpointCallReceiver? st endpointId = some receiverTid)
    (hWith : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st = (stWith, .ok (summary, sgi)))
    (hCallerV : SeLe4n.ThreadId.toValid? caller = some callerV)
    (hRecvV : SeLe4n.ThreadId.toValid? receiverTid = some receiverV)
    (hNone : callDonationSchedContext? stWith callerV.val receiverV.val = none)
    (c : CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_endpointCallOnCore endpointId caller msg endpointRights
          receiverSlotBase executingCore st := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ c).mp hMem
  rw [endpointCallDispatchReplenishCores_of_no_donation endpointId caller msg endpointRights
    receiverSlotBase executingCore st stWith receiverTid callerV receiverV summary sgi hRecv
    hWith hCallerV hRecvV hNone] at this
  simp at this

/-- **WS-RR RR8.12 Cut C3a**: and on the block path — no receiver, so no
rendezvous and no donation — none either. -/
theorem schedLockSet_endpointCallOnCore_no_replenishQueue_of_no_receiver
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hRecv : endpointCallReceiver? st endpointId = none) (c : CoreId) :
    (SchedLockId.replenishQueue ⟨c⟩, Concurrency.AccessMode.write)
      ∉ schedLockSet_endpointCallOnCore endpointId caller msg endpointRights
          receiverSlotBase executingCore st := by
  intro hMem
  have := (mem_schedFootprintOfCores_replenishQueue_iff _ _ c).mp hMem
  rw [endpointCallDispatchReplenishCores_of_no_receiver endpointId caller msg endpointRights
    receiverSlotBase executingCore st hRecv] at this
  simp at this

/-- **WS-RR RR8.12 Cut C3a (the empty segment, transition side)**: on the block
path the live dispatch is the WithCaps leg alone
(`endpointCallCrossCoreDispatch_no_receiver`), which writes no replenish queue. -/
theorem endpointCallCrossCoreDispatch_replenishQueueOnCore_of_no_receiver
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st : SystemState)
    (hRecv : endpointCallReceiver? st endpointId = none) (c : CoreId) :
    (endpointCallCrossCoreDispatch endpointId caller msg endpointRights receiverSlotBase
        executingCore st).1.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
  rw [endpointCallCrossCoreDispatch_no_receiver endpointId caller msg endpointRights
    receiverSlotBase executingCore st hRecv]
  exact endpointCallWithCapsOnCore_replenishQueueOnCore endpointId caller msg endpointRights
    receiverSlotBase executingCore st c

/-- **WS-RR RR8.12 Cut C3a (the empty segment, transition side)**: and where the
guard declines on a rendezvous, the live dispatch writes no replenish queue either
— the WithCaps leg never does
(`endpointCallWithCapsOnCore_replenishQueueOnCore`), the donation's migration arm
is not taken (`applyCallDonationOnCore_replenishQueueOnCore_of_no_donation`), and
the chain walk re-buckets run queues alone
(`propagatePipChainCrossCore_replenishQueueOnCore`).  So the empty segment is
exact, not merely narrow: the footprint declares no replenish lock there, and the
transition writes none. -/
theorem endpointCallCrossCoreDispatch_replenishQueueOnCore_of_no_donation
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (endpointRights : AccessRightSet) (receiverSlotBase : SeLe4n.Slot)
    (executingCore : CoreId) (st stWith stDisp : SystemState)
    (receiverTid : SeLe4n.ThreadId) (callerV receiverV : SeLe4n.ValidThreadId)
    (summary : CapTransferSummary) (sgi : Option (CoreId × SgiKind))
    (res : Except KernelError (CapTransferSummary × Option (CoreId × SgiKind)))
    (hRecv : endpointCallReceiver? st endpointId = some receiverTid)
    (hWith : endpointCallWithCapsOnCore endpointId caller msg endpointRights
      receiverSlotBase executingCore st = (stWith, .ok (summary, sgi)))
    (hCallerV : SeLe4n.ThreadId.toValid? caller = some callerV)
    (hRecvV : SeLe4n.ThreadId.toValid? receiverTid = some receiverV)
    (hNone : callDonationSchedContext? stWith callerV.val receiverV.val = none)
    (hDisp : endpointCallCrossCoreDispatch endpointId caller msg endpointRights
      receiverSlotBase executingCore st = (stDisp, res)) (c : CoreId) :
    stDisp.scheduler.replenishQueueOnCore c = st.scheduler.replenishQueueOnCore c := by
  have hRecv' : (match st.getEndpoint? endpointId with
      | some ep => ep.receiveQ.head
      | none => none) = some receiverTid := hRecv
  have hWithRep : stWith.scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c := by
    have h := endpointCallWithCapsOnCore_replenishQueueOnCore endpointId caller msg
      endpointRights receiverSlotBase executingCore st c
    rw [hWith] at h
    exact h
  unfold endpointCallCrossCoreDispatch at hDisp
  simp only [hWith, hRecv', hCallerV, hRecvV] at hDisp
  cases hDon : applyCallDonationOnCore stWith callerV receiverV (determineTargetCore st caller)
      (determineTargetCore st receiverTid) with
  | error e =>
    rw [hDon] at hDisp
    simp only [] at hDisp
    rw [← (Prod.mk.inj hDisp).1]
    exact hWithRep
  | ok stDon =>
    rw [hDon] at hDisp
    simp only [] at hDisp
    rw [← (Prod.mk.inj hDisp).1,
      PriorityInheritance.propagatePipChainCrossCore_replenishQueueOnCore,
      applyCallDonationOnCore_replenishQueueOnCore_of_no_donation stWith stDon callerV
        receiverV _ _ hNone hDon c]
    exact hWithRep

end SeLe4n.Kernel
