-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-SM SM6.C: PRODUCTION (LANDED).  The pure `.reply` / `.replyRecv` dispatch ops
-- below the API layer; the live `API.dispatchWithCap{,Checked}` `.reply` /
-- `.replyRecv` arms route through `endpointReplyCrossCoreDispatch{,Checked}` /
-- `endpointReplyRecvCrossCoreDispatch{,Checked}` here, deriving the executing core
-- from the live state (`determineExecutingCore`).  See
-- docs/planning/SMP_CROSS_CORE_IPC_PLAN.md §3.1, §4.3, §5 (SM6.C).

import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInvariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.Operations.Donation.Primitives
import SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers

/-!
# WS-SM SM6.C — Cross-core `.reply` / `.replyRecv` dispatch (pure; below the API layer)

The pure cross-core reply dispatch operations — `endpointReplyCrossCoreDispatch`,
`endpointReplyRecvCrossCoreDispatch`, and the information-flow-checked
`endpointReplyCrossCoreDispatchChecked` / `endpointReplyRecvCrossCoreDispatchChecked`.
These live *below* `SeLe4n.Kernel.API` (no `Platform.FFI` dependency) so the live
`.reply` / `.replyRecv` dispatch arms can route through them — the cross-core
generalisation of the single-core `endpointReplyWithDonation` /
`endpointReplyRecvWithDonation`.

Each dispatch composes:

* the cross-core reply (`endpointReplyOnCore` / `endpointReplyRecvOnCore` — wakes
  the original caller on its *home* core);
* the SchedContext **donation return** (`applyReplyDonationOnCore` — returns the
  replier's donated SC to the original owner and deschedules the now-passive
  replier on *its own* core); and
* the cross-core priority-inheritance **reversion** (`propagatePipChainCrossCore`
  — `revert_eq_propagate`: reversion is functionally propagation, walking the
  blocking chain up from the unblocked caller, migrating each link's run-queue
  bucket on its home core, plan §4.3).

The surfaced SGI is the reply-leg caller wake's; the cross-core PIP-chain SGIs are
re-derived from the committed-state diff by the live syscall entry
(`computeCrossCoreSgis`), exactly as the SM6.A `.call` dispatch surfaces only the
receiver-wake SGI and takes `propagatePipChainCrossCore.1` for the state.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  SM6.C.3 — Cross-core donation return (`applyReplyDonationOnCore`)
-- ============================================================================

/-- WS-SM SM6.C.3 (plan §4.3): the cross-core generalisation of
`applyReplyDonation`.  Returns the replier's donated SchedContext to its original
owner (`returnDonatedSchedContextValid`, an object-store-only rebinding that is
cross-core-safe) and deschedules the now-passive replier on *its own* core via
`removeRunnableOnCore … executingCore` (rather than the boot-pinned
`removeRunnable`).  A replier that holds no donated SC is a no-op (the common
non-donating reply). -/
def applyReplyDonationOnCore (st : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : Except KernelError SystemState :=
  let replier : SeLe4n.ThreadId := replierVtid.val
  match lookupTcb st replier with
  | none => .ok st
  | some replierTcb =>
    match replierTcb.schedContextBinding with
    | .donated scId originalOwner =>
      match SeLe4n.ThreadId.toValid? originalOwner with
      | some ownerVtid =>
          match returnDonatedSchedContextValid st replierVtid scId ownerVtid with
          | .error e => .error e
          | .ok st' => .ok (removeRunnableOnCore st' replier executingCore)
      | none => .error .invalidArgument
    | _ => .ok st

/-- WS-SM SM6.C.3 (bootCore bridge): `applyReplyDonationOnCore … bootCoreId` is
exactly the single-core `applyReplyDonation` — the `removeRunnableOnCore …
bootCoreId = removeRunnable` backward-compatibility bridge carried through the
donation return. -/
theorem applyReplyDonationOnCore_bootCoreId (st : SystemState)
    (replierVtid : SeLe4n.ValidThreadId) :
    applyReplyDonationOnCore st replierVtid bootCoreId = applyReplyDonation st replierVtid := rfl

-- ============================================================================
-- §2  SM6.C.3 — Donation-chain lock-set extension
-- ============================================================================

/-- WS-SM SM6.C.3 (plan §4.3): the cross-core donation-chain lock-set extension
for reply.  When the reply returns a SchedContext to its original owner, the
`endpointReply` lock-set is *exactly* the non-returning lock-set extended with the
returned SchedContext's **write** lock and the original owner's TCB **write**
lock — so the SC migration (`returnDonatedSchedContextValid` rebinding
`boundThread` across cores, SM5.H.4) and the owner's re-activation both run under
held write locks, serialised against every other core. -/
theorem lockSet_endpointReply_donation_extension
    (replier : SeLe4n.ThreadId) (cnRoot : SeLe4n.ObjId) (target : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId) :
    lockSet_endpointReply replier cnRoot target (some scId) (some originalOwner)
      = lockSetExtendOpt
          (lockSetExtendOpt
            (lockSet_endpointReply replier cnRoot target none none)
            (some (schedContextLock scId, .write)))
          (some (tcbLock originalOwner, .write)) := by
  unfold lockSet_endpointReply
  rfl

-- ============================================================================
-- §3  SM6.C — Full cross-core `.reply` dispatch (reply + donation + PIP revert)
-- ============================================================================

/-- WS-SM SM6.C (operation): the full cross-core `Reply` syscall semantics.  The
cross-core reply (`endpointReplyOnCore` — caller woken on its home core), then the
SchedContext donation **return** (`applyReplyDonationOnCore` — the passive server
returns the donated SC and is descheduled on its own core), then the cross-core
priority-inheritance **reversion** (`propagatePipChainCrossCore` — the unblocked
caller's blocking chain re-derives each holder's boost from its remaining
waiters, migrating buckets on home cores).  Surfaces the reply-leg caller-wake
SGI; the chain-walk SGIs are re-derived from the committed diff.  Mirrors the live
single-core `.reply` dispatch arm (`API.dispatchWithCap`). -/
def endpointReplyCrossCoreDispatch
    (replier : SeLe4n.ThreadId) (target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  match endpointReplyOnCore replier target msg executingCore st with
  | (_, .error e) => (st, .error e)
  | (st1, .ok replySgi?) =>
      match SeLe4n.ThreadId.toValid? replier with
      | some replierV =>
          match applyReplyDonationOnCore st1 replierV executingCore with
          | .error e => (st, .error e)
          | .ok st2 =>
              ((PriorityInheritance.propagatePipChainCrossCore st2 replier executingCore).1, .ok replySgi?)
      | none => (st, .error .invalidArgument)

/-- WS-SM SM6.C (live `.reply` enforcement): the **information-flow-checked**
cross-core reply dispatch — the cross-core analogue of `endpointReplyChecked`
composed with `endpointReplyCrossCoreDispatch`.  Mirrors the single-core checked
`.reply` arm: it first applies the SM-IF security guard
(`securityFlowsTo replierLabel targetLabel`, rejecting with `.flowDenied` on a
disallowed flow — the reply may flow information from the replier's domain to the
caller's), then runs the full cross-core dispatch. -/
def endpointReplyCrossCoreDispatchChecked
    (ctx : LabelingContext) (replier : SeLe4n.ThreadId) (target : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (Option (CoreId × SgiKind)) :=
  if securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) then
    endpointReplyCrossCoreDispatch replier target msg executingCore st
  else
    (st, .error .flowDenied)

/-- WS-SM SM6.C: a disallowed flow is rejected before any state change — the
checked cross-core reply dispatch is fail-closed (state unchanged, `.flowDenied`). -/
theorem endpointReplyCrossCoreDispatchChecked_flow_denied
    (ctx : LabelingContext) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = false) :
    endpointReplyCrossCoreDispatchChecked ctx replier target msg executingCore st
      = (st, .error .flowDenied) := by
  simp [endpointReplyCrossCoreDispatchChecked, hDeny]

/-- WS-SM SM6.C: when the flow is permitted, the checked dispatch is exactly the
unchecked cross-core reply dispatch — the guard is a pure precondition. -/
theorem endpointReplyCrossCoreDispatchChecked_flow_allowed
    (ctx : LabelingContext) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = true) :
    endpointReplyCrossCoreDispatchChecked ctx replier target msg executingCore st
      = endpointReplyCrossCoreDispatch replier target msg executingCore st := by
  simp [endpointReplyCrossCoreDispatchChecked, hAllow]

-- ============================================================================
-- §4  SM6.C.5 — Full cross-core `.replyRecv` dispatch
-- ============================================================================

/-- WS-SM SM6.C.5 (operation): the full cross-core `ReplyRecv` syscall semantics —
the cross-core reply-and-receive (`endpointReplyRecvOnCore`) then the donation
return + cross-core PIP reversion for the reply leg, mirroring the single-core
`endpointReplyRecvWithDonation`.  Surfaces the union of the reply+receive cross-core
SGIs. -/
def endpointReplyRecvCrossCoreDispatch
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId) (replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState) :
    SystemState × Except KernelError (List (CoreId × SgiKind)) :=
  match endpointReplyRecvOnCore endpointId receiver replyTarget msg executingCore st with
  | (_, .error e) => (st, .error e)
  | (st1, .ok sgis) =>
      match SeLe4n.ThreadId.toValid? receiver with
      | some receiverV =>
          match applyReplyDonationOnCore st1 receiverV executingCore with
          | .error e => (st, .error e)
          | .ok st2 =>
              ((PriorityInheritance.propagatePipChainCrossCore st2 receiver executingCore).1, .ok sgis)
      | none => (st, .error .invalidArgument)

/-- WS-SM SM6.C.5 (live `.replyRecv` enforcement): the information-flow-checked
cross-core reply-and-receive dispatch.  Mirrors the single-core
`endpointReplyRecvChecked`'s **two** flow gates: the reply leg (receiver →
replyTarget) and the receive leg (endpoint → receiver).  Both must hold. -/
def endpointReplyRecvCrossCoreDispatchChecked
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyTarget : SeLe4n.ThreadId) (msg : IpcMessage) (executingCore : CoreId)
    (st : SystemState) :
    SystemState × Except KernelError (List (CoreId × SgiKind)) :=
  if securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf replyTarget) then
    if securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) then
      endpointReplyRecvCrossCoreDispatch endpointId receiver replyTarget msg executingCore st
    else
      (st, .error .flowDenied)
  else
    (st, .error .flowDenied)

/-- WS-SM SM6.C.5: the checked replyRecv dispatch is fail-closed on a denied reply
leg. -/
theorem endpointReplyRecvCrossCoreDispatchChecked_reply_flow_denied
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState)
    (hDeny : securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf replyTarget) = false) :
    endpointReplyRecvCrossCoreDispatchChecked ctx endpointId receiver replyTarget msg executingCore st
      = (st, .error .flowDenied) := by
  simp [endpointReplyRecvCrossCoreDispatchChecked, hDeny]

/-- WS-SM SM6.C.5: the checked replyRecv dispatch is fail-closed on a denied
receive leg (even when the reply leg is permitted). -/
theorem endpointReplyRecvCrossCoreDispatchChecked_recv_flow_denied
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState)
    (hReply : securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf replyTarget) = true)
    (hDeny : securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) = false) :
    endpointReplyRecvCrossCoreDispatchChecked ctx endpointId receiver replyTarget msg executingCore st
      = (st, .error .flowDenied) := by
  simp [endpointReplyRecvCrossCoreDispatchChecked, hReply, hDeny]

/-- WS-SM SM6.C: when the reply leg flow is permitted, the checked reply dispatch
is exactly the unchecked cross-core dispatch — the guard is a pure precondition.
The single-gate companion of the `.replyRecv` flow-allowed lemma. -/
theorem endpointReplyCrossCoreDispatchChecked_eq_unchecked_of_flow
    (ctx : LabelingContext) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState)
    (hAllow : securityFlowsTo (ctx.threadLabelOf replier) (ctx.threadLabelOf target) = true) :
    endpointReplyCrossCoreDispatchChecked ctx replier target msg executingCore st
      = endpointReplyCrossCoreDispatch replier target msg executingCore st :=
  endpointReplyCrossCoreDispatchChecked_flow_allowed ctx replier target msg executingCore st hAllow

/-- WS-SM SM6.C.5: when *both* flow legs (reply receiver → replyTarget, receive
endpoint → receiver) are permitted, the checked replyRecv dispatch is exactly the
unchecked cross-core dispatch. -/
theorem endpointReplyRecvCrossCoreDispatchChecked_flow_allowed
    (ctx : LabelingContext) (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (executingCore : CoreId) (st : SystemState)
    (hReply : securityFlowsTo (ctx.threadLabelOf receiver) (ctx.threadLabelOf replyTarget) = true)
    (hRecv : securityFlowsTo (ctx.endpointLabelOf endpointId) (ctx.threadLabelOf receiver) = true) :
    endpointReplyRecvCrossCoreDispatchChecked ctx endpointId receiver replyTarget msg executingCore st
      = endpointReplyRecvCrossCoreDispatch endpointId receiver replyTarget msg executingCore st := by
  simp [endpointReplyRecvCrossCoreDispatchChecked, hReply, hRecv]

-- ============================================================================
-- §5  SM6.C.9 — Reply donation-chain length bound (donation k > 2)
-- ============================================================================

/-- WS-SM SM6.C.9 (reply chain length bound): the cross-core priority-inheritance
**reversion** the reply dispatch runs (`propagatePipChainCrossCore` over the
unblocked caller's blocking chain) emits **at most `fuel`** cross-core SGIs —
with the default `fuel := objectIndex.length`, at most one per kernel object.  A
deep donation chain (k > 2 nested passive servers) therefore terminates and pokes
a bounded number of remote cores: the chain walk is structurally recursive on
fuel, and the acyclicity invariant
(`propagatePipChainCrossCore_preserves_blockingAcyclic`) guarantees it never
revisits a holder, so `objectIndex.length` fuel always exhausts the chain. -/
theorem endpointReply_donation_chain_length_bounded
    (st : SystemState) (caller : SeLe4n.ThreadId) (executingCore : CoreId) (fuel : Nat) :
    (PriorityInheritance.propagatePipChainCrossCore st caller executingCore fuel).2.length ≤ fuel := by
  induction fuel generalizing st caller with
  | zero => simp [PriorityInheritance.propagatePipChainCrossCore]
  | succ n ih =>
    rw [PriorityInheritance.propagatePipChainCrossCore_step]
    cases hsgi : (PriorityInheritance.pipBoostWithWake st caller executingCore).2 with
    | none =>
      cases hbs : PriorityInheritance.blockingServer st caller with
      | none => simp [hsgi]
      | some nextServer =>
        simp only [hsgi]
        exact Nat.le_trans
          (by simpa using ih (PriorityInheritance.pipBoostWithWake st caller executingCore).1 nextServer)
          (Nat.le_succ n)
    | some s =>
      cases hbs : PriorityInheritance.blockingServer st caller with
      | none => simp only [hsgi]; exact Nat.succ_le_succ (Nat.zero_le n)
      | some nextServer =>
        simp only [hsgi, List.singleton_append, List.length_cons]
        exact Nat.succ_le_succ (ih (PriorityInheritance.pipBoostWithWake st caller executingCore).1 nextServer)

end SeLe4n.Kernel
