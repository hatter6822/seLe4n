-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Core
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.Architecture.SyscallReturn

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Z6-C: Timeout-driven IPC unblocking
-- ============================================================================

-- ============================================================================
-- AG8-A (H3-IPC-01/I-01): Timeout sentinel eliminated.
--
-- Previous design used a fragile composite check:
--   (1) gpr x0 = 0xFFFFFFFF (timeoutErrorCode sentinel), AND
--   (2) ipcState = .ready
--
-- This has been replaced with an explicit `timedOut : Bool` field on TCB,
-- eliminating the risk of sentinel collision with legitimate IPC data.
-- `timeoutThread` sets `timedOut := true`; `timeoutAwareReceive` checks and
-- clears it. The register x0 is no longer modified by timeout operations.
--
-- History: AE4-F (U-23/IPC-01) documented the migration path. AG8-A
-- implements it.
-- ============================================================================

/-- WS-OD OD1.2: the server whose priority-inheritance boost must be recomputed
once `tid` leaves the blocking graph — `some` exactly when `tid` was waiting on a
reply from it.  Named rather than inlined because the timeout reads it and the
`passiveServerIdle` abort does not, and a second spelling is how the two drift.

Reading it from the **pre**-state is sound: `endpointQueueRemove` writes queue
links only, so the removed thread's `ipcState` is the same before and after. -/
def timeoutBlockingServer? (tcb : TCB) : Option SeLe4n.ThreadId :=
  match tcb.ipcState with
  | .blockedOnReply _ (some serverId) => some serverId
  | _ => none

/-- WS-OD OD1.2: the same question asked of a state — `none` when the thread is
absent, which is the conservative answer (no revert).  Named so `timeoutThread`'s
body has **one** match rather than a nested pair, which is what keeps its
preservation proofs a single `split`. -/
def timeoutBlockingServerOf? (st : SystemState) (tid : SeLe4n.ThreadId) :
    Option SeLe4n.ThreadId :=
  match lookupTcb st tid with
  | some tcb => timeoutBlockingServer? tcb
  | none => none

/-- WS-OD OD1.2: the timeout's **object-only prefix** — take the thread out of
its endpoint queue and rewrite its TCB to the timed-out shape, and stop there.

`timeoutThread` is this followed by the wake and the priority-inheritance
revert; both of those write the **scheduler**, and that is exactly what the
cancellation reclaim cannot do.  `returnDonationToCancelledCaller` states in its
own docstring that it writes `objects` and nothing else, which is what makes
`cancelIpcBlocking_scheduler_eq` true — and four cross-core results consume that
theorem.  So the reclaim calls this prefix, not `timeoutThread`.

The thread it leaves behind is `.ready`, off every queue and (on the reclaim's
path) `.unbound`: a legitimate passive-server shape, and the correct one, since
an unbound thread is unschedulable anyway.  Semantically this *is* a timeout in
MCS terms — the budget the operation was issued on has been revoked — which is
why it stages `Architecture.timeoutFrame` rather than minting a new error. -/
def abortPendingIpcOnEndpoint
    (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId)
    (st : SystemState) : Except KernelError SystemState :=
  -- Step 1: Remove thread from endpoint queue
  match endpointQueueRemove endpointId isReceiveQ tid st with
  | .error e => .error e
  | .ok st1 =>
    -- Step 2: Look up the thread (now with cleared queue links)
    match lookupTcb st1 tid with
    | none => .error .objectNotFound
    | some tcb =>
      -- Step 3: Reset IPC state, clear pending message and timeout budget,
      -- set explicit timedOut flag, update thread state.
      -- AG8-A: Uses timedOut := true instead of sentinel in register x0.
      -- WS-SM SM6.D (PR #822 review): a server-first receive that timed out also
      -- relinquishes its stashed reply (`pendingReceiveReply`) — the stash is only
      -- well-formed while the server is `.blockedOnReceive`, so leaving it set on the
      -- now-`.ready` thread would violate `pendingReceiveReplyWellFormed`.  (No-op for
      -- non-`blockedOnReceive` timed-out threads, which carry no stash.)
      -- WS-RR RR7.14: and stage the **timeout error frame** into the saved
      -- register context.  Without it the thread resumes at the SM10.1 context
      -- restore reading whatever its own argument spill left in `x0`-`x5` — its
      -- own request registers, decoded as a return value.  Folded into this
      -- record update rather than applied as a second state write, so the
      -- transition still commits exactly one object
      -- (`Architecture.stageTimeoutFrame_eq_withReturnFrame` ties the two
      -- spellings).  `timedOut := true` stays: it is the *kernel-side* fact the
      -- scheduler and the invariants read; the frame is the *userspace-side*
      -- answer, and neither substitutes for the other.
      let tcb' : TCB := ({ tcb with
        ipcState := .ready,
        pendingMessage := none,
        timeoutBudget := none,
        threadState := .Ready,
        timedOut := true,
        pendingReceiveReply := none } : TCB).withReturnFrame
          Architecture.timeoutFrame
      match storeObject tid.toObjId (.tcb tcb') st1 with
      | .error e => .error e
      | .ok ((), st2) => .ok st2

/-- WS-OD OD1.2: the abort preserves the object-store invariant — its two writes
are `endpointQueueRemove` (which preserves it) and one TCB `storeObject` insert.
Stated here, beside the definition, so `timeoutThread`'s own preservation and the
cancellation reclaim's both compose it rather than re-running the case analysis. -/
theorem abortPendingIpcOnEndpoint_preserves_objects_invExt
    (epId : SeLe4n.ObjId) (isRecvQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState) (hInv : st.objects.invExt)
    (hStep : abortPendingIpcOnEndpoint epId isRecvQ tid st = .ok st') :
    st'.objects.invExt := by
  unfold abortPendingIpcOnEndpoint at hStep
  split at hStep
  · simp at hStep
  · rename_i st1 hEQR
    have hInv1 := endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hEQR
    split at hStep
    · simp at hStep
    · rename_i tcb hLook
      simp only [storeObject] at hStep
      split at hStep <;>
        · simp only [Except.ok.injEq] at hStep
          subst hStep
          exact RHTable_insert_preserves_invExt st1.objects _ _ hInv1

/-- WS-OD OD1.2: **the abort writes no scheduler state.**  This is the property
the cancellation reclaim is built on — `returnDonationToCancelledCaller` writes
`objects` and nothing else, which is what makes `cancelIpcBlocking_scheduler_eq`
true, and four cross-core results consume that theorem.  `timeoutThread` is the
abort *plus* a wake and a PIP revert, and both of those do write the scheduler;
that is exactly why the reclaim calls this prefix rather than the timeout. -/
theorem abortPendingIpcOnEndpoint_scheduler_eq
    (epId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (h : abortPendingIpcOnEndpoint epId isReceiveQ tid st = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold abortPendingIpcOnEndpoint at h
  split at h
  · simp at h
  · rename_i st1 hER
    have hSched1 := endpointQueueRemove_scheduler_eq epId isReceiveQ tid st st1 hER
    split at h
    · simp at h
    · rename_i tcb hLk
      simp only [storeObject] at h
      split at h <;>
        · simp only [Except.ok.injEq] at h
          subst h
          exact hSched1

/-- Z6-C1/C2/C3: Unblock a thread whose IPC operation has timed out due to
SchedContext budget expiry.

This operation:
1. **Queue removal** (Z6-C2): Removes the thread from the endpoint's send
   or receive queue using `endpointQueueRemove`.
2. **IPC state reset** (Z6-C1): Sets `tcb.ipcState := .ready` and clears
   `tcb.pendingMessage := none` and `tcb.timeoutBudget := none`.
3. **Scheduler re-enqueue** (Z6-C3; target-aware since PR #880 round 8): Sets
   the explicit `timedOut := true` flag on the TCB (AG8-A) and wakes the
   thread on its **home core** via the target-aware `wakeThread`
   (`determineTargetCore` — the affinity core, or the boot core when unbound),
   returning the cross-core `.reschedule` SGI when the home core is remote.
   The pre-round-8 `ensureRunnable` hard-coded the boot queue, so a timeout
   fired by a secondary core's budget tick placed an affinity-bound thread on
   a queue whose dispatcher rejects it (`switchToThreadOnCore`'s
   `affinityAdmitsCore` gate) — stranding the timed-out thread.

The `isReceiveQ` parameter indicates which queue the thread is blocked on:
- `true`: thread was in `blockedOnReceive` on the endpoint's receiveQ
- `false`: thread was in `blockedOnSend`/`blockedOnCall` on the endpoint's sendQ

**Precondition (AUD-Z6-2):** The caller must ensure `tid` refers to a thread
in a blocking IPC state (`blockedOnSend`, `blockedOnReceive`, `blockedOnCall`,
or `blockedOnReply`) on the endpoint identified by `endpointId`. The sole caller
`timeoutBlockedThreads` validates this via `tcbBlockingInfo`, which returns
`none` for non-blocking states. Calling this on a non-blocked thread would
incorrectly reset its state and write the timeout error code.

**AK1-F (I-M04) — PIP revert call-state invariant:** The PIP revert path
(`maybeBlockingServer` / `revertPriorityInheritance`) only handles the
`.blockedOnReply _ (some serverId)` case. This is correct because:

(i) `pipBoost.isSome` is established only by `propagatePipBoost` in
    `Scheduler.PriorityInheritance.Propagate`, which is called exclusively
    from the reply-blocking chain construction (when a client enters
    `.blockedOnReply` via `endpointCall` / `endpointSendDualChecked`'s
    handshake branch). No other IPC state produces a PIP boost.

(ii) Under `ipcInvariantFull`, the implication `tcb.pipBoost.isSome →
     ∃ ep rt, tcb.ipcState = .blockedOnReply ep rt` holds. This is the
     frame-lemma bundle `propagatePipBoost_*` in
     `PriorityInheritance/Preservation.lean`.

(iii) Therefore, clients with `.blockedOnSend` / `.blockedOnReceive` /
      `.blockedOnNotification` / `.blockedOnCall` never have a PIP boost to
      revert — the other arms of `timeoutThread`'s `match maybeBlockingServer`
      discriminator's `none` branch are correct by invariant.

This relationship is fragile in the sense that any future change that adds
PIP boosting outside the reply-chain (e.g., dynamic priority inheritance
for notification wait queues) would require extending the revert logic
here. The invariant is pin-pointed by
`blockingGraph_pipBoost_implies_blockedOnReply` (D4; see
`Scheduler/PriorityInheritance/BlockingGraph.lean`).

Returns the updated state paired with the optional cross-core `.reschedule`
SGI the caller must emit after its state commit (`none` for a local or
unbound wake), or an error if endpoint/thread lookup fails.  The
`executingCore` parameter is the core running the timeout (the budget
tick's core) — the SGI decision compares the wake target against it. -/
def timeoutThread
    (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId)
    (st : SystemState) : Except KernelError (SystemState × Option (Concurrency.CoreId × Concurrency.SgiKind)) :=
  -- WS-OD OD1.2: the object-only prefix, then the two scheduler writes.  The
  -- prefix is shared with the cancellation reclaim, which must not perform
  -- those two — see `abortPendingIpcOnEndpoint`.
  match abortPendingIpcOnEndpoint endpointId isReceiveQ tid st with
  | .error e => .error e
  | .ok st2 =>
    -- D4-N: Capture the blocking server before the prefix clears `ipcState` —
    -- if the thread was `.blockedOnReply`, the server's pipBoost must be
    -- recomputed once this client leaves the blocking graph.  Read from the
    -- **pre**-state, which agrees with the post-removal reading because
    -- `endpointQueueRemove` writes queue links only.  The `none` arm is
    -- unreachable (the prefix succeeded, so the TCB was there) and is the
    -- conservative answer: no revert.
    let maybeBlockingServer := timeoutBlockingServerOf? st tid
    -- Step 4: Re-enqueue in RunQueue at current priority
    -- PR #880 round 8: wake on the thread's HOME core (affinity target),
    -- not the boot queue — `wakeThread` places via `determineTargetCore`
    -- and returns the `.reschedule` SGI when the home core is remote.
    let woken := wakeThread st2 tid executingCore
    -- D4-N: Revert PIP for the server if the timed-out thread was a waiter.
    -- Now that the client's ipcState is cleared, waitersOf won't include it,
    -- so revertPriorityInheritance correctly recomputes the server's pipBoost
    -- from remaining waiters only.
    match maybeBlockingServer with
    | some serverId =>
      .ok (PriorityInheritance.revertPriorityInheritance woken.1 serverId, woken.2)
    | none => .ok woken

/-- AK1-H (I-M06): Composition — `timeoutThread` succeeds whenever the
    caller has witnessed that (i) an endpoint exists at `endpointId`, and
    (ii) a TCB exists at `tid.toObjId` (non-reserved `tid`). These
    preconditions are established by `timeoutBlockedThreads`'s outer
    guards (`st.scThreadIndex[scId]?` lookup + `tcbBlockingInfo` +
    endpoint-member derivation from `tcb.ipcState`).

    This formally closes the gap between `endpointQueueRemove`'s
    unreachability lemmas (`queueRemove_predecessor_exists` /
    `queueRemove_successor_exists`) and the operational call site in the
    timer-tick path. With this composition in hand, the
    `| .error e => (st', errs ++ [(tid, e)])` branch at
    `Scheduler/Operations/Core.lean:513` is formally dead under valid
    invariant state.

    Note: `lookupTcb pair.2 tid` succeeds after `endpointQueueRemove`
    because the operation only modifies queue links and tail/head
    pointers; the TCB at `tid.toObjId` is still present (with cleared
    links). `storeObject` is unconditional `.ok`. Therefore the three
    explicit error branches inside `timeoutThread` are all unreachable
    under the preconditions. -/
theorem timeoutThread_succeeds_under_preconditions
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (st : SystemState) (ep : Endpoint) (tcb : TCB)
    (hEp : st.objects[endpointId]? = some (.endpoint ep))
    (hLk : lookupTcb st tid = some tcb)
    (hLk1 : ∀ st1, endpointQueueRemove endpointId isReceiveQ tid st = .ok st1 →
      ∃ tcb1, lookupTcb st1 tid = some tcb1) :
    ∃ r, timeoutThread endpointId isReceiveQ tid executingCore st = .ok r := by
  -- Destructure the first step via the AK1-H endpointQueueRemove composition.
  obtain ⟨st1, hRemove⟩ :=
    endpointQueueRemove_succeeds_under_forwardBackward endpointId isReceiveQ tid st ep tcb hEp hLk
  unfold timeoutThread abortPendingIpcOnEndpoint
  rw [hRemove]
  -- Discharge lookupTcb st1 via the `hLk1` hypothesis supplied by the caller.
  -- Under `crossSubsystemInvariant`, the caller can produce this witness
  -- because `endpointQueueRemove` preserves TCB existence at `tid.toObjId`
  -- (only clears queue links). See
  -- `endpointQueueRemove_tcb_forward` in `IPC/Invariant/*` for the formal
  -- discharge that makes `hLk1` trivially provable at call sites.
  obtain ⟨tcb1, hLk1'⟩ := hLk1 st1 hRemove
  simp only [hLk1']
  -- Remaining steps are unconditional: storeObject returns .ok, match is total.
  -- Destructure the storeObject step (unconditional .ok).
  cases hStore : storeObject tid.toObjId (.tcb _) st1 with
  | ok pair =>
    -- WS-OD OD1.2: the blocking-server capture reads the **pre**-state now, so
    -- the split is on `tcb`'s state rather than the post-removal `tcb1`'s.  The
    -- two agree — `endpointQueueRemove` writes queue links only — but the proof
    -- follows the definition rather than the fact.
    cases hBS : timeoutBlockingServerOf? st tid with
    | none => exact ⟨_, rfl⟩
    | some serverId => exact ⟨_, rfl⟩
  | error e =>
    -- storeObject is unconditional .ok (Model/State.lean).
    exfalso; unfold storeObject at hStore; cases hStore

/-- Z6-I: Timeout-aware receive wrapper.

Checks whether a thread was timed out by the scheduler during a prior
blocking receive. The actual timeout is applied asynchronously by
`timeoutBlockedThreads` in the timer tick path (`timerTickBudget`), which
sets `timedOut := true` and resets ipcState to `.ready`.

AG8-A: Detection uses explicit `tcb.timedOut ∧ tcb.ipcState = .ready` check,
replacing the fragile sentinel pattern (gpr x0 = 0xFFFFFFFF).

AI4-C (L-05): The previously unused `endpointId` parameter has been removed.
If future validation is needed, it can be re-added with actual usage. -/
def timeoutAwareReceive
    (receiver : SeLe4n.ThreadId)
    : Kernel IpcTimeoutResult :=
  fun st =>
    match lookupTcb st receiver with
    | none => .error .objectNotFound
    | some tcb =>
      -- AG8-A: Check explicit timedOut flag instead of register sentinel
      if tcb.timedOut ∧ tcb.ipcState = .ready then
        -- Thread was timed out by the scheduler — report timeout
        -- Clear the timedOut flag to avoid re-triggering
        let tcb' := { tcb with timedOut := false }
        match storeObject receiver.toObjId (.tcb tcb') st with
        | .error e => .error e
        | .ok ((), st') => .ok (.timedOut, st')
      else
        -- Normal receive path — timeout metadata is set by Z6-G in the blocking path
        match tcb.pendingMessage with
        | some msg => .ok (.completed msg, st)
        -- AH2-G: Return error for missing pending message (protocol violation).
        -- Under normal IPC invariants, a thread reaching this point should always
        -- have a pendingMessage set by the sender. The `none` case indicates a
        -- violated IPC protocol — surface it as an error rather than silently
        -- returning an empty message.
        | none => .error .endpointQueueEmpty

end SeLe4n.Kernel
