/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.DualQueue.Transport
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate

/-! # Z7: SchedContext Donation / Passive Servers

SchedContext donation enables passive servers — threads that consume zero CPU
when idle by borrowing the client's SchedContext during IPC Call/Reply.

## Donation Protocol

1. Client calls server via `endpointCall`. If the server is passive (unbound),
   the client's SchedContext is temporarily donated to the server.
2. Server receives `.donated(clientScId, clientTid)` binding. The SchedContext's
   `boundThread` is updated to point to the server.
3. Server runs on the client's CPU budget.
4. Server replies via `endpointReply` or `endpointReplyRecv`. The SchedContext
   is returned to the original client.
5. Server becomes passive again (unbound, not in RunQueue).

## Architecture

The donation logic is implemented as post-processing wrappers around the
existing IPC primitives (`endpointCall`, `endpointReply`, `endpointReplyRecv`).
This design preserves all existing IPC invariant proofs unchanged — the core
IPC functions are not modified. Donation is applied after the core operation
completes, modifying only `schedContextBinding` fields and RunQueue membership.

## Cross-cutting: Timeout + Donation

When a client's SchedContext is donated to a server and the budget expires:
- The server is preempted (budget exhaustion via `timerTickBudget`)
- The client is timed out (budget-bounded IPC via `timeoutBlockedThreads`)
- The SchedContext returns to the client via timeout cleanup, not reply
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- Z7-B: Post-call donation (endpointCall → donation to passive server)
-- ============================================================================

/-- Z7-B: Apply SchedContext donation after a successful `endpointCall`.

After the caller blocks on reply and the receiver is woken, check if:
1. The receiver is passive (schedContextBinding = .unbound)
2. The caller has a bound SchedContext

If both conditions hold, donate the caller's SchedContext to the receiver.
Otherwise, return the state unchanged.

This function modifies only `objects` (SchedContext and TCB schedContextBinding
fields). It does NOT modify the scheduler RunQueue or current thread. -/
def applyCallDonation
    (st : SystemState)
    (caller : SeLe4n.ThreadId) (receiver : SeLe4n.ThreadId) : SystemState :=
  -- Check if receiver is passive
  match lookupTcb st receiver with
  | none => st
  | some receiverTcb =>
    match receiverTcb.schedContextBinding with
    | .unbound =>
      -- Receiver is passive — check if caller has a SchedContext to donate
      match lookupTcb st caller with
      | none => st
      | some callerTcb =>
        match callerTcb.schedContextBinding with
        | .bound clientScId =>
          match donateSchedContext st caller receiver clientScId with
          | .error _ => st
          | .ok st' => st'
        | _ => st
    | _ => st  -- Receiver already has SC, no donation needed

/-- Z7-B: storeObject preserves scheduler. -/
private theorem storeObject_scheduler_eq_local (st : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (pair : Unit × SystemState)
    (h : storeObject oid obj st = .ok pair) :
    pair.2.scheduler = st.scheduler := by
  unfold storeObject at h; cases h; rfl

/-- Z7-B: donateSchedContext only modifies objects — scheduler is preserved. -/
theorem donateSchedContext_scheduler_eq
    (st st' : SystemState)
    (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold donateSchedContext at h
  revert h
  cases hObj : st.objects[clientScId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      -- AUD-3b: Handle the boundThread validation branch
      split
      · intro h; cases h  -- boundThread != clientTid → error → contradiction
      · cases hS1 : storeObject clientScId.toObjId _ st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hLookup : lookupTcb p1.2 serverTid with
          | none => intro h; cases h
          | some _ =>
            simp only []
            cases hS2 : storeObject serverTid.toObjId _ p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only [Except.ok.injEq]
              intro hEq; subst hEq
              have h1 := storeObject_scheduler_eq_local st _ _ _ hS1
              have h2 := storeObject_scheduler_eq_local p1.2 _ _ _ hS2
              exact h2.trans h1
    | _ => simp only []; intro h; cases h

/-- Z7-B: applyCallDonation preserves the scheduler exactly. -/
theorem applyCallDonation_scheduler_eq
    (st : SystemState) (caller receiver : SeLe4n.ThreadId) :
    (applyCallDonation st caller receiver).scheduler = st.scheduler := by
  unfold applyCallDonation
  cases hRecv : lookupTcb st receiver with
  | none => rfl
  | some receiverTcb =>
    simp only []
    cases hBinding : receiverTcb.schedContextBinding with
    | unbound =>
      simp only []
      cases hCaller : lookupTcb st caller with
      | none => rfl
      | some callerTcb =>
        simp only []
        cases hCallerBinding : callerTcb.schedContextBinding with
        | unbound => rfl
        | bound clientScId =>
          simp only []
          cases hDonate : donateSchedContext st caller receiver clientScId with
          | error _ => rfl
          | ok st' => exact donateSchedContext_scheduler_eq st st' caller receiver clientScId hDonate
        | donated scId owner => rfl
    | bound scId => rfl
    | donated scId owner => rfl

-- ============================================================================
-- Z7-C: Post-reply donation return (endpointReply → return SC to client)
-- ============================================================================

/-- Z7-C: Apply SchedContext return after a successful `endpointReply`.

If the replier has a donated SchedContext binding (.donated scId originalOwner),
return the SchedContext to the original owner and remove the (now passive)
replier from the RunQueue. Otherwise, return the state unchanged. -/
def applyReplyDonation (st : SystemState) (replier : SeLe4n.ThreadId) : SystemState :=
  match lookupTcb st replier with
  | none => st
  | some replierTcb =>
    match replierTcb.schedContextBinding with
    | .donated scId originalOwner =>
      match returnDonatedSchedContext st replier scId originalOwner with
      | .error _ => st
      | .ok st' => removeRunnable st' replier
    | _ => st

-- ============================================================================
-- Z7-E: Pre-receive donation cleanup
-- ============================================================================

/-- Z7-E: Clean up stale donation before a server blocks on receive.

If the receiver has a `.donated` binding from a previous call that was never
replied to (abnormal path), return the SchedContext to the original owner
before blocking. Otherwise, return the state unchanged. -/
def cleanupPreReceiveDonation (st : SystemState) (receiver : SeLe4n.ThreadId) : SystemState :=
  match lookupTcb st receiver with
  | none => st
  | some recvTcb =>
    match recvTcb.schedContextBinding with
    | .donated scId originalOwner =>
      match returnDonatedSchedContext st receiver scId originalOwner with
      | .error _ => st
      | .ok st' => st'
    | _ => st

-- ============================================================================
-- Z7: Donation-aware IPC operation wrappers
-- ============================================================================

/-- Z7: Donation-aware endpointCall. Composes the standard `endpointCall` with
post-call SchedContext donation to passive servers.

Before calling `endpointCall`, checks if the endpoint has a waiting receiver
(handshake path). If so, records the receiver's ThreadId. After `endpointCall`
completes, applies donation from the caller to the receiver if the receiver
was passive (unbound). -/
def endpointCallWithDonation
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    -- Pre-check: determine receiver before endpointCall pops it
    let maybeReceiver := match st.objects[endpointId]? with
      | some (.endpoint ep) => ep.receiveQ.head
      | _ => none
    match endpointCall endpointId caller msg st with
    | .error e => .error e
    | .ok ((), st') =>
      match maybeReceiver with
      | some receiverTid =>
        -- Handshake path: a receiver was woken — apply donation
        let st'' := applyCallDonation st' caller receiverTid
        -- D4-L: Apply PIP — propagate priority inheritance from the server
        -- upward through the blocking chain. The server may itself be blocked
        -- on another server, requiring transitive propagation.
        .ok ((), PriorityInheritance.propagatePriorityInheritance st'' receiverTid)
      | none =>
        -- Blocking path: no receiver was available, caller blocked
        .ok ((), st')

/-- Z7: Donation-aware endpointReply. Composes the standard `endpointReply`
with post-reply SchedContext return from the server. -/
def endpointReplyWithDonation
    (replier : SeLe4n.ThreadId) (target : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    match endpointReply replier target msg st with
    | .error e => .error e
    | .ok ((), st') =>
      -- Apply donation return: if replier has donated SC, return it
      let st'' := applyReplyDonation st' replier
      -- D4-M: Revert PIP — the client (target) is unblocked, so the replier's
      -- pipBoost must be recomputed from remaining waiters. Propagate reversion
      -- upward through the chain.
      .ok ((), PriorityInheritance.revertPriorityInheritance st'' replier)

/-- Z7: Donation-aware endpointReplyRecv. Composes:
1. Standard endpointReplyRecv (reply + receive) — server still holds donated SC during reply
2. Return old donation from replier AFTER the reply completes
3. (New donation from incoming caller is handled by the Call path)

**Ordering rationale (AUD-3)**: The donation return happens AFTER `endpointReplyRecv`
completes, not before. The server needs the donated SchedContext while replying
(it's the currently running thread with that SC's budget). After the reply delivers
the message and the server enters the receive path, the SC is returned. -/
def endpointReplyRecvWithDonation
    (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId)
    (replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) : Kernel Unit :=
  fun st =>
    match endpointReplyRecv endpointId receiver replyTarget msg st with
    | .error e => .error e
    | .ok ((), st') =>
      -- Z7-D1: Return old donation AFTER reply+receive completes
      let st'' := applyReplyDonation st' receiver
      -- D4-M: Revert PIP for the reply portion
      .ok ((), PriorityInheritance.revertPriorityInheritance st'' receiver)

-- ============================================================================
-- Z7-J/K: Donation operation structural theorems
-- ============================================================================

/-- Z7-J1: After donateSchedContext, the server's binding is correctly set to .donated.
This establishes the server-side of the bidirectional donation reference. -/
theorem donateSchedContext_server_binding
    (st st' : SystemState)
    (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (hObjInv : st.objects.invExt)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    ∃ tcb', st'.objects[serverTid.toObjId]? = some (.tcb tcb') ∧
      tcb'.schedContextBinding = .donated clientScId clientTid := by
  unfold donateSchedContext at h
  revert h
  cases hObj : st.objects[clientScId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      split
      · intro h; cases h
      · cases hS1 : storeObject clientScId.toObjId _ st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hL : lookupTcb p1.2 serverTid with
          | none => intro h; cases h
          | some serverTcb =>
            simp only []
            cases hS2 : storeObject serverTid.toObjId _ p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only [Except.ok.injEq]
              intro hEq; subst hEq
              have hInvP1 : p1.2.objects.invExt := by
                unfold storeObject at hS1; cases hS1
                exact RHTable_insert_preserves_invExt _ _ _ hObjInv
              have : p2.2.objects[serverTid.toObjId]? =
                  some (.tcb { serverTcb with schedContextBinding := .donated clientScId clientTid }) := by
                unfold storeObject at hS2; cases hS2
                exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInvP1
              exact ⟨_, this, rfl⟩
    | _ => simp only []; intro h; cases h

/-- Z7-K2: After returnDonatedSchedContext, the server's binding is .unbound. -/
theorem returnDonatedSchedContext_server_unbound
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    ∃ tcb', st'.objects[serverTid.toObjId]? = some (.tcb tcb') ∧
      tcb'.schedContextBinding = .unbound := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some _ =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some serverTcb =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq; subst hEq
                have hInvP1 : p1.2.objects.invExt := by
                  unfold storeObject at hS1; cases hS1
                  exact RHTable_insert_preserves_invExt _ _ _ hObjInv
                have hInvP2 : p2.2.objects.invExt := by
                  unfold storeObject at hS2; cases hS2
                  exact RHTable_insert_preserves_invExt _ _ _ hInvP1
                have : p3.2.objects[serverTid.toObjId]? =
                    some (.tcb { serverTcb with schedContextBinding := .unbound }) := by
                  unfold storeObject at hS3; cases hS3
                  exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInvP2
                exact ⟨_, this, rfl⟩
    | _ => simp only []; intro h; cases h

-- ============================================================================
-- Z7-L/M: Frame theorems for core IPC operations
--
-- The core IPC functions (endpointCall, endpointReply, endpointReplyRecv)
-- do NOT modify TCB.schedContextBinding fields. They only modify:
-- - ipcState, pendingMessage, queuePrev/Next/PPrev (IPC state)
-- - scheduler.runQueue, scheduler.current (scheduler state)
-- - objects (endpoint queue metadata)
--
-- Therefore, all four donation invariants (donationChainAcyclic,
-- donationOwnerValid, passiveServerIdle, donationBudgetTransfer) are
-- preserved through core IPC operations by field-disjointness (frame property).
--
-- The donation invariants only need explicit preservation proofs for
-- applyCallDonation and applyReplyDonation, which DO modify
-- schedContextBinding. These proofs are provided as external hypotheses
-- in the Structural.lean composition layer, following the established
-- pattern for all externalized IPC invariants.
--
-- Cross-store preservation theorems (Z7-J2, Z7-K1) that require invExt
-- for proving object lookup across different storeObject calls are deferred
-- to the Z8 API Surface phase, which will connect the full proof chain.
-- ============================================================================

-- ============================================================================
-- AG8-G: Donation Atomicity Under Interrupt Disable (H3-IPC-04)
-- ============================================================================

/-!
## AG8-G: Donation Atomicity Proof Obligation

Donation operations (`donateSchedContext`, `returnDonatedSchedContext`) modify
multiple TCBs and the blocking graph in a multi-step sequence. On hardware,
interrupts must be disabled throughout this sequence to prevent inconsistent
intermediate states where:

1. The server has a donated SchedContext but the owner's binding hasn't been
   updated yet (broken bidirectional consistency → `donationOwnerValid` violation)
2. Priority inheritance propagation is partially applied (blocking graph
   inconsistent with PIP boost values)

## Proof Structure

The atomicity argument has three components:

1. **Kernel runs with interrupts disabled**: ARM64 exception entry (SVC, IRQ)
   automatically masks interrupts (PSTATE.I = 1). The kernel never re-enables
   interrupts during a syscall path. This is proven by the AG5-G preservation
   theorems in `ExceptionModel.lean`.

2. **Donation occurs within a single syscall**: `endpointCallWithDonation` and
   `endpointReplyWithDonation` are called from the API dispatch layer, which
   executes entirely within a single exception entry/exit cycle.

3. **No interrupt can fire between donation steps**: Since interrupts remain
   disabled from exception entry through exception return (ERET), the multi-step
   donation sequence executes atomically with respect to the interrupt controller.

The `donationAtomicRegion` predicate formalizes this: the system state transition
from pre-donation to post-donation occurs with `interruptsEnabled = false`.
-/

/-- AG8-G: Predicate asserting that a state transition occurs within an
interrupt-disabled region. In the sequential single-core model, this is
captured by `st.machine.interruptsEnabled = false` throughout the transition.

On hardware, this is enforced by:
- ARM64 exception entry masking PSTATE.I
- Kernel never calling `enableInterrupts` during syscall processing
- AG5-G preservation theorems proving all kernel operations preserve the
  disabled state -/
def donationAtomicRegion (st st' : SystemState) : Prop :=
  st.machine.interruptsEnabled = false ∧
  st'.machine.interruptsEnabled = false

/-- AG8-G: storeObject preserves machine (local helper matching Z7-B pattern). -/
private theorem storeObject_machine_eq_local (st : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (pair : Unit × SystemState)
    (h : storeObject oid obj st = .ok pair) :
    pair.2.machine = st.machine := by
  unfold storeObject at h; cases h; rfl

/-- AG8-G: `donateSchedContext` preserves machine state.
Mirrors the proof structure of `donateSchedContext_scheduler_eq` (Z7-B). -/
theorem donateSchedContext_machine_eq
    (st st' : SystemState)
    (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    st'.machine = st.machine := by
  unfold donateSchedContext at h
  revert h
  cases hObj : st.objects[clientScId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      split
      · intro h; cases h
      · cases hS1 : storeObject clientScId.toObjId _ st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hLookup : lookupTcb p1.2 serverTid with
          | none => intro h; cases h
          | some _ =>
            simp only []
            cases hS2 : storeObject serverTid.toObjId _ p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only [Except.ok.injEq]
              intro hEq; subst hEq
              have h1 := storeObject_machine_eq_local st _ _ _ hS1
              have h2 := storeObject_machine_eq_local p1.2 _ _ _ hS2
              exact h2.trans h1
    | _ => simp only []; intro h; cases h

/-- AG8-G: Donation is atomic — `donateSchedContext` preserves the
interrupt-disabled state. Derives the post-condition from
`donateSchedContext_machine_eq`: since the entire `machine` field is
preserved, `interruptsEnabled` remains `false` through the operation. -/
theorem donateSchedContext_atomicRegion
    (st st' : SystemState)
    (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (hPre : st.machine.interruptsEnabled = false)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    donationAtomicRegion st st' := by
  constructor
  · exact hPre
  · have hMach := donateSchedContext_machine_eq st st' clientTid serverTid clientScId h
    rw [hMach]; exact hPre

-- ============================================================================
-- AG8-G.2: returnDonatedSchedContext machine state preservation
-- ============================================================================

/-- AG8-G.2: `returnDonatedSchedContext` preserves machine state.
Symmetric coverage with `donateSchedContext_machine_eq`. The function
performs 3 sequential `storeObject` calls and an `scThreadIndex` update,
none of which modify the machine state. -/
theorem returnDonatedSchedContext_machine_eq
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    st'.machine = st.machine := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      cases hS1 : storeObject scId.toObjId _ st with
      | error _ => intro h; cases h
      | ok p1 =>
        simp only []
        cases hL1 : lookupTcb p1.2 originalOwner with
        | none => intro h; cases h
        | some _ =>
          simp only []
          cases hS2 : storeObject originalOwner.toObjId _ p1.2 with
          | error _ => intro h; cases h
          | ok p2 =>
            simp only []
            cases hL2 : lookupTcb p2.2 serverTid with
            | none => intro h; cases h
            | some _ =>
              simp only []
              cases hS3 : storeObject serverTid.toObjId _ p2.2 with
              | error _ => intro h; cases h
              | ok p3 =>
                simp only [Except.ok.injEq]
                intro hEq; subst hEq
                have h1 := storeObject_machine_eq_local st _ _ _ hS1
                have h2 := storeObject_machine_eq_local p1.2 _ _ _ hS2
                have h3 := storeObject_machine_eq_local p2.2 _ _ _ hS3
                exact h3.trans (h2.trans h1)
    | _ => simp only []; intro h; cases h

/-- AG8-G: Return donation is atomic — `returnDonatedSchedContext` preserves
the interrupt-disabled state. Derives the post-condition from
`returnDonatedSchedContext_machine_eq`. -/
theorem returnDonatedSchedContext_atomicRegion
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hPre : st.machine.interruptsEnabled = false)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    donationAtomicRegion st st' := by
  constructor
  · exact hPre
  · have hMach := returnDonatedSchedContext_machine_eq st st' serverTid scId originalOwner h
    rw [hMach]; exact hPre

-- ============================================================================
-- AG8-G: Wrapper function machine state preservation
-- ============================================================================

/-- AG8-G: applyCallDonation preserves machine state.
Composition of `donateSchedContext_machine_eq`: all fallback paths return `st`
unchanged, and the success path delegates to `donateSchedContext` which
preserves machine state. -/
theorem applyCallDonation_machine_eq
    (st : SystemState) (caller receiver : SeLe4n.ThreadId) :
    (applyCallDonation st caller receiver).machine = st.machine := by
  unfold applyCallDonation
  cases lookupTcb st receiver with
  | none => rfl
  | some receiverTcb =>
    simp only []
    cases receiverTcb.schedContextBinding with
    | unbound =>
      simp only []
      cases lookupTcb st caller with
      | none => rfl
      | some callerTcb =>
        simp only []
        cases callerTcb.schedContextBinding with
        | unbound => rfl
        | bound clientScId =>
          simp only []
          cases hDonate : donateSchedContext st caller receiver clientScId with
          | error _ => rfl
          | ok st' => exact donateSchedContext_machine_eq st st' caller receiver clientScId hDonate
        | donated scId owner => rfl
    | bound scId => rfl
    | donated scId owner => rfl

/-- AG8-G: removeRunnable preserves machine state — it only modifies scheduler. -/
private theorem removeRunnable_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).machine = st.machine := by
  unfold removeRunnable; rfl

/-- AG8-G: applyReplyDonation preserves machine state.
Composition of `returnDonatedSchedContext_machine_eq` and `removeRunnable_machine_eq`:
all fallback paths return `st` unchanged, and the success path delegates to
`returnDonatedSchedContext` (preserves machine) followed by `removeRunnable`
(only modifies scheduler). -/
theorem applyReplyDonation_machine_eq
    (st : SystemState) (replier : SeLe4n.ThreadId) :
    (applyReplyDonation st replier).machine = st.machine := by
  unfold applyReplyDonation
  cases lookupTcb st replier with
  | none => rfl
  | some replierTcb =>
    simp only []
    cases replierTcb.schedContextBinding with
    | unbound => rfl
    | bound scId => rfl
    | donated scId originalOwner =>
      simp only []
      cases hReturn : returnDonatedSchedContext st replier scId originalOwner with
      | error _ => rfl
      | ok st' =>
        simp only []
        have hMach := returnDonatedSchedContext_machine_eq st st' replier scId originalOwner hReturn
        have hRem := removeRunnable_machine_eq st' replier
        exact hRem.trans hMach

/-- AG8-G: cleanupPreReceiveDonation preserves machine state.
All fallback paths return `st` unchanged, and the success path delegates to
`returnDonatedSchedContext` which preserves machine state. -/
theorem cleanupPreReceiveDonation_machine_eq
    (st : SystemState) (receiver : SeLe4n.ThreadId) :
    (cleanupPreReceiveDonation st receiver).machine = st.machine := by
  unfold cleanupPreReceiveDonation
  cases lookupTcb st receiver with
  | none => rfl
  | some recvTcb =>
    simp only []
    cases recvTcb.schedContextBinding with
    | unbound => rfl
    | bound scId => rfl
    | donated scId originalOwner =>
      simp only []
      cases hReturn : returnDonatedSchedContext st receiver scId originalOwner with
      | error _ => rfl
      | ok st' => exact returnDonatedSchedContext_machine_eq st st' receiver scId originalOwner hReturn

end SeLe4n.Kernel
