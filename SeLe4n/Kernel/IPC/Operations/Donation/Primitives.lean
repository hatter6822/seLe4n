-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Operations.Endpoint

/-! # Z7: Donation Primitives (AN3-A / H-01)

Donation primitives extracted from `SeLe4n.Kernel.IPC.Operations.Donation`
so the top-level IPC operations hub can re-export them without reintroducing
the `Donation.lean -> Transport.lean -> Core.lean -> Operations` cycle.

This module contains **only** the donation helpers that depend solely on
`SeLe4n.Kernel.IPC.Operations.Endpoint` (`lookupTcb`, `storeObject`,
`removeRunnable`, `donateSchedContext`, `returnDonatedSchedContext`,
`cleanupPreReceiveDonation`). The transport-dependent wrappers
(`endpointCallWithDonation`, `endpointReplyWithDonation`,
`endpointReplyRecvWithDonation` and their unfold lemmas) remain in the
sibling module `SeLe4n.Kernel.IPC.Operations.Donation`, which also imports
this file so that legacy single-import consumers continue to see the full
donation API unchanged.

See WS-AN AN3-A (historical record in CHANGELOG.md) for
rationale.
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
fields). It does NOT modify the scheduler RunQueue or current thread.

**AN10-residual-1 deep-audit pass (signature tightening)**: both `caller`
and `receiver` are now `ValidThreadId`.  The Lean type system enforces
the dispatch-boundary discipline at this function's signature —
construction of a `ValidThreadId` requires a non-sentinel proof, so
calling `applyCallDonation st sentinel sentinel` is a compile-time
error.  Production callers (`dispatchWithCap` in `API.lean`,
`endpointCallWithDonation` in `Donation.lean`) construct
`ValidThreadId` from their raw `ThreadId` arguments via
`ThreadId.toValid?` with `.error .invalidArgument` rejection; under
the AL7 dispatch-gate (`validateThreadIdArg`) the rejection is
structurally unreachable but provides defense-in-depth. -/
def applyCallDonation
    (st : SystemState)
    (callerVtid : SeLe4n.ValidThreadId) (receiverVtid : SeLe4n.ValidThreadId)
    : Except KernelError SystemState :=
  let caller : SeLe4n.ThreadId := callerVtid.val
  let receiver : SeLe4n.ThreadId := receiverVtid.val
  -- Check if receiver is passive
  match lookupTcb st receiver with
  | none => .ok st                          -- No-op: receiver not found
  | some receiverTcb =>
    match receiverTcb.schedContextBinding with
    | .unbound =>
      -- Receiver is passive — check if caller has a SchedContext to donate
      match lookupTcb st caller with
      | none => .ok st                      -- No-op: caller not found
      | some callerTcb =>
        match callerTcb.schedContextBinding with
        | .bound clientScId =>
          -- AH2-A: Propagate donation errors instead of swallowing them.
          -- AN10-residual-1 deep-audit (H5): direct call to the typed
          -- wrapper.  Type-level enforcement of the dispatch-boundary
          -- discipline at this function's signature.
          match donateSchedContextValid st callerVtid receiverVtid clientScId with
          | .error e => .error e
          | .ok st' => .ok st'
        | _ => .ok st                       -- No-op: caller has no SC to donate
    | _ => .ok st  -- Receiver already has SC, no donation needed

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
          -- F-3: donor-clear store between the SC store and the server store
          cases hLC : lookupTcb p1.2 clientTid with
          | none => intro h; cases h
          | some _ =>
            simp only []
            cases hS2 : storeObject clientTid.toObjId _ p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only []
              cases hLookup : lookupTcb p2.2 serverTid with
              | none => intro h; cases h
              | some _ =>
                simp only []
                cases hS3 : storeObject serverTid.toObjId _ p2.2 with
                | error _ => intro h; cases h
                | ok p3 =>
                  simp only [Except.ok.injEq]
                  intro hEq; subst hEq
                  have h1 := storeObject_scheduler_eq_local st _ _ _ hS1
                  have h2 := storeObject_scheduler_eq_local p1.2 _ _ _ hS2
                  have h3 := storeObject_scheduler_eq_local p2.2 _ _ _ hS3
                  exact h3.trans (h2.trans h1)
    | _ => simp only []; intro h; cases h

/-- Z7-B/AH2-D: applyCallDonation preserves the scheduler exactly. -/
theorem applyCallDonation_scheduler_eq
    (st : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (st' : SystemState)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    st'.scheduler = st.scheduler := by
  unfold applyCallDonation at h
  cases hRecv : lookupTcb st receiverVtid.val with
  | none => simp [hRecv] at h; cases h; rfl
  | some receiverTcb =>
    simp only [hRecv] at h
    cases hBinding : receiverTcb.schedContextBinding with
    | unbound =>
      simp only [hBinding] at h
      cases hCaller : lookupTcb st callerVtid.val with
      | none => simp [hCaller] at h; cases h; rfl
      | some callerTcb =>
        simp only [hCaller] at h
        cases hCallerBinding : callerTcb.schedContextBinding with
        | unbound => simp [hCallerBinding] at h; cases h; rfl
        | bound clientScId =>
          -- AN10-residual-1 deep-audit: body now calls `donateSchedContextValid`
          -- directly with the typed arguments; reduce via `_eq` lemma.
          simp only [hCallerBinding, donateSchedContextValid] at h
          cases hDonate : donateSchedContext st callerVtid.val receiverVtid.val clientScId with
          | error _ => simp [hDonate] at h
          | ok stDon =>
              simp [hDonate] at h; rw [← h]
              exact donateSchedContext_scheduler_eq st stDon callerVtid.val receiverVtid.val clientScId hDonate
        | donated scId owner => simp [hCallerBinding] at h; cases h; rfl
    | bound scId => simp [hBinding] at h; cases h; rfl
    | donated scId owner => simp [hBinding] at h; cases h; rfl

-- ============================================================================
-- Z7-C: Post-reply donation return (endpointReply → return SC to client)
-- ============================================================================

/-- Z7-C: Apply SchedContext return after a successful `endpointReply`.

If the replier has a donated SchedContext binding (.donated scId originalOwner),
return the SchedContext to the original owner and remove the (now passive)
replier from the RunQueue. Otherwise, return the state unchanged.

**AN10-residual-1 deep-audit pass (signature tightening)**: `replier` is
now `ValidThreadId` — type-level enforcement at the function entry.
The `originalOwner` is a stored field of the `.donated` constructor
(set by `donateSchedContext` from a previously-validated client tid);
it is promoted via `ThreadId.toValid?` with `.error .invalidArgument`
rejection.  Under `donationOwnerValid` (an `ipcInvariantFull`
conjunct), `originalOwner` is structurally non-sentinel, so the
rejection arm is unreachable in production but provides
defense-in-depth for any path that hasn't yet established that
invariant. -/
def applyReplyDonation (st : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    : Except KernelError SystemState :=
  let replier : SeLe4n.ThreadId := replierVtid.val
  match lookupTcb st replier with
  | none => .ok st                          -- No-op: replier not found
  | some replierTcb =>
    match replierTcb.schedContextBinding with
    | .donated scId originalOwner =>
      -- AH2-B: Propagate return errors instead of swallowing them.
      -- AN10-residual-1 deep-audit (H6): direct call to the typed wrapper
      -- after promoting the stored `originalOwner` field via `toValid?`.
      match SeLe4n.ThreadId.toValid? originalOwner with
      | some ownerVtid =>
          match returnDonatedSchedContextValid st replierVtid scId ownerVtid with
          | .error e => .error e
          | .ok st' => .ok (removeRunnable st' replier)
      | none => .error .invalidArgument
    | _ => .ok st                           -- No-op: no donation to return

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
          -- F-3: donor-clear store between the SC store and the server store
          cases hLC : lookupTcb p1.2 clientTid with
          | none => intro h; cases h
          | some _ =>
            simp only []
            cases hS2 : storeObject clientTid.toObjId _ p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only []
              cases hL : lookupTcb p2.2 serverTid with
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
                    some (.tcb { serverTcb with schedContextBinding := .donated clientScId clientTid }) := by
                    unfold storeObject at hS3; cases hS3
                    exact RobinHood.RHTable.getElem?_insert_self _ _ _ hInvP2
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
      -- WS-RR RR2.8: the new `sc.boundThread = some serverTid` guard.
      split
      · intro h; cases h
      · cases hS1 : storeObject scId.toObjId _ st with
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
          -- F-3: donor-clear store between the SC store and the server store
          cases hLC : lookupTcb p1.2 clientTid with
          | none => intro h; cases h
          | some _ =>
            simp only []
            cases hS2 : storeObject clientTid.toObjId _ p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only []
              cases hLookup : lookupTcb p2.2 serverTid with
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
      -- WS-RR RR2.8: the new `sc.boundThread = some serverTid` guard.
      split
      · intro h; cases h
      · cases hS1 : storeObject scId.toObjId _ st with
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

/-- AG8-G/AH2-D: applyCallDonation preserves machine state.
Composition of `donateSchedContext_machine_eq`: all no-op paths return `.ok st`
unchanged, and the success path delegates to `donateSchedContext` which
preserves machine state. -/
theorem applyCallDonation_machine_eq
    (st : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (st' : SystemState)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    st'.machine = st.machine := by
  unfold applyCallDonation at h
  cases hRecv : lookupTcb st receiverVtid.val with
  | none => simp [hRecv] at h; cases h; rfl
  | some receiverTcb =>
    simp only [hRecv] at h
    cases hBinding : receiverTcb.schedContextBinding with
    | unbound =>
      simp only [hBinding] at h
      cases hCaller : lookupTcb st callerVtid.val with
      | none => simp [hCaller] at h; cases h; rfl
      | some callerTcb =>
        simp only [hCaller] at h
        cases hCallerBinding : callerTcb.schedContextBinding with
        | unbound => simp [hCallerBinding] at h; cases h; rfl
        | bound clientScId =>
          -- AN10-residual-1 deep-audit: body now calls `donateSchedContextValid`
          -- directly with typed args; reduce via `_eq` lemma.
          simp only [hCallerBinding, donateSchedContextValid] at h
          cases hDonate : donateSchedContext st callerVtid.val receiverVtid.val clientScId with
          | error _ => simp [hDonate] at h
          | ok stDon =>
              simp [hDonate] at h; rw [← h]
              exact donateSchedContext_machine_eq st stDon callerVtid.val receiverVtid.val clientScId hDonate
        | donated scId owner => simp [hCallerBinding] at h; cases h; rfl
    | bound scId => simp [hBinding] at h; cases h; rfl
    | donated scId owner => simp [hBinding] at h; cases h; rfl

/-- AG8-G: removeRunnable preserves machine state — it only modifies scheduler. -/
private theorem removeRunnable_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeRunnable st tid).machine = st.machine := by
  unfold removeRunnable; rfl

/-- AG8-G/AH2-D: applyReplyDonation preserves machine state.
Composition of `returnDonatedSchedContext_machine_eq` and `removeRunnable_machine_eq`:
all no-op paths return `.ok st` unchanged, and the success path delegates to
`returnDonatedSchedContext` (preserves machine) followed by `removeRunnable`
(only modifies scheduler). -/
theorem applyReplyDonation_machine_eq
    (st : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (st' : SystemState)
    (h : applyReplyDonation st replierVtid = .ok st') :
    st'.machine = st.machine := by
  unfold applyReplyDonation at h
  cases hLookup : lookupTcb st replierVtid.val with
  | none => simp [hLookup] at h; cases h; rfl
  | some replierTcb =>
    simp only [hLookup] at h
    cases hBinding : replierTcb.schedContextBinding with
    | unbound => simp [hBinding] at h; cases h; rfl
    | bound scId => simp [hBinding] at h; cases h; rfl
    | donated scId originalOwner =>
      simp only [hBinding] at h
      -- AN10-residual-1 deep-audit: body now case-splits ONLY on
      -- `originalOwner.toValid?` (the `replier` is already a
      -- `ValidThreadId` argument).  The `none` arm yields `.error`
      -- which contradicts `.ok st'`; the `some` arm reduces via the
      -- wrapper `_eq` lemma + `toValid?_some_val_eq`.
      cases hOV : SeLe4n.ThreadId.toValid? originalOwner with
      | none => simp only [hOV] at h; cases h
      | some ownerVtid =>
          have hOEq : ownerVtid.val = originalOwner :=
            SeLe4n.ThreadId.toValid?_some_val_eq originalOwner ownerVtid hOV
          simp only [hOV, returnDonatedSchedContextValid, hOEq] at h
          cases hReturn : returnDonatedSchedContext st replierVtid.val scId originalOwner with
          | error _ => simp [hReturn] at h
          | ok st'' =>
            simp [hReturn] at h; cases h
            have hMach := returnDonatedSchedContext_machine_eq st st'' replierVtid.val scId originalOwner hReturn
            have hRem := removeRunnable_machine_eq st'' replierVtid.val
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

-- ============================================================================
-- WS-RR RR2.3: donation object-store frames — what the SchedContext rebinding
-- does NOT change
-- ============================================================================
--
-- The cross-core donation arms migrate the donated SchedContext's pending CBS
-- replenishments between the donor's and the donee's home cores (RR2.2 / RR2.8),
-- and the SM5.H affinity invariant they restore is stated over
-- `determineTargetCore` (a `cpuAffinity` read) and `getSchedContext?`.  Proving
-- the migration lands the entries where the invariant wants them therefore needs
-- to know exactly which of those two readings the rebinding itself moves: it
-- moves the SchedContext's `boundThread`, and **nothing else** — no thread's
-- `cpuAffinity`, and no other SchedContext.
--
-- Stated here, with the sibling `donateSchedContext_*` frames, rather than at
-- the consumer: the facts are about this operation's object writes.

/-- WS-RR RR2.19 (typed store frame): a `storeObject` at a key other than a
thread's leaves that thread's typed reading alone.

The typed counterpart of `storeObject_objects_ne`, stated once so a multi-store
walk reads its threads through `getTcb?` instead of indexing the object store at
each step. -/
theorem storeObject_getTcb?_ne (st st' : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (tid : SeLe4n.ThreadId) (hNe : tid.toObjId ≠ oid)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject oid obj st = .ok ((), st')) :
    st'.getTcb? tid = st.getTcb? tid := by
  unfold SystemState.getTcb?
  rw [storeObject_objects_ne st st' oid tid.toObjId obj hNe hObjInv hStore]

/-- WS-RR RR2.19 (typed store frame): a `storeObject` of a TCB at a thread's own
key is exactly what that thread then reads. -/
theorem storeObject_getTcb?_self (st st' : SystemState) (tid : SeLe4n.ThreadId) (t : TCB)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject tid.toObjId (.tcb t) st = .ok ((), st')) :
    st'.getTcb? tid = some t := by
  unfold SystemState.getTcb?
  rw [storeObject_objects_eq st st' tid.toObjId _ hObjInv hStore]

/-- WS-RR RR2.19: a thread key and a SchedContext key that both resolve are
distinct — the two typed readers cannot both succeed at one key. -/
theorem getTcb?_getSchedContext?_key_ne (st : SystemState) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (t : TCB) (sc : SchedContext)
    (hT : st.getTcb? tid = some t) (hS : st.getSchedContext? scId = some sc) :
    tid.toObjId ≠ scId.toObjId := by
  intro hEq
  rw [SystemState.getTcb?_eq_some_iff, hEq,
    (SystemState.getSchedContext?_eq_some_iff st scId sc).mp hS] at hT
  cases hT

/-- WS-RR RR2.3 (typed bridge): `lookupTcb`'s success is `getTcb?`'s.  The two
differ only in `lookupTcb`'s extra sentinel guard, which a success has already
passed, so the AK7 typed accessor is available wherever the operations' own
`lookupTcb` step succeeded — and the frames below can be stated over the typed
reader instead of a raw object-store index. -/
theorem getTcb?_of_lookupTcb (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (h : lookupTcb st tid = some tcb) : st.getTcb? tid = some tcb :=
  (SystemState.getTcb?_eq_some_iff st tid tcb).mpr (lookupTcb_some_objects st tid tcb h)

/-- WS-RR RR2.3 (frame helper): a `storeObject` that replaces one SchedContext
with another leaves every thread's TCB resolution unchanged — neither the
written value nor the previous occupant is a TCB. -/
private theorem storeObject_schedContextAt_getTcb?_eq
    (st st' : SystemState) (stored : SeLe4n.SchedContextId) (scOld scNew : SchedContext)
    (hOld : st.getSchedContext? stored = some scOld)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject stored.toObjId (.schedContext scNew) st = .ok ((), st'))
    (tid : SeLe4n.ThreadId) :
    st'.getTcb? tid = st.getTcb? tid := by
  have hRaw := (SystemState.getSchedContext?_eq_some_iff st stored scOld).mp hOld
  unfold SystemState.getTcb?
  by_cases h : tid.toObjId = stored.toObjId
  · rw [h, storeObject_objects_eq st st' stored.toObjId _ hObjInv hStore, hRaw]
  · rw [storeObject_objects_ne st st' stored.toObjId tid.toObjId _ h hObjInv hStore]

/-- WS-RR RR2.3 (frame helper): a `storeObject` that replaces one TCB with
another of the same `cpuAffinity` leaves every thread's home-core reading
unchanged. -/
private theorem storeObject_tcbAt_getTcb?_cpuAffinity_eq
    (st st' : SystemState) (stored : SeLe4n.ThreadId) (tOld tNew : TCB)
    (hOld : st.getTcb? stored = some tOld)
    (hAff : tNew.cpuAffinity = tOld.cpuAffinity)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject stored.toObjId (.tcb tNew) st = .ok ((), st'))
    (tid : SeLe4n.ThreadId) :
    (st'.getTcb? tid).map (·.cpuAffinity) = (st.getTcb? tid).map (·.cpuAffinity) := by
  have hRaw := (SystemState.getTcb?_eq_some_iff st stored tOld).mp hOld
  unfold SystemState.getTcb?
  by_cases h : tid.toObjId = stored.toObjId
  · rw [h, storeObject_objects_eq st st' stored.toObjId _ hObjInv hStore, hRaw]
    simp [hAff]
  · rw [storeObject_objects_ne st st' stored.toObjId tid.toObjId _ h hObjInv hStore]

/-- WS-RR RR2.3 (frame helper): a `storeObject` that replaces one TCB with
another leaves every SchedContext resolution unchanged. -/
private theorem storeObject_tcbAt_getSchedContext?_eq
    (st st' : SystemState) (stored : SeLe4n.ThreadId) (tOld tNew : TCB)
    (hOld : st.getTcb? stored = some tOld)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject stored.toObjId (.tcb tNew) st = .ok ((), st'))
    (scId : SeLe4n.SchedContextId) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  have hRaw := (SystemState.getTcb?_eq_some_iff st stored tOld).mp hOld
  unfold SystemState.getSchedContext?
  by_cases h : scId.toObjId = stored.toObjId
  · rw [h, storeObject_objects_eq st st' stored.toObjId _ hObjInv hStore, hRaw]
  · rw [storeObject_objects_ne st st' stored.toObjId scId.toObjId _ h hObjInv hStore]

/-- WS-RR RR2.3 (frame helper): a `storeObject` writing a SchedContext leaves
every **other** SchedContext's resolution unchanged. -/
private theorem storeObject_schedContext_getSchedContext?_ne
    (st st' : SystemState) (target scId : SeLe4n.SchedContextId) (scNew : SchedContext)
    (hNe : scId ≠ target)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject target.toObjId (.schedContext scNew) st = .ok ((), st')) :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?
  rw [storeObject_objects_ne st st' target.toObjId scId.toObjId _
    (fun h => hNe (SeLe4n.SchedContextId.toObjId_injective _ _ h)) hObjInv hStore]

/-- WS-RR RR2.3: `donateSchedContext` never changes any thread's `cpuAffinity`.

Its three stores are: the SchedContext's `boundThread` (a non-TCB slot whose
previous occupant is also a SchedContext), the donor TCB's
`schedContextBinding`, and the donee TCB's `schedContextBinding` — each a
record update that leaves `cpuAffinity` alone.  So the SM5.C.9 home-core
reading `determineTargetCore` is the same before and after the rebinding, which
is what lets the replenishment migration's endpoints be resolved from the
pre-state. -/
theorem donateSchedContext_getTcb?_cpuAffinity_eq
    (st st' : SystemState)
    (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (hObjInv : st.objects.invExt)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st')
    (tid : SeLe4n.ThreadId) :
    (st'.getTcb? tid).map (·.cpuAffinity) = (st.getTcb? tid).map (·.cpuAffinity) := by
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
      · cases hS1 : storeObject clientScId.toObjId (.schedContext { sc with boundThread := some serverTid }) st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hLC : lookupTcb p1.2 clientTid with
          | none => intro h; cases h
          | some clientTcb =>
            simp only []
            cases hS2 : storeObject clientTid.toObjId
                (.tcb { clientTcb with schedContextBinding := .unbound }) p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only []
              cases hL : lookupTcb p2.2 serverTid with
              | none => intro h; cases h
              | some serverTcb =>
                simp only []
                cases hS3 : storeObject serverTid.toObjId
                    (.tcb { serverTcb with schedContextBinding := .donated clientScId clientTid }) p2.2 with
                | error _ => intro h; cases h
                | ok p3 =>
                  simp only [Except.ok.injEq]
                  intro hEq; subst hEq
                  obtain ⟨u1, s1⟩ := p1; cases u1
                  obtain ⟨u2, s2⟩ := p2; cases u2
                  obtain ⟨u3, s3⟩ := p3; cases u3
                  have hInv1 : s1.objects.invExt :=
                    storeObject_preserves_objects_invExt st _ _ _ hObjInv hS1
                  have hInv2 : s2.objects.invExt :=
                    storeObject_preserves_objects_invExt s1 _ _ _ hInv1 hS2
                  have hRaw1 : s1.getTcb? clientTid = some clientTcb :=
                    getTcb?_of_lookupTcb s1 clientTid clientTcb hLC
                  have hRaw2 : s2.getTcb? serverTid = some serverTcb :=
                    getTcb?_of_lookupTcb s2 serverTid serverTcb hL
                  have hScPreT : st.getSchedContext? clientScId = some sc := by
                    unfold SystemState.getSchedContext?; rw [hObj]
                  have e1 := storeObject_schedContextAt_getTcb?_eq st s1 clientScId sc _ hScPreT hObjInv hS1 tid
                  have e2 := storeObject_tcbAt_getTcb?_cpuAffinity_eq s1 s2 clientTid clientTcb
                    { clientTcb with schedContextBinding := .unbound } hRaw1 rfl hInv1 hS2 tid
                  have e3 := storeObject_tcbAt_getTcb?_cpuAffinity_eq s2 s3 serverTid serverTcb
                    { serverTcb with schedContextBinding := .donated clientScId clientTid }
                    hRaw2 rfl hInv2 hS3 tid
                  -- The `scThreadIndex` re-keying at the end is not an object write.
                  show ((({ s3 with scThreadIndex := _ } : SystemState)).getTcb? tid).map (·.cpuAffinity) = _
                  rw [show (({ s3 with scThreadIndex :=
                      (scThreadIndexRemove
                        (scThreadIndexAdd s3.scThreadIndex clientScId serverTid)
                        clientScId clientTid) } : SystemState)).getTcb? tid = s3.getTcb? tid from rfl]
                  rw [e3, e2, e1]
    | _ => simp only []; intro h; cases h

/-- WS-RR RR2.3: `donateSchedContext` frames every SchedContext **other than**
the one it rebinds. -/
theorem donateSchedContext_getSchedContext?_ne
    (st st' : SystemState)
    (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId scId : SeLe4n.SchedContextId)
    (hNe : scId ≠ clientScId)
    (hObjInv : st.objects.invExt)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    st'.getSchedContext? scId = st.getSchedContext? scId := by
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
      · cases hS1 : storeObject clientScId.toObjId (.schedContext { sc with boundThread := some serverTid }) st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hLC : lookupTcb p1.2 clientTid with
          | none => intro h; cases h
          | some clientTcb =>
            simp only []
            cases hS2 : storeObject clientTid.toObjId
                (.tcb { clientTcb with schedContextBinding := .unbound }) p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only []
              cases hL : lookupTcb p2.2 serverTid with
              | none => intro h; cases h
              | some serverTcb =>
                simp only []
                cases hS3 : storeObject serverTid.toObjId
                    (.tcb { serverTcb with schedContextBinding := .donated clientScId clientTid }) p2.2 with
                | error _ => intro h; cases h
                | ok p3 =>
                  simp only [Except.ok.injEq]
                  intro hEq; subst hEq
                  obtain ⟨u1, s1⟩ := p1; cases u1
                  obtain ⟨u2, s2⟩ := p2; cases u2
                  obtain ⟨u3, s3⟩ := p3; cases u3
                  have hInv1 : s1.objects.invExt :=
                    storeObject_preserves_objects_invExt st _ _ _ hObjInv hS1
                  have hInv2 : s2.objects.invExt :=
                    storeObject_preserves_objects_invExt s1 _ _ _ hInv1 hS2
                  have hRaw1 : s1.getTcb? clientTid = some clientTcb :=
                    getTcb?_of_lookupTcb s1 clientTid clientTcb hLC
                  have hRaw2 : s2.getTcb? serverTid = some serverTcb :=
                    getTcb?_of_lookupTcb s2 serverTid serverTcb hL
                  have e1 := storeObject_schedContext_getSchedContext?_ne st s1 clientScId scId _
                    hNe hObjInv hS1
                  have e2 := storeObject_tcbAt_getSchedContext?_eq s1 s2 clientTid clientTcb
                    { clientTcb with schedContextBinding := .unbound } hRaw1 hInv1 hS2 scId
                  have e3 := storeObject_tcbAt_getSchedContext?_eq s2 s3 serverTid serverTcb
                    { serverTcb with schedContextBinding := .donated clientScId clientTid }
                    hRaw2 hInv2 hS3 scId
                  rw [show (({ s3 with scThreadIndex :=
                      (scThreadIndexRemove
                        (scThreadIndexAdd s3.scThreadIndex clientScId serverTid)
                        clientScId clientTid) } : SystemState)).getSchedContext? scId
                      = s3.getSchedContext? scId from rfl]
                  rw [e3, e2, e1]
    | _ => simp only []; intro h; cases h

/-- WS-RR RR2.3: after `donateSchedContext`, the rebound SchedContext's
`boundThread` is the **server** — the donee.  This is the post-state half of
`donateSchedContext_ok_implies_sc_bound` (whose pre-state half says it was the
donor), and it is what makes the replenishment migration's destination the
donee's home core rather than the donor's. -/
theorem donateSchedContext_post_boundThread
    (st st' : SystemState)
    (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (hObjInv : st.objects.invExt)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    ∃ sc', st'.getSchedContext? clientScId = some sc' ∧ sc'.boundThread = some serverTid := by
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
      · cases hS1 : storeObject clientScId.toObjId (.schedContext { sc with boundThread := some serverTid }) st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hLC : lookupTcb p1.2 clientTid with
          | none => intro h; cases h
          | some clientTcb =>
            simp only []
            cases hS2 : storeObject clientTid.toObjId
                (.tcb { clientTcb with schedContextBinding := .unbound }) p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only []
              cases hL : lookupTcb p2.2 serverTid with
              | none => intro h; cases h
              | some serverTcb =>
                simp only []
                cases hS3 : storeObject serverTid.toObjId
                    (.tcb { serverTcb with schedContextBinding := .donated clientScId clientTid }) p2.2 with
                | error _ => intro h; cases h
                | ok p3 =>
                  simp only [Except.ok.injEq]
                  intro hEq; subst hEq
                  obtain ⟨u1, s1⟩ := p1; cases u1
                  obtain ⟨u2, s2⟩ := p2; cases u2
                  obtain ⟨u3, s3⟩ := p3; cases u3
                  have hInv1 : s1.objects.invExt :=
                    storeObject_preserves_objects_invExt st _ _ _ hObjInv hS1
                  have hInv2 : s2.objects.invExt :=
                    storeObject_preserves_objects_invExt s1 _ _ _ hInv1 hS2
                  have hRaw1 : s1.getTcb? clientTid = some clientTcb :=
                    getTcb?_of_lookupTcb s1 clientTid clientTcb hLC
                  have hRaw2 : s2.getTcb? serverTid = some serverTcb :=
                    getTcb?_of_lookupTcb s2 serverTid serverTcb hL
                  have e1 : s1.getSchedContext? clientScId
                      = some { sc with boundThread := some serverTid } := by
                    unfold SystemState.getSchedContext?
                    rw [storeObject_objects_eq st s1 clientScId.toObjId _ hObjInv hS1]
                  have e2 := storeObject_tcbAt_getSchedContext?_eq s1 s2 clientTid clientTcb
                    { clientTcb with schedContextBinding := .unbound } hRaw1 hInv1 hS2 clientScId
                  have e3 := storeObject_tcbAt_getSchedContext?_eq s2 s3 serverTid serverTcb
                    { serverTcb with schedContextBinding := .donated clientScId clientTid }
                    hRaw2 hInv2 hS3 clientScId
                  refine ⟨{ sc with boundThread := some serverTid }, ?_, rfl⟩
                  rw [show (({ s3 with scThreadIndex :=
                      (scThreadIndexRemove
                        (scThreadIndexAdd s3.scThreadIndex clientScId serverTid)
                        clientScId clientTid) } : SystemState)).getSchedContext? clientScId
                      = s3.getSchedContext? clientScId from rfl]
                  rw [e3, e2, e1]
    | _ => simp only []; intro h; cases h

-- ============================================================================
-- WS-RR RR2.8/RR2.9: donation-**return** object-store frames — the mirrors of
-- the donation frames above
-- ============================================================================

/-- WS-RR RR2.8 (precondition witness, the mirror of
`donateSchedContext_ok_implies_sc_bound`): on success the SchedContext existed
and was bound to the **server**.  This is what the RR2.8 guard bought: the
replenishment migration's *source* core is now derived from the return
succeeding rather than assumed of its caller. -/
theorem returnDonatedSchedContext_ok_implies_sc_bound
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    ∃ sc : SchedContext,
      st.getSchedContext? scId = some sc ∧
      sc.boundThread = some serverTid := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      cases hBne : (sc.boundThread != some serverTid) with
      | true => simp only [if_true]; intro h; cases h
      | false =>
        simp only [Bool.false_eq_true, if_false]
        intro _
        exact ⟨sc, by unfold SystemState.getSchedContext?; rw [hObj], by simpa using hBne⟩
    | _ => simp only []; intro h; cases h

/-- WS-RR RR2.9: `returnDonatedSchedContext` never changes any thread's
`cpuAffinity` — the mirror of `donateSchedContext_getTcb?_cpuAffinity_eq`. -/
theorem returnDonatedSchedContext_getTcb?_cpuAffinity_eq
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st')
    (tid : SeLe4n.ThreadId) :
    (st'.getTcb? tid).map (·.cpuAffinity) = (st.getTcb? tid).map (·.cpuAffinity) := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      split
      · intro h; cases h
      · cases hS1 : storeObject scId.toObjId (.schedContext { sc with boundThread := some originalOwner }) st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hL1 : lookupTcb p1.2 originalOwner with
          | none => intro h; cases h
          | some ownerTcb =>
            simp only []
            cases hS2 : storeObject originalOwner.toObjId
                (.tcb { ownerTcb with schedContextBinding := .bound scId }) p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only []
              cases hL2 : lookupTcb p2.2 serverTid with
              | none => intro h; cases h
              | some serverTcb =>
                simp only []
                cases hS3 : storeObject serverTid.toObjId
                    (.tcb { serverTcb with schedContextBinding := .unbound }) p2.2 with
                | error _ => intro h; cases h
                | ok p3 =>
                  simp only [Except.ok.injEq]
                  intro hEq; subst hEq
                  obtain ⟨u1, s1⟩ := p1; cases u1
                  obtain ⟨u2, s2⟩ := p2; cases u2
                  obtain ⟨u3, s3⟩ := p3; cases u3
                  have hInv1 : s1.objects.invExt :=
                    storeObject_preserves_objects_invExt st _ _ _ hObjInv hS1
                  have hInv2 : s2.objects.invExt :=
                    storeObject_preserves_objects_invExt s1 _ _ _ hInv1 hS2
                  have hRaw1 : s1.getTcb? originalOwner = some ownerTcb :=
                    getTcb?_of_lookupTcb s1 originalOwner ownerTcb hL1
                  have hRaw2 : s2.getTcb? serverTid = some serverTcb :=
                    getTcb?_of_lookupTcb s2 serverTid serverTcb hL2
                  have hScPreT : st.getSchedContext? scId = some sc := by
                    unfold SystemState.getSchedContext?; rw [hObj]
                  have e1 := storeObject_schedContextAt_getTcb?_eq st s1 scId sc _ hScPreT hObjInv hS1 tid
                  have e2 := storeObject_tcbAt_getTcb?_cpuAffinity_eq s1 s2 originalOwner ownerTcb
                    { ownerTcb with schedContextBinding := .bound scId } hRaw1 rfl hInv1 hS2 tid
                  have e3 := storeObject_tcbAt_getTcb?_cpuAffinity_eq s2 s3 serverTid serverTcb
                    { serverTcb with schedContextBinding := .unbound } hRaw2 rfl hInv2 hS3 tid
                  rw [show (({ s3 with scThreadIndex :=
                      (scThreadIndexAdd
                        (scThreadIndexRemove s3.scThreadIndex scId serverTid)
                        scId originalOwner) } : SystemState)).getTcb? tid = s3.getTcb? tid from rfl]
                  rw [e3, e2, e1]
    | _ => simp only []; intro h; cases h

/-- WS-RR RR2.9: `returnDonatedSchedContext` frames every SchedContext **other
than** the one it rebinds. -/
theorem returnDonatedSchedContext_getSchedContext?_ne
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId scId' : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hNe : scId' ≠ scId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    st'.getSchedContext? scId' = st.getSchedContext? scId' := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      split
      · intro h; cases h
      · cases hS1 : storeObject scId.toObjId (.schedContext { sc with boundThread := some originalOwner }) st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hL1 : lookupTcb p1.2 originalOwner with
          | none => intro h; cases h
          | some ownerTcb =>
            simp only []
            cases hS2 : storeObject originalOwner.toObjId
                (.tcb { ownerTcb with schedContextBinding := .bound scId }) p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only []
              cases hL2 : lookupTcb p2.2 serverTid with
              | none => intro h; cases h
              | some serverTcb =>
                simp only []
                cases hS3 : storeObject serverTid.toObjId
                    (.tcb { serverTcb with schedContextBinding := .unbound }) p2.2 with
                | error _ => intro h; cases h
                | ok p3 =>
                  simp only [Except.ok.injEq]
                  intro hEq; subst hEq
                  obtain ⟨u1, s1⟩ := p1; cases u1
                  obtain ⟨u2, s2⟩ := p2; cases u2
                  obtain ⟨u3, s3⟩ := p3; cases u3
                  have hInv1 : s1.objects.invExt :=
                    storeObject_preserves_objects_invExt st _ _ _ hObjInv hS1
                  have hInv2 : s2.objects.invExt :=
                    storeObject_preserves_objects_invExt s1 _ _ _ hInv1 hS2
                  have hRaw1 : s1.getTcb? originalOwner = some ownerTcb :=
                    getTcb?_of_lookupTcb s1 originalOwner ownerTcb hL1
                  have hRaw2 : s2.getTcb? serverTid = some serverTcb :=
                    getTcb?_of_lookupTcb s2 serverTid serverTcb hL2
                  have e1 := storeObject_schedContext_getSchedContext?_ne st s1 scId scId' _
                    hNe hObjInv hS1
                  have e2 := storeObject_tcbAt_getSchedContext?_eq s1 s2 originalOwner ownerTcb
                    { ownerTcb with schedContextBinding := .bound scId } hRaw1 hInv1 hS2 scId'
                  have e3 := storeObject_tcbAt_getSchedContext?_eq s2 s3 serverTid serverTcb
                    { serverTcb with schedContextBinding := .unbound } hRaw2 hInv2 hS3 scId'
                  rw [show (({ s3 with scThreadIndex :=
                      (scThreadIndexAdd
                        (scThreadIndexRemove s3.scThreadIndex scId serverTid)
                        scId originalOwner) } : SystemState)).getSchedContext? scId'
                      = s3.getSchedContext? scId' from rfl]
                  rw [e3, e2, e1]
    | _ => simp only []; intro h; cases h

/-- WS-RR RR2.9: after `returnDonatedSchedContext`, the rebound SchedContext's
`boundThread` is the **original owner** — the mirror of
`donateSchedContext_post_boundThread`, and the fact that makes the
replenishment migration's destination the owner's home core. -/
theorem returnDonatedSchedContext_post_boundThread
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    ∃ sc', st'.getSchedContext? scId = some sc' ∧ sc'.boundThread = some originalOwner := by
  unfold returnDonatedSchedContext at h
  revert h
  cases hObj : st.objects[scId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      split
      · intro h; cases h
      · cases hS1 : storeObject scId.toObjId (.schedContext { sc with boundThread := some originalOwner }) st with
        | error _ => intro h; cases h
        | ok p1 =>
          simp only []
          cases hL1 : lookupTcb p1.2 originalOwner with
          | none => intro h; cases h
          | some ownerTcb =>
            simp only []
            cases hS2 : storeObject originalOwner.toObjId
                (.tcb { ownerTcb with schedContextBinding := .bound scId }) p1.2 with
            | error _ => intro h; cases h
            | ok p2 =>
              simp only []
              cases hL2 : lookupTcb p2.2 serverTid with
              | none => intro h; cases h
              | some serverTcb =>
                simp only []
                cases hS3 : storeObject serverTid.toObjId
                    (.tcb { serverTcb with schedContextBinding := .unbound }) p2.2 with
                | error _ => intro h; cases h
                | ok p3 =>
                  simp only [Except.ok.injEq]
                  intro hEq; subst hEq
                  obtain ⟨u1, s1⟩ := p1; cases u1
                  obtain ⟨u2, s2⟩ := p2; cases u2
                  obtain ⟨u3, s3⟩ := p3; cases u3
                  have hInv1 : s1.objects.invExt :=
                    storeObject_preserves_objects_invExt st _ _ _ hObjInv hS1
                  have hInv2 : s2.objects.invExt :=
                    storeObject_preserves_objects_invExt s1 _ _ _ hInv1 hS2
                  have hRaw1 : s1.getTcb? originalOwner = some ownerTcb :=
                    getTcb?_of_lookupTcb s1 originalOwner ownerTcb hL1
                  have hRaw2 : s2.getTcb? serverTid = some serverTcb :=
                    getTcb?_of_lookupTcb s2 serverTid serverTcb hL2
                  have e1 : s1.getSchedContext? scId
                      = some { sc with boundThread := some originalOwner } := by
                    unfold SystemState.getSchedContext?
                    rw [storeObject_objects_eq st s1 scId.toObjId _ hObjInv hS1]
                  have e2 := storeObject_tcbAt_getSchedContext?_eq s1 s2 originalOwner ownerTcb
                    { ownerTcb with schedContextBinding := .bound scId } hRaw1 hInv1 hS2 scId
                  have e3 := storeObject_tcbAt_getSchedContext?_eq s2 s3 serverTid serverTcb
                    { serverTcb with schedContextBinding := .unbound } hRaw2 hInv2 hS3 scId
                  refine ⟨{ sc with boundThread := some originalOwner }, ?_, rfl⟩
                  rw [show (({ s3 with scThreadIndex :=
                      (scThreadIndexAdd
                        (scThreadIndexRemove s3.scThreadIndex scId serverTid)
                        scId originalOwner) } : SystemState)).getSchedContext? scId
                      = s3.getSchedContext? scId from rfl]
                  rw [e3, e2, e1]
    | _ => simp only []; intro h; cases h

end SeLe4n.Kernel
