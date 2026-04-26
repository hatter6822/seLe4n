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

See §6 (Phase AN3-A) of `docs/dev_history/audits/AUDIT_v0.30.6_WORKSTREAM_PLAN.md`
for rationale.
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

end SeLe4n.Kernel
