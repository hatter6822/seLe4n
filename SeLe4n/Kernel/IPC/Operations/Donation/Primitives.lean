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
        -- **WS-OD OD4.2**: the caller's *effective* scheduling context, bound or
        -- donated — seL4-MCS's `maybeDonateSchedContext`, which reads
        -- `sender->tcbSchedContext` and does not care how the sender came to
        -- hold it.  Before this the guard matched `.bound` alone, so a chain
        -- stopped at the first passive server: at call depth ≥ 2 the callee
        -- stayed `.unbound`, received no budget and was never selected.
        --
        -- The resolver is `SchedContextBinding.scId?` rather than a second
        -- two-arm match, so "which context does this thread hold" is answered
        -- in one place; `donationReturnBinding_scId?` already relies on that
        -- single answer for the pop.
        match callerTcb.schedContextBinding.scId? with
        | some clientScId =>
          -- AH2-A: Propagate donation errors instead of swallowing them.
          -- AN10-residual-1 deep-audit (H5): direct call to the typed
          -- wrapper.  Type-level enforcement of the dispatch-boundary
          -- discipline at this function's signature.
          match donateSchedContextValid st callerVtid receiverVtid clientScId with
          | .error e => .error e
          | .ok st' => .ok st'
        | none => .ok st                    -- No-op: caller has no SC to donate
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
  -- WS-OD OD4.1: read off the operation's own decomposition rather than by a
  -- second copy of its case analysis.  The fourth store made that copy
  -- non-compiling, which is what the shared derivation exists to prevent.
  obtain ⟨_, _, _, _, _, _, s1, s2, s3, s4, _, _, _, _, hS1, hS2, _, hS3, _, hS4, hEq⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  have h1 := storeObject_scheduler_eq_local st _ _ _ hS1
  have h2 := storeObject_scheduler_eq_local s1 _ _ _ hS2
  have h3 := storeObject_scheduler_eq_local s2 _ _ _ hS3
  have h4 := storeObject_scheduler_eq_local s3 _ _ _ hS4
  rw [hEq]
  show s4.scheduler = st.scheduler
  exact h4.trans (h3.trans (h2.trans h1))

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
        -- **WS-OD OD4.2**: the split is on the caller's *effective* context, the
        -- one thing the widened guard reads.
        cases hCallerBinding : callerTcb.schedContextBinding.scId? with
        | none => simp [hCallerBinding] at h; cases h; rfl
        | some clientScId =>
          -- AN10-residual-1 deep-audit: body now calls `donateSchedContextValid`
          -- directly with the typed arguments; reduce via `_eq` lemma.
          simp only [hCallerBinding, donateSchedContextValid] at h
          cases hDonate : donateSchedContext st callerVtid.val receiverVtid.val clientScId with
          | error _ => simp [hDonate] at h
          | ok stDon =>
              simp [hDonate] at h; rw [← h]
              exact donateSchedContext_scheduler_eq st stDon callerVtid.val receiverVtid.val clientScId hDonate
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
          -- **WS-OD OD4.4**: the new owner is resolved off the scheduling
          -- context's own reply stack, on this pop's pre-state.  At the bottom
          -- of the stack that is `none` and the return rebinds `.bound scId`
          -- exactly as before; one level up it names the outer caller, and the
          -- context settles on the thread that is still owed it instead of on
          -- the intermediate donor — which would otherwise acquire another
          -- domain's reservation permanently (plan §3.2).
          match returnDonatedSchedContextResolved st replierVtid.val scId ownerVtid.val with
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
  obtain ⟨_, _, _, serverTcb, _, _, s1, s2, s3, s4, _, _, _, _, hS1, hS2, _, hS3, _, hS4,
      hEq⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  refine ⟨{ serverTcb with schedContextBinding := .donated clientScId clientTid }, ?_, rfl⟩
  rw [hEq]
  show s4.objects[serverTid.toObjId]? = _
  exact storeObject_objects_eq s3 s4 serverTid.toObjId _ hInv3 hS4

/-- Z7-K2: After returnDonatedSchedContext, the server's binding is .unbound. -/
theorem returnDonatedSchedContext_server_unbound
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    ∃ tcb', st'.objects[serverTid.toObjId]? = some (.tcb tcb') ∧
      tcb'.schedContextBinding = .unbound := by
  -- WS-OD OD3.1: read off the operation's own decomposition rather than by a
  -- second copy of its case analysis.  The fourth store made that copy
  -- non-compiling, which is exactly what the shared derivation exists to
  -- prevent — and what it prevented at three other sites in this file.
  obtain ⟨_, _, _, serverTcb, s1, s2, s3, s4, _, _, _, hS1, hClear, _, hS3, _, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  refine ⟨{ serverTcb with schedContextBinding := .unbound }, ?_, rfl⟩
  rw [hEq]
  show s4.objects[serverTid.toObjId]? = _
  exact storeObject_objects_eq' s3 serverTid.toObjId _ _ hInv3 hS4

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
  obtain ⟨_, _, _, _, _, _, s1, s2, s3, s4, _, _, _, _, hS1, hS2, _, hS3, _, hS4, hEq⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  have h1 := storeObject_machine_eq_local st _ _ _ hS1
  have h2 := storeObject_machine_eq_local s1 _ _ _ hS2
  have h3 := storeObject_machine_eq_local s2 _ _ _ hS3
  have h4 := storeObject_machine_eq_local s3 _ _ _ hS4
  rw [hEq]
  show s4.machine = st.machine
  exact h4.trans (h3.trans (h2.trans h1))

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
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    st'.machine = st.machine := by
  -- WS-RR RR7.22 (residual, remediation): read off the shared decomposition
  -- rather than re-running its case analysis, which this file used to carry a
  -- second copy of.
  obtain ⟨_, _, _, _, s1, s2, s3, s4, _, _, _, h1, hClear, _, h3, _, h4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  rw [hEq]
  show s4.machine = st.machine
  rw [SeLe4n.Model.storeObject_machine_eq s3 s4 _ _ h4,
    SeLe4n.Model.storeObject_machine_eq s2 s3 _ _ h3,
    storeDonationHeadClear_machine_eq hClear,
    SeLe4n.Model.storeObject_machine_eq st s1 _ _ h1]

/-- AG8-G: Return donation is atomic — `returnDonatedSchedContext` preserves
the interrupt-disabled state. Derives the post-condition from
`returnDonatedSchedContext_machine_eq`. -/
theorem returnDonatedSchedContext_atomicRegion
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hPre : st.machine.interruptsEnabled = false)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    donationAtomicRegion st st' := by
  constructor
  · exact hPre
  · have hMach := returnDonatedSchedContext_machine_eq st st' serverTid scId originalOwner newOwner? h
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
        -- **WS-OD OD4.2**: the split is on the caller's *effective* context, the
        -- one thing the widened guard reads.
        cases hCallerBinding : callerTcb.schedContextBinding.scId? with
        | none => simp [hCallerBinding] at h; cases h; rfl
        | some clientScId =>
          -- AN10-residual-1 deep-audit: body now calls `donateSchedContextValid`
          -- directly with the typed arguments; reduce via `_eq` lemma.
          simp only [hCallerBinding, donateSchedContextValid] at h
          cases hDonate : donateSchedContext st callerVtid.val receiverVtid.val clientScId with
          | error _ => simp [hDonate] at h
          | ok stDon =>
              simp [hDonate] at h; rw [← h]
              exact donateSchedContext_machine_eq st stDon callerVtid.val receiverVtid.val clientScId hDonate
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
          simp only [hOV, hOEq] at h
          -- WS-OD OD4.4: the split is on the *resolved* return, which is the
          -- operation the arm now runs; the frame is lifted through its own
          -- decomposition rather than restated at a fixed `newOwner?`.
          cases hReturn : returnDonatedSchedContextResolved st replierVtid.val scId
              originalOwner with
          | error _ => simp [hReturn] at h
          | ok st'' =>
            simp [hReturn] at h; cases h
            obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hReturn
            have hMach := returnDonatedSchedContext_machine_eq st st'' replierVtid.val scId
              originalOwner n hPop
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
      cases hReturn : returnDonatedSchedContextResolved st receiver scId originalOwner with
      | error _ => rfl
      | ok st' =>
        obtain ⟨n, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hReturn
        exact returnDonatedSchedContext_machine_eq st st' receiver scId originalOwner n hPop

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
  obtain ⟨sc, donorTcb, clientTcb, serverTcb, pushRid, pushReply, s1, s2, s3, s4,
      hObj, _, _, hFrame, hS1, hS2, hLC, hS3, hL, hS4, hEq⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  -- The pushed Reply resolves at the state its own store runs on: it resolved in
  -- `st` (that is what `donationPushFrame?` validated), and the SchedContext
  -- store before it lands at a key holding a SchedContext, hence a different one.
  have hRepPre : st.getReply? pushRid = some pushReply :=
    (donationPushFrame?_ok st donorTcb pushRid pushReply hFrame).2.1
  have hRepRaw := (SystemState.getReply?_eq_some_iff st pushRid pushReply).mp hRepPre
  -- WS-OD OD4.1: the two non-TCB stores land at different keys, off the shared
  -- typed distinctness lemma rather than a fifth copy of its three-line proof.
  have hKeyNe := getReply?_getSchedContext?_key_ne st pushRid clientScId pushReply sc
    hRepPre hObj
  have hRep1 : s1.getReply? pushRid = some pushReply := by
    rw [SystemState.getReply?_eq_some_iff,
      storeObject_objects_ne st s1 clientScId.toObjId pushRid.toObjId _ hKeyNe hObjInv hS1]
    exact hRepRaw
  have hRaw1 : s2.getTcb? clientTid = some clientTcb :=
    getTcb?_of_lookupTcb s2 clientTid clientTcb hLC
  have hRaw2 : s3.getTcb? serverTid = some serverTcb :=
    getTcb?_of_lookupTcb s3 serverTid serverTcb hL
  have e1 := storeObject_schedContextAt_getTcb?_eq st s1 clientScId sc _ hObj hObjInv hS1 tid
  have e2 := storeObject_replyAt_getTcb?_eq s1 s2 pushRid pushReply _ hRep1 hInv1 hS2 tid
  have e3 := storeObject_tcbAt_getTcb?_cpuAffinity_eq s2 s3 clientTid clientTcb
    { clientTcb with schedContextBinding := .unbound } hRaw1 rfl hInv2 hS3 tid
  have e4 := storeObject_tcbAt_getTcb?_cpuAffinity_eq s3 s4 serverTid serverTcb
    { serverTcb with schedContextBinding := .donated clientScId clientTid }
    hRaw2 rfl hInv3 hS4 tid
  -- The `scThreadIndex` re-keying at the end is not an object write.
  rw [hEq]
  show (s4.getTcb? tid).map (·.cpuAffinity) = _
  rw [e4, e3, e2, e1]

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
  obtain ⟨sc, donorTcb, clientTcb, serverTcb, pushRid, pushReply, s1, s2, s3, s4,
      hObj, _, _, hFrame, hS1, hS2, hLC, hS3, hL, hS4, hEq⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  -- The pushed Reply resolves at the state its own store runs on: it resolved in
  -- `st` (that is what `donationPushFrame?` validated), and the SchedContext
  -- store before it lands at a key holding a SchedContext, hence a different one.
  have hRepPre : st.getReply? pushRid = some pushReply :=
    (donationPushFrame?_ok st donorTcb pushRid pushReply hFrame).2.1
  have hRepRaw := (SystemState.getReply?_eq_some_iff st pushRid pushReply).mp hRepPre
  -- WS-OD OD4.1: the two non-TCB stores land at different keys, off the shared
  -- typed distinctness lemma rather than a fifth copy of its three-line proof.
  have hKeyNe := getReply?_getSchedContext?_key_ne st pushRid clientScId pushReply sc
    hRepPre hObj
  have hRep1 : s1.getReply? pushRid = some pushReply := by
    rw [SystemState.getReply?_eq_some_iff,
      storeObject_objects_ne st s1 clientScId.toObjId pushRid.toObjId _ hKeyNe hObjInv hS1]
    exact hRepRaw
  have hRaw1 : s2.getTcb? clientTid = some clientTcb :=
    getTcb?_of_lookupTcb s2 clientTid clientTcb hLC
  have hRaw2 : s3.getTcb? serverTid = some serverTcb :=
    getTcb?_of_lookupTcb s3 serverTid serverTcb hL
  have e1 := storeObject_schedContext_getSchedContext?_ne st s1 clientScId scId _
    hNe hObjInv hS1
  have e2 := storeObject_replyAt_getSchedContext?_eq s1 s2 pushRid pushReply _ hRep1 hInv1 hS2 scId
  have e3 := storeObject_tcbAt_getSchedContext?_eq s2 s3 clientTid clientTcb
    { clientTcb with schedContextBinding := .unbound } hRaw1 hInv2 hS3 scId
  have e4 := storeObject_tcbAt_getSchedContext?_eq s3 s4 serverTid serverTcb
    { serverTcb with schedContextBinding := .donated clientScId clientTid }
    hRaw2 hInv3 hS4 scId
  rw [hEq]
  show s4.getSchedContext? scId = _
  rw [e4, e3, e2, e1]

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
  obtain ⟨sc, donorTcb, clientTcb, serverTcb, pushRid, pushReply, s1, s2, s3, s4,
      hObj, _, _, hFrame, hS1, hS2, hLC, hS3, hL, hS4, hEq⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  -- The pushed Reply resolves at the state its own store runs on: it resolved in
  -- `st` (that is what `donationPushFrame?` validated), and the SchedContext
  -- store before it lands at a key holding a SchedContext, hence a different one.
  have hRepPre : st.getReply? pushRid = some pushReply :=
    (donationPushFrame?_ok st donorTcb pushRid pushReply hFrame).2.1
  have hRepRaw := (SystemState.getReply?_eq_some_iff st pushRid pushReply).mp hRepPre
  -- WS-OD OD4.1: the two non-TCB stores land at different keys, off the shared
  -- typed distinctness lemma rather than a fifth copy of its three-line proof.
  have hKeyNe := getReply?_getSchedContext?_key_ne st pushRid clientScId pushReply sc
    hRepPre hObj
  have hRep1 : s1.getReply? pushRid = some pushReply := by
    rw [SystemState.getReply?_eq_some_iff,
      storeObject_objects_ne st s1 clientScId.toObjId pushRid.toObjId _ hKeyNe hObjInv hS1]
    exact hRepRaw
  have hRaw1 : s2.getTcb? clientTid = some clientTcb :=
    getTcb?_of_lookupTcb s2 clientTid clientTcb hLC
  have hRaw2 : s3.getTcb? serverTid = some serverTcb :=
    getTcb?_of_lookupTcb s3 serverTid serverTcb hL
  have e1 : s1.getSchedContext? clientScId
      = some { sc with boundThread := some serverTid, scReply := some pushRid } := by
    rw [SystemState.getSchedContext?_eq_some_iff,
      storeObject_objects_eq st s1 clientScId.toObjId _ hObjInv hS1]
  have e2 := storeObject_replyAt_getSchedContext?_eq s1 s2 pushRid pushReply _ hRep1 hInv1 hS2
    clientScId
  have e3 := storeObject_tcbAt_getSchedContext?_eq s2 s3 clientTid clientTcb
    { clientTcb with schedContextBinding := .unbound } hRaw1 hInv2 hS3 clientScId
  have e4 := storeObject_tcbAt_getSchedContext?_eq s3 s4 serverTid serverTcb
    { serverTcb with schedContextBinding := .donated clientScId clientTid }
    hRaw2 hInv3 hS4 clientScId
  refine ⟨{ sc with boundThread := some serverTid, scReply := some pushRid }, ?_, rfl⟩
  rw [hEq]
  show s4.getSchedContext? clientScId = _
  rw [e4, e3, e2, e1]

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
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
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
`cpuAffinity` — the mirror of `donateSchedContext_getTcb?_cpuAffinity_eq`.

WS-OD OD3.1: read off `returnDonatedSchedContext_ok_storeChain` rather than by a
second copy of the operation's case analysis.  The head clear is one extra hop
(`storeDonationHeadClear_getTcb?_eq`), which is exactly the shape the shared
derivation exists to keep: the pop added a store and this proof gained a
rewrite, not an arm. -/
theorem returnDonatedSchedContext_getTcb?_cpuAffinity_eq
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st')
    (tid : SeLe4n.ThreadId) :
    (st'.getTcb? tid).map (·.cpuAffinity) = (st.getTcb? tid).map (·.cpuAffinity) := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have hScPre : st.getSchedContext? scId = some sc := by
    unfold SystemState.getSchedContext?; rw [hSc]
  have hRaw1 : s2.getTcb? originalOwner = some clientTcb :=
    getTcb?_of_lookupTcb s2 originalOwner clientTcb hL1
  have hRaw2 : s3.getTcb? serverTid = some serverTcb :=
    getTcb?_of_lookupTcb s3 serverTid serverTcb hL2
  have e1 := storeObject_schedContextAt_getTcb?_eq st s1 scId sc _ hScPre hObjInv hS1 tid
  have e2 := storeDonationHeadClear_getTcb?_eq hInv1 hClear tid
  have e3 := storeObject_tcbAt_getTcb?_cpuAffinity_eq s2 s3 originalOwner clientTcb
    { clientTcb with schedContextBinding := donationReturnBinding scId newOwner? }
    hRaw1 rfl hInv2 hS3 tid
  have e4 := storeObject_tcbAt_getTcb?_cpuAffinity_eq s3 s4 serverTid serverTcb
    { serverTcb with schedContextBinding := .unbound } hRaw2 rfl hInv3 hS4 tid
  have hGet : st'.getTcb? tid = s4.getTcb? tid := by rw [hEq]; rfl
  rw [hGet, e4, e3, e2, e1]

/-- WS-RR RR2.9: `returnDonatedSchedContext` frames every SchedContext **other
than** the one it rebinds.

WS-OD OD3.1: the pop's head clear writes a **Reply**, so it frames every
SchedContext — including the one being rebound — which is why the extra hop is
`storeDonationHeadClear_getSchedContext?_eq` and needs no disjointness
side-condition of its own. -/
theorem returnDonatedSchedContext_getSchedContext?_ne
    (st st' : SystemState)
    (serverTid : SeLe4n.ThreadId)
    (scId scId' : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId)
    (hNe : scId' ≠ scId)
    (hObjInv : st.objects.invExt)
    (newOwner? : Option SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    st'.getSchedContext? scId' = st.getSchedContext? scId' := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _hHead, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeDonationHeadClear_preserves_objects_invExt hInv1 hClear
  have hInv3 : s3.objects.invExt := storeObject_preserves_objects_invExt s2 s3 _ _ hInv2 hS3
  have hRaw1 : s2.getTcb? originalOwner = some clientTcb :=
    getTcb?_of_lookupTcb s2 originalOwner clientTcb hL1
  have hRaw2 : s3.getTcb? serverTid = some serverTcb :=
    getTcb?_of_lookupTcb s3 serverTid serverTcb hL2
  have e1 := storeObject_schedContext_getSchedContext?_ne st s1 scId scId' _ hNe hObjInv hS1
  have e2 := storeDonationHeadClear_getSchedContext?_eq hInv1 hClear scId'
  have e3 := storeObject_tcbAt_getSchedContext?_eq s2 s3 originalOwner clientTcb
    { clientTcb with schedContextBinding := donationReturnBinding scId newOwner? }
    hRaw1 hInv2 hS3 scId'
  have e4 := storeObject_tcbAt_getSchedContext?_eq s3 s4 serverTid serverTcb
    { serverTcb with schedContextBinding := .unbound } hRaw2 hInv3 hS4 scId'
  have hGet : st'.getSchedContext? scId' = s4.getSchedContext? scId' := by rw [hEq]; rfl
  rw [hGet, e4, e3, e2, e1]

end SeLe4n.Kernel
