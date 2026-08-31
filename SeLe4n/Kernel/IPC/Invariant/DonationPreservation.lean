-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- WS-RR RR2.5: PRODUCTION.  The invariant surface of the SchedContext donation
-- primitives, which had none before RR2 wired them onto reachable paths.

import SeLe4n.Kernel.IPC.Invariant.Structural
import SeLe4n.Kernel.IPC.Operations.Donation

/-!
# WS-RR RR2.5 — the donation primitives preserve the IPC invariant bundle

`donateSchedContext` and `returnDonatedSchedContext` are the only kernel
operations that write a TCB's `schedContextBinding`, which is exactly the field
the bundle's four donation conjuncts read.  Every other IPC transition frames
them (`sameSchedContextBindings`), which is why the whole preservation surface
for those conjuncts was a *frame* surface and the primitives themselves carried
no preservation theorem at all.

That was tolerable while `applyCallDonation` sat behind a boot-pinned wrapper.
It stopped being tolerable at RR2.7 / RR2.12, which put both primitives on the
**live** cross-core `.call` and `.reply` paths — after which "the donation
preserves the invariant" is a claim about a reachable transition and has to be
proved rather than framed.

## Structure

* §1 — the **object-store walk**: what the three stores of each primitive do,
  pointwise, with the key-distinctness facts a successful run witnesses.
* §2 — the derived readings (`getTcb?` at each of the three keys, everything
  else framed).
* §3 — the four donation conjuncts plus `passiveServerIdle`, for
  `applyCallDonation`.
* §4 — the same for `applyReplyDonation` / `applyReplyDonationOnCore`.
* §5 — the whole-bundle theorems, and their per-core forms.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Model.SystemState
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  The object-store walk
-- ============================================================================

/-- WS-RR RR2.5: a successful `donateSchedContext` exposes its three stores and
their inputs.  Everything §2 derives is read off this: the SchedContext it
rebinds (bound to the donor, per the operation's own AUD-3b guard), the donor
TCB it clears, the donee TCB it marks `.donated`, and the fact that the final
state differs from the last store's only in `scThreadIndex`, which no IPC
conjunct reads. -/
theorem donateSchedContext_walk
    (st st' : SystemState) (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    ∃ (sc : SchedContext) (clientTcb serverTcb : TCB) (s1 s2 s3 : SystemState),
      st.objects[clientScId.toObjId]? = some (.schedContext sc) ∧
      sc.boundThread = some clientTid ∧
      storeObject clientScId.toObjId
        (.schedContext { sc with boundThread := some serverTid }) st = .ok ((), s1) ∧
      lookupTcb s1 clientTid = some clientTcb ∧
      storeObject clientTid.toObjId
        (.tcb { clientTcb with schedContextBinding := .unbound }) s1 = .ok ((), s2) ∧
      lookupTcb s2 serverTid = some serverTcb ∧
      storeObject serverTid.toObjId
        (.tcb { serverTcb with schedContextBinding := .donated clientScId clientTid })
        s2 = .ok ((), s3) ∧
      st'.objects = s3.objects ∧ st'.scheduler = s3.scheduler := by
  unfold donateSchedContext at h
  revert h
  cases hObj : st.objects[clientScId.toObjId]? with
  | none => intro h; cases h
  | some obj =>
    cases obj with
    | schedContext sc =>
      simp only []
      cases hBne : (sc.boundThread != some clientTid) with
      | true => simp only [if_true]; intro h; cases h
      | false =>
        simp only [Bool.false_eq_true, if_false]
        cases hS1 : storeObject clientScId.toObjId
            (.schedContext { sc with boundThread := some serverTid }) st with
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
                    (.tcb { serverTcb with schedContextBinding := .donated clientScId clientTid })
                    p2.2 with
                | error _ => intro h; cases h
                | ok p3 =>
                  simp only [Except.ok.injEq]
                  intro hEq; subst hEq
                  obtain ⟨u1, s1⟩ := p1; cases u1
                  obtain ⟨u2, s2⟩ := p2; cases u2
                  obtain ⟨u3, s3⟩ := p3; cases u3
                  exact ⟨sc, clientTcb, serverTcb, s1, s2, s3, rfl,
                    by simpa using hBne, hS1, hLC, hS2, hL, hS3, rfl, rfl⟩
    | _ => simp only []; intro h; cases h

/-- WS-RR RR2.5: a successful `returnDonatedSchedContext` exposes its three
stores and their inputs — the mirror of `donateSchedContext_walk`, with the
`sc.boundThread = some serverTid` witness RR2.8's guard added. -/
theorem returnDonatedSchedContext_walk
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    ∃ (sc : SchedContext) (ownerTcb serverTcb : TCB) (s1 s2 s3 : SystemState),
      st.objects[scId.toObjId]? = some (.schedContext sc) ∧
      sc.boundThread = some serverTid ∧
      storeObject scId.toObjId
        (.schedContext { sc with boundThread := some originalOwner }) st = .ok ((), s1) ∧
      lookupTcb s1 originalOwner = some ownerTcb ∧
      storeObject originalOwner.toObjId
        (.tcb { ownerTcb with schedContextBinding := .bound scId }) s1 = .ok ((), s2) ∧
      lookupTcb s2 serverTid = some serverTcb ∧
      storeObject serverTid.toObjId
        (.tcb { serverTcb with schedContextBinding := .unbound }) s2 = .ok ((), s3) ∧
      st'.objects = s3.objects ∧ st'.scheduler = s3.scheduler := by
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
        cases hS1 : storeObject scId.toObjId
            (.schedContext { sc with boundThread := some originalOwner }) st with
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
                  exact ⟨sc, ownerTcb, serverTcb, s1, s2, s3, rfl,
                    by simpa using hBne, hS1, hL1, hS2, hL2, hS3, rfl, rfl⟩
    | _ => simp only []; intro h; cases h

-- ============================================================================
-- §2  The derived readings
-- ============================================================================

/-- WS-RR RR2.5: what `donateSchedContext` does to every thread's TCB, pointwise.

The donor's binding is cleared, the donee's becomes `.donated`, every other
thread reads through, and **no other field of any TCB moves** — the two written
TCBs are record updates of their pre-state selves.  `clientTid ≠ serverTid` is a
hypothesis rather than a derived fact: `donateSchedContext` alone does not
exclude a self-donation, but `applyCallDonation` does (its donee must be
`.unbound` and its donor `.bound`), and §3 discharges it there. -/
theorem donateSchedContext_getTcb?_char
    (st st' : SystemState) (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId)
    (hObjInv : st.objects.invExt) (hNe : clientTid ≠ serverTid)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    (∃ clientTcb, st.getTcb? clientTid = some clientTcb ∧
        st'.getTcb? clientTid = some { clientTcb with schedContextBinding := .unbound }) ∧
    (∃ serverTcb, st.getTcb? serverTid = some serverTcb ∧
        st'.getTcb? serverTid = some
          { serverTcb with schedContextBinding := .donated clientScId clientTid }) ∧
    (∀ tid, tid ≠ clientTid → tid ≠ serverTid → st'.getTcb? tid = st.getTcb? tid) := by
  obtain ⟨sc, clientTcb, serverTcb, s1, s2, s3, hSc, _, hS1, hLC, hS2, hLS, hS3, hObjEq, _⟩ :=
    donateSchedContext_walk st st' clientTid serverTid clientScId h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
  have hSc1 : s1.objects[clientScId.toObjId]? =
      some (.schedContext { sc with boundThread := some serverTid }) :=
    storeObject_objects_eq st s1 _ _ hObjInv hS1
  have hClient1 : s1.objects[clientTid.toObjId]? = some (.tcb clientTcb) :=
    lookupTcb_some_objects s1 clientTid clientTcb hLC
  have hNeScClient : clientTid.toObjId ≠ clientScId.toObjId := by
    intro he; rw [he, hSc1] at hClient1; cases hClient1
  have hServer2 : s2.objects[serverTid.toObjId]? = some (.tcb serverTcb) :=
    lookupTcb_some_objects s2 serverTid serverTcb hLS
  have hNeCS : clientTid.toObjId ≠ serverTid.toObjId := by
    intro he; exact hNe (SeLe4n.ThreadId.toObjId_injective _ _ he)
  have hServer1 : s1.objects[serverTid.toObjId]? = some (.tcb serverTcb) := by
    rw [← storeObject_objects_ne s1 s2 clientTid.toObjId serverTid.toObjId _
      (Ne.symm hNeCS) hInv1 hS2]
    exact hServer2
  have hNeScServer : serverTid.toObjId ≠ clientScId.toObjId := by
    intro he; rw [he, hSc1] at hServer1; cases hServer1
  -- Pull both TCBs back past the SchedContext store.
  have hClientPre : st.objects[clientTid.toObjId]? = some (.tcb clientTcb) := by
    rw [← storeObject_objects_ne st s1 clientScId.toObjId clientTid.toObjId _
      hNeScClient hObjInv hS1]
    exact hClient1
  have hServerPre : st.objects[serverTid.toObjId]? = some (.tcb serverTcb) := by
    rw [← storeObject_objects_ne st s1 clientScId.toObjId serverTid.toObjId _
      hNeScServer hObjInv hS1]
    exact hServer1
  -- Push the two written TCBs forward to the final state.
  have hClient3 : s3.objects[clientTid.toObjId]? =
      some (.tcb { clientTcb with schedContextBinding := .unbound }) := by
    rw [storeObject_objects_ne s2 s3 serverTid.toObjId clientTid.toObjId _ hNeCS hInv2 hS3]
    exact storeObject_objects_eq s1 s2 _ _ hInv1 hS2
  have hServer3 : s3.objects[serverTid.toObjId]? =
      some (.tcb { serverTcb with schedContextBinding := .donated clientScId clientTid }) :=
    storeObject_objects_eq s2 s3 _ _ hInv2 hS3
  refine ⟨⟨clientTcb, ?_, ?_⟩, ⟨serverTcb, ?_, ?_⟩, ?_⟩
  · unfold SystemState.getTcb?; rw [hClientPre]
  · unfold SystemState.getTcb?; rw [hObjEq, hClient3]
  · unfold SystemState.getTcb?; rw [hServerPre]
  · unfold SystemState.getTcb?; rw [hObjEq, hServer3]
  · intro tid hNeC hNeS
    have h1 : tid.toObjId ≠ clientTid.toObjId := fun he =>
      hNeC (SeLe4n.ThreadId.toObjId_injective _ _ he)
    have h2 : tid.toObjId ≠ serverTid.toObjId := fun he =>
      hNeS (SeLe4n.ThreadId.toObjId_injective _ _ he)
    unfold SystemState.getTcb?
    rw [hObjEq,
      storeObject_objects_ne s2 s3 serverTid.toObjId tid.toObjId _ h2 hInv2 hS3,
      storeObject_objects_ne s1 s2 clientTid.toObjId tid.toObjId _ h1 hInv1 hS2]
    by_cases hScEq : tid.toObjId = clientScId.toObjId
    · rw [hScEq, hSc1, hSc]
    · rw [storeObject_objects_ne st s1 clientScId.toObjId tid.toObjId _ hScEq hObjInv hS1]

/-- WS-RR RR2.5: the mirror for `returnDonatedSchedContext` — the donee's binding
is cleared, the original owner's becomes `.bound`, everything else reads
through. -/
theorem returnDonatedSchedContext_getTcb?_char
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hNe : originalOwner ≠ serverTid)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    (∃ ownerTcb, st.getTcb? originalOwner = some ownerTcb ∧
        st'.getTcb? originalOwner = some { ownerTcb with schedContextBinding := .bound scId }) ∧
    (∃ serverTcb, st.getTcb? serverTid = some serverTcb ∧
        st'.getTcb? serverTid = some { serverTcb with schedContextBinding := .unbound }) ∧
    (∀ tid, tid ≠ originalOwner → tid ≠ serverTid → st'.getTcb? tid = st.getTcb? tid) := by
  obtain ⟨sc, ownerTcb, serverTcb, s1, s2, s3, hSc, _, hS1, hL1, hS2, hL2, hS3, hObjEq, _⟩ :=
    returnDonatedSchedContext_walk st st' serverTid scId originalOwner h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
  have hSc1 : s1.objects[scId.toObjId]? =
      some (.schedContext { sc with boundThread := some originalOwner }) :=
    storeObject_objects_eq st s1 _ _ hObjInv hS1
  have hOwner1 : s1.objects[originalOwner.toObjId]? = some (.tcb ownerTcb) :=
    lookupTcb_some_objects s1 originalOwner ownerTcb hL1
  have hNeScOwner : originalOwner.toObjId ≠ scId.toObjId := by
    intro he; rw [he, hSc1] at hOwner1; cases hOwner1
  have hServer2 : s2.objects[serverTid.toObjId]? = some (.tcb serverTcb) :=
    lookupTcb_some_objects s2 serverTid serverTcb hL2
  have hNeOS : originalOwner.toObjId ≠ serverTid.toObjId := by
    intro he; exact hNe (SeLe4n.ThreadId.toObjId_injective _ _ he)
  have hServer1 : s1.objects[serverTid.toObjId]? = some (.tcb serverTcb) := by
    rw [← storeObject_objects_ne s1 s2 originalOwner.toObjId serverTid.toObjId _
      (Ne.symm hNeOS) hInv1 hS2]
    exact hServer2
  have hNeScServer : serverTid.toObjId ≠ scId.toObjId := by
    intro he; rw [he, hSc1] at hServer1; cases hServer1
  have hOwnerPre : st.objects[originalOwner.toObjId]? = some (.tcb ownerTcb) := by
    rw [← storeObject_objects_ne st s1 scId.toObjId originalOwner.toObjId _
      hNeScOwner hObjInv hS1]
    exact hOwner1
  have hServerPre : st.objects[serverTid.toObjId]? = some (.tcb serverTcb) := by
    rw [← storeObject_objects_ne st s1 scId.toObjId serverTid.toObjId _
      hNeScServer hObjInv hS1]
    exact hServer1
  have hOwner3 : s3.objects[originalOwner.toObjId]? =
      some (.tcb { ownerTcb with schedContextBinding := .bound scId }) := by
    rw [storeObject_objects_ne s2 s3 serverTid.toObjId originalOwner.toObjId _ hNeOS hInv2 hS3]
    exact storeObject_objects_eq s1 s2 _ _ hInv1 hS2
  have hServer3 : s3.objects[serverTid.toObjId]? =
      some (.tcb { serverTcb with schedContextBinding := .unbound }) :=
    storeObject_objects_eq s2 s3 _ _ hInv2 hS3
  refine ⟨⟨ownerTcb, ?_, ?_⟩, ⟨serverTcb, ?_, ?_⟩, ?_⟩
  · unfold SystemState.getTcb?; rw [hOwnerPre]
  · unfold SystemState.getTcb?; rw [hObjEq, hOwner3]
  · unfold SystemState.getTcb?; rw [hServerPre]
  · unfold SystemState.getTcb?; rw [hObjEq, hServer3]
  · intro tid hNeO hNeS
    have h1 : tid.toObjId ≠ originalOwner.toObjId := fun he =>
      hNeO (SeLe4n.ThreadId.toObjId_injective _ _ he)
    have h2 : tid.toObjId ≠ serverTid.toObjId := fun he =>
      hNeS (SeLe4n.ThreadId.toObjId_injective _ _ he)
    unfold SystemState.getTcb?
    rw [hObjEq,
      storeObject_objects_ne s2 s3 serverTid.toObjId tid.toObjId _ h2 hInv2 hS3,
      storeObject_objects_ne s1 s2 originalOwner.toObjId tid.toObjId _ h1 hInv1 hS2]
    by_cases hScEq : tid.toObjId = scId.toObjId
    · rw [hScEq, hSc1, hSc]
    · rw [storeObject_objects_ne st s1 scId.toObjId tid.toObjId _ hScEq hObjInv hS1]

-- ============================================================================
-- §3  RR2.5 — `applyCallDonation` preserves the donation conjuncts
-- ============================================================================

/-- WS-RR RR2.5: what `callDonationSchedContext? = some scId` witnesses about the
pre-state — the donee is passive and the donor holds exactly that
SchedContext. -/
theorem callDonationSchedContext?_some_char
    (st : SystemState) (caller receiver : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (h : callDonationSchedContext? st caller receiver = some scId) :
    (∃ rTcb, lookupTcb st receiver = some rTcb ∧ rTcb.schedContextBinding = .unbound) ∧
    (∃ cTcb, lookupTcb st caller = some cTcb ∧ cTcb.schedContextBinding = .bound scId) := by
  unfold callDonationSchedContext? at h
  cases hR : lookupTcb st receiver with
  | none => rw [hR] at h; simp at h
  | some rTcb =>
    rw [hR] at h
    simp only [] at h
    cases hRB : rTcb.schedContextBinding with
    | bound _ => rw [hRB] at h; simp at h
    | donated _ _ => rw [hRB] at h; simp at h
    | unbound =>
      rw [hRB] at h
      simp only [] at h
      cases hC : lookupTcb st caller with
      | none => rw [hC] at h; simp at h
      | some cTcb =>
        rw [hC] at h
        simp only [] at h
        cases hCB : cTcb.schedContextBinding with
        | unbound => rw [hCB] at h; simp at h
        | donated _ _ => rw [hCB] at h; simp at h
        | bound scId' =>
          rw [hCB] at h
          simp only [Option.some.injEq] at h
          subst h
          exact ⟨⟨rTcb, rfl, hRB⟩, ⟨cTcb, rfl, hCB⟩⟩

/-- WS-RR RR2.5: a call donation never donates to its own donor.  The donee's
binding is `.unbound` and the donor's is `.bound`, and one TCB cannot be both. -/
theorem callDonationSchedContext?_caller_ne_receiver
    (st : SystemState) (caller receiver : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (h : callDonationSchedContext? st caller receiver = some scId) :
    caller ≠ receiver := by
  obtain ⟨⟨rTcb, hR, hRB⟩, ⟨cTcb, hC, hCB⟩⟩ := callDonationSchedContext?_some_char st caller
    receiver scId h
  intro hEq
  rw [hEq, hR] at hC
  obtain rfl : rTcb = cTcb := Option.some.inj hC
  rw [hRB] at hCB
  cases hCB

/-- **WS-RR RR2.5**: the call donation preserves `donationOwnerValid`.

The new donation the transition creates — the donee holding `.donated scId
caller` — satisfies both clauses by construction: the SchedContext is rebound to
the donee (`donateSchedContext_post_boundThread`), and the donor is left
`.unbound` and, by hypothesis, blocked awaiting the reply.  Every *pre-existing*
donation survives because neither of the two threads the transition rewrites can
be one of its readings: the donated SchedContext cannot be `scId` (the pre-state
`sc.boundThread` is the donor, and the donor is not the donation's subject), and
the owner cannot be the donor (an owner is `.unbound`, the donor is `.bound`) or
the donee (`hReceiverNotOwner`).

`hCallerBlockedOnReply` and `hReceiverNotOwner` are exactly what the live `.call`
rendezvous establishes: it stores the caller `.blockedOnReply` before the
donation runs, and it wakes the receiver to `.ready`, which `donationOwnerValid`
forbids a donation owner from being. -/
theorem applyCallDonation_preserves_donationOwnerValid
    (st st' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (hObjInv : st.objects.invExt)
    (hDOV : donationOwnerValid st)
    (hCallerBlockedOnReply : ∀ tcb, st.getTcb? callerVtid.val = some tcb →
        ∃ ep rt, tcb.ipcState = .blockedOnReply ep rt)
    (hReceiverNotOwner : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
        st.getTcb? tid = some tcb → tcb.schedContextBinding ≠ .donated scId receiverVtid.val)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    donationOwnerValid st' := by
  rw [applyCallDonation_characterisation] at h
  cases hSc : callDonationSchedContext? st callerVtid.val receiverVtid.val with
  | none => rw [hSc] at h; cases h; exact hDOV
  | some scId =>
    rw [hSc] at h
    obtain ⟨⟨rTcb, hR, hRB⟩, ⟨cTcb, hC, hCB⟩⟩ :=
      callDonationSchedContext?_some_char st callerVtid.val receiverVtid.val scId hSc
    have hNe := callDonationSchedContext?_caller_ne_receiver st callerVtid.val receiverVtid.val
      scId hSc
    obtain ⟨⟨cTcb0, hCPre, hCPost⟩, ⟨rTcb0, hRPre, hRPost⟩, hOther⟩ :=
      donateSchedContext_getTcb?_char st st' callerVtid.val receiverVtid.val scId hObjInv hNe h
    obtain ⟨scPost, hScPost, hScPostBound⟩ :=
      donateSchedContext_post_boundThread st st' callerVtid.val receiverVtid.val scId hObjInv h
    obtain ⟨scPre, hScPreRaw, hScPreBound⟩ :=
      donateSchedContext_ok_implies_sc_bound st st' callerVtid.val receiverVtid.val scId h
    have hScNe : ∀ scId', scId' ≠ scId →
        st'.getSchedContext? scId' = st.getSchedContext? scId' := fun scId' hne =>
      donateSchedContext_getSchedContext?_ne st st' callerVtid.val receiverVtid.val scId scId'
        hne hObjInv h
    -- The donor's TCB, as read by the characterisation, is the one the guard saw.
    have hCEq : cTcb0 = cTcb := by
      have := hCPre.symm.trans (getTcb?_of_lookupTcb st callerVtid.val cTcb hC)
      exact Option.some.inj this
    have hREq : rTcb0 = rTcb := by
      have := hRPre.symm.trans (getTcb?_of_lookupTcb st receiverVtid.val rTcb hR)
      exact Option.some.inj this
    rw [hCEq] at hCPre hCPost
    rw [hREq] at hRPre hRPost
    intro tid tcb' scId' owner' hTcb' hBind'
    by_cases hTidR : tid = receiverVtid.val
    · -- The new donation.
      have hEq : tcb' = { rTcb with schedContextBinding := .donated scId callerVtid.val } := by
        have hx := hRPost.symm.trans
          ((getTcb?_eq_some_iff st' receiverVtid.val tcb').mpr (hTidR ▸ hTcb'))
        exact (Option.some.inj hx).symm
      rw [hEq] at hBind'
      simp only [] at hBind'
      obtain ⟨hScEq, hOwnEq⟩ := SchedContextBinding.donated.inj hBind'
      subst hScEq; subst hOwnEq
      refine ⟨⟨scPost, (getSchedContext?_eq_some_iff st' scId scPost).mp hScPost,
        by rw [hTidR]; exact hScPostBound⟩, ?_⟩
      obtain ⟨ep, rt, hIpc⟩ := hCallerBlockedOnReply cTcb hCPre
      exact ⟨{ cTcb with schedContextBinding := .unbound },
        (getTcb?_eq_some_iff st' callerVtid.val _).mp hCPost, rfl, ⟨ep, rt, hIpc⟩⟩
    · by_cases hTidC : tid = callerVtid.val
      · -- The donor is left `.unbound`, so it is not a donation.
        have hEq : tcb' = { cTcb with schedContextBinding := .unbound } := by
          have hx := hCPost.symm.trans
            ((getTcb?_eq_some_iff st' callerVtid.val tcb').mpr (hTidC ▸ hTcb'))
          exact (Option.some.inj hx).symm
        rw [hEq] at hBind'
        simp only [] at hBind'
        cases hBind'
      · -- An untouched donation.
        have hPre : st.getTcb? tid = some tcb' := by
          rw [← hOther tid hTidC hTidR]
          exact (getTcb?_eq_some_iff st' tid tcb').mpr hTcb'
        obtain ⟨⟨scOld, hScOld, hScOldBound⟩, ownerTcb, hOwner, hOwnerUnbound, hOwnerBlk⟩ :=
          hDOV tid tcb' scId' owner' ((getTcb?_eq_some_iff st tid tcb').mp hPre) hBind'
        have hScId'Ne : scId' ≠ scId := by
          intro hEq; subst hEq
          rw [hScPreRaw] at hScOld
          obtain rfl : scPre = scOld := KernelObject.schedContext.inj (Option.some.inj hScOld)
          rw [hScPreBound] at hScOldBound
          exact hTidC (Option.some.inj hScOldBound).symm
        have hOwnerNeC : owner' ≠ callerVtid.val := by
          intro hEq
          rw [hEq] at hOwner
          have hSame := hCPre.symm.trans
            ((getTcb?_eq_some_iff st callerVtid.val ownerTcb).mpr hOwner)
          obtain rfl : cTcb = ownerTcb := Option.some.inj hSame
          rw [hCB] at hOwnerUnbound
          cases hOwnerUnbound
        have hOwnerNeR : owner' ≠ receiverVtid.val := by
          intro hEq
          rw [hEq] at hBind'
          exact hReceiverNotOwner tid tcb' scId' hPre hBind'
        refine ⟨⟨scOld, ?_, hScOldBound⟩, ownerTcb, ?_, hOwnerUnbound, hOwnerBlk⟩
        · have hScT : st.getSchedContext? scId' = some scOld :=
            (getSchedContext?_eq_some_iff st scId' scOld).mpr hScOld
          exact (getSchedContext?_eq_some_iff st' scId' scOld).mp
            ((hScNe scId' hScId'Ne).trans hScT)
        · have hOwnerT : st.getTcb? owner' = some ownerTcb :=
            (getTcb?_eq_some_iff st owner' ownerTcb).mpr hOwner
          rw [← hOther owner' hOwnerNeC hOwnerNeR] at hOwnerT
          exact (getTcb?_eq_some_iff st' owner' ownerTcb).mp hOwnerT

/-- WS-RR RR2.5: everything a *donating* `applyCallDonation` establishes, in one
place, so each conjunct below is a three-way case split on the thread rather than
a re-derivation of the store walk. -/
theorem applyCallDonation_donating_char
    (st st' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (scId : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt)
    (hSc : callDonationSchedContext? st callerVtid.val receiverVtid.val = some scId)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    ∃ cTcb rTcb,
      callerVtid.val ≠ receiverVtid.val ∧
      st.getTcb? callerVtid.val = some cTcb ∧ cTcb.schedContextBinding = .bound scId ∧
      st.getTcb? receiverVtid.val = some rTcb ∧ rTcb.schedContextBinding = .unbound ∧
      st'.getTcb? callerVtid.val = some { cTcb with schedContextBinding := .unbound } ∧
      st'.getTcb? receiverVtid.val =
        some { rTcb with schedContextBinding := .donated scId callerVtid.val } ∧
      (∀ tid, tid ≠ callerVtid.val → tid ≠ receiverVtid.val →
        st'.getTcb? tid = st.getTcb? tid) ∧
      (∃ scPost, st'.getSchedContext? scId = some scPost ∧
        scPost.boundThread = some receiverVtid.val) ∧
      (∃ scPre, st.getSchedContext? scId = some scPre ∧
        scPre.boundThread = some callerVtid.val) ∧
      (∀ scId', scId' ≠ scId → st'.getSchedContext? scId' = st.getSchedContext? scId') := by
  rw [applyCallDonation_characterisation, hSc] at h
  obtain ⟨⟨rTcb, hR, hRB⟩, ⟨cTcb, hC, hCB⟩⟩ :=
    callDonationSchedContext?_some_char st callerVtid.val receiverVtid.val scId hSc
  have hNe := callDonationSchedContext?_caller_ne_receiver st callerVtid.val receiverVtid.val
    scId hSc
  obtain ⟨⟨cTcb0, hCPre, hCPost⟩, ⟨rTcb0, hRPre, hRPost⟩, hOther⟩ :=
    donateSchedContext_getTcb?_char st st' callerVtid.val receiverVtid.val scId hObjInv hNe h
  have hCEq : cTcb0 = cTcb :=
    Option.some.inj (hCPre.symm.trans (getTcb?_of_lookupTcb st callerVtid.val cTcb hC))
  have hREq : rTcb0 = rTcb :=
    Option.some.inj (hRPre.symm.trans (getTcb?_of_lookupTcb st receiverVtid.val rTcb hR))
  rw [hCEq] at hCPre hCPost
  rw [hREq] at hRPre hRPost
  obtain ⟨scPre, hScPreRaw, hScPreBound⟩ :=
    donateSchedContext_ok_implies_sc_bound st st' callerVtid.val receiverVtid.val scId h
  exact ⟨cTcb, rTcb, hNe, hCPre, hCB, hRPre, hRB, hCPost, hRPost, hOther,
    donateSchedContext_post_boundThread st st' callerVtid.val receiverVtid.val scId hObjInv h,
    ⟨scPre, (getSchedContext?_eq_some_iff st scId scPre).mpr hScPreRaw, hScPreBound⟩,
    fun scId' hne => donateSchedContext_getSchedContext?_ne st st' callerVtid.val
      receiverVtid.val scId scId' hne hObjInv h⟩

/-- WS-RR RR2.5: a *donating* `applyCallDonation` rewrites exactly two bindings —
the donor to `.unbound`, the donee to `.donated` — and reads every other thread
through.  This is the case split the remaining donation conjuncts run on. -/
theorem applyCallDonation_donating_binding
    (st st' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (scId : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt)
    (hSc : callDonationSchedContext? st callerVtid.val receiverVtid.val = some scId)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st')
    (tid : SeLe4n.ThreadId) (tcb' : TCB) (hTcb' : st'.getTcb? tid = some tcb') :
    (tid = callerVtid.val ∧ tcb'.schedContextBinding = .unbound) ∨
    (tid = receiverVtid.val ∧
      tcb'.schedContextBinding = .donated scId callerVtid.val) ∨
    (tid ≠ callerVtid.val ∧ tid ≠ receiverVtid.val ∧ st.getTcb? tid = some tcb') := by
  obtain ⟨cTcb, rTcb, _, _, _, _, _, hCPost, hRPost, hOther, _⟩ :=
    applyCallDonation_donating_char st st' callerVtid receiverVtid scId hObjInv hSc h
  by_cases hCid : tid = callerVtid.val
  · rw [hCid] at hTcb'
    have hEq : { cTcb with schedContextBinding := .unbound } = tcb' :=
      Option.some.inj (hCPost.symm.trans hTcb')
    exact Or.inl ⟨hCid, by rw [← hEq]⟩
  · by_cases hRid : tid = receiverVtid.val
    · rw [hRid] at hTcb'
      have hEq : { rTcb with schedContextBinding := .donated scId callerVtid.val } = tcb' :=
        Option.some.inj (hRPost.symm.trans hTcb')
      exact Or.inr (Or.inl ⟨hRid, by rw [← hEq]⟩)
    · exact Or.inr (Or.inr ⟨hCid, hRid, (hOther tid hCid hRid) ▸ hTcb'⟩)

/-- **WS-RR RR2.5**: the call donation preserves `donationOwnerUnique`.

The only donation it creates is the donee's, whose owner is the donor.  No
*other* thread can already name the donor as its owner: `donationOwnerValid`
would then force the donor `.unbound`, and the guard saw it `.bound`. -/
theorem applyCallDonation_preserves_donationOwnerUnique
    (st st' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (hObjInv : st.objects.invExt)
    (hDOV : donationOwnerValid st) (hDOU : donationOwnerUnique st)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    donationOwnerUnique st' := by
  cases hSc : callDonationSchedContext? st callerVtid.val receiverVtid.val with
  | none =>
      rw [applyCallDonation_characterisation, hSc] at h; cases h; exact hDOU
  | some scId =>
    obtain ⟨cTcb, _, _, hCPre, hCB, _⟩ :=
      applyCallDonation_donating_char st st' callerVtid receiverVtid scId hObjInv hSc h
    -- No pre-state donation can name the donor as its owner.
    have hNoOwner : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (s : SeLe4n.SchedContextId),
        st.getTcb? tid = some tcb → tcb.schedContextBinding ≠ .donated s callerVtid.val := by
      intro tid tcb s hTcb hBind
      obtain ⟨_, ownerTcb, hOwner, hOwnerUnbound, _⟩ :=
        hDOV tid tcb s callerVtid.val ((getTcb?_eq_some_iff st tid tcb).mp hTcb) hBind
      have hSame : some cTcb = some ownerTcb :=
        hCPre.symm.trans ((getTcb?_eq_some_iff st callerVtid.val ownerTcb).mpr hOwner)
      rw [← Option.some.inj hSame, hCB] at hOwnerUnbound
      cases hOwnerUnbound
    intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner h1 h2 hB1 hB2
    have hT1 : st'.getTcb? tid1 = some tcb1 := (getTcb?_eq_some_iff st' tid1 tcb1).mpr h1
    have hT2 : st'.getTcb? tid2 = some tcb2 := (getTcb?_eq_some_iff st' tid2 tcb2).mpr h2
    rcases applyCallDonation_donating_binding st st' callerVtid receiverVtid scId hObjInv hSc h
      tid1 tcb1 hT1 with ⟨_, hU⟩ | ⟨hR1, hD1⟩ | ⟨_, _, hPre1⟩
    · rw [hU] at hB1; cases hB1
    · rcases applyCallDonation_donating_binding st st' callerVtid receiverVtid scId hObjInv hSc h
        tid2 tcb2 hT2 with ⟨_, hU⟩ | ⟨hR2, _⟩ | ⟨_, _, hPre2⟩
      · rw [hU] at hB2; cases hB2
      · rw [hR1, hR2]
      · -- `tid1` is the donee, so `owner` is the donor, which nothing else owns.
        rw [hD1] at hB1
        obtain ⟨_, hOwnEq⟩ := SchedContextBinding.donated.inj hB1
        rw [← hOwnEq] at hB2
        exact absurd hB2 (hNoOwner tid2 tcb2 scId2 hPre2)
    · rcases applyCallDonation_donating_binding st st' callerVtid receiverVtid scId hObjInv hSc h
        tid2 tcb2 hT2 with ⟨_, hU⟩ | ⟨_, hD2⟩ | ⟨_, _, hPre2⟩
      · rw [hU] at hB2; cases hB2
      · rw [hD2] at hB2
        obtain ⟨_, hOwnEq⟩ := SchedContextBinding.donated.inj hB2
        rw [← hOwnEq] at hB1
        exact absurd hB1 (hNoOwner tid1 tcb1 scId1 hPre1)
      · exact hDOU tid1 tid2 tcb1 tcb2 scId1 scId2 owner
          ((getTcb?_eq_some_iff st tid1 tcb1).mp hPre1)
          ((getTcb?_eq_some_iff st tid2 tcb2).mp hPre2) hB1 hB2

/-- **WS-RR RR2.5**: the call donation preserves `donationBudgetTransfer`.

The transition moves the SchedContext's *only* reference from the donor's
`.bound` to the donee's `.donated`; the donor is left holding none.  A second
holder of that SchedContext in the post-state would have been a second holder in
the pre-state alongside the donor, which the pre-state conjunct forbids. -/
theorem applyCallDonation_preserves_donationBudgetTransfer
    (st st' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (hObjInv : st.objects.invExt)
    (hDBT : donationBudgetTransfer st)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    donationBudgetTransfer st' := by
  cases hSc : callDonationSchedContext? st callerVtid.val receiverVtid.val with
  | none =>
      rw [applyCallDonation_characterisation, hSc] at h; cases h; exact hDBT
  | some scId =>
    obtain ⟨cTcb, _, _, hCPre, hCB, _⟩ :=
      applyCallDonation_donating_char st st' callerVtid receiverVtid scId hObjInv hSc h
    have hCScId : cTcb.schedContextBinding.scId? = some scId := by rw [hCB]; rfl
    have hCObj : st.objects[callerVtid.val.toObjId]? = some (.tcb cTcb) :=
      (getTcb?_eq_some_iff st callerVtid.val cTcb).mp hCPre
    intro tid1 tid2 tcb1 tcb2 s h1 h2 hNe hS1 hS2
    have hT1 : st'.getTcb? tid1 = some tcb1 := (getTcb?_eq_some_iff st' tid1 tcb1).mpr h1
    have hT2 : st'.getTcb? tid2 = some tcb2 := (getTcb?_eq_some_iff st' tid2 tcb2).mpr h2
    -- A post-state holder is either the donee (holding `scId`) or an untouched
    -- thread holding exactly what it held before; the donor holds nothing.
    have hClassify : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st'.getTcb? tid = some tcb →
        tcb.schedContextBinding.scId? = some s →
        (tid = receiverVtid.val ∧ s = scId) ∨
        (tid ≠ callerVtid.val ∧ tid ≠ receiverVtid.val ∧ st.getTcb? tid = some tcb) := by
      intro tid tcb hTcb hHold
      rcases applyCallDonation_donating_binding st st' callerVtid receiverVtid scId hObjInv hSc h
        tid tcb hTcb with ⟨_, hU⟩ | ⟨hRid, hD⟩ | rest
      · rw [hU] at hHold; cases hHold
      · rw [hD] at hHold
        exact Or.inl ⟨hRid, (Option.some.inj hHold).symm⟩
      · exact Or.inr rest
    rcases hClassify tid1 tcb1 hT1 hS1 with ⟨hR1, hSEq⟩ | ⟨hC1, _, hPre1⟩
    · rcases hClassify tid2 tcb2 hT2 hS2 with ⟨hR2, _⟩ | ⟨hC2, _, hPre2⟩
      · exact hNe (hR1.trans hR2.symm)
      · rw [hSEq] at hS2
        exact hDBT tid2 callerVtid.val tcb2 cTcb scId
          ((getTcb?_eq_some_iff st tid2 tcb2).mp hPre2) hCObj hC2 hS2 hCScId
    · rcases hClassify tid2 tcb2 hT2 hS2 with ⟨_, hSEq⟩ | ⟨hC2, _, hPre2⟩
      · rw [hSEq] at hS1
        exact hDBT tid1 callerVtid.val tcb1 cTcb scId
          ((getTcb?_eq_some_iff st tid1 tcb1).mp hPre1) hCObj hC1 hS1 hCScId
      · exact hDBT tid1 tid2 tcb1 tcb2 s
          ((getTcb?_eq_some_iff st tid1 tcb1).mp hPre1)
          ((getTcb?_eq_some_iff st tid2 tcb2).mp hPre2) hNe hS1 hS2

/-- **WS-RR RR2.5**: the call donation preserves `passiveServerIdle`.

It leaves the scheduler alone, so the only new obligation is the donor, which the
transition makes `.unbound` — and the same `hCallerBlockedOnReply` that
`donationOwnerValid` needs puts it in `.blockedOnReply`, an allowed passive
state.  The donee moves *out* of `.unbound`, discharging its obligation. -/
theorem applyCallDonation_preserves_passiveServerIdle
    (st st' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (hObjInv : st.objects.invExt)
    (hPSI : passiveServerIdle st)
    (hCallerBlockedOnReply : ∀ tcb, st.getTcb? callerVtid.val = some tcb →
        ∃ ep rt, tcb.ipcState = .blockedOnReply ep rt)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    passiveServerIdle st' := by
  have hSched := applyCallDonation_scheduler_eq st callerVtid receiverVtid st' h
  cases hSc : callDonationSchedContext? st callerVtid.val receiverVtid.val with
  | none =>
      rw [applyCallDonation_characterisation, hSc] at h; cases h; exact hPSI
  | some scId =>
    obtain ⟨cTcb, rTcb, _, hCPre, _, _, _, hCPost, hRPost, hOther, _⟩ :=
      applyCallDonation_donating_char st st' callerVtid receiverVtid scId hObjInv hSc h
    intro tid tcb' hTcb' hUnbound hNotInQ hNotCur
    have hT : st'.getTcb? tid = some tcb' := (getTcb?_eq_some_iff st' tid tcb').mpr hTcb'
    by_cases hCid : tid = callerVtid.val
    · -- The donor: `ipcState` is untouched, and it is blocked awaiting the reply.
      rw [hCid] at hT
      have hEq : { cTcb with schedContextBinding := .unbound } = tcb' :=
        Option.some.inj (hCPost.symm.trans hT)
      obtain ⟨ep, rt, hIpcC⟩ := hCallerBlockedOnReply cTcb hCPre
      exact Or.inr (Or.inr ⟨ep, rt, by rw [← hEq]; exact hIpcC⟩)
    · by_cases hRid : tid = receiverVtid.val
      · -- The donee is no longer `.unbound`, so it carries no obligation.
        rw [hRid] at hT
        have hEq : { rTcb with schedContextBinding := .donated scId callerVtid.val } = tcb' :=
          Option.some.inj (hRPost.symm.trans hT)
        rw [← hEq] at hUnbound
        cases hUnbound
      · rw [hSched] at hNotInQ hNotCur
        have hPre : st.getTcb? tid = some tcb' := (hOther tid hCid hRid) ▸ hT
        exact hPSI tid tcb' ((getTcb?_eq_some_iff st tid tcb').mp hPre) hUnbound hNotInQ hNotCur

-- ============================================================================
-- §4  The non-donation split
-- ============================================================================

/-- WS-RR RR2.5: the object-store relation a donation primitive establishes,
stated over exactly the readings the fifteen non-donation conjuncts make.

Every TCB is its counterpart up to `schedContextBinding`; every non-TCB,
non-SchedContext object is identical; and SchedContexts exist in lockstep (their
*values* may differ — the rebinding moves `boundThread` — but only
`donationOwnerValid`, which is not among the fifteen, reads that). -/
structure donationReadAgreement (st st' : SystemState) : Prop where
  /-- a post-state TCB is its pre-state self up to the binding -/
  tcbBwd : ∀ (oid : SeLe4n.ObjId) (tx : TCB), st'.objects[oid]? = some (.tcb tx) →
    ∃ ty, st.objects[oid]? = some (.tcb ty) ∧
      tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
      tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
      tx.queuePPrev = ty.queuePPrev ∧
      tx.timeoutBudget = ty.timeoutBudget ∧ tx.replyObject = ty.replyObject ∧
      tx.pendingReceiveReply = ty.pendingReceiveReply
  /-- and conversely -/
  tcbFwd : ∀ (oid : SeLe4n.ObjId) (ty : TCB), st.objects[oid]? = some (.tcb ty) →
    ∃ tx, st'.objects[oid]? = some (.tcb tx) ∧
      tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
      tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
      tx.queuePPrev = ty.queuePPrev ∧
      tx.timeoutBudget = ty.timeoutBudget ∧ tx.replyObject = ty.replyObject ∧
      tx.pendingReceiveReply = ty.pendingReceiveReply
  /-- endpoints, notifications, replies, CNodes and untypeds are identical -/
  otherKind : ∀ (oid : SeLe4n.ObjId) (k : KernelObject),
    (∀ t, k ≠ .tcb t) → (∀ sc, k ≠ .schedContext sc) →
    (st'.objects[oid]? = some k ↔ st.objects[oid]? = some k)
  /-- a SchedContext that existed still exists -/
  scExists : ∀ (oid : SeLe4n.ObjId) (sc : SchedContext),
    st.objects[oid]? = some (.schedContext sc) →
    ∃ sc', st'.objects[oid]? = some (.schedContext sc')

namespace donationReadAgreement

/-- Reflexivity — a state agrees with itself. -/
theorem refl (st : SystemState) : donationReadAgreement st st :=
  ⟨fun _ tx h => ⟨tx, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   fun _ ty h => ⟨ty, h, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
   fun _ _ _ _ => Iff.rfl,
   fun _ sc h => ⟨sc, h⟩⟩

/-- Transitivity — chain two donation stores. -/
theorem trans {st st' st'' : SystemState}
    (h1 : donationReadAgreement st st') (h2 : donationReadAgreement st' st'') :
    donationReadAgreement st st'' where
  tcbBwd := by
    intro oid tx hx
    obtain ⟨ty, hy, e1, e2, e3, e4, e5, e6, e7, e8⟩ := h2.tcbBwd oid tx hx
    obtain ⟨tz, hz, f1, f2, f3, f4, f5, f6, f7, f8⟩ := h1.tcbBwd oid ty hy
    exact ⟨tz, hz, e1.trans f1, e2.trans f2, e3.trans f3, e4.trans f4, e5.trans f5,
      e6.trans f6, e7.trans f7, e8.trans f8⟩
  tcbFwd := by
    intro oid ty hy
    obtain ⟨tx, hx, e1, e2, e3, e4, e5, e6, e7, e8⟩ := h1.tcbFwd oid ty hy
    obtain ⟨tz, hz, f1, f2, f3, f4, f5, f6, f7, f8⟩ := h2.tcbFwd oid tx hx
    exact ⟨tz, hz, f1.trans e1, f2.trans e2, f3.trans e3, f4.trans e4, f5.trans e5,
      f6.trans e6, f7.trans e7, f8.trans e8⟩
  otherKind := fun oid k hk hsc => (h2.otherKind oid k hk hsc).trans (h1.otherKind oid k hk hsc)
  scExists := by
    intro oid sc h
    obtain ⟨sc', h'⟩ := h1.scExists oid sc h
    exact h2.scExists oid sc' h'

end donationReadAgreement

/-- WS-RR RR2.5: a `storeObject` replacing one SchedContext with another
establishes the read agreement — no TCB moves and no other kind of object
moves. -/
theorem donationReadAgreement_of_schedContextStore
    (st st' : SystemState) (scKey : SeLe4n.ObjId) (scOld scNew : SchedContext)
    (hPre : st.objects[scKey]? = some (.schedContext scOld))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject scKey (.schedContext scNew) st = .ok ((), st')) :
    donationReadAgreement st st' := by
  have hAt := storeObject_objects_eq st st' scKey _ hObjInv hStore
  have hNe : ∀ (oid : SeLe4n.ObjId), oid ≠ scKey → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' scKey oid _ h hObjInv hStore
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro oid tx hx
    by_cases hEq : oid = scKey
    · rw [hEq, hAt] at hx; cases hx
    · rw [hNe oid hEq] at hx; exact ⟨tx, hx, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro oid ty hy
    by_cases hEq : oid = scKey
    · rw [hEq, hPre] at hy; cases hy
    · exact ⟨ty, by rw [hNe oid hEq]; exact hy, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro oid k _ hsc
    by_cases hEq : oid = scKey
    · subst hEq
      rw [hAt, hPre]
      constructor
      · intro h; exact absurd (Option.some.inj h).symm (hsc scNew)
      · intro h; exact absurd (Option.some.inj h).symm (hsc scOld)
    · rw [hNe oid hEq]
  · intro oid sc h
    by_cases hEq : oid = scKey
    · exact ⟨scNew, by rw [hEq, hAt]⟩
    · exact ⟨sc, by rw [hNe oid hEq]; exact h⟩

/-- WS-RR RR2.5: a `storeObject` replacing one TCB with another that differs
**only** in `schedContextBinding` establishes the read agreement. -/
theorem donationReadAgreement_of_tcbBindingStore
    (st st' : SystemState) (tcbKey : SeLe4n.ObjId) (oldTcb : TCB)
    (b : SchedContextBinding)
    (hPre : st.objects[tcbKey]? = some (.tcb oldTcb))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject tcbKey (.tcb { oldTcb with schedContextBinding := b }) st
      = .ok ((), st')) :
    donationReadAgreement st st' := by
  have hAt := storeObject_objects_eq st st' tcbKey _ hObjInv hStore
  have hNe : ∀ (oid : SeLe4n.ObjId), oid ≠ tcbKey → st'.objects[oid]? = st.objects[oid]? :=
    fun oid h => storeObject_objects_ne st st' tcbKey oid _ h hObjInv hStore
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro oid tx hx
    by_cases hEq : oid = tcbKey
    · rw [hEq, hAt] at hx
      obtain rfl : { oldTcb with schedContextBinding := b } = tx := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hx
      exact ⟨oldTcb, by rw [hEq]; exact hPre, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · rw [hNe oid hEq] at hx; exact ⟨tx, hx, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro oid ty hy
    by_cases hEq : oid = tcbKey
    · rw [hEq, hPre] at hy
      obtain rfl : oldTcb = ty := by
        simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hy
      exact ⟨{ oldTcb with schedContextBinding := b }, by rw [hEq]; exact hAt,
        rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · exact ⟨ty, by rw [hNe oid hEq]; exact hy, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · intro oid k hk _
    by_cases hEq : oid = tcbKey
    · subst hEq
      rw [hAt, hPre]
      constructor
      · intro h; exact absurd (Option.some.inj h).symm (hk _)
      · intro h; exact absurd (Option.some.inj h).symm (hk oldTcb)
    · rw [hNe oid hEq]
  · intro oid sc h
    by_cases hEq : oid = tcbKey
    · rw [hEq, hPre] at h; cases h
    · exact ⟨sc, by rw [hNe oid hEq]; exact h⟩


/-- WS-RR RR2.5: a state that shares an object store with one that agrees, agrees.
`donationReadAgreement` reads nothing but `objects`, and the primitives' walk
lemmas expose `st'.objects = s3.objects` rather than `st' = s3`. -/
theorem donationReadAgreement_of_objects_eq {st s s' : SystemState}
    (hObjs : s'.objects = s.objects) (h : donationReadAgreement st s) :
    donationReadAgreement st s' where
  tcbBwd := fun oid tx hx => h.tcbBwd oid tx (by rw [← hObjs]; exact hx)
  tcbFwd := fun oid ty hy => by
    obtain ⟨tx, hx, rest⟩ := h.tcbFwd oid ty hy
    exact ⟨tx, by rw [hObjs]; exact hx, rest⟩
  otherKind := fun oid k hk hsc => by rw [hObjs]; exact h.otherKind oid k hk hsc
  scExists := fun oid sc hSc => by
    obtain ⟨sc', hSc'⟩ := h.scExists oid sc hSc
    exact ⟨sc', by rw [hObjs]; exact hSc'⟩

/-- WS-RR RR2.5: `donateSchedContext` establishes the read agreement — its three
stores are one SchedContext rebinding and two binding-only TCB updates, and the
agreement is closed under composition. -/
theorem donateSchedContext_donationReadAgreement
    (st st' : SystemState) (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId) (hObjInv : st.objects.invExt)
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    donationReadAgreement st st' := by
  obtain ⟨sc, clientTcb, serverTcb, s1, s2, s3, hSc, _, hS1, hLC, hS2, hLS, hS3, hObjEq, _⟩ :=
    donateSchedContext_walk st st' clientTid serverTid clientScId h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
  have a1 : donationReadAgreement st s1 :=
    donationReadAgreement_of_schedContextStore st s1 clientScId.toObjId sc _ hSc hObjInv hS1
  have a2 : donationReadAgreement s1 s2 :=
    donationReadAgreement_of_tcbBindingStore s1 s2 clientTid.toObjId clientTcb .unbound
      (lookupTcb_some_objects s1 clientTid clientTcb hLC) hInv1 hS2
  have a3 : donationReadAgreement s2 s3 :=
    donationReadAgreement_of_tcbBindingStore s2 s3 serverTid.toObjId serverTcb
      (.donated clientScId clientTid)
      (lookupTcb_some_objects s2 serverTid serverTcb hLS) hInv2 hS3
  exact donationReadAgreement_of_objects_eq hObjEq
    ((a1.trans a2).trans a3)

/-- WS-RR RR2.5: `returnDonatedSchedContext` establishes the read agreement — the
mirror of `donateSchedContext_donationReadAgreement`. -/
theorem returnDonatedSchedContext_donationReadAgreement
    (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    donationReadAgreement st st' := by
  obtain ⟨sc, ownerTcb, serverTcb, s1, s2, s3, hSc, _, hS1, hL1, hS2, hL2, hS3, hObjEq, _⟩ :=
    returnDonatedSchedContext_walk st st' serverTid scId originalOwner h
  have hInv1 : s1.objects.invExt := storeObject_preserves_objects_invExt st s1 _ _ hObjInv hS1
  have hInv2 : s2.objects.invExt := storeObject_preserves_objects_invExt s1 s2 _ _ hInv1 hS2
  have a1 : donationReadAgreement st s1 :=
    donationReadAgreement_of_schedContextStore st s1 scId.toObjId sc _ hSc hObjInv hS1
  have a2 : donationReadAgreement s1 s2 :=
    donationReadAgreement_of_tcbBindingStore s1 s2 originalOwner.toObjId ownerTcb (.bound scId)
      (lookupTcb_some_objects s1 originalOwner ownerTcb hL1) hInv1 hS2
  have a3 : donationReadAgreement s2 s3 :=
    donationReadAgreement_of_tcbBindingStore s2 s3 serverTid.toObjId serverTcb .unbound
      (lookupTcb_some_objects s2 serverTid serverTcb hL2) hInv2 hS3
  exact donationReadAgreement_of_objects_eq hObjEq
    ((a1.trans a2).trans a3)

-- ============================================================================
-- §5  The bundle transports across a read agreement
-- ============================================================================

/-- WS-RR RR2.5: the fifteen `ipcInvariantFull` conjuncts that read no
`schedContextBinding` transport across a `donationReadAgreement`; the five that
do — `donationChainAcyclic`, `donationOwnerValid`, `passiveServerIdle`,
`donationBudgetTransfer`, `donationOwnerUnique` — are supplied on the post-state,
where §6/§7 prove them from the primitives' own characterisations.

The eleven structural ones come from `ipcInvariantCore_of_nonBindingAgreements`;
the four the core does not carry (`replyCallerLinkage`,
`pendingReceiveReplyWellFormed`, `endpointQueueTailBlockedConsistent`,
`queueNextTargetBlocked`) are discharged here, each reading only fields the
agreement pins (`replyObject`, `pendingReceiveReply`, `ipcState`, `queueNext`)
and object kinds it frames (`.reply`, `.endpoint`). -/
theorem ipcInvariantFull_of_donationReadAgreement
    (st st' : SystemState) (hInv : ipcInvariantFull st)
    (hAgree : donationReadAgreement st st')
    (hAcyclic : donationChainAcyclic st') (hOwnerValid : donationOwnerValid st')
    (hPassiveIdle : passiveServerIdle st') (hBudgetTransfer : donationBudgetTransfer st')
    (hOwnerUnique : donationOwnerUnique st') :
    ipcInvariantFull st' := by
  obtain ⟨hBwd, hFwd, hNT, hSC⟩ := hAgree
  -- The core driver reads a strictly narrower agreement than the one above.
  have hCore : ipcInvariantCore st' := by
    refine ipcInvariantCore_of_nonBindingAgreements st st' hInv.toCore hNT hSC
      (fun s tx h => ?_) (fun s ty h => ?_)
      hAcyclic hOwnerValid hPassiveIdle hBudgetTransfer
    · obtain ⟨ty, h1, e1, e2, e3, e4, e5, e6, _, _⟩ := hBwd s tx h
      exact ⟨ty, h1, e1, e2, e3, e4, e5, e6⟩
    · obtain ⟨tx, h1, e1, e2, e3, e4, e5, e6, _, _⟩ := hFwd s ty h
      exact ⟨tx, h1, e1, e2, e3, e4, e5, e6⟩
  refine ipcInvariantFull_of_core_replyCallerLinkage hCore ⟨⟨?_, ?_⟩, ?_⟩ ⟨?_, ?_⟩ hOwnerUnique
    ?_ ?_
  -- 16a. replyCallerLinkageReciprocal, TCB → Reply.
  · intro tid tcb rid hTcb hReplyObj
    obtain ⟨ty, hTy, _, _, _, _, _, _, hRO, _⟩ := hBwd tid.toObjId tcb hTcb
    obtain ⟨r, hR, hCaller⟩ :=
      hInv.replyCallerLinkage.1.1 tid ty rid hTy (hRO ▸ hReplyObj)
    exact ⟨r, (hNT rid.toObjId (.reply r) (fun _ => by exact KernelObject.noConfusion)
      (fun _ => by exact KernelObject.noConfusion)).mpr hR, hCaller⟩
  -- 16b. replyCallerLinkageReciprocal, Reply → TCB.
  · intro rid r tid hR hCaller
    have hRPre := (hNT rid.toObjId (.reply r) (fun _ => by exact KernelObject.noConfusion)
      (fun _ => by exact KernelObject.noConfusion)).mp hR
    obtain ⟨ty, hTy, hRO, ep, rt, hIpc⟩ := hInv.replyCallerLinkage.1.2 rid r tid hRPre hCaller
    obtain ⟨tx, hTx, hIS, _, _, _, _, _, hROeq, _⟩ := hFwd tid.toObjId ty hTy
    exact ⟨tx, hTx, hROeq ▸ hRO, ep, rt, hIS ▸ hIpc⟩
  -- 16c. blockedOnReplyHasReplyObject.
  · intro tid tcb ep rt hTcb hIpc
    obtain ⟨ty, hTy, hIS, _, _, _, _, _, hRO, _⟩ := hBwd tid.toObjId tcb hTcb
    obtain ⟨rid, hRid⟩ := hInv.replyCallerLinkage.2 tid ty ep rt hTy (hIS ▸ hIpc)
    exact ⟨rid, hRO ▸ hRid⟩
  -- 17a. pendingReceiveReplyWellFormed, the stash is well-formed.
  · intro tid tcb rid hTcb hStash
    rw [getTcb?_eq_some_iff] at hTcb
    obtain ⟨ty, hTy, hIS, _, _, _, _, _, _, hPRR⟩ := hBwd tid.toObjId tcb hTcb
    obtain ⟨⟨ep, hEp⟩, r, hR, hCaller⟩ := hInv.pendingReceiveReplyWellFormed.1 tid ty rid
      ((getTcb?_eq_some_iff st tid ty).mpr hTy) (hPRR ▸ hStash)
    refine ⟨⟨ep, hIS ▸ hEp⟩, r, ?_, hCaller⟩
    rw [getReply?_eq_some_iff] at hR ⊢
    exact (hNT rid.toObjId (.reply r) (fun _ => by exact KernelObject.noConfusion)
      (fun _ => by exact KernelObject.noConfusion)).mpr hR
  -- 17b. pendingReceiveReplyWellFormed, the stash is injective.
  · intro tid₁ tid₂ tcb₁ tcb₂ rid hTcb₁ hTcb₂ hS₁ hS₂
    rw [getTcb?_eq_some_iff] at hTcb₁ hTcb₂
    obtain ⟨ty₁, hTy₁, _, _, _, _, _, _, _, hPRR₁⟩ := hBwd tid₁.toObjId tcb₁ hTcb₁
    obtain ⟨ty₂, hTy₂, _, _, _, _, _, _, _, hPRR₂⟩ := hBwd tid₂.toObjId tcb₂ hTcb₂
    exact hInv.pendingReceiveReplyWellFormed.2 tid₁ tid₂ ty₁ ty₂ rid
      ((getTcb?_eq_some_iff st tid₁ ty₁).mpr hTy₁)
      ((getTcb?_eq_some_iff st tid₂ ty₂).mpr hTy₂) (hPRR₁ ▸ hS₁) (hPRR₂ ▸ hS₂)
  -- 19. endpointQueueTailBlockedConsistent.
  · intro epId ep tl tcb hEp hTcb
    have hEpPre := (hNT epId (.endpoint ep) (fun _ => by exact KernelObject.noConfusion)
      (fun _ => by exact KernelObject.noConfusion)).mp hEp
    obtain ⟨ty, hTy, hIS, _⟩ := hBwd tl.toObjId tcb hTcb
    obtain ⟨hRecv, hSend⟩ := hInv.endpointQueueTailBlockedConsistent epId ep tl ty hEpPre hTy
    exact ⟨fun h => hIS ▸ hRecv h, fun h => hIS ▸ hSend h⟩
  -- 20. queueNextTargetBlocked.
  · intro a b tcbA tcbB hA hB hNext
    obtain ⟨tyA, hTyA, hISA, _, hQNA, _⟩ := hBwd a.toObjId tcbA hA
    obtain ⟨tyB, hTyB, hISB, _⟩ := hBwd b.toObjId tcbB hB
    obtain ⟨hRecv, hSend⟩ :=
      hInv.queueNextTargetBlocked a b tyA tyB hTyA hTyB (hQNA ▸ hNext)
    refine ⟨fun ep h => hISB ▸ hRecv ep (hISA ▸ h), fun ep h => ?_⟩
    have h' : tyA.ipcState = .blockedOnSend ep ∨ tyA.ipcState = .blockedOnCall ep := by
      rcases h with h | h
      · exact Or.inl (hISA ▸ h)
      · exact Or.inr (hISA ▸ h)
    rcases hSend ep h' with h'' | h''
    · exact Or.inl (hISB ▸ h'')
    · exact Or.inr (hISB ▸ h'')


-- ============================================================================
-- §6  RR2.5 — the whole bundle, on the call path
-- ============================================================================

/-- WS-RR RR2.5: `applyCallDonation` establishes the read agreement — the no-op
arm reflexively, the donating arm through `donateSchedContext`. -/
theorem applyCallDonation_donationReadAgreement
    (st st' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (hObjInv : st.objects.invExt)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    donationReadAgreement st st' := by
  cases hSc : callDonationSchedContext? st callerVtid.val receiverVtid.val with
  | none =>
      rw [applyCallDonation_characterisation, hSc] at h
      cases h; exact donationReadAgreement.refl st
  | some scId =>
      rw [applyCallDonation_characterisation, hSc] at h
      exact donateSchedContext_donationReadAgreement st st' callerVtid.val receiverVtid.val
        scId hObjInv h

/-- **WS-RR RR2.5**: `applyCallDonation` preserves the whole twenty-conjunct IPC
bundle.

The fifteen binding-free conjuncts ride the read agreement; the five that read a
`schedContextBinding` are the four proved above plus `donationChainAcyclic`,
which `donationOwnerValid` subsumes.

Both hypotheses are properties of the *rendezvous*, not of the donation, and are
exactly what the live `.call` path establishes before the donation runs:

* `hCallerBlockedOnReply` — the caller has been stored `.blockedOnReply` by the
  call's own blocking store.  Without it the donee would hold `.donated scId
  caller` while the caller sat `.ready`, which `donationOwnerValid` forbids: the
  donor must be recoverable through the reply it is waiting on.
* `hReceiverNotOwner` — nothing already owns a donation whose owner is the
  receiver.  The receiver has just been woken out of the endpoint's receive
  queue, and `donationOwnerValid` requires a donation owner to be
  `.blockedOnReply`. -/
theorem applyCallDonation_preserves_ipcInvariantFull
    (st st' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hCallerBlockedOnReply : ∀ tcb, st.getTcb? callerVtid.val = some tcb →
        ∃ ep rt, tcb.ipcState = .blockedOnReply ep rt)
    (hReceiverNotOwner : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
        st.getTcb? tid = some tcb → tcb.schedContextBinding ≠ .donated scId receiverVtid.val)
    (h : applyCallDonation st callerVtid receiverVtid = .ok st') :
    ipcInvariantFull st' := by
  have hDOV : donationOwnerValid st' :=
    applyCallDonation_preserves_donationOwnerValid st st' callerVtid receiverVtid hObjInv
      hInv.donationOwnerValid hCallerBlockedOnReply hReceiverNotOwner h
  exact ipcInvariantFull_of_donationReadAgreement st st' hInv
    (applyCallDonation_donationReadAgreement st st' callerVtid receiverVtid hObjInv h)
    (donationOwnerValid_implies_donationChainAcyclic st' hDOV) hDOV
    (applyCallDonation_preserves_passiveServerIdle st st' callerVtid receiverVtid hObjInv
      hInv.passiveServerIdle hCallerBlockedOnReply h)
    (applyCallDonation_preserves_donationBudgetTransfer st st' callerVtid receiverVtid hObjInv
      hInv.donationBudgetTransfer h)
    (applyCallDonation_preserves_donationOwnerUnique st st' callerVtid receiverVtid hObjInv
      hInv.donationOwnerValid hInv.donationOwnerUnique h)

/-- **WS-RR RR2.5**: the per-core call donation preserves the bundle.

`applyCallDonationOnCore` is `applyCallDonation` followed by the SM5.H
replenishment migration, which rewrites only `SchedulerState.replenishQueueOnCore`
— an object-store frame that no IPC conjunct reads. -/
theorem applyCallDonationOnCore_preserves_ipcInvariantFull
    (st st'' : SystemState) (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : Concurrency.CoreId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hCallerBlockedOnReply : ∀ tcb, st.getTcb? callerVtid.val = some tcb →
        ∃ ep rt, tcb.ipcState = .blockedOnReply ep rt)
    (hReceiverNotOwner : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (scId : SeLe4n.SchedContextId),
        st.getTcb? tid = some tcb → tcb.schedContextBinding ≠ .donated scId receiverVtid.val)
    (h : applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome = .ok st'') :
    ipcInvariantFull st'' := by
  obtain ⟨st', hDon, _⟩ :=
    applyCallDonationOnCore_ok_decompose st st'' callerVtid receiverVtid donorHome doneeHome h
  have hFull' : ipcInvariantFull st' :=
    applyCallDonation_preserves_ipcInvariantFull st st' callerVtid receiverVtid hObjInv hInv
      hCallerBlockedOnReply hReceiverNotOwner hDon
  have hObjs : st''.objects = st'.objects :=
    applyCallDonationOnCore_objects_eq st st' st'' callerVtid receiverVtid donorHome doneeHome
      hDon h
  have hRq := applyCallDonationOnCore_runQueue_current_eq st st'' callerVtid receiverVtid
    donorHome doneeHome bootCoreId h
  have hSchedFrame := applyCallDonation_scheduler_eq st callerVtid receiverVtid st' hDon
  exact ipcInvariantFull_of_donationReadAgreement st' st'' hFull'
    (donationReadAgreement_of_objects_eq hObjs (donationReadAgreement.refl st'))
    (donationChainAcyclic_of_objects_eq hObjs hFull'.donationChainAcyclic)
    (donationOwnerValid_of_objects_eq hObjs hFull'.donationOwnerValid)
    (passiveServerIdle_of_frame
      (passiveServerIdleFrame.of_objects_scheduler_eq hObjs
        (by rw [hRq.1, hSchedFrame]) (by rw [hRq.2, hSchedFrame]))
      hFull'.passiveServerIdle)
    (donationBudgetTransfer_of_objects_eq hObjs hFull'.donationBudgetTransfer)
    (donationOwnerUnique_of_objects_eq hObjs hFull'.donationOwnerUnique)


-- ============================================================================
-- §7  RR2.5 — the whole bundle, on the reply path
-- ============================================================================

/-- WS-RR RR2.5: what `replyDonationReturn? = some (scId, owner)` witnesses about
the pre-state — the replier holds exactly that donation, the owner exists, and
the two are distinct.

`owner ≠ replier` is derived, not assumed: `donationOwnerValid` puts the owner
`.unbound` while the replier is `.donated`, and one TCB cannot be both. -/
theorem replyDonationReturn?_some_char
    (st : SystemState) (replier : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hDOV : donationOwnerValid st)
    (hRet : replyDonationReturn? st replier = some (scId, owner)) :
    ∃ pTcb, st.getTcb? replier = some pTcb ∧
      pTcb.schedContextBinding = .donated scId owner ∧
      ∃ oTcb, st.getTcb? owner = some oTcb ∧ owner ≠ replier := by
  obtain ⟨pTcb, hL, hB⟩ : ∃ pTcb, lookupTcb st replier = some pTcb ∧
      pTcb.schedContextBinding = .donated scId owner := by
    unfold replyDonationReturn? at hRet
    revert hRet
    cases hL : lookupTcb st replier with
    | none => intro hRet; cases hRet
    | some pTcb =>
      simp only []
      cases hBind : pTcb.schedContextBinding with
      | unbound => intro hRet; cases hRet
      | bound _ => intro hRet; cases hRet
      | donated s o =>
        simp only [Option.some.injEq, Prod.mk.injEq]
        intro hRet
        exact ⟨pTcb, rfl, by rw [hBind, hRet.1, hRet.2]⟩
  have hPPre : st.getTcb? replier = some pTcb := getTcb?_of_lookupTcb st _ pTcb hL
  obtain ⟨_, oTcb, hOwnerObj, hOwnerUnbound, _⟩ :=
    hDOV replier pTcb scId owner ((getTcb?_eq_some_iff st _ pTcb).mp hPPre) hB
  have hOPre : st.getTcb? owner = some oTcb := (getTcb?_eq_some_iff st owner oTcb).mpr hOwnerObj
  refine ⟨pTcb, hPPre, hB, oTcb, hOPre, ?_⟩
  intro hEq
  have hSame : some oTcb = some pTcb := (hEq ▸ hOPre).symm.trans hPPre
  have hOU := hOwnerUnbound
  rw [Option.some.inj hSame, hB] at hOU
  cases hOU

/-- WS-RR RR2.5: a successful `applyReplyDonation` is the return followed by the
replier's deschedule, or the identity. -/
theorem applyReplyDonation_ok_decompose
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (h : applyReplyDonation st replierVtid = .ok st'') :
    (replyDonationReturn? st replierVtid.val = none ∧ st'' = st) ∨
    ∃ (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (st' : SystemState),
      replyDonationReturn? st replierVtid.val = some (scId, owner) ∧
      returnDonatedSchedContext st replierVtid.val scId owner = .ok st' ∧
      st'' = removeRunnable st' replierVtid.val := by
  rw [applyReplyDonation_characterisation] at h
  cases hRet : replyDonationReturn? st replierVtid.val with
  | none => rw [hRet] at h; exact Or.inl ⟨rfl, (Except.ok.inj h).symm⟩
  | some pair =>
    obtain ⟨scId, owner⟩ := pair
    rw [hRet] at h
    simp only [] at h
    cases hV : SeLe4n.ThreadId.toValid? owner with
    | none => rw [hV] at h; simp only [] at h; cases h
    | some ownerVtid =>
      rw [hV] at h
      simp only [] at h
      cases hR : returnDonatedSchedContextValid st replierVtid scId ownerVtid with
      | error e => rw [hR] at h; simp only [] at h; cases h
      | ok st' =>
        rw [hR] at h
        simp only [Except.ok.injEq] at h
        have hOwnerEq : ownerVtid.val = owner :=
          SeLe4n.ThreadId.toValid?_some_val_eq owner ownerVtid hV
        rw [returnDonatedSchedContextValid_eq, hOwnerEq] at hR
        exact Or.inr ⟨scId, owner, st', rfl, hR, h.symm⟩

/-- WS-RR RR2.5: a *returning* `applyReplyDonation` rewrites exactly two
bindings — the original owner back to `.bound`, the replier to `.unbound` — and
reads every other thread through.  Stated on the intermediate state `st'`,
before the deschedule, which touches no object. -/
theorem returnDonatedSchedContext_binding_trichotomy
    (st st' : SystemState) (replier owner : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (pTcb oTcb : TCB)
    (hOPost : st'.getTcb? owner = some { oTcb with schedContextBinding := .bound scId })
    (hPPost : st'.getTcb? replier = some { pTcb with schedContextBinding := .unbound })
    (hOther : ∀ tid, tid ≠ owner → tid ≠ replier → st'.getTcb? tid = st.getTcb? tid)
    (tid : SeLe4n.ThreadId) (tcb' : TCB) (hTcb' : st'.getTcb? tid = some tcb') :
    (tid = owner ∧ tcb'.schedContextBinding = .bound scId) ∨
    (tid = replier ∧ tcb'.schedContextBinding = .unbound) ∨
    (tid ≠ owner ∧ tid ≠ replier ∧ st.getTcb? tid = some tcb') := by
  by_cases hO : tid = owner
  · rw [hO] at hTcb'
    have hEq : { oTcb with schedContextBinding := .bound scId } = tcb' :=
      Option.some.inj (hOPost.symm.trans hTcb')
    exact Or.inl ⟨hO, by rw [← hEq]⟩
  · by_cases hP : tid = replier
    · rw [hP] at hTcb'
      have hEq : { pTcb with schedContextBinding := .unbound } = tcb' :=
        Option.some.inj (hPPost.symm.trans hTcb')
      exact Or.inr (Or.inl ⟨hP, by rw [← hEq]⟩)
    · exact Or.inr (Or.inr ⟨hO, hP, (hOther tid hO hP) ▸ hTcb'⟩)

/-- **WS-RR RR2.5**: the donation return preserves the whole IPC bundle.

The return is the exact inverse of the call donation and needs *no* new
hypothesis for the four store-reading conjuncts: every surviving donation is one
the replier's own donation could not have collided with, and the pre-state
conjuncts say so.

* `donationOwnerValid` — a surviving donation cannot name the replier as owner
  (the replier is `.donated`, and an owner is `.unbound`) nor the returning owner
  (`donationOwnerUnique` would then equate it with the replier), and cannot hold
  the returned SchedContext (`donationBudgetTransfer`).
* `donationBudgetTransfer` — the owner's fresh `.bound scId` collides only with a
  thread that already collided with the replier's `.donated scId`.

The one genuine precondition is `hReplierIdleAllowed`, and it is about the
*deschedule*, not the return: `applyReplyDonation` takes the replier off the run
queue, so a thread that `passiveServerIdle` had no obligation for acquires one.
The reply path leaves the replier `.ready` (`.reply`) or `.blockedOnReceive`
(`.replyRecv`), both of which `passiveServerIdleAllowed` admits. -/
theorem returnDonatedSchedContext_preserves_ipcInvariantFull
    (st st' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hRet : replyDonationReturn? st replierVtid.val = some (scId, owner))
    (hReplierIdleAllowed : ∀ tcb, st.getTcb? replierVtid.val = some tcb →
        passiveServerIdleAllowed tcb.ipcState)
    (h : returnDonatedSchedContext st replierVtid.val scId owner = .ok st') :
    ipcInvariantFull st' := by
  obtain ⟨pTcb, hPPre, hPB, oTcb, hOPre, hNe⟩ :=
    replyDonationReturn?_some_char st replierVtid.val scId owner
      hInv.donationOwnerValid hRet
  obtain ⟨⟨oTcb0, hOPre0, hOPost⟩, ⟨pTcb0, hPPre0, hPPost⟩, hOther⟩ :=
    returnDonatedSchedContext_getTcb?_char st st' replierVtid.val scId owner hObjInv hNe h
  have hOEq : oTcb0 = oTcb := Option.some.inj (hOPre0.symm.trans hOPre)
  have hPEq : pTcb0 = pTcb := Option.some.inj (hPPre0.symm.trans hPPre)
  rw [hOEq] at hOPost
  rw [hPEq] at hPPost
  have hSched := returnDonatedSchedContext_scheduler_eq st st' replierVtid.val scId owner h
  have hAgree := returnDonatedSchedContext_donationReadAgreement st st' replierVtid.val scId
    owner hObjInv h
  have hScNe : ∀ scId', scId' ≠ scId →
      st'.getSchedContext? scId' = st.getSchedContext? scId' := fun scId' hne =>
    returnDonatedSchedContext_getSchedContext?_ne st st' replierVtid.val scId scId' owner
      hne hObjInv h
  have hTri := returnDonatedSchedContext_binding_trichotomy st st' replierVtid.val owner scId
    pTcb oTcb hOPost hPPost hOther
  -- (1) `donationOwnerValid` on the intermediate state.
  have hDOV' : donationOwnerValid st' := by
    intro tid tcb' scId' owner' hTcb' hBind'
    rcases hTri tid tcb' ((getTcb?_eq_some_iff st' tid tcb').mpr hTcb') with
      ⟨_, hBnd⟩ | ⟨_, hBnd⟩ | ⟨hNeO, hNeP, hPre⟩
    · rw [hBnd] at hBind'; cases hBind'
    · rw [hBnd] at hBind'; cases hBind'
    · obtain ⟨⟨scOld, hScOld, hScOldBound⟩, ownerTcb, hOwner, hOwnerUnbound, hOwnerBlk⟩ :=
        hInv.donationOwnerValid tid tcb' scId' owner'
          ((getTcb?_eq_some_iff st tid tcb').mp hPre) hBind'
      -- The returned SchedContext was the replier's, so no survivor holds it.
      have hScId'Ne : scId' ≠ scId := by
        intro hEq; subst hEq
        exact hInv.donationBudgetTransfer tid replierVtid.val tcb' pTcb scId'
          ((getTcb?_eq_some_iff st tid tcb').mp hPre)
          ((getTcb?_eq_some_iff st _ pTcb).mp hPPre) hNeP
          (by rw [hBind']; rfl) (by rw [hPB]; rfl)
      -- The survivor's owner is neither the replier nor the returning owner.
      have hOwnerNeP : owner' ≠ replierVtid.val := by
        intro hEq
        rw [hEq] at hOwner
        have hSame : some pTcb = some ownerTcb :=
          hPPre.symm.trans ((getTcb?_eq_some_iff st _ ownerTcb).mpr hOwner)
        have hOU := hOwnerUnbound
        rw [← Option.some.inj hSame, hPB] at hOU
        cases hOU
      have hOwnerNeO : owner' ≠ owner := by
        intro hEq
        rw [hEq] at hBind'
        exact hNeP (hInv.donationOwnerUnique tid replierVtid.val tcb' pTcb scId' scId owner
          ((getTcb?_eq_some_iff st tid tcb').mp hPre)
          ((getTcb?_eq_some_iff st _ pTcb).mp hPPre) hBind' hPB)
      refine ⟨⟨scOld, ?_, hScOldBound⟩, ownerTcb, ?_, hOwnerUnbound, hOwnerBlk⟩
      · exact (getSchedContext?_eq_some_iff st' scId' scOld).mp
          ((hScNe scId' hScId'Ne).trans ((getSchedContext?_eq_some_iff st scId' scOld).mpr hScOld))
      · exact (getTcb?_eq_some_iff st' owner' ownerTcb).mp
          ((hOther owner' hOwnerNeO hOwnerNeP).trans
            ((getTcb?_eq_some_iff st owner' ownerTcb).mpr hOwner))
  -- (2) `donationOwnerUnique`: every surviving donation is a pre-state donation.
  have hDOU' : donationOwnerUnique st' := by
    intro tid1 tid2 tcb1 tcb2 scId1 scId2 owner' h1 h2 hB1 hB2
    rcases hTri tid1 tcb1 ((getTcb?_eq_some_iff st' tid1 tcb1).mpr h1) with
      ⟨_, hBnd⟩ | ⟨_, hBnd⟩ | ⟨_, _, hPre1⟩
    · rw [hBnd] at hB1; cases hB1
    · rw [hBnd] at hB1; cases hB1
    · rcases hTri tid2 tcb2 ((getTcb?_eq_some_iff st' tid2 tcb2).mpr h2) with
        ⟨_, hBnd⟩ | ⟨_, hBnd⟩ | ⟨_, _, hPre2⟩
      · rw [hBnd] at hB2; cases hB2
      · rw [hBnd] at hB2; cases hB2
      · exact hInv.donationOwnerUnique tid1 tid2 tcb1 tcb2 scId1 scId2 owner'
          ((getTcb?_eq_some_iff st tid1 tcb1).mp hPre1)
          ((getTcb?_eq_some_iff st tid2 tcb2).mp hPre2) hB1 hB2
  -- (3) `donationBudgetTransfer`: the owner's fresh `.bound` inherits the
  --     replier's exclusivity.
  have hDBT' : donationBudgetTransfer st' := by
    have hClassify : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (s : SeLe4n.SchedContextId),
        st'.getTcb? tid = some tcb → tcb.schedContextBinding.scId? = some s →
        (tid = owner ∧ s = scId) ∨
        (tid ≠ owner ∧ tid ≠ replierVtid.val ∧ st.getTcb? tid = some tcb) := by
      intro tid tcb s hTcb hHold
      rcases hTri tid tcb hTcb with ⟨hO, hBnd⟩ | ⟨_, hBnd⟩ | rest
      · rw [hBnd] at hHold
        exact Or.inl ⟨hO, (Option.some.inj hHold).symm⟩
      · rw [hBnd] at hHold; cases hHold
      · exact Or.inr rest
    have hPScId : pTcb.schedContextBinding.scId? = some scId := by rw [hPB]; rfl
    have hPObj : st.objects[replierVtid.val.toObjId]? = some (.tcb pTcb) :=
      (getTcb?_eq_some_iff st replierVtid.val pTcb).mp hPPre
    intro tid1 tid2 tcb1 tcb2 s h1 h2 hNeT hS1 hS2
    rcases hClassify tid1 tcb1 s ((getTcb?_eq_some_iff st' tid1 tcb1).mpr h1) hS1 with
      ⟨hO1, hSEq⟩ | ⟨hO1, hP1, hPre1⟩
    · rcases hClassify tid2 tcb2 s ((getTcb?_eq_some_iff st' tid2 tcb2).mpr h2) hS2 with
        ⟨hO2, _⟩ | ⟨_, hP2, hPre2⟩
      · exact hNeT (hO1.trans hO2.symm)
      · rw [hSEq] at hS2
        exact hInv.donationBudgetTransfer tid2 replierVtid.val tcb2 pTcb scId
          ((getTcb?_eq_some_iff st tid2 tcb2).mp hPre2) hPObj hP2 hS2 hPScId
    · rcases hClassify tid2 tcb2 s ((getTcb?_eq_some_iff st' tid2 tcb2).mpr h2) hS2 with
        ⟨_, hSEq⟩ | ⟨_, hP2, hPre2⟩
      · rw [hSEq] at hS1
        exact hInv.donationBudgetTransfer tid1 replierVtid.val tcb1 pTcb scId
          ((getTcb?_eq_some_iff st tid1 tcb1).mp hPre1) hPObj hP1 hS1 hPScId
      · exact hInv.donationBudgetTransfer tid1 tid2 tcb1 tcb2 s
          ((getTcb?_eq_some_iff st tid1 tcb1).mp hPre1)
          ((getTcb?_eq_some_iff st tid2 tcb2).mp hPre2) hNeT hS1 hS2
  -- (4) `passiveServerIdle`: the replier is the only thread the return makes
  --     `.unbound`, and the reply left it in an allowed state.
  have hAllowed : passiveServerIdleAllowed pTcb.ipcState := hReplierIdleAllowed pTcb hPPre
  have hPSI' : passiveServerIdle st' := by
    intro tid tcb' hTcb' hUnbound hNotInQ hNotCur
    rcases hTri tid tcb' ((getTcb?_eq_some_iff st' tid tcb').mpr hTcb') with
      ⟨_, hBnd⟩ | ⟨hP, hBnd⟩ | ⟨_, _, hPre⟩
    · rw [hBnd] at hUnbound; cases hUnbound
    · rw [hP] at hTcb'
      have hEq : { pTcb with schedContextBinding := .unbound } = tcb' :=
        Option.some.inj (hPPost.symm.trans ((getTcb?_eq_some_iff st' _ tcb').mpr hTcb'))
      rw [← hEq]
      exact hAllowed
    · rw [hSched] at hNotInQ hNotCur
      exact hInv.passiveServerIdle tid tcb' ((getTcb?_eq_some_iff st tid tcb').mp hPre)
        hUnbound hNotInQ hNotCur
  exact ipcInvariantFull_of_donationReadAgreement st st' hInv hAgree
    (donationOwnerValid_implies_donationChainAcyclic st' hDOV') hDOV' hPSI' hDBT' hDOU'


/-- WS-RR RR2.5: the replier's deschedule preserves the bundle, given the replier
is in a state `passiveServerIdle` admits.

Stated over an arbitrary object-preserving deschedule rather than over
`removeRunnable` itself, because the cross-core `.reply` path deschedules with
`removeRunnableOnCore` on the *executing* core and composes a replenishment
migration in between — both object-store frames, neither of them `removeRunnable`. -/
theorem ipcInvariantFull_of_descheduleFrame
    (st' st'' : SystemState) (hInv : ipcInvariantFull st')
    (hObjs : st''.objects = st'.objects)
    (hFrame : passiveServerIdleFrame st' st'') :
    ipcInvariantFull st'' :=
  ipcInvariantFull_of_donationReadAgreement st' st'' hInv
    (donationReadAgreement_of_objects_eq hObjs (donationReadAgreement.refl st'))
    (donationChainAcyclic_of_objects_eq hObjs hInv.donationChainAcyclic)
    (donationOwnerValid_of_objects_eq hObjs hInv.donationOwnerValid)
    (passiveServerIdle_of_frame hFrame hInv.passiveServerIdle)
    (donationBudgetTransfer_of_objects_eq hObjs hInv.donationBudgetTransfer)
    (donationOwnerUnique_of_objects_eq hObjs hInv.donationOwnerUnique)

/-- **WS-RR RR2.5**: `applyReplyDonation` preserves the whole twenty-conjunct IPC
bundle — the return (`returnDonatedSchedContext_preserves_ipcInvariantFull`)
followed by the replier's deschedule.

`hReplierIdleAllowed` is the single precondition, and it is about the
*deschedule*, not the return: taking the replier off the run queue hands
`passiveServerIdle` an obligation it did not have.  The reply path leaves the
replier `.ready` (`.reply`) or `.blockedOnReceive` (`.replyRecv`), both of which
`passiveServerIdleAllowed` admits. -/
theorem applyReplyDonation_preserves_ipcInvariantFull
    (st st'' : SystemState) (replierVtid : SeLe4n.ValidThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : ipcInvariantFull st)
    (hReplierIdleAllowed : ∀ tcb, st.getTcb? replierVtid.val = some tcb →
        passiveServerIdleAllowed tcb.ipcState)
    (h : applyReplyDonation st replierVtid = .ok st'') :
    ipcInvariantFull st'' := by
  rcases applyReplyDonation_ok_decompose st st'' replierVtid h with
    ⟨_, hEq⟩ | ⟨scId, owner, st', hRet, hR, hEq⟩
  · rw [hEq]; exact hInv
  · have hFull' : ipcInvariantFull st' :=
      returnDonatedSchedContext_preserves_ipcInvariantFull st st' replierVtid scId owner
        hObjInv hInv hRet hReplierIdleAllowed hR
    obtain ⟨pTcb, hPPre, hPB, _, _, hNe⟩ :=
      replyDonationReturn?_some_char st replierVtid.val scId owner hInv.donationOwnerValid hRet
    obtain ⟨_, ⟨pTcb0, hPPre0, hPPost⟩, _⟩ :=
      returnDonatedSchedContext_getTcb?_char st st' replierVtid.val scId owner hObjInv hNe hR
    have hPEq : pTcb0 = pTcb := Option.some.inj (hPPre0.symm.trans hPPre)
    rw [hPEq] at hPPost
    rw [hEq]
    refine ipcInvariantFull_of_descheduleFrame st' _ hFull'
      (removeRunnable_preserves_objects st' replierVtid.val)
      (removeRunnable_passiveServerIdleFrame st' replierVtid.val (fun tcb hTcb => ?_))
    have hEqT : { pTcb with schedContextBinding := .unbound } = tcb :=
      Option.some.inj (hPPost.symm.trans ((getTcb?_eq_some_iff st' _ tcb).mpr hTcb))
    exact Or.inr (by rw [← hEqT]; exact hReplierIdleAllowed pTcb hPPre)

end SeLe4n.Kernel
