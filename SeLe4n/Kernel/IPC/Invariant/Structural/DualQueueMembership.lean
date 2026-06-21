-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.Invariant.CallReplyRecv
import SeLe4n.Kernel.IPC.Invariant.NotificationPreservation
import SeLe4n.Kernel.IPC.Invariant.QueueNoDup
import SeLe4n.Kernel.IPC.Invariant.QueueMembership
import SeLe4n.Kernel.IPC.Invariant.QueueNextBlocking
import SeLe4n.Kernel.IPC.Invariant.WaitingThreadHelpers
import SeLe4n.Kernel.IPC.Invariant.Structural.QueueNextTransport
import SeLe4n.Kernel.IPC.Invariant.Structural.StoreObjectFrame

/-! # IPC Structural Preservation — Part 3 (DualQueueMembership)

Extracted from `SeLe4n.Kernel.IPC.Invariant.Structural` as part of
AN3-C (IPC-M02 / Theme 4.7) to keep each module under the
2000-LOC maintenance ceiling.  Declarations are unchanged in order,
content, and proof; only the file boundary has moved.  The parent
`Structural.lean` re-exports every child so all existing
`import SeLe4n.Kernel.IPC.Invariant.Structural` consumers continue
to typecheck without modification.

Contains the composed `ipcInvariantFull` preservation witnesses
(notificationSignal/Wait, endpointReply, endpointSendDual, etc.),
the V3-K `endpointQueueNoDup` preservation cluster, the V3-J
`ipcStateQueueConsistent` / `queueMembershipConsistent` cluster,
the WithCaps-wrapper `ipcInvariantFull` theorems, and the
T4-A/B/C compound preservation proofs.
-/

-- AN3-C: linter directives inherited from parent Structural.lean.
set_option linter.unusedVariables false

namespace SeLe4n.Kernel

open SeLe4n.Model


-- ============================================================================
-- WS-SM SM6.D (#7.1 reply-objects fold): per-conjunct frame lemmas for the
-- atomic reply-link (`SystemState.linkCallerReply`) and the server-first stash
-- store that the folded `endpointReceiveDual` now performs.  These mirror the
-- `linkCallerReply_preserves_<C>` helpers in `Structural.StoreObjectFrame`, but
-- here the framed conjuncts are the single structural ones consumed by the V3-K
-- / V3-J per-conjunct preservation theorems below (`endpointQueueNoDup`,
-- `ipcStateQueueMembershipConsistent`, `ipcStateQueueConsistent`).
--
-- `linkCallerReply` writes a `.reply` (via `linkReply`, a non-ep/non-tcb store)
-- then a caller `.tcb` differing only in `replyObject`; the stash writes a
-- receiver `.tcb` differing only in `pendingReceiveReply`.  None of these three
-- conjuncts reads `replyObject` or `pendingReceiveReply` (only `ipcState`,
-- `queueNext`, and endpoint objects), so a TCB store agreeing on those two read
-- fields frames each conjunct.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): a `.tcb` store that agrees with the previous TCB on
`ipcState` and `queueNext` preserves `endpointQueueNoDup` — the conjunct reads
endpoint queue heads (untouched: not an endpoint store) and `queueNext` for the
no-self-loop clause (unchanged by hypothesis). -/
private theorem storeObject_tcb_readAgree_preserves_endpointQueueNoDup
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb tcbNew : TCB)
    (hQN : tcbNew.queueNext = tcb.queueNext)
    (hInv : endpointQueueNoDup st) (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb tcbNew) st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  intro oid ep hEp
  have hNeEp : oid ≠ id := by
    intro hEq; subst hEq; rw [storeObject_objects_eq st st' oid _ hObjInv hStore] at hEp; cases hEp
  rw [storeObject_objects_ne st st' id oid _ hNeEp hObjInv hStore] at hEp
  obtain ⟨_, hDisj⟩ := hInv oid ep hEp
  refine ⟨?_, hDisj⟩
  intro tid tcbT hTcb
  by_cases hEqT : tid.toObjId = id
  · -- The stored TCB: its queueNext equals the previous TCB's (hQN), so the
    -- pre-state no-self-loop fact transports.
    subst hEqT
    rw [storeObject_objects_eq st st' tid.toObjId _ hObjInv hStore] at hTcb
    cases hTcb
    rw [hQN]
    exact (hInv oid ep hEp).1 tid tcb hPrev
  · rw [storeObject_objects_ne st st' id tid.toObjId _ hEqT hObjInv hStore] at hTcb
    exact (hInv oid ep hEp).1 tid tcbT hTcb

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): a `.tcb` store that agrees with the previous TCB on
`ipcState` and `queueNext` preserves `ipcStateQueueMembershipConsistent` — the
conjunct dispatches on `ipcState` (unchanged) and witnesses the endpoint plus a
`queueNext`-prev chain (both transported, the prev's `queueNext` via `hQN`). -/
private theorem storeObject_tcb_readAgree_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb tcbNew : TCB)
    (hIS : tcbNew.ipcState = tcb.ipcState) (hQN : tcbNew.queueNext = tcb.queueNext)
    (hInv : ipcStateQueueMembershipConsistent st) (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb tcbNew) st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  -- Backward read-field agreement: every post-store `.tcb` corresponds to a
  -- pre-store `.tcb` with the same ipcState and queueNext.
  have hBwd : ∀ (s : SeLe4n.ObjId) (ty : TCB), st.objects[s]? = some (.tcb ty) →
      ∃ tx, st'.objects[s]? = some (.tcb tx) ∧
        tx.ipcState = ty.ipcState ∧ tx.queueNext = ty.queueNext := by
    intro s ty hObj
    by_cases hs : s = id
    · subst hs; rw [hPrev] at hObj; cases hObj
      exact ⟨tcbNew, storeObject_objects_eq st st' s _ hObjInv hStore, hIS, hQN⟩
    · exact ⟨ty, by rw [storeObject_objects_ne st st' id s _ hs hObjInv hStore]; exact hObj, rfl, rfl⟩
  have hFwd : ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.queueNext = ty.queueNext := by
    intro s tx hObj
    by_cases hs : s = id
    · subst hs; rw [storeObject_objects_eq st st' s _ hObjInv hStore] at hObj; cases hObj
      exact ⟨tcb, hPrev, hIS, hQN⟩
    · exact ⟨tx, by rw [← storeObject_objects_ne st st' id s _ hs hObjInv hStore]; exact hObj, rfl, rfl⟩
  -- Endpoint objects frame: not an endpoint store.
  have hEpAgree : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) ↔ st'.objects[epId]? = some (.endpoint ep) := by
    intro epId ep
    by_cases hs : epId = id
    · subst hs
      constructor
      · intro h; rw [hPrev] at h; cases h
      · intro h; rw [storeObject_objects_eq st st' epId _ hObjInv hStore] at h; cases h
    · rw [storeObject_objects_ne st st' id epId _ hs hObjInv hStore]
  intro tid tcbT hTcb
  obtain ⟨ty, hPreTcb, hISeq, hQNeq⟩ := hFwd tid.toObjId tcbT hTcb
  have hbase := hInv tid ty hPreTcb
  rw [hISeq]
  cases hq : ty.ipcState with
  | ready => exact True.intro
  | blockedOnNotification _ => exact True.intro
  | blockedOnReply _ _ => exact True.intro
  | blockedOnSend epId =>
      rw [hq] at hbase; obtain ⟨ep, hEpSt, hcond⟩ := hbase
      refine ⟨ep, (hEpAgree epId ep).mp hEpSt, ?_⟩
      cases hcond with
      | inl h => exact Or.inl h
      | inr h =>
          obtain ⟨prev, prevTcb, hPrevSt, hQNp⟩ := h
          obtain ⟨xx, hStX, _, hQNxx⟩ := hBwd prev.toObjId prevTcb hPrevSt
          exact Or.inr ⟨prev, xx, hStX, hQNxx.trans hQNp⟩
  | blockedOnReceive epId =>
      rw [hq] at hbase; obtain ⟨ep, hEpSt, hcond⟩ := hbase
      refine ⟨ep, (hEpAgree epId ep).mp hEpSt, ?_⟩
      cases hcond with
      | inl h => exact Or.inl h
      | inr h =>
          obtain ⟨prev, prevTcb, hPrevSt, hQNp⟩ := h
          obtain ⟨xx, hStX, _, hQNxx⟩ := hBwd prev.toObjId prevTcb hPrevSt
          exact Or.inr ⟨prev, xx, hStX, hQNxx.trans hQNp⟩
  | blockedOnCall epId =>
      rw [hq] at hbase; obtain ⟨ep, hEpSt, hcond⟩ := hbase
      refine ⟨ep, (hEpAgree epId ep).mp hEpSt, ?_⟩
      cases hcond with
      | inl h => exact Or.inl h
      | inr h =>
          obtain ⟨prev, prevTcb, hPrevSt, hQNp⟩ := h
          obtain ⟨xx, hStX, _, hQNxx⟩ := hBwd prev.toObjId prevTcb hPrevSt
          exact Or.inr ⟨prev, xx, hStX, hQNxx.trans hQNp⟩

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): a `.tcb` store that agrees with the previous TCB on
`ipcState` preserves `ipcStateQueueConsistent` — the conjunct dispatches on
`ipcState` (unchanged) and witnesses endpoint existence (endpoints untouched). -/
private theorem storeObject_tcb_readAgree_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb tcbNew : TCB)
    (hIS : tcbNew.ipcState = tcb.ipcState)
    (hInv : ipcStateQueueConsistent st) (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb tcbNew) st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  have hEpAgree : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) → st'.objects[epId]? = some (.endpoint ep) := by
    intro epId ep h
    by_cases hs : epId = id
    · subst hs; rw [hPrev] at h; cases h
    · rw [storeObject_objects_ne st st' id epId _ hs hObjInv hStore]; exact h
  intro tid tcbT hTcb
  by_cases hEqT : tid.toObjId = id
  · subst hEqT
    rw [storeObject_objects_eq st st' tid.toObjId _ hObjInv hStore] at hTcb
    cases hTcb
    rw [hIS]
    have hPre := hInv tid tcb hPrev
    cases hq : tcb.ipcState with
    | ready | blockedOnNotification _ | blockedOnReply _ _ => exact True.intro
    | blockedOnSend epId =>
        rw [hq] at hPre; obtain ⟨ep, hEp⟩ := hPre; exact ⟨ep, hEpAgree epId ep hEp⟩
    | blockedOnReceive epId =>
        rw [hq] at hPre; obtain ⟨ep, hEp⟩ := hPre; exact ⟨ep, hEpAgree epId ep hEp⟩
    | blockedOnCall epId =>
        rw [hq] at hPre; obtain ⟨ep, hEp⟩ := hPre; exact ⟨ep, hEpAgree epId ep hEp⟩
  · rw [storeObject_objects_ne st st' id tid.toObjId _ hEqT hObjInv hStore] at hTcb
    have hPre := hInv tid tcbT hTcb
    cases hq : tcbT.ipcState with
    | ready | blockedOnNotification _ | blockedOnReply _ _ => exact True.intro
    | blockedOnSend epId =>
        rw [hq] at hPre; obtain ⟨ep, hEp⟩ := hPre; exact ⟨ep, hEpAgree epId ep hEp⟩
    | blockedOnReceive epId =>
        rw [hq] at hPre; obtain ⟨ep, hEp⟩ := hPre; exact ⟨ep, hEpAgree epId ep hEp⟩
    | blockedOnCall epId =>
        rw [hq] at hPre; obtain ⟨ep, hEp⟩ := hPre; exact ⟨ep, hEpAgree epId ep hEp⟩

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): `linkCallerReply` preserves `endpointQueueNoDup`.
A `.reply` store (non-ep/non-tcb) then a caller `.tcb` store changing only
`replyObject` (`queueNext` unchanged). -/
private theorem linkCallerReply_preserves_endpointQueueNoDup
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hInv : endpointQueueNoDup st) (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  unfold SystemState.linkCallerReply at hStep
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hInv1 : endpointQueueNoDup st1 := by
      unfold SystemState.linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => simp [hGetR] at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · exact storeObject_non_ep_non_tcb_preserves_endpointQueueNoDup
            st st1 rid.toObjId _ hInv hObjInv (fun ep h => by cases h) (fun tcb h => by cases h) hLink
        · simp at hLink
    have hObjInv1 := SystemState.linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · have hTcbPre : st1.objects[caller.toObjId]? = some (.tcb tcb) :=
          (SystemState.getTcb?_eq_some_iff st1 caller tcb).mp hT
        exact storeObject_tcb_readAgree_preserves_endpointQueueNoDup
          st1 st' caller.toObjId tcb { tcb with replyObject := some rid } rfl
          hInv1 hObjInv1 hTcbPre hStep
      · simp at hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): `linkCallerReply` preserves
`ipcStateQueueMembershipConsistent`.  The `.reply` store frames it (non-ep/
non-tcb); the caller `.tcb` store changes only `replyObject` (ipcState +
queueNext unchanged). -/
private theorem linkCallerReply_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hInv : ipcStateQueueMembershipConsistent st) (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  unfold SystemState.linkCallerReply at hStep
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hInv1 : ipcStateQueueMembershipConsistent st1 := by
      unfold SystemState.linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => simp [hGetR] at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · have hReplyAt : st.objects[rid.toObjId]? = some (.reply r) :=
            (getReply?_eq_some_iff st rid r).mp hGetR
          exact storeObject_non_ep_non_tcb_preserves_ipcStateQueueMembershipConsistent
            st st1 rid.toObjId _ hInv hObjInv (fun ep h => by cases h) (fun tcb h => by cases h)
            (fun ep => by rw [hReplyAt]; exact fun h => by cases h)
            (fun tcb => by rw [hReplyAt]; exact fun h => by cases h) hLink
        · simp at hLink
    have hObjInv1 := SystemState.linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · have hTcbPre : st1.objects[caller.toObjId]? = some (.tcb tcb) :=
          (SystemState.getTcb?_eq_some_iff st1 caller tcb).mp hT
        exact storeObject_tcb_readAgree_preserves_ipcStateQueueMembershipConsistent
          st1 st' caller.toObjId tcb { tcb with replyObject := some rid } rfl rfl
          hInv1 hObjInv1 hTcbPre hStep
      · simp at hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.1 fold): `linkCallerReply` preserves `ipcStateQueueConsistent`.
The `.reply` store frames it; the caller `.tcb` store changes only `replyObject`
(ipcState unchanged). -/
private theorem linkCallerReply_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hInv : ipcStateQueueConsistent st) (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold SystemState.linkCallerReply at hStep
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hInv1 : ipcStateQueueConsistent st1 := by
      unfold SystemState.linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => simp [hGetR] at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · have hReplyAt : st.objects[rid.toObjId]? = some (.reply r) :=
            (getReply?_eq_some_iff st rid r).mp hGetR
          intro tid tcbT hTcb
          by_cases hEq : tid.toObjId = rid.toObjId
          · rw [hEq, storeObject_objects_eq st st1 rid.toObjId _ hObjInv hLink] at hTcb; cases hTcb
          · have hPreObj : st.objects[tid.toObjId]? = some (.tcb tcbT) := by
              rwa [storeObject_objects_ne st st1 rid.toObjId tid.toObjId _ hEq hObjInv hLink] at hTcb
            have hPre := hInv tid tcbT hPreObj
            cases hq : tcbT.ipcState with
            | ready | blockedOnNotification _ | blockedOnReply _ _ => exact True.intro
            | blockedOnSend epId =>
                rw [hq] at hPre; obtain ⟨ep, hEp⟩ := hPre
                have hNeEp : epId ≠ rid.toObjId := by
                  intro h; rw [h, hReplyAt] at hEp; cases hEp
                exact ⟨ep, by rw [storeObject_objects_ne st st1 rid.toObjId epId _ hNeEp hObjInv hLink]; exact hEp⟩
            | blockedOnReceive epId =>
                rw [hq] at hPre; obtain ⟨ep, hEp⟩ := hPre
                have hNeEp : epId ≠ rid.toObjId := by
                  intro h; rw [h, hReplyAt] at hEp; cases hEp
                exact ⟨ep, by rw [storeObject_objects_ne st st1 rid.toObjId epId _ hNeEp hObjInv hLink]; exact hEp⟩
            | blockedOnCall epId =>
                rw [hq] at hPre; obtain ⟨ep, hEp⟩ := hPre
                have hNeEp : epId ≠ rid.toObjId := by
                  intro h; rw [h, hReplyAt] at hEp; cases hEp
                exact ⟨ep, by rw [storeObject_objects_ne st st1 rid.toObjId epId _ hNeEp hObjInv hLink]; exact hEp⟩
        · simp at hLink
    have hObjInv1 := SystemState.linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · have hTcbPre : st1.objects[caller.toObjId]? = some (.tcb tcb) :=
          (SystemState.getTcb?_eq_some_iff st1 caller tcb).mp hT
        exact storeObject_tcb_readAgree_preserves_ipcStateQueueConsistent
          st1 st' caller.toObjId tcb { tcb with replyObject := some rid } rfl
          hInv1 hObjInv1 hTcbPre hStep
      · simp at hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.3 fold): `linkServerStashedReply` preserves `endpointQueueNoDup`.
Composes `linkCallerReply` with one server `.tcb` re-store that clears
`pendingReceiveReply` (`queueNext` unchanged). -/
private theorem linkServerStashedReply_preserves_endpointQueueNoDup
    (st st' : SystemState) (caller server : SeLe4n.ThreadId)
    (hInv : endpointQueueNoDup st) (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  unfold SystemState.linkServerStashedReply at hStep
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    cases hLink : SystemState.linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hInv1 := linkCallerReply_preserves_endpointQueueNoDup st st1 caller rid hInv hObjInv hLink
      have hObjInv1 := linkCallerReply_preserves_objects_invExt st st1 caller rid hObjInv hLink
      cases hT : st1.getTcb? server with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq; exact hInv1
      | some sTcb =>
        simp only [hT] at hStep
        have hTcbPre : st1.objects[server.toObjId]? = some (.tcb sTcb) :=
          (getTcb?_eq_some_iff st1 server sTcb).mp hT
        exact storeObject_tcb_readAgree_preserves_endpointQueueNoDup
          st1 st' server.toObjId sTcb { sTcb with pendingReceiveReply := none } rfl
          hInv1 hObjInv1 hTcbPre hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.3 fold): `linkServerStashedReply` preserves
`ipcStateQueueMembershipConsistent`.  The server `.tcb` re-store clears
`pendingReceiveReply` (`ipcState` + `queueNext` unchanged). -/
private theorem linkServerStashedReply_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (caller server : SeLe4n.ThreadId)
    (hInv : ipcStateQueueMembershipConsistent st) (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  unfold SystemState.linkServerStashedReply at hStep
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    cases hLink : SystemState.linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hInv1 := linkCallerReply_preserves_ipcStateQueueMembershipConsistent st st1 caller rid hInv hObjInv hLink
      have hObjInv1 := linkCallerReply_preserves_objects_invExt st st1 caller rid hObjInv hLink
      cases hT : st1.getTcb? server with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq; exact hInv1
      | some sTcb =>
        simp only [hT] at hStep
        have hTcbPre : st1.objects[server.toObjId]? = some (.tcb sTcb) :=
          (getTcb?_eq_some_iff st1 server sTcb).mp hT
        exact storeObject_tcb_readAgree_preserves_ipcStateQueueMembershipConsistent
          st1 st' server.toObjId sTcb { sTcb with pendingReceiveReply := none } rfl rfl
          hInv1 hObjInv1 hTcbPre hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.3 fold): `linkServerStashedReply` preserves
`ipcStateQueueConsistent`.  The server `.tcb` re-store clears `pendingReceiveReply`
(`ipcState` unchanged). -/
private theorem linkServerStashedReply_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (caller server : SeLe4n.ThreadId)
    (hInv : ipcStateQueueConsistent st) (hObjInv : st.objects.invExt)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold SystemState.linkServerStashedReply at hStep
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    cases hLink : SystemState.linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hInv1 := linkCallerReply_preserves_ipcStateQueueConsistent st st1 caller rid hInv hObjInv hLink
      have hObjInv1 := linkCallerReply_preserves_objects_invExt st st1 caller rid hObjInv hLink
      cases hT : st1.getTcb? server with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq; exact hInv1
      | some sTcb =>
        simp only [hT] at hStep
        have hTcbPre : st1.objects[server.toObjId]? = some (.tcb sTcb) :=
          (getTcb?_eq_some_iff st1 server sTcb).mp hT
        exact storeObject_tcb_readAgree_preserves_ipcStateQueueConsistent
          st1 st' server.toObjId sTcb { sTcb with pendingReceiveReply := none } rfl
          hInv1 hObjInv1 hTcbPre hStep


-- ============================================================================
-- WS-H12e/R3-B: Composed ipcInvariantFull preservation theorems
-- ============================================================================

-- R3-B/M-18: `notificationSignal_preserves_ipcInvariantFull` and
-- `notificationWait_preserves_ipcInvariantFull` (all four core components derived from
-- pre-state invariants) are defined at the **end** of this file in IPC de-threading D2
-- form — they thread only `replyCallerLinkageReciprocal st'` and *preserve* the third
-- clause via `notification{Signal,Wait}_preserves_blockedOnReplyHasReplyObject`, placed
-- after those frame theorems to satisfy definition ordering.

-- R3-B/M-18: `endpointReply_preserves_ipcInvariantFull` (all four core components derived
-- from pre-state invariants) is defined at the **end** of this file in IPC de-threading D2
-- form — it threads only `replyCallerLinkageReciprocal st'` and *preserves* the third
-- clause via `endpointReply_preserves_blockedOnReplyHasReplyObject`, placed after that
-- frame theorem to satisfy definition ordering.

-- ============================================================================
-- V3-K IPC operation proofs: endpointQueueNoDup preservation
-- ============================================================================

/-- V3-K-op-4: endpointSendDual preserves endpointQueueNoDup.
Rendezvous: PopHead + storeMsg + ensureRunnable chain.
Block: Enqueue (opposite empty) + storeMsg + removeRunnable chain. -/
theorem endpointSendDual_preserves_endpointQueueNoDup
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : endpointQueueNoDup st)
    (hDQSI : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Rendezvous path: PopHead + storeTcbIpcStateAndMessage + ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hDQSI1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant endpointId true st pair.2.2 pair.1 hObjInv hPop hDQSI
          cases hMsg : storeTcbReceiveComplete pair.2.2 pair.1 (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hNoDup1 := endpointQueuePopHead_preserves_endpointQueueNoDup endpointId true st pair.2.2 pair.1 pair.2.1 hInv hDQSI hDQSI1 hObjInv hPop
            exact ensureRunnable_preserves_endpointQueueNoDup _ _ <|
              storeTcbReceiveComplete_preserves_endpointQueueNoDup pair.2.2 st2 pair.1 (some msg) hNoDup1 hObjInv1 hMsg
      | none =>
        -- Block path: Enqueue + storeTcbIpcStateAndMessage + removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
          have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
            endpointId false sender st st1 hEnq hDQSI hObjInv hFreshSender hSendTailFresh
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hNoDup1 := endpointQueueEnqueue_preserves_endpointQueueNoDup endpointId false sender st st1 hInv hDQSI1 hObjInv
              (fun ep' hEp' => by simp only [Bool.false_eq]; rw [hEp'] at hObj; cases hObj; exact hHead) hEnq
            exact removeRunnable_preserves_endpointQueueNoDup _ _ <|
              storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup st1 st2 sender (.blockedOnSend endpointId) (some msg) hNoDup1 hObjInv1 hMsg

/-- V3-K-op-5: endpointReceiveDual preserves endpointQueueNoDup.
Rendezvous (Call sub-path): PopHead + storeMsg + storePendingMessage chain.
Rendezvous (Send sub-path): PopHead + storeMsg + ensureRunnable + storePendingMessage chain.
Block: Enqueue (opposite empty) + storeIpcState + removeRunnable chain. -/
theorem endpointReceiveDual_preserves_endpointQueueNoDup
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (hInv : endpointQueueNoDup st)
    (hDQSI : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st')) :
    endpointQueueNoDup st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Rendezvous: PopHead from sendQ
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hDQSI1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant endpointId false st pair.2.2 pair.1 hObjInv hPop hDQSI
          have hNoDup1 := endpointQueuePopHead_preserves_endpointQueueNoDup endpointId false st pair.2.2 pair.1 pair.2.1 hInv hDQSI hDQSI1 hObjInv hPop
          -- Case split on senderWasCall
          split at hStep
          · -- Call sub-path: storeTcbIpcStateAndMessage + linkCallerReply + receiver update
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
              have hNoDup2 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup pair.2.2 st2 pair.1 _ none hNoDup1 hObjInv1 hMsg
              -- WS-SM SM6.D (#7.1 fold): atomic reply-link of the dequeued caller.
              cases hReplyId : replyId with
              | none => simp [hReplyId] at hStep
              | some rid =>
                simp only [hReplyId] at hStep
                cases hLink : SystemState.linkCallerReply pair.1 rid st2 with
                | error e => simp [hLink] at hStep
                | ok pLink =>
                  obtain ⟨_, stLinked⟩ := pLink
                  simp only [hLink] at hStep
                  have hObjInvLink : stLinked.objects.invExt :=
                    linkCallerReply_preserves_objects_invExt st2 stLinked pair.1 rid hObjInv2 hLink
                  have hNoDupLink := linkCallerReply_preserves_endpointQueueNoDup st2 stLinked pair.1 rid hNoDup2 hObjInv2 hLink
                  -- AK1-D: atomic (.ready, senderMsg) receiver update
                  cases hPend : storeTcbIpcStateAndMessage stLinked receiver .ready pair.2.1.pendingMessage with
                  | error e => simp [hPend] at hStep
                  | ok st3 =>
                    simp only [hPend] at hStep
                    obtain ⟨_, rfl⟩ := hStep
                    exact storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup stLinked _ receiver _ _ hNoDupLink hObjInvLink hPend
          · -- Send sub-path: storeTcbIpcStateAndMessage + ensureRunnable + storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
              have hNoDup2 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup pair.2.2 st2 pair.1 _ none hNoDup1 hObjInv1 hMsg
              have hObjInvR : (ensureRunnable st2 pair.1).objects.invExt :=
                ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInv2
              have hNoDupR := ensureRunnable_preserves_endpointQueueNoDup st2 pair.1 hNoDup2
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready pair.2.1.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st3 =>
                simp only [hPend] at hStep
                obtain ⟨_, rfl⟩ := hStep
                exact storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup _ _ receiver _ _ hNoDupR hObjInvR hPend
      | none =>
        -- Block path: cleanup → Enqueue receiveQ + storeTcbIpcState + removeRunnable
        -- AI4-A: cleanupPreReceiveDonation before enqueue
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hInvClean := cleanupPreReceiveDonation_preserves_endpointQueueNoDup st receiver hObjInv hInv
          have hDQSIClean := cleanupPreReceiveDonation_preserves_dualQueueSystemInvariant st receiver hObjInv hDQSI
          have hFreshReceiverClean : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
              (cleanupPreReceiveDonation st receiver).objects[epId]? = some (.endpoint ep) →
              ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
              ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver :=
            fun epId ep hEp =>
              hFreshReceiver epId ep (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv epId ep hEp)
          have hRecvTailFreshClean : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
              (cleanupPreReceiveDonation st receiver).objects[endpointId]? = some (.endpoint ep) →
              ep.receiveQ.tail = some tailTid →
              ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
                (cleanupPreReceiveDonation st receiver).objects[epId']? = some (.endpoint ep') →
                (epId' ≠ endpointId →
                  ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
                (epId' = endpointId →
                  ep'.sendQ.tail ≠ some tailTid) :=
            fun ep tailTid hEp hTail epId' ep' hEp' =>
              hRecvTailFresh ep tailTid
                (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv endpointId ep hEp) hTail
                epId' ep'
                (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv epId' ep' hEp')
          have hObjClean := cleanupPreReceiveDonation_endpoint_forward st receiver hObjInv endpointId ep hObj
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hEnq hDQSIClean hObjInvClean hFreshReceiverClean hRecvTailFreshClean
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc] at hStep
              have hNoDup1 := endpointQueueEnqueue_preserves_endpointQueueNoDup endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hInvClean hDQSI1 hObjInvClean
                (fun ep' hEp' => by simp only [↓reduceIte]; rw [hEp'] at hObjClean; cases hObjClean; exact hHead) hEnq
              have hNoDup2 := storeTcbIpcState_preserves_endpointQueueNoDup st1 st2 receiver _ hNoDup1 hObjInv1 hIpc
              have hObjInv2 := storeTcbIpcState_preserves_objects_invExt st1 st2 receiver _ hObjInv1 hIpc
              -- WS-SM SM6.D (#7.1 fold): server-first stash store on the blocked receiver.
              cases hGetR : st2.getTcb? receiver with
              | none =>
                simp only [hGetR, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                exact removeRunnable_preserves_endpointQueueNoDup _ _ hNoDup2
              | some rTcb =>
                simp only [hGetR] at hStep
                cases hStash : storeObject receiver.toObjId
                    (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                | error e => simp [hStash] at hStep
                | ok pStash =>
                  obtain ⟨_, stStashed⟩ := pStash
                  simp only [hStash, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, rfl⟩ := hStep
                  have hTcbPre : st2.objects[receiver.toObjId]? = some (.tcb rTcb) :=
                    (SystemState.getTcb?_eq_some_iff st2 receiver rTcb).mp hGetR
                  exact removeRunnable_preserves_endpointQueueNoDup _ _
                    (storeObject_tcb_readAgree_preserves_endpointQueueNoDup
                      st2 stStashed receiver.toObjId rTcb
                      { rTcb with pendingReceiveReply := replyId } rfl
                      hNoDup2 hObjInv2 hTcbPre hStash)

/-- V3-K-op-6: endpointCall preserves endpointQueueNoDup.
Rendezvous: PopHead + storeMsg + ensureRunnable + storeIpcState + removeRunnable chain.
Block: Enqueue (opposite empty) + storeMsg + removeRunnable chain. -/
theorem endpointCall_preserves_endpointQueueNoDup
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : endpointQueueNoDup st)
    (hDQSI : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Rendezvous path: PopHead + storeMsg + ensureRunnable + storeIpcState + removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hDQSI1 := endpointQueuePopHead_preserves_dualQueueSystemInvariant endpointId true st pair.2.2 pair.1 hObjInv hPop hDQSI
          have hNoDup1 := endpointQueuePopHead_preserves_endpointQueueNoDup endpointId true st pair.2.2 pair.1 pair.2.1 hInv hDQSI hDQSI1 hObjInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ (some msg) hObjInv1 hMsg
            have hNoDup2 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup pair.2.2 st2 pair.1 _ (some msg) hNoDup1 hObjInv1 hMsg
            have hObjInvE : (ensureRunnable st2 pair.1).objects.invExt :=
                ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInv2
            have hNoDupE := ensureRunnable_preserves_endpointQueueNoDup st2 pair.1 hNoDup2
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage atomically clears caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st3 =>
              simp only [hIpc] at hStep
              have hNoDup3 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup _ st3 caller _ none hNoDupE hObjInvE hIpc
              have hObjInv3 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ st3 caller _ none hObjInvE hIpc
              -- WS-SM SM6.D (#7.3 fold): thread the server-first reply link.
              cases hLink : SystemState.linkServerStashedReply caller pair.1 st3 with
              | error e => simp [hLink] at hStep
              | ok pL =>
                obtain ⟨_, st5⟩ := pL
                simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                have hNoDup5 := linkServerStashedReply_preserves_endpointQueueNoDup st3 st5 caller pair.1 hNoDup3 hObjInv3 hLink
                exact removeRunnable_preserves_endpointQueueNoDup _ _ hNoDup5
      | none =>
        -- Block path: Enqueue + storeTcbIpcStateAndMessage + removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
          have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
            endpointId false caller st st1 hEnq hDQSI hObjInv hFreshCaller hSendTailFresh
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hNoDup1 := endpointQueueEnqueue_preserves_endpointQueueNoDup endpointId false caller st st1 hInv hDQSI1 hObjInv
              (fun ep' hEp' => by simp only [Bool.false_eq]; rw [hEp'] at hObj; cases hObj; exact hHead) hEnq
            exact removeRunnable_preserves_endpointQueueNoDup _ _ <|
              storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup st1 st2 caller _ (some msg) hNoDup1 hObjInv1 hMsg

/-- V3-K-op-7: endpointReplyRecv preserves endpointQueueNoDup.
Composes endpointReply (already proven) with endpointReceiveDual.
Freshness preconditions for the receiver are stated on the pre-state and
transported through the reply phase via endpoint backward lemmas. -/
theorem endpointReplyRecv_preserves_endpointQueueNoDup
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (replyId : Option SeLe4n.ReplyId)
    (st st' : SystemState)
    (hInv : endpointQueueNoDup st)
    (hDQSI : dualQueueSystemInvariant st)
    (hObjInv : st.objects.invExt)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    endpointQueueNoDup st' := by
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ expectedReplier =>
      simp only [hIpc] at hStep
      -- Use suffices to extract reply phase + receiveDual structure
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver replyId (ensureRunnable st1 replyTarget) = .ok stR →
            endpointQueueNoDup stR.2) by
        -- AK1-B (I-H02): Fail-closed on expectedReplier = none
        cases expectedReplier with
        | none => simp at hStep
        | some expected =>
          simp only at hStep
          split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver replyId (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
      -- Main proof body: reply phase + receive phase
      intro st1 hMsg stR hRecv
      have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget .ready (some msg) hObjInv hMsg
      have hNoDup1 := storeTcbIpcStateAndMessage_preserves_endpointQueueNoDup st st1 replyTarget .ready (some msg) hInv hObjInv hMsg
      have hDQSI1 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hObjInv hMsg hDQSI
      have hNoDupE := ensureRunnable_preserves_endpointQueueNoDup st1 replyTarget hNoDup1
      have hDQSIE := ensureRunnable_preserves_dualQueueSystemInvariant st1 replyTarget hDQSI1
      have hObjInvE : (ensureRunnable st1 replyTarget).objects.invExt :=
        ensureRunnable_preserves_objects st1 replyTarget ▸ hObjInv1
      -- Transport freshness through storeTcbIpcStateAndMessage + ensureRunnable
      have hFreshReceiver' : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
          (ensureRunnable st1 replyTarget).objects[epId]? = some (.endpoint ep) →
          ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
          ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver := by
        intro epId ep hEp
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp
        exact hFreshReceiver epId ep
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId ep hObjInv hMsg hEp)
      have hRecvTailFresh' : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
          (ensureRunnable st1 replyTarget).objects[endpointId]? = some (.endpoint ep) →
          ep.receiveQ.tail = some tailTid →
          ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
            (ensureRunnable st1 replyTarget).objects[epId']? = some (.endpoint ep') →
            (epId' ≠ endpointId →
              ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
            (epId' = endpointId →
              ep'.sendQ.tail ≠ some tailTid) := by
        intro ep tailTid hEp hTail epId' ep' hEp'
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp hEp'
        exact hRecvTailFresh ep tailTid
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) endpointId ep hObjInv hMsg hEp)
          hTail epId' ep'
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId' ep' hObjInv hMsg hEp')
      exact endpointReceiveDual_preserves_endpointQueueNoDup endpointId receiver replyId
        (ensureRunnable st1 replyTarget) stR.2 stR.1
        hNoDupE hDQSIE hObjInvE hFreshReceiver' hRecvTailFresh'
        (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)

-- ============================================================================
-- Section: Compound V3-J preservation for IPC operations
-- ============================================================================

/-- V3-J compound: endpointSendDual preserves ipcStateQueueMembershipConsistent.
Rendezvous path: PopHead(except_head) + storeTcb(.ready, partial→full) + ensureRunnable.
Block path: Enqueue + storeTcb(.blockedOnSend, general with reachability) + removeRunnable. -/
theorem endpointSendDual_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInvFull : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  have hInv := hInvFull.2.2.2.2.2.2.1
  have hDQSI := hInvFull.2.1
  have hQNBC := hInvFull.2.2.2.2.2.2.2.1
  have hQHBC := hInvFull.2.2.2.2.2.2.2.2.1
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hDQWF : dualQueueEndpointWellFormed endpointId st := hDQSI.1 endpointId ep hObj
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- RENDEZVOUS PATH: PopHead + storeTcb(.ready) + ensureRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨receiver, headTcb, st1⟩ := triple
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st st1 receiver headTcb hObjInv hPop
          -- Derive hHeadBlocked from queueHeadBlockedConsistent
          have hHeadBlocked : headTcb.ipcState = .blockedOnReceive endpointId := by
            have hRetH := endpointQueuePopHead_returns_head endpointId true st ep receiver st1 hObj hPop
            simp only [↓reduceIte] at hRetH
            have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId true st ep receiver headTcb st1 hObj hPop
            exact (hQHBC endpointId ep receiver headTcb hObj hPreTcb).1 hRetH
          have hPartialV3J :=
            endpointQueuePopHead_preserves_ipcStateQueueMembershipConsistent_except_head
              endpointId true st st1 receiver headTcb ep hInv hObjInv hQNBC hObj
              (by simp only [↓reduceIte]; exact hHeadBlocked) hPop
          cases hMsg : storeTcbReceiveComplete st1 receiver (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            exact ensureRunnable_preserves_ipcStateQueueMembershipConsistent st2 receiver <|
              storeTcbReceiveComplete_partial_preserves_ipcStateQueueMembershipConsistent
                st1 st2 receiver (some msg) hPartialV3J hObjInv1 hMsg
      | none =>
        -- BLOCK PATH: Enqueue + storeTcb(.blockedOnSend) + removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
            endpointId false sender st st1 hObjInv hEnq
          have hV3J1 := endpointQueueEnqueue_preserves_ipcStateQueueMembershipConsistent
            endpointId false sender st st1 hInv hObjInv hDQWF hEnq
          -- Get DQSI for st1 (for acyclicity)
          have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
            endpointId false sender st st1 hEnq hDQSI hObjInv hFreshSender
            (fun ep' tailTid hEp' hTail epId' ep'' hEp'' => by
              rw [hObj] at hEp'; cases hEp'
              exact hSendTailFresh ep tailTid hObj hTail epId' ep'' hEp'')
          -- Get reachability for sender after enqueue
          have hNotTail : ∀ ep', st.objects[endpointId]? = some (.endpoint ep') →
              (if false then ep'.receiveQ else ep'.sendQ).tail ≠ some sender := by
            intro ep' hEp'
            rw [hObj] at hEp'; cases hEp'
            exact (hFreshSender endpointId ep hObj).2.1
          have hReach := endpointQueueEnqueue_thread_reachable
            endpointId false sender st st1 hObjInv hNotTail hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            -- sender.toObjId ≠ endpointId (TCB vs endpoint)
            have hNeSenderEp : endpointId ≠ sender.toObjId := by
              intro h; unfold endpointQueueEnqueue at hEnq
              rw [hObj] at hEnq; simp only at hEnq
              cases hL : lookupTcb st sender with
              | none => simp [hL] at hEnq
              | some tcb =>
                have := lookupTcb_some_objects st sender tcb hL
                rw [← h, hObj] at this; cases this
            exact removeRunnable_preserves_ipcStateQueueMembershipConsistent st2 sender <|
              storeTcbIpcStateAndMessage_general_preserves_ipcStateQueueMembershipConsistent
                st1 st2 sender (.blockedOnSend endpointId) (some msg) hV3J1 hObjInv1 hMsg
                (fun epId hEq => by
                  cases hEq
                  obtain ⟨ep', hEp1, hR⟩ := hReach
                  have hEpFrame := storeTcbIpcStateAndMessage_preserves_objects_ne
                    st1 st2 sender (.blockedOnSend endpointId) (some msg)
                    endpointId hNeSenderEp hObjInv1 hMsg
                  rw [hEpFrame]
                  exact ⟨ep', hEp1, hR.elim Or.inl fun ⟨prev, prevTcb, hP, hQN⟩ => by
                    refine Or.inr ⟨prev, prevTcb, ?_, hQN⟩
                    have hNePrev : prev.toObjId ≠ sender.toObjId := by
                      intro h
                      have hPrevEq := ThreadId.toObjId_injective prev sender h
                      rw [hPrevEq] at hP
                      exact absurd hQN (tcbQueueChainAcyclic_no_self_loop hDQSI1.2.2 sender prevTcb hP)
                    rw [storeTcbIpcStateAndMessage_preserves_objects_ne
                      st1 st2 sender (.blockedOnSend endpointId) (some msg)
                      prev.toObjId hNePrev hObjInv1 hMsg]
                    exact hP⟩)
                (fun _ h => absurd h (by simp))
                (fun _ h => absurd h (by simp))

/-- V3-J compound: endpointReceiveDual preserves ipcStateQueueMembershipConsistent.
Rendezvous (Call sub-path): PopHead(sendQ) + storeTcb(.blockedOnReply) + storeTcbPendingMessage.
Rendezvous (Send sub-path): PopHead(sendQ) + storeTcb(.ready) + ensureRunnable + storeTcbPendingMessage.
Block path: Enqueue(receiveQ) + storeTcbIpcState(.blockedOnReceive, general) + removeRunnable. -/
theorem endpointReceiveDual_preserves_ipcStateQueueMembershipConsistent
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId)
    (hInv : ipcStateQueueMembershipConsistent st)
    (hDQSI : dualQueueSystemInvariant st)
    (hQNBC : queueNextBlockingConsistent st)
    (hQHBC : queueHeadBlockedConsistent st)
    (hObjInv : st.objects.invExt)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st')) :
    ipcStateQueueMembershipConsistent st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hDQWF : dualQueueEndpointWellFormed endpointId st := hDQSI.1 endpointId ep hObj
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- RENDEZVOUS: PopHead from sendQ
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          -- Head was in sendQ, so blocked on send or call
          have hHeadBlocked :
              pair.2.1.ipcState = .blockedOnSend endpointId ∨
              pair.2.1.ipcState = .blockedOnCall endpointId := by
            have hRetH := endpointQueuePopHead_returns_head endpointId false st ep pair.1 pair.2.2 hObj hPop
            have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId false st ep pair.1 pair.2.1 pair.2.2 hObj hPop
            exact (hQHBC endpointId ep pair.1 pair.2.1 hObj hPreTcb).2 hRetH
          have hPartialV3J :=
            endpointQueuePopHead_preserves_ipcStateQueueMembershipConsistent_except_head
              endpointId false st pair.2.2 pair.1 pair.2.1 ep hInv hObjInv hQNBC hObj
              hHeadBlocked hPop
          split at hStep
          · -- Call sub-path: storeTcb(.blockedOnReply) + linkCallerReply + receiver update
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
              have hV3J2 :=
                storeTcbIpcStateAndMessage_partial_preserves_ipcStateQueueMembershipConsistent
                  pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hPartialV3J hObjInv1
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp)) hMsg
              -- WS-SM SM6.D (#7.1 fold): atomic reply-link of the dequeued caller.
              cases hReplyId : replyId with
              | none => simp [hReplyId] at hStep
              | some rid =>
                simp only [hReplyId] at hStep
                cases hLink : SystemState.linkCallerReply pair.1 rid st2 with
                | error e => simp [hLink] at hStep
                | ok pLink =>
                  obtain ⟨_, stLinked⟩ := pLink
                  simp only [hLink] at hStep
                  have hObjInvLink : stLinked.objects.invExt :=
                    linkCallerReply_preserves_objects_invExt st2 stLinked pair.1 rid hObjInv2 hLink
                  have hV3JLink := linkCallerReply_preserves_ipcStateQueueMembershipConsistent st2 stLinked pair.1 rid hV3J2 hObjInv2 hLink
                  -- AK1-D: atomic (.ready, senderMsg) receiver update
                  cases hPend : storeTcbIpcStateAndMessage stLinked receiver .ready pair.2.1.pendingMessage with
                  | error e => simp [hPend] at hStep
                  | ok st3 =>
                    simp only [hPend] at hStep; obtain ⟨_, rfl⟩ := hStep
                    exact storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
                      stLinked _ receiver .ready _ hV3JLink hObjInvLink
                      (fun epId h => absurd h (by simp))
                      (fun epId h => absurd h (by simp))
                      (fun epId h => absurd h (by simp)) hPend
          · -- Send sub-path: storeTcb(.ready) + ensureRunnable + storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInv1 hMsg
              have hV3J2 :=
                storeTcbIpcStateAndMessage_partial_preserves_ipcStateQueueMembershipConsistent
                  pair.2.2 st2 pair.1 .ready none hPartialV3J hObjInv1
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp)) hMsg
              have hObjInvR : (ensureRunnable st2 pair.1).objects.invExt :=
                ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInv2
              have hV3JR := ensureRunnable_preserves_ipcStateQueueMembershipConsistent st2 pair.1 hV3J2
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready pair.2.1.pendingMessage with
              | error e => simp [hPend] at hStep
              | ok st3 =>
                simp only [hPend] at hStep; obtain ⟨_, rfl⟩ := hStep
                exact storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
                  _ _ receiver .ready _ hV3JR hObjInvR
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp))
                  (fun epId h => absurd h (by simp)) hPend
      | none =>
        -- BLOCK PATH: cleanup → Enqueue(receiveQ) + storeTcbIpcState(.blockedOnReceive) + removeRunnable
        -- AI4-A: cleanupPreReceiveDonation before enqueue
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hInvClean := cleanupPreReceiveDonation_preserves_ipcStateQueueMembershipConsistent st receiver hObjInv hInv
          have hDQSIClean := cleanupPreReceiveDonation_preserves_dualQueueSystemInvariant st receiver hObjInv hDQSI
          have hObjClean := cleanupPreReceiveDonation_endpoint_forward st receiver hObjInv endpointId ep hObj
          have hDQWFClean := cleanupPreReceiveDonation_preserves_dualQueueEndpointWellFormed st receiver hObjInv hDQSI endpointId ep hObjClean
          have hFreshReceiverClean : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
              (cleanupPreReceiveDonation st receiver).objects[epId]? = some (.endpoint ep) →
              ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
              ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver :=
            fun epId ep hEp =>
              hFreshReceiver epId ep (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv epId ep hEp)
          have hRecvTailFreshClean : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
              (cleanupPreReceiveDonation st receiver).objects[endpointId]? = some (.endpoint ep) →
              ep.receiveQ.tail = some tailTid →
              ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
                (cleanupPreReceiveDonation st receiver).objects[epId']? = some (.endpoint ep') →
                (epId' ≠ endpointId →
                  ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
                (epId' = endpointId →
                  ep'.sendQ.tail ≠ some tailTid) :=
            fun ep tailTid hEp hTail epId' ep' hEp' =>
              hRecvTailFresh ep tailTid
                (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv endpointId ep hEp) hTail
                epId' ep'
                (cleanupPreReceiveDonation_endpoint_backward st receiver hObjInv epId' ep' hEp')
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hV3J1 := endpointQueueEnqueue_preserves_ipcStateQueueMembershipConsistent
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hInvClean hObjInvClean hDQWFClean hEnq
            have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hEnq hDQSIClean hObjInvClean hFreshReceiverClean hRecvTailFreshClean
            have hNotTail : ∀ ep', (cleanupPreReceiveDonation st receiver).objects[endpointId]? = some (.endpoint ep') →
                (if true then ep'.receiveQ else ep'.sendQ).tail ≠ some receiver := by
              intro ep' hEp'
              rw [hObjClean] at hEp'; cases hEp'
              exact (hFreshReceiverClean endpointId ep hObjClean).2.2.2
            have hReach := endpointQueueEnqueue_thread_reachable
              endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hNotTail hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc] at hStep
              have hNeRecvEp : endpointId ≠ receiver.toObjId := by
                intro h; unfold endpointQueueEnqueue at hEnq
                rw [hObjClean] at hEnq; simp only at hEnq
                cases hL : lookupTcb (cleanupPreReceiveDonation st receiver) receiver with
                | none => simp [hL] at hEnq
                | some tcb =>
                  have := lookupTcb_some_objects (cleanupPreReceiveDonation st receiver) receiver tcb hL
                  rw [← h, hObjClean] at this; cases this
              have hObjInv2 := storeTcbIpcState_preserves_objects_invExt st1 st2 receiver _ hObjInv1 hIpc
              have hV3J2 :=
                storeTcbIpcState_general_preserves_ipcStateQueueMembershipConsistent
                  st1 st2 receiver (.blockedOnReceive endpointId) hV3J1 hObjInv1 hIpc
                  (fun _ h => absurd h (by simp))
                  (fun epId hEq => by
                    cases hEq
                    obtain ⟨ep', hEp1, hR⟩ := hReach
                    have hEpFrame := storeTcbIpcState_preserves_objects_ne
                      st1 st2 receiver (.blockedOnReceive endpointId)
                      endpointId hNeRecvEp hObjInv1 hIpc
                    rw [hEpFrame]
                    exact ⟨ep', hEp1, hR.elim Or.inl fun ⟨prev, prevTcb, hP, hQN⟩ => by
                      refine Or.inr ⟨prev, prevTcb, ?_, hQN⟩
                      have hNePrev : prev.toObjId ≠ receiver.toObjId := by
                        intro h
                        have hPrevEq := ThreadId.toObjId_injective prev receiver h
                        rw [hPrevEq] at hP
                        exact absurd hQN (tcbQueueChainAcyclic_no_self_loop hDQSI1.2.2 receiver prevTcb hP)
                      rw [storeTcbIpcState_preserves_objects_ne
                        st1 st2 receiver (.blockedOnReceive endpointId)
                        prev.toObjId hNePrev hObjInv1 hIpc]
                      exact hP⟩)
                  (fun _ h => absurd h (by simp))
              -- WS-SM SM6.D (#7.1 fold): server-first stash store on the blocked receiver.
              cases hGetR : st2.getTcb? receiver with
              | none =>
                simp only [hGetR, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                exact removeRunnable_preserves_ipcStateQueueMembershipConsistent _ receiver hV3J2
              | some rTcb =>
                simp only [hGetR] at hStep
                cases hStash : storeObject receiver.toObjId
                    (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                | error e => simp [hStash] at hStep
                | ok pStash =>
                  obtain ⟨_, stStashed⟩ := pStash
                  simp only [hStash, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, rfl⟩ := hStep
                  have hTcbPre : st2.objects[receiver.toObjId]? = some (.tcb rTcb) :=
                    (SystemState.getTcb?_eq_some_iff st2 receiver rTcb).mp hGetR
                  exact removeRunnable_preserves_ipcStateQueueMembershipConsistent _ receiver
                    (storeObject_tcb_readAgree_preserves_ipcStateQueueMembershipConsistent
                      st2 stStashed receiver.toObjId rTcb
                      { rTcb with pendingReceiveReply := replyId } rfl rfl
                      hV3J2 hObjInv2 hTcbPre hStash)

/-- V3-J compound: endpointCall preserves ipcStateQueueMembershipConsistent.
Rendezvous: PopHead(receiveQ) + storeTcb(.ready, partial→full) + ensureRunnable +
storeTcbIpcState(.blockedOnReply) + removeRunnable.
Block: Enqueue(sendQ) + storeTcb(.blockedOnCall, general) + removeRunnable. -/
theorem endpointCall_preserves_ipcStateQueueMembershipConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInvFull : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hFreshCaller : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some caller ∧ ep.sendQ.tail ≠ some caller ∧
      ep.receiveQ.head ≠ some caller ∧ ep.receiveQ.tail ≠ some caller)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid))
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  have hInv := hInvFull.2.2.2.2.2.2.1
  have hDQSI := hInvFull.2.1
  have hQNBC := hInvFull.2.2.2.2.2.2.2.1
  have hQHBC := hInvFull.2.2.2.2.2.2.2.2.1
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      have hDQWF : dualQueueEndpointWellFormed endpointId st := hDQSI.1 endpointId ep hObj
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- RENDEZVOUS: PopHead(receiveQ) + storeTcb(.ready) + ensureRunnable + storeTcbIpcState(.blockedOnReply) + removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt
            endpointId true st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hHeadBlocked : pair.2.1.ipcState = .blockedOnReceive endpointId := by
            have hRetH := endpointQueuePopHead_returns_head endpointId true st ep pair.1 pair.2.2 hObj hPop
            have hPreTcb := endpointQueuePopHead_returns_pre_tcb endpointId true st ep pair.1 pair.2.1 pair.2.2 hObj hPop
            exact (hQHBC endpointId ep pair.1 pair.2.1 hObj hPreTcb).1 hRetH
          have hPartialV3J :=
            endpointQueuePopHead_preserves_ipcStateQueueMembershipConsistent_except_head
              endpointId true st pair.2.2 pair.1 pair.2.1 ep hInv hObjInv hQNBC hObj
              (by simp only [↓reduceIte]; exact hHeadBlocked) hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ (some msg) hObjInv1 hMsg
            have hV3J2 :=
              storeTcbIpcStateAndMessage_partial_preserves_ipcStateQueueMembershipConsistent
                pair.2.2 st2 pair.1 .ready (some msg) hPartialV3J hObjInv1
                (fun epId h => absurd h (by simp))
                (fun epId h => absurd h (by simp))
                (fun epId h => absurd h (by simp)) hMsg
            have hObjInvE : (ensureRunnable st2 pair.1).objects.invExt :=
              ensureRunnable_preserves_objects st2 pair.1 ▸ hObjInv2
            have hV3JE := ensureRunnable_preserves_ipcStateQueueMembershipConsistent st2 pair.1 hV3J2
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage atomically clears caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st3 =>
              simp only [hIpc] at hStep
              have hV3J3 := storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
                  _ st3 caller _ none hV3JE hObjInvE
                  (fun _ h => absurd h (by simp))
                  (fun _ h => absurd h (by simp))
                  (fun _ h => absurd h (by simp)) hIpc
              have hObjInv3 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ st3 caller _ none hObjInvE hIpc
              -- WS-SM SM6.D (#7.3 fold): thread the server-first reply link.
              cases hLink : SystemState.linkServerStashedReply caller pair.1 st3 with
              | error e => simp [hLink] at hStep
              | ok pL =>
                obtain ⟨_, st5⟩ := pL
                simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                have hV3J5 := linkServerStashedReply_preserves_ipcStateQueueMembershipConsistent st3 st5 caller pair.1 hV3J3 hObjInv3 hLink
                exact removeRunnable_preserves_ipcStateQueueMembershipConsistent _ caller hV3J5
      | none =>
        -- BLOCK PATH: Enqueue(sendQ) + storeTcbIpcStateAndMessage(.blockedOnCall) + removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt
            endpointId false caller st st1 hObjInv hEnq
          have hV3J1 := endpointQueueEnqueue_preserves_ipcStateQueueMembershipConsistent
            endpointId false caller st st1 hInv hObjInv hDQWF hEnq
          have hDQSI1 := endpointQueueEnqueue_preserves_dualQueueSystemInvariant
            endpointId false caller st st1 hEnq hDQSI hObjInv hFreshCaller hSendTailFresh
          have hNotTail : ∀ ep', st.objects[endpointId]? = some (.endpoint ep') →
              (if false then ep'.receiveQ else ep'.sendQ).tail ≠ some caller := by
            intro ep' hEp'
            rw [hObj] at hEp'; cases hEp'
            exact (hFreshCaller endpointId ep hObj).2.1
          have hReach := endpointQueueEnqueue_thread_reachable
            endpointId false caller st st1 hObjInv hNotTail hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hNeCallerEp : endpointId ≠ caller.toObjId := by
              intro h; unfold endpointQueueEnqueue at hEnq
              rw [hObj] at hEnq; simp only at hEnq
              cases hL : lookupTcb st caller with
              | none => simp [hL] at hEnq
              | some tcb =>
                have := lookupTcb_some_objects st caller tcb hL
                rw [← h, hObj] at this; cases this
            exact removeRunnable_preserves_ipcStateQueueMembershipConsistent st2 caller <|
              storeTcbIpcStateAndMessage_general_preserves_ipcStateQueueMembershipConsistent
                st1 st2 caller (.blockedOnCall endpointId) (some msg) hV3J1 hObjInv1 hMsg
                (fun _ h => absurd h (by simp))
                (fun _ h => absurd h (by simp))
                (fun epId hEq => by
                  cases hEq
                  obtain ⟨ep', hEp1, hR⟩ := hReach
                  have hEpFrame := storeTcbIpcStateAndMessage_preserves_objects_ne
                    st1 st2 caller (.blockedOnCall endpointId) (some msg)
                    endpointId hNeCallerEp hObjInv1 hMsg
                  rw [hEpFrame]
                  exact ⟨ep', hEp1, hR.elim Or.inl fun ⟨prev, prevTcb, hP, hQN⟩ => by
                    refine Or.inr ⟨prev, prevTcb, ?_, hQN⟩
                    have hNePrev : prev.toObjId ≠ caller.toObjId := by
                      intro h
                      have hPrevEq := ThreadId.toObjId_injective prev caller h
                      rw [hPrevEq] at hP
                      exact absurd hQN (tcbQueueChainAcyclic_no_self_loop hDQSI1.2.2 caller prevTcb hP)
                    rw [storeTcbIpcStateAndMessage_preserves_objects_ne
                      st1 st2 caller (.blockedOnCall endpointId) (some msg)
                      prev.toObjId hNePrev hObjInv1 hMsg]
                    exact hP⟩)

/-- V3-J compound: endpointReplyRecv preserves ipcStateQueueMembershipConsistent.
Composes reply phase (storeTcb + ensureRunnable) with endpointReceiveDual. -/
theorem endpointReplyRecv_preserves_ipcStateQueueMembershipConsistent
    (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (replyId : Option SeLe4n.ReplyId) (st st' : SystemState)
    (hInvFull : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.sendQ.tail ≠ some tailTid))
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    ipcStateQueueMembershipConsistent st' := by
  have hInv := hInvFull.2.2.2.2.2.2.1
  have hDQSI := hInvFull.2.1
  have hQNBC := hInvFull.2.2.2.2.2.2.2.1
  have hQHBC := hInvFull.2.2.2.2.2.2.2.2.1
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some replyTcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : replyTcb.ipcState with
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnCall _ =>
      simp [hIpc] at hStep
    | blockedOnReply _ expectedReplier =>
      simp only [hIpc] at hStep
      suffices ∀ st1, storeTcbIpcStateAndMessage st replyTarget .ready (some msg) = .ok st1 →
          (∀ stR, endpointReceiveDual endpointId receiver replyId (ensureRunnable st1 replyTarget) = .ok stR →
            ipcStateQueueMembershipConsistent stR.2) by
        -- AK1-B (I-H02): Fail-closed on expectedReplier = none
        cases expectedReplier with
        | none => simp at hStep
        | some expected =>
          simp only at hStep
          split at hStep
          · revert hStep
            cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
            | error e => simp
            | ok st1 =>
              simp only []
              cases hRecv : endpointReceiveDual endpointId receiver replyId (ensureRunnable st1 replyTarget) with
              | error e => simp
              | ok result =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, hEq⟩; subst hEq
                exact this st1 hMsg result hRecv
          · simp_all
      -- Main proof body
      intro st1 hMsg stR hRecv
      have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget _ (some msg) hObjInv hMsg
      have hV3J1 := storeTcbIpcStateAndMessage_preserves_ipcStateQueueMembershipConsistent
        st st1 replyTarget .ready (some msg) hInv hObjInv
        (fun _ h => by cases h) (fun _ h => by cases h) (fun _ h => by cases h) hMsg
      have hDQSI1 := storeTcbIpcStateAndMessage_preserves_dualQueueSystemInvariant _ _ _ _ _ hObjInv hMsg hDQSI
      have hQNBC1 := storeTcbIpcStateAndMessage_ready_preserves_queueNextBlockingConsistent
        st st1 replyTarget (some msg) hQNBC hObjInv hMsg
      have hObjInvE : (ensureRunnable st1 replyTarget).objects.invExt :=
        ensureRunnable_preserves_objects st1 replyTarget ▸ hObjInv1
      have hV3JE := ensureRunnable_preserves_ipcStateQueueMembershipConsistent st1 replyTarget hV3J1
      have hDQSIE := ensureRunnable_preserves_dualQueueSystemInvariant st1 replyTarget hDQSI1
      have hQNBCE := ensureRunnable_preserves_queueNextBlockingConsistent st1 replyTarget hQNBC1
      -- QHBC: replyTarget was .blockedOnReply, so it's not a queue head by pre-state QHBC.
      -- storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent needs hNotHead.
      have hNotHead : ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
          st.objects[epId']? = some (.endpoint ep') →
          ep'.receiveQ.head ≠ some replyTarget ∧ ep'.sendQ.head ≠ some replyTarget := by
        intro epId' ep' hEp'
        constructor <;> intro hH
        · have := (hQHBC epId' ep' replyTarget replyTcb hEp'
            (lookupTcb_some_objects st replyTarget replyTcb hLookup)).1 hH
          rw [hIpc] at this; cases this
        · have := (hQHBC epId' ep' replyTarget replyTcb hEp'
            (lookupTcb_some_objects st replyTarget replyTcb hLookup)).2 hH
          rw [hIpc] at this; cases this with
          | inl h => cases h
          | inr h => cases h
      have hQHBC1 := storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent
        st st1 replyTarget .ready (some msg) hQHBC hObjInv hMsg hNotHead
      have hQHBCE := ensureRunnable_preserves_queueHeadBlockedConsistent st1 replyTarget hQHBC1
      -- Transport freshness conditions through reply phase
      have hFreshReceiver' : ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
          (ensureRunnable st1 replyTarget).objects[epId']? = some (.endpoint ep') →
          ep'.sendQ.head ≠ some receiver ∧ ep'.sendQ.tail ≠ some receiver ∧
          ep'.receiveQ.head ≠ some receiver ∧ ep'.receiveQ.tail ≠ some receiver := by
        intro epId' ep' hEp'
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp'
        exact hFreshReceiver epId' ep'
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId' ep' hObjInv hMsg hEp')
      have hRecvTailFresh' : ∀ (ep' : Endpoint) (tailTid : SeLe4n.ThreadId),
          (ensureRunnable st1 replyTarget).objects[endpointId]? = some (.endpoint ep') →
          ep'.receiveQ.tail = some tailTid →
          ∀ (epId' : SeLe4n.ObjId) (ep'' : Endpoint),
            (ensureRunnable st1 replyTarget).objects[epId']? = some (.endpoint ep'') →
            (epId' ≠ endpointId →
              ep''.sendQ.tail ≠ some tailTid ∧ ep''.receiveQ.tail ≠ some tailTid) ∧
            (epId' = endpointId →
              ep''.sendQ.tail ≠ some tailTid) := by
        intro ep' tailTid hEp' hTail epId' ep'' hEp''
        rw [show (ensureRunnable st1 replyTarget).objects = st1.objects from
          ensureRunnable_preserves_objects st1 replyTarget] at hEp' hEp''
        exact hRecvTailFresh ep' tailTid
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) endpointId ep' hObjInv hMsg hEp')
          hTail epId' ep''
          (storeTcbIpcStateAndMessage_endpoint_backward st st1 replyTarget .ready (some msg) epId' ep'' hObjInv hMsg hEp'')
      -- Delegate to endpointReceiveDual preservation
      exact endpointReceiveDual_preserves_ipcStateQueueMembershipConsistent
        endpointId receiver replyId _ stR.2 stR.1
        hV3JE hDQSIE hQNBCE hQHBCE hObjInvE hFreshReceiver' hRecvTailFresh'
        (by have : stR = (stR.1, stR.2) := Prod.ext rfl rfl; rw [this] at hRecv; exact hRecv)

-- U4-K/R3-B: `endpointSendDual_preserves_ipcInvariantFull` (`allPendingMessagesBounded` /
-- `badgeWellFormed` derived internally; only `dualQueueSystemInvariant` needs freshness
-- preconditions) is defined at the **end** of this file in IPC de-threading D2 form:
-- it threads only `replyCallerLinkageReciprocal st'` and *preserves* the third clause via
-- `endpointSendDual_preserves_blockedOnReplyHasReplyObject`, placed after that frame
-- theorem to satisfy definition ordering.

-- IPC de-threading D2: `endpointReceiveDual_preserves_ipcInvariantFull` and
-- `endpointCall_preserves_ipcInvariantFull` are defined at the **end** of this file in
-- *de-threaded* form: they no longer assume the full `replyCallerLinkage st'`, instead
-- threading only its reciprocal half (`replyCallerLinkageReciprocal st'`) and concretely
-- *establishing* the third clause (`blockedOnReplyHasReplyObject st'`) from the pre-state
-- via `endpoint{ReceiveDual,Call}_establishes_blockedOnReplyHasReplyObject`.  They are
-- placed after those establish theorems to satisfy definition ordering.  (The reciprocal
-- half was threaded pre-#7.4; de-threading the new third clause is the #7.4 origin-gap
-- closure at the transition boundary.)

-- U4-K: `endpointReplyRecv_preserves_ipcInvariantFull` (`allPendingMessagesBounded` /
-- `badgeWellFormed` derived internally) is defined at the **end** of this file in IPC
-- de-threading D2 form — it threads only `replyCallerLinkageReciprocal st'` and *preserves*
-- the third clause via `endpointReplyRecv_preserves_blockedOnReplyHasReplyObject` (which
-- composes the unblock frame with the `endpointReceiveDual` receive-leg establish), placed
-- after that frame theorem to satisfy definition ordering.

/-- T4-K (L-P10): Convenience theorem for composing `ipcInvariantFull` from its
individual components. Reduces boilerplate for callers that must manually
compose the invariant by providing all proofs in one call. -/
theorem ipcInvariantFull_compositional
    (st : SystemState)
    (hIpc : ipcInvariant st)
    (hDual : dualQueueSystemInvariant st)
    (hBounded : allPendingMessagesBounded st)
    (hBadge : badgeWellFormed st)
    (hWtpmn : waitingThreadsPendingMessageNone st)
    (hNoDup : endpointQueueNoDup st)
    (hQMC : ipcStateQueueMembershipConsistent st)
    (hQNBC : queueNextBlockingConsistent st)
    (hQHBC : queueHeadBlockedConsistent st)
    (hBlockedTimeout : blockedThreadTimeoutConsistent st)
    (hDCA : donationChainAcyclic st)
    (hDOV : donationOwnerValid st)
    (hPSI : passiveServerIdle st)
    (hDBT : donationBudgetTransfer st)
    (hBRT : blockedOnReplyHasTarget st)
    (hRCL : replyCallerLinkage st)
    (hPRR : pendingReceiveReplyWellFormed st) :
    ipcInvariantFull st :=
  ⟨hIpc, hDual, hBounded, hBadge, hWtpmn, hNoDup, hQMC, hQNBC, hQHBC, hBlockedTimeout, hDCA, hDOV, hPSI, hDBT, hBRT, hRCL, hPRR⟩

-- ============================================================================
-- T4-E/F (M-IPC-3): WithCaps wrappers preserve ipcInvariantFull
-- ============================================================================

-- T4-E (M-IPC-3): `endpointSendDualWithCaps_preserves_ipcInvariantFull` is defined at the
-- **end** of this file in IPC de-threading D2 form (threads only
-- `replyCallerLinkageReciprocal st'`; preserves the third clause via
-- `endpointSendDualWithCaps_preserves_blockedOnReplyHasReplyObject`).
-- T4-F (M-IPC-3): `endpointReceiveDualWithCaps_preserves_ipcInvariantFull` is defined at
-- the **end** of this file in IPC de-threading D2 form (threads only
-- `replyCallerLinkageReciprocal st'`; establishes the third clause via
-- `endpointReceiveDualWithCaps_establishes_blockedOnReplyHasReplyObject`).
-- T4-E (M-IPC-3): `endpointCallWithCaps_preserves_ipcInvariantFull` is defined at the
-- **end** of this file in IPC de-threading D2 form (threads only
-- `replyCallerLinkageReciprocal st'`; establishes the third clause via
-- `endpointCallWithCaps_establishes_blockedOnReplyHasReplyObject`).

-- ============================================================================
-- WS-L3/L3-B: Standalone tcbQueueLinkIntegrity preservation
-- ============================================================================

/-- WS-L3/L3-B1: PopHead preserves `tcbQueueLinkIntegrity` as a standalone
property. Extracts from the bundled `dualQueueSystemInvariant` preservation. -/
theorem endpointQueuePopHead_preserves_tcbQueueLinkIntegrity
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hInv : dualQueueSystemInvariant st) :
    tcbQueueLinkIntegrity st' :=
  (endpointQueuePopHead_preserves_dualQueueSystemInvariant
    endpointId isReceiveQ st st' tid hObjInv hStep hInv).2.1

/-- WS-L3/L3-B2: Enqueue preserves `tcbQueueLinkIntegrity` as a standalone
property. Extracts from the bundled `dualQueueSystemInvariant` preservation. -/
theorem endpointQueueEnqueue_preserves_tcbQueueLinkIntegrity
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hInv : dualQueueSystemInvariant st)
    (hFreshTid : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some enqueueTid ∧ ep.sendQ.tail ≠ some enqueueTid ∧
      ep.receiveQ.head ≠ some enqueueTid ∧ ep.receiveQ.tail ≠ some enqueueTid)
    (hTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      (if isReceiveQ then ep.receiveQ else ep.sendQ).tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          (if isReceiveQ then ep'.sendQ else ep'.receiveQ).tail ≠ some tailTid)) :
    tcbQueueLinkIntegrity st' :=
  (endpointQueueEnqueue_preserves_dualQueueSystemInvariant
    endpointId isReceiveQ enqueueTid st st' hStep hInv hObjInv hFreshTid hTailFresh).2.1

-- ============================================================================
-- WS-L3/L3-C2: ipcStateQueueConsistent preservation for queue operations
-- ============================================================================

/-- WS-L3/L3-C2: PopHead preserves ipcStateQueueConsistent. PopHead does not
modify any thread's ipcState and preserves all endpoints, so the forward
implication (blocked → endpoint exists) is maintained. -/
theorem endpointQueuePopHead_preserves_ipcStateQueueConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (headTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid, headTcb, st'))
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  -- Step 1: find the pre-state TCB with same ipcState
  obtain ⟨tcb, hTcb, hIpc⟩ := endpointQueuePopHead_tcb_ipcState_backward
    endpointId isReceiveQ st st' tid tid' tcb' hObjInv hStep hTcb'
  -- Step 2: apply pre-state invariant
  have hPre := hInv tid' tcb hTcb
  -- Step 3: show endpoints survive the operation
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hObjInv hStep hEp
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hObjInv hStep hEp
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueuePopHead_endpoint_forward endpointId isReceiveQ st st' tid headTcb epId ep hObjInv hStep hEp

/-- WS-L3/L3-C2: Enqueue preserves ipcStateQueueConsistent. Enqueue does not
modify any thread's ipcState and preserves all endpoints. -/
theorem endpointQueueEnqueue_preserves_ipcStateQueueConsistent
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st')
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  obtain ⟨tcb, hTcb, hIpc⟩ := endpointQueueEnqueue_tcb_ipcState_backward
    endpointId isReceiveQ enqueueTid st st' tid' tcb' hObjInv hStep hTcb'
  have hPre := hInv tid' tcb hTcb
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hObjInv hStep hEp
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hObjInv hStep hEp
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact endpointQueueEnqueue_endpoint_forward endpointId isReceiveQ enqueueTid st st' epId ep hObjInv hStep hEp

-- ============================================================================
-- WS-L3/L3-C3: ipcStateQueueConsistent preservation — sub-operation helpers
-- ============================================================================

/-- WS-L3/L3-C3 helper: `ensureRunnable` preserves `ipcStateQueueConsistent`.
`ensureRunnable` only modifies the scheduler (run queue), not objects. -/
theorem ensureRunnable_preserves_ipcStateQueueConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent (ensureRunnable st tid) := by
  unfold ipcStateQueueConsistent
  simp only [ensureRunnable_preserves_objects]
  exact hInv

/-- WS-L3/L3-C3 helper: `removeRunnable` preserves `ipcStateQueueConsistent`.
`removeRunnable` only modifies the scheduler, not objects. -/
theorem removeRunnable_preserves_ipcStateQueueConsistent
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent (removeRunnable st tid) := by
  unfold ipcStateQueueConsistent
  simp only [removeRunnable_preserves_objects]
  exact hInv

/-- WS-L3/L3-C3 helper: `storeTcbIpcStateAndMessage` preserves
`ipcStateQueueConsistent` when the new ipcState satisfies the invariant
obligation in the pre-state. Specifically:
- If ipc = blockedOnSend/Receive/Call epId, then the endpoint at epId
  must exist in the pre-state (the operation preserves it).
- If ipc = ready/blockedOnReply/blockedOnNotification, no obligation. -/
theorem storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (hInv : ipcStateQueueConsistent st)
    (hNewIpc : match ipc with
      | .blockedOnSend epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnReceive epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnCall epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | _ => True) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  by_cases hEq : tid'.toObjId = tid.toObjId
  · -- Target TCB: ipcState was set to `ipc`
    have hIpcEq := storeTcbIpcStateAndMessage_ipcState_eq st st' tid ipc msg hObjInv hStep tcb' (hEq ▸ hTcb')
    rw [hIpcEq]
    cases ipc with
    | ready | blockedOnNotification _ | blockedOnReply _ _ => trivial
    | blockedOnSend epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid _ msg epId ep hObjInv hEp hStep⟩
    | blockedOnReceive epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid _ msg epId ep hObjInv hEp hStep⟩
    | blockedOnCall epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid _ msg epId ep hObjInv hEp hStep⟩
  · -- Non-target TCB: object unchanged, pre-state invariant applies
    have hObjEq := storeTcbIpcStateAndMessage_preserves_objects_ne st st' tid ipc msg tid'.toObjId hEq hObjInv hStep
    rw [hObjEq] at hTcb'
    have hPre := hInv tid' tcb' hTcb'
    match h : tcb'.ipcState with
    | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
    | .blockedOnSend epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid ipc msg epId ep hObjInv hEp hStep⟩
    | .blockedOnReceive epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid ipc msg epId ep hObjInv hEp hStep⟩
    | .blockedOnCall epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcStateAndMessage_preserves_endpoint st st' tid ipc msg epId ep hObjInv hEp hStep⟩

/-- Finding F-1: `storeTcbReceiveComplete` preserves `ipcStateQueueConsistent`.
The stored ipcState is `.ready`, which carries no endpoint-existence obligation,
so no `hNewIpc` precondition is needed.  Mirror of
`storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent`. -/
theorem storeTcbReceiveComplete_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st')
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  by_cases hEq : tid'.toObjId = tid.toObjId
  · -- Target TCB: ipcState was set to `.ready`, no obligation
    have hIpcEq := storeTcbReceiveComplete_ipcState_eq st st' tid msg hObjInv hStep tcb' (hEq ▸ hTcb')
    rw [hIpcEq]; trivial
  · -- Non-target TCB: object unchanged, pre-state invariant applies
    have hObjEq := storeTcbReceiveComplete_preserves_objects_ne st st' tid msg tid'.toObjId hEq hObjInv hStep
    rw [hObjEq] at hTcb'
    have hPre := hInv tid' tcb' hTcb'
    match h : tcb'.ipcState with
    | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
    | .blockedOnSend epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbReceiveComplete_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩
    | .blockedOnReceive epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbReceiveComplete_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩
    | .blockedOnCall epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbReceiveComplete_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩

/-- WS-L3/L3-C3 helper: `storeTcbIpcState` preserves `ipcStateQueueConsistent`
under the same conditions as `storeTcbIpcStateAndMessage`. -/
theorem storeTcbIpcState_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcState st tid ipc = .ok st')
    (hInv : ipcStateQueueConsistent st)
    (hNewIpc : match ipc with
      | .blockedOnSend epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnReceive epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | .blockedOnCall epId => ∃ ep, st.objects[epId]? = some (.endpoint ep)
      | _ => True) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  by_cases hEq : tid'.toObjId = tid.toObjId
  · have hIpcEq := storeTcbIpcState_ipcState_eq st st' tid ipc hObjInv hStep tcb' (hEq ▸ hTcb')
    rw [hIpcEq]
    cases ipc with
    | ready | blockedOnNotification _ | blockedOnReply _ _ => trivial
    | blockedOnSend epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid _ epId ep hEp hObjInv hStep⟩
    | blockedOnReceive epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid _ epId ep hEp hObjInv hStep⟩
    | blockedOnCall epId =>
      obtain ⟨ep, hEp⟩ := hNewIpc
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid _ epId ep hEp hObjInv hStep⟩
  · have hObjEq := storeTcbIpcState_preserves_objects_ne st st' tid ipc tid'.toObjId hEq hObjInv hStep
    rw [hObjEq] at hTcb'
    have hPre := hInv tid' tcb' hTcb'
    match h : tcb'.ipcState with
    | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
    | .blockedOnSend epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid ipc epId ep hEp hObjInv hStep⟩
    | .blockedOnReceive epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid ipc epId ep hEp hObjInv hStep⟩
    | .blockedOnCall epId =>
      rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
      exact ⟨ep, storeTcbIpcState_preserves_endpoint st st' tid ipc epId ep hEp hObjInv hStep⟩

/-- WS-L3/L3-C3 helper: `storeTcbPendingMessage` preserves
`ipcStateQueueConsistent`. This operation only changes pendingMessage,
not ipcState, so the invariant is trivially preserved. -/
theorem storeTcbPendingMessage_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbPendingMessage st tid msg = .ok st')
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid' tcb' hTcb'
  obtain ⟨tcb, hTcb, hIpc⟩ := storeTcbPendingMessage_tcb_ipcState_backward st st' tid msg tid' tcb' hObjInv hStep hTcb'
  have hPre := hInv tid' tcb hTcb
  rw [← hIpc]
  match h : tcb.ipcState with
  | .ready | .blockedOnNotification _ | .blockedOnReply _ _ => trivial
  | .blockedOnSend epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact ⟨ep, storeTcbPendingMessage_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩
  | .blockedOnReceive epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact ⟨ep, storeTcbPendingMessage_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩
  | .blockedOnCall epId =>
    rw [h] at hPre; obtain ⟨ep, hEp⟩ := hPre
    exact ⟨ep, storeTcbPendingMessage_preserves_endpoint st st' tid msg epId ep hObjInv hEp hStep⟩

-- ============================================================================
-- WS-L3/L3-C3: ipcStateQueueConsistent preservation — high-level IPC ops
-- ============================================================================

/-- WS-L3/L3-C3: endpointSendDual preserves ipcStateQueueConsistent.
Handshake path: PopHead (preserves) → storeTcbIpcStateAndMessage to .ready
(removes obligation) → ensureRunnable (preserves).
Blocking path: Enqueue (preserves) → storeTcbIpcStateAndMessage to
.blockedOnSend endpointId (endpoint exists from initial lookup) →
removeRunnable (preserves). -/
theorem endpointSendDual_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨receiver, _tcb, stPop⟩ := triple
          cases hMsg : storeTcbReceiveComplete stPop receiver (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hObjInvPop : stPop.objects.invExt :=
              endpointQueuePopHead_preserves_objects_invExt endpointId true st stPop receiver _tcb hObjInv hPop
            exact ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbReceiveComplete_preserves_ipcStateQueueConsistent _ _ _ _ hObjInvPop hMsg
                (endpointQueuePopHead_preserves_ipcStateQueueConsistent endpointId true st stPop receiver _tcb
                  hObjInv hPop hInv)
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hObjInvEnq : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
            exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvEnq hMsg
                (endpointQueueEnqueue_preserves_ipcStateQueueConsistent endpointId false sender st st1
                  hObjInv hEnq hInv)
                (endpointQueueEnqueue_endpoint_forward _ _ sender st st1 endpointId ep hObjInv hEnq hObj)

/-- WS-L3/L3-C3: endpointReceiveDual preserves ipcStateQueueConsistent.
Rendezvous (call): PopHead → storeTcbIpcStateAndMessage(.blockedOnReply, trivial)
→ storeTcbPendingMessage (preserves).
Rendezvous (send): PopHead → storeTcbIpcStateAndMessage(.ready, trivial) →
ensureRunnable → storeTcbPendingMessage (preserves).
Blocking: Enqueue → storeTcbIpcState(.blockedOnReceive epId, endpoint exists)
→ removeRunnable (preserves). -/
theorem endpointReceiveDual_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver resultTid : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (resultTid, st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨sender, senderTcb, stPop⟩ := triple
          have hObjInvPop : stPop.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st stPop sender senderTcb hObjInv hPop
          have hInvPop := endpointQueuePopHead_preserves_ipcStateQueueConsistent
            endpointId false st stPop sender senderTcb hObjInv hPop hInv
          -- Branch on senderWasCall
          split at hStep
          · -- Call path: storeTcbIpcStateAndMessage(.blockedOnReply) → linkCallerReply → receiver update
            cases hMsg : storeTcbIpcStateAndMessage stPop sender (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 sender _ _ hObjInvPop hMsg
              have hInvMsg := storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg hInvPop trivial
              -- WS-SM SM6.D (#7.1 fold): atomic reply-link of the dequeued caller.
              cases hReplyId : replyId with
              | none => simp [hReplyId] at hStep
              | some rid =>
                simp only [hReplyId] at hStep
                cases hLink : SystemState.linkCallerReply sender rid st2 with
                | error e => simp [hLink] at hStep
                | ok pLink =>
                  obtain ⟨_, stLinked⟩ := pLink
                  simp only [hLink] at hStep
                  have hObjInvLink : stLinked.objects.invExt :=
                    linkCallerReply_preserves_objects_invExt st2 stLinked sender rid hObjInvMsg hLink
                  have hInvLink := linkCallerReply_preserves_ipcStateQueueConsistent st2 stLinked sender rid hInvMsg hObjInvMsg hLink
                  -- AK1-D: atomic (.ready, senderMsg) receiver update
                  cases hPM : storeTcbIpcStateAndMessage stLinked receiver .ready senderTcb.pendingMessage with
                  | error e => simp [hPM] at hStep
                  | ok st3 =>
                    simp only [hPM] at hStep
                    have hEq : st3 = st' := by
                      have := Except.ok.inj hStep; exact (Prod.mk.inj this).2
                    subst hEq
                    exact storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvLink hPM
                      hInvLink trivial
          · -- Send path: storeTcbIpcStateAndMessage(.ready) → ensureRunnable → storeTcbPendingMessage
            cases hMsg : storeTcbIpcStateAndMessage stPop sender .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              -- AK1-D: atomic (.ready, senderMsg) receiver update
              cases hPM : storeTcbIpcStateAndMessage (ensureRunnable st2 sender) receiver .ready senderTcb.pendingMessage with
              | error e => simp [hPM] at hStep
              | ok st3 =>
                simp only [hPM] at hStep
                have hEq : st3 = st' := by
                  have := Except.ok.inj hStep; exact (Prod.mk.inj this).2
                subst hEq
                have hObjInvMsgS : st2.objects.invExt :=
                  storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 sender _ _ hObjInvPop hMsg
                have hObjInvEns : (ensureRunnable st2 sender).objects.invExt :=
                  ensureRunnable_preserves_objects st2 sender ▸ hObjInvMsgS
                exact storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvEns hPM
                  (ensureRunnable_preserves_ipcStateQueueConsistent _ _
                    (storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg hInvPop trivial)) trivial
      | none =>
        -- AI4-A: cleanupPreReceiveDonation before enqueue
        -- AK1-A (I-H01): Destructure checked variant, bridge to defensive form.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hInvClean := cleanupPreReceiveDonation_preserves_ipcStateQueueConsistent st receiver hObjInv hInv
          have hObjClean := cleanupPreReceiveDonation_endpoint_forward st receiver hObjInv endpointId ep hObj
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc] at hStep
              have hObjInvEnqR : st1.objects.invExt :=
                endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
              have hObjInv2 : st2.objects.invExt :=
                storeTcbIpcState_preserves_objects_invExt st1 st2 receiver _ hObjInvEnqR hIpc
              have hInv2 :=
                storeTcbIpcState_preserves_ipcStateQueueConsistent _ _ _ _ hObjInvEnqR hIpc
                  (endpointQueueEnqueue_preserves_ipcStateQueueConsistent endpointId true receiver (cleanupPreReceiveDonation st receiver) st1
                    hObjInvClean hEnq hInvClean)
                  (endpointQueueEnqueue_endpoint_forward _ _ receiver (cleanupPreReceiveDonation st receiver) st1 endpointId ep hObjInvClean hEnq hObjClean)
              -- WS-SM SM6.D (#7.1 fold): server-first stash store on the blocked receiver.
              cases hGetR : st2.getTcb? receiver with
              | none =>
                simp only [hGetR, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact removeRunnable_preserves_ipcStateQueueConsistent _ _ hInv2
              | some rTcb =>
                simp only [hGetR] at hStep
                cases hStash : storeObject receiver.toObjId
                    (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                | error e => simp [hStash] at hStep
                | ok pStash =>
                  obtain ⟨_, stStashed⟩ := pStash
                  simp only [hStash, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, hEq⟩ := hStep; subst hEq
                  have hTcbPre : st2.objects[receiver.toObjId]? = some (.tcb rTcb) :=
                    (SystemState.getTcb?_eq_some_iff st2 receiver rTcb).mp hGetR
                  exact removeRunnable_preserves_ipcStateQueueConsistent _ _
                    (storeObject_tcb_readAgree_preserves_ipcStateQueueConsistent
                      st2 stStashed receiver.toObjId rTcb
                      { rTcb with pendingReceiveReply := replyId } rfl
                      hInv2 hObjInv2 hTcbPre hStash)

/-- WS-L3/L3-C3: endpointReply preserves ipcStateQueueConsistent.
Reply sets target from blockedOnReply to .ready (removes obligation),
then ensureRunnable (preserves). The _fromTcb variant is rewritten to
the standard form via the equivalence theorem. -/
theorem endpointReply_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (replier target : SeLe4n.ThreadId)
    (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      -- Rewrite _fromTcb to standard form
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      -- AK1-B (I-H02): Fail-closed on replyTarget = none
      cases replyTarget with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · -- authorized = true
          cases hStore : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st2 =>
            simp only [hStore] at hStep
            have hEq := (Prod.mk.inj (Except.ok.inj hStep)).2; rw [← hEq]
            exact ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv hStore hInv trivial
        · -- authorized = false → error
          simp at hStep
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ | blockedOnNotification _ =>
      simp [hIpc] at hStep

-- ============================================================================
-- T4-A/B/C (M-IPC-1): ipcStateQueueConsistent preservation for compound ops
-- ============================================================================

/-- T4-A (M-IPC-1): storeObject on a notification preserves ipcStateQueueConsistent.
Notification objects are neither TCBs nor endpoints, so the invariant—which only
queries TCB ipcState and endpoint existence—is trivially preserved. -/
theorem storeObject_notification_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (nid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : ∃ ntfn', st.objects[nid]? = some (.notification ntfn'))
    (hObjInv : st.objects.invExt)
    (hStore : storeObject nid (.notification ntfn) st = .ok ((), st'))
    (hInv : ipcStateQueueConsistent st) :
    ipcStateQueueConsistent st' := by
  intro tid tcb hTcb
  have hNeTcb : tid.toObjId ≠ nid := by
    intro h; obtain ⟨n', hn'⟩ := hNtfn
    rw [h, storeObject_objects_eq st st' nid _ hObjInv hStore] at hTcb; cases hTcb
  rw [storeObject_objects_ne st st' nid tid.toObjId _ hNeTcb hObjInv hStore] at hTcb
  have hOrig := hInv tid tcb hTcb
  cases hIpc : tcb.ipcState with
  | blockedOnSend epId =>
    simp only [hIpc] at hOrig; obtain ⟨ep, hEp⟩ := hOrig
    have hNeEp : epId ≠ nid := by
      intro h; obtain ⟨n', hn'⟩ := hNtfn; rw [h] at hEp; rw [hn'] at hEp; cases hEp
    exact ⟨ep, by rw [storeObject_objects_ne st st' nid epId _ hNeEp hObjInv hStore]; exact hEp⟩
  | blockedOnReceive epId =>
    simp only [hIpc] at hOrig; obtain ⟨ep, hEp⟩ := hOrig
    have hNeEp : epId ≠ nid := by
      intro h; obtain ⟨n', hn'⟩ := hNtfn; rw [h] at hEp; rw [hn'] at hEp; cases hEp
    exact ⟨ep, by rw [storeObject_objects_ne st st' nid epId _ hNeEp hObjInv hStore]; exact hEp⟩
  | blockedOnCall epId =>
    simp only [hIpc] at hOrig; obtain ⟨ep, hEp⟩ := hOrig
    have hNeEp : epId ≠ nid := by
      intro h; obtain ⟨n', hn'⟩ := hNtfn; rw [h] at hEp; rw [hn'] at hEp; cases hEp
    exact ⟨ep, by rw [storeObject_objects_ne st st' nid epId _ hNeEp hObjInv hStore]; exact hEp⟩
  | ready | blockedOnReply _ _ | blockedOnNotification _ => trivial

/-- T4-C (M-IPC-1): notificationSignal preserves ipcStateQueueConsistent.
Signal either wakes a waiter (→ .ready, trivial) or accumulates a badge
(notification-only update, no TCB ipcState change). -/
theorem notificationSignal_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold notificationSignal at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      -- WS-RC R4.C: signal pops via `NoDupList.tail?`.
      cases hWaiters : ntfn.waitingThreads.tail? with
      | some headTail =>
        obtain ⟨waiter, rest⟩ := headTail
        -- Wake path: storeObject (notification) → storeTcbIpcStateAndMessage (waiter, .ready) → ensureRunnable
        simp only [hWaiters] at hStep
        generalize hStore1 : storeObject notificationId _ st = r1 at hStep
        cases r1 with
        | error e => simp at hStep
        | ok pair1 =>
          simp only [] at hStep
          generalize hMsg : storeTcbIpcStateAndMessage pair1.2 waiter .ready _ = rMsg at hStep
          cases rMsg with
          | error e => simp at hStep
          | ok st2 =>
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
            exact ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv1 hMsg
                (storeObject_notification_preserves_ipcStateQueueConsistent st pair1.2 notificationId _
                  ⟨ntfn, hObj⟩ hObjInv hStore1 hInv) trivial
      | none =>
        -- Accumulate path: storeObject (notification) only
        simp only [hWaiters] at hStep
        exact storeObject_notification_preserves_ipcStateQueueConsistent st st' notificationId _
          ⟨ntfn, hObj⟩ hObjInv hStep hInv

/-- T4-C (M-IPC-1): notificationWait preserves ipcStateQueueConsistent.
Wait either consumes a pending badge (→ .ready, trivial) or blocks the waiter
on the notification (→ .blockedOnNotification, which is _ => True). -/
theorem notificationWait_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId)
    (waiter : SeLe4n.ThreadId) (result : Option SeLe4n.Badge)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcStateQueueConsistent st' := by
  unfold notificationWait at hStep
  cases hObj : st.objects[notificationId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | endpoint _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | notification ntfn =>
      simp only [hObj] at hStep
      cases hBadge : ntfn.pendingBadge with
      | some badge =>
        -- Consume path: storeObject (notification) → storeTcbIpcState (waiter, .ready)
        simp only [hBadge] at hStep
        generalize hStore1 : storeObject notificationId _ st = r1 at hStep
        cases r1 with
        | error e => simp at hStep
        | ok pair1 =>
          simp only [] at hStep
          cases hIpc : storeTcbIpcState pair1.2 waiter .ready with
          | error e => simp [hIpc] at hStep
          | ok st2 =>
            simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨rfl, rfl⟩ := hStep
            have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
            exact storeTcbIpcState_preserves_ipcStateQueueConsistent _ _ _ _ hObjInv1 hIpc
              (storeObject_notification_preserves_ipcStateQueueConsistent st pair1.2 notificationId _
                ⟨ntfn, hObj⟩ hObjInv hStore1 hInv) trivial
      | none =>
        -- Block path: lookupTcb → storeObject (notification) → storeTcbIpcState_fromTcb (.blockedOnNotification) → removeRunnable
        simp only [hBadge] at hStep
        cases hLookup : lookupTcb st waiter with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          split at hStep
          · simp at hStep -- already waiting → error
          · -- WS-RC R4.C: consWithGuard? case-split
            split at hStep
            · simp at hStep -- consWithGuard? = none → .alreadyWaiting
            · generalize hStore1 : storeObject notificationId _ st = r1 at hStep
              cases r1 with
            | error e => simp at hStep
            | ok pair1 =>
              simp only [] at hStep
              have hTcbObj := lookupTcb_some_objects st waiter tcb hLookup
              have hNe : waiter.toObjId ≠ notificationId := by
                intro h; rw [h] at hTcbObj; rw [hObj] at hTcbObj; cases hTcbObj
              have hTcbObj' : pair1.2.objects[waiter.toObjId]? = some (.tcb tcb) := by
                rw [storeObject_objects_ne st pair1.2 notificationId waiter.toObjId _ hNe hObjInv hStore1]
                exact hTcbObj
              have hLookup' : lookupTcb pair1.2 waiter = some tcb := by
                unfold lookupTcb; split
                · -- isReserved: contradiction (original lookupTcb succeeded so not reserved)
                  rename_i hRes
                  unfold lookupTcb at hLookup; simp [hRes] at hLookup
                · rw [hTcbObj']
              rw [storeTcbIpcState_fromTcb_eq hLookup'] at hStep
              cases hIpc : storeTcbIpcState pair1.2 waiter (.blockedOnNotification notificationId) with
              | error e => simp [hIpc] at hStep
              | ok st2 =>
                simp only [hIpc, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨rfl, rfl⟩ := hStep
                have hObjInv1 := storeObject_preserves_objects_invExt' st notificationId _ pair1 hObjInv hStore1
                exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
                  storeTcbIpcState_preserves_ipcStateQueueConsistent _ _ _ _ hObjInv1 hIpc
                    (storeObject_notification_preserves_ipcStateQueueConsistent st pair1.2 notificationId _
                      ⟨ntfn, hObj⟩ hObjInv hStore1 hInv) trivial

/-- T4-A (M-IPC-1): endpointCall preserves ipcStateQueueConsistent.
The handshake path sets receiver to .ready (trivial) and caller to .blockedOnReply
(falls under _ => True). The blocking path sets caller to .blockedOnCall with
an endpoint existence obligation discharged by endpointQueueEnqueue_endpoint_forward. -/
theorem endpointCall_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ => simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        -- Handshake path: PopHead → storeTcbIpcStateAndMessage(receiver, .ready) → ensureRunnable →
        --                 storeTcbIpcState(caller, .blockedOnReply) → removeRunnable
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok triple =>
          simp only [hHead, hPop] at hStep
          obtain ⟨receiver, _tcb, stPop⟩ := triple
          cases hMsg : storeTcbIpcStateAndMessage stPop receiver .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInvPop := endpointQueuePopHead_preserves_objects_invExt endpointId true st stPop receiver _tcb hObjInv hPop
            have hObjInvMsg := storeTcbIpcStateAndMessage_preserves_objects_invExt stPop st2 receiver _ _ hObjInvPop hMsg
            have hObjInvEns := ensureRunnable_preserves_objects st2 receiver ▸ hObjInvMsg
            -- AK1-C (I-M01): storeTcbIpcStateAndMessage atomically clears caller's pendingMessage
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 receiver) caller (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hIpc] at hStep
            | ok st3 =>
              simp only [hIpc] at hStep
              have hISQC3 : ipcStateQueueConsistent st3 :=
                storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ none hObjInvEns hIpc
                  (ensureRunnable_preserves_ipcStateQueueConsistent _ _ <|
                    storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvPop hMsg
                      (endpointQueuePopHead_preserves_ipcStateQueueConsistent endpointId true st stPop receiver _tcb
                        hObjInv hPop hInv) trivial) trivial
              have hObjInv3 := storeTcbIpcStateAndMessage_preserves_objects_invExt _ st3 caller _ none hObjInvEns hIpc
              -- WS-SM SM6.D (#7.3 fold): thread the server-first reply link.
              cases hLink : SystemState.linkServerStashedReply caller receiver st3 with
              | error e => simp [hLink] at hStep
              | ok pL =>
                obtain ⟨_, st5⟩ := pL
                simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                have hISQC5 := linkServerStashedReply_preserves_ipcStateQueueConsistent st3 st5 caller receiver hISQC3 hObjInv3 hLink
                exact removeRunnable_preserves_ipcStateQueueConsistent _ _ hISQC5
      | none =>
        -- Blocking path: Enqueue → storeTcbIpcStateAndMessage(caller, .blockedOnCall) → removeRunnable
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hObjInvEnq := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
            exact removeRunnable_preserves_ipcStateQueueConsistent _ _ <|
              storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInvEnq hMsg
                (endpointQueueEnqueue_preserves_ipcStateQueueConsistent endpointId false caller st st1
                  hObjInv hEnq hInv)
                (endpointQueueEnqueue_endpoint_forward _ _ caller st st1 endpointId ep hObjInv hEnq hObj)

/-- T4-B (M-IPC-1): endpointReplyRecv preserves ipcStateQueueConsistent.
ReplyRecv first replies (target → .ready, trivial obligation), then enters
the full endpointReceiveDual path, which has proven preservation. -/
theorem endpointReplyRecv_preserves_ipcStateQueueConsistent
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (hInv : ipcStateQueueConsistent st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    ipcStateQueueConsistent st' := by
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    cases hIpcS : tcb.ipcState with
    | blockedOnReply epId replyTarget' =>
      simp only [hIpcS] at hStep
      rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
      -- AK1-B (I-H02): Fail-closed on replyTarget' = none
      cases replyTarget' with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · -- authorized
          cases hStore : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp [hStore] at hStep
          | ok st1 =>
            simp only [hStore] at hStep
            have hObjInv1 := storeTcbIpcStateAndMessage_preserves_objects_invExt st st1 replyTarget _ _ hObjInv hStore
            have hInv1 := storeTcbIpcStateAndMessage_preserves_ipcStateQueueConsistent _ _ _ _ _ hObjInv hStore hInv trivial
            have hObjInvEns := ensureRunnable_preserves_objects st1 replyTarget ▸ hObjInv1
            have hInvEns := ensureRunnable_preserves_ipcStateQueueConsistent st1 replyTarget hInv1
            -- endpointReceiveDual on ensured state
            generalize hRecv : endpointReceiveDual endpointId receiver replyId (ensureRunnable st1 replyTarget) = rRecv at hStep
            cases rRecv with
            | error e => simp at hStep
            | ok pair =>
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              exact endpointReceiveDual_preserves_ipcStateQueueConsistent _ _ _ _ pair.1 replyId hInvEns hObjInvEns hRecv
        · simp at hStep -- unauthorized → error
    | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnCall _ | blockedOnNotification _ =>
      simp [hIpcS] at hStep

-- ============================================================================
-- WS-SM SM6.D: storing a `.reply` over a slot that already held a `.reply`
-- preserves `ipcInvariantFull`.
--
-- A `.reply` object is foreign to every `ipcInvariantFull` conjunct: no
-- conjunct dereferences a `.reply`.  The uniform `reply_store_kind_agree`
-- helper below captures the single fact that drives all fifteen conjuncts —
-- for every *non-reply* object kind, the pre- and post-store lookups agree
-- (the post-store slot at `id` holds `.reply r'` and the pre-store slot held
-- `.reply r`, so neither side can witness a non-reply kind at `id`, and every
-- other slot is untouched by `storeObject_objects_ne`).
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: after storing `.reply r'` over a slot that held `.reply r`,
the lookup of any *non-`.reply`* object agrees between pre- and post-state.
This is the single uniform fact behind every `ipcInvariantFull` conjunct:
none of them reads a `.reply`, so each object lookup they perform is
unchanged. -/
private theorem reply_store_kind_agree
    (st st' : SystemState) (id : SeLe4n.ObjId) (r r' : SeLe4n.Kernel.Reply)
    (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.reply r))
    (hStore : storeObject id (.reply r') st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (k : KernelObject), (∀ rr, k ≠ .reply rr) →
      (st'.objects[s]? = some k ↔ st.objects[s]? = some k) := by
  intro s k hk
  by_cases hs : s = id
  · subst hs
    rw [storeObject_objects_eq st st' s (.reply r') hObjInv hStore, hPrev]
    constructor
    · intro h; cases h; exact absurd rfl (hk r')
    · intro h; cases h; exact absurd rfl (hk r)
  · rw [storeObject_objects_ne st st' id s (.reply r') hs hObjInv hStore]

-- ----------------------------------------------------------------------------
-- Conjunct 2 (`dualQueueSystemInvariant`) support: transport each sub-predicate
-- through `reply_store_kind_agree`.  The three sub-predicates
-- (`dualQueueEndpointWellFormed` per endpoint, `tcbQueueLinkIntegrity`,
-- `tcbQueueChainAcyclic`) dereference only endpoints and TCBs — both non-reply.
-- ----------------------------------------------------------------------------

/-- WS-SM SM6.D: a `QueueNextPath` in the post-state transports back to the
pre-state.  Each constructor carries a `.tcb` lookup, transported by
`reply_store_kind_agree`; this gives `tcbQueueChainAcyclic` preservation. -/
private theorem reply_store_QueueNextPath_backward
    {st st' : SystemState}
    (hAgree : ∀ (s : SeLe4n.ObjId) (k : KernelObject), (∀ rr, k ≠ .reply rr) →
      (st'.objects[s]? = some k ↔ st.objects[s]? = some k))
    {a b : SeLe4n.ThreadId} (hPath : QueueNextPath st' a b) :
    QueueNextPath st a b := by
  induction hPath with
  | single src dst tcb hObj hNext =>
      exact .single src dst tcb
        ((hAgree src.toObjId (.tcb tcb) (fun rr => by exact KernelObject.noConfusion)).mp hObj)
        hNext
  | cons src mid dst tcb hObj hNext _ ih =>
      exact .cons src mid dst tcb
        ((hAgree src.toObjId (.tcb tcb) (fun rr => by exact KernelObject.noConfusion)).mp hObj)
        hNext ih

/-- WS-SM SM6.D: `intrusiveQueueWellFormed` for a fixed queue `q` transports
forward across the `.reply` store.  The two boundary clauses witness `.tcb`
objects (non-reply), transported via `reply_store_kind_agree`; the emptiness
clause references only `q` itself, which is unchanged. -/
private theorem reply_store_intrusiveQueueWellFormed_forward
    {st st' : SystemState}
    (hAgree : ∀ (s : SeLe4n.ObjId) (k : KernelObject), (∀ rr, k ≠ .reply rr) →
      (st'.objects[s]? = some k ↔ st.objects[s]? = some k))
    {q : IntrusiveQueue} (hWF : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hEmpty, hHead, hTail⟩ := hWF
  refine ⟨hEmpty, ?_, ?_⟩
  · intro hd hHd
    obtain ⟨tcb, hObj, hPrev⟩ := hHead hd hHd
    exact ⟨tcb, (hAgree hd.toObjId (.tcb tcb)
      (fun rr => by exact KernelObject.noConfusion)).mpr hObj, hPrev⟩
  · intro tl hTl
    obtain ⟨tcb, hObj, hNext⟩ := hTail tl hTl
    exact ⟨tcb, (hAgree tl.toObjId (.tcb tcb)
      (fun rr => by exact KernelObject.noConfusion)).mpr hObj, hNext⟩

/-- WS-SM SM6.D: `tcbQueueLinkIntegrity` transports forward across the `.reply`
store.  Every lookup it touches is a `.tcb` (non-reply). -/
private theorem reply_store_tcbQueueLinkIntegrity_forward
    {st st' : SystemState}
    (hAgree : ∀ (s : SeLe4n.ObjId) (k : KernelObject), (∀ rr, k ≠ .reply rr) →
      (st'.objects[s]? = some k ↔ st.objects[s]? = some k))
    (hLI : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity st' := by
  obtain ⟨hFwd, hRev⟩ := hLI
  refine ⟨?_, ?_⟩
  · intro a tcbA hA b hNext
    have hA' := (hAgree a.toObjId (.tcb tcbA)
      (fun rr => by exact KernelObject.noConfusion)).mp hA
    obtain ⟨tcbB, hB, hBPrev⟩ := hFwd a tcbA hA' b hNext
    exact ⟨tcbB, (hAgree b.toObjId (.tcb tcbB)
      (fun rr => by exact KernelObject.noConfusion)).mpr hB, hBPrev⟩
  · intro b tcbB hB a hPrev
    have hB' := (hAgree b.toObjId (.tcb tcbB)
      (fun rr => by exact KernelObject.noConfusion)).mp hB
    obtain ⟨tcbA, hA, hANext⟩ := hRev b tcbB hB' a hPrev
    exact ⟨tcbA, (hAgree a.toObjId (.tcb tcbA)
      (fun rr => by exact KernelObject.noConfusion)).mpr hA, hANext⟩

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: storing a `.reply` object over a slot that already held a
`.reply` preserves the full IPC invariant.  No `ipcInvariantFull` conjunct
reads `.reply` objects, and the slot held a `.reply` both before and after, so
every notification/TCB/endpoint/cnode/schedContext lookup is unchanged. -/
theorem storeObject_reply_preserves_ipcInvariantCore
    (st st' : SystemState) (id : SeLe4n.ObjId) (r r' : SeLe4n.Kernel.Reply)
    (hInv : ipcInvariantCore st) (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.reply r))
    (hStore : storeObject id (.reply r') st = .ok ((), st')) :
    ipcInvariantCore st' := by
  -- The single uniform fact: non-reply lookups agree pre/post-store.
  have hAgree := reply_store_kind_agree st st' id r r' hObjInv hPrev hStore
  -- The scheduler is untouched by `storeObject`.
  have hSched : st'.scheduler = st.scheduler :=
    storeObject_scheduler_eq st st' id (.reply r') hStore
  refine ⟨?c1, ?c2, ?c3, ?c4, ?c5, ?c6, ?c7, ?c8, ?c9, ?c10, ?c11, ?c12, ?c13,
    ?c14, ?c15⟩
  -- 1. ipcInvariant: reads `.notification` only.
  · intro oid ntfn hObj
    exact hInv.ipcInvariant oid ntfn ((hAgree oid (.notification ntfn)
      (fun rr => by exact KernelObject.noConfusion)).mp hObj)
  -- 2. dualQueueSystemInvariant: per-endpoint well-formedness + link integrity
  --    + chain acyclicity.  All lookups are `.endpoint`/`.tcb` (non-reply).
  · obtain ⟨hEpWF, hLI, hAcyc⟩ := hInv.dualQueueSystemInvariant
    refine ⟨?_, reply_store_tcbQueueLinkIntegrity_forward hAgree hLI, ?_⟩
    · intro epId ep hEp
      have hEp' := (hAgree epId (.endpoint ep)
        (fun rr => by exact KernelObject.noConfusion)).mp hEp
      have := hEpWF epId ep hEp'
      -- `dualQueueEndpointWellFormed` on st' reduces via the same endpoint.
      unfold dualQueueEndpointWellFormed at this ⊢
      rw [hEp'] at this; rw [hEp]
      obtain ⟨hSend, hRecv⟩ := this
      exact ⟨reply_store_intrusiveQueueWellFormed_forward hAgree hSend,
             reply_store_intrusiveQueueWellFormed_forward hAgree hRecv⟩
    · intro tid hPath
      exact hAcyc tid (reply_store_QueueNextPath_backward hAgree hPath)
  -- 3. allPendingMessagesBounded: reads `.tcb` only.
  · intro tid tcb msg hObj hMsg
    exact hInv.allPendingMessagesBounded tid tcb msg
      ((hAgree tid.toObjId (.tcb tcb)
        (fun rr => by exact KernelObject.noConfusion)).mp hObj) hMsg
  -- 4. badgeWellFormed: notification badges (reads `.notification`) +
  --    capability badges (reads `.cnode`).
  · obtain ⟨hNB, hCB⟩ := hInv.badgeWellFormed
    refine ⟨?_, ?_⟩
    · intro oid ntfn badge hObj hBadge
      exact hNB oid ntfn badge ((hAgree oid (.notification ntfn)
        (fun rr => by exact KernelObject.noConfusion)).mp hObj) hBadge
    · intro oid cn slot cap badge hObj hLook hBadge
      exact hCB oid cn slot cap badge ((hAgree oid (.cnode cn)
        (fun rr => by exact KernelObject.noConfusion)).mp hObj) hLook hBadge
  -- 5. waitingThreadsPendingMessageNone: reads `.tcb` only.
  · intro tid tcb hObj
    exact hInv.waitingThreadsPendingMessageNone tid tcb
      ((hAgree tid.toObjId (.tcb tcb)
        (fun rr => by exact KernelObject.noConfusion)).mp hObj)
  -- 6. endpointQueueNoDup: hypothesis `.endpoint`; body universally re-derives
  --    a `.tcb` self-loop fact (transport that lookup with `.mp`).
  · intro oid ep hObj
    have hEp' := (hAgree oid (.endpoint ep)
      (fun rr => by exact KernelObject.noConfusion)).mp hObj
    obtain ⟨hSelf, hDisj⟩ := hInv.endpointQueueNoDup oid ep hEp'
    refine ⟨?_, hDisj⟩
    intro tid tcb hTcb
    exact hSelf tid tcb ((hAgree tid.toObjId (.tcb tcb)
      (fun rr => by exact KernelObject.noConfusion)).mp hTcb)
  -- 7. ipcStateQueueMembershipConsistent: a `.reply` store is non-endpoint,
  --    non-TCB, and the slot held `.reply r` before — exactly the precondition
  --    of the reusable non-ep/non-tcb frame lemma.
  · exact storeObject_non_ep_non_tcb_preserves_ipcStateQueueMembershipConsistent
      st st' id (.reply r')
      hInv.ipcStateQueueMembershipConsistent hObjInv
      (fun ep => by exact KernelObject.noConfusion)
      (fun tcb => by exact KernelObject.noConfusion)
      (fun ep => by rw [hPrev]; simp)
      (fun tcb => by rw [hPrev]; simp)
      hStore
  -- 8. queueNextBlockingConsistent: two `.tcb` hypotheses only.
  · intro a b tcbA tcbB hA hB hNext
    exact hInv.queueNextBlockingConsistent a b tcbA tcbB
      ((hAgree a.toObjId (.tcb tcbA)
        (fun rr => by exact KernelObject.noConfusion)).mp hA)
      ((hAgree b.toObjId (.tcb tcbB)
        (fun rr => by exact KernelObject.noConfusion)).mp hB) hNext
  -- 9. queueHeadBlockedConsistent: `.endpoint` + `.tcb` hypotheses only.
  · intro epId ep hd tcb hEp hHd
    exact hInv.queueHeadBlockedConsistent epId ep hd tcb
      ((hAgree epId (.endpoint ep)
        (fun rr => by exact KernelObject.noConfusion)).mp hEp)
      ((hAgree hd.toObjId (.tcb tcb)
        (fun rr => by exact KernelObject.noConfusion)).mp hHd)
  -- 10. blockedThreadTimeoutConsistent: hypothesis `.tcb`; conclusion has a
  --     `.schedContext` existence witness to transport forward.
  · intro tid tcb scId hObj hBudget
    have hTcb' := (hAgree tid.toObjId (.tcb tcb)
      (fun rr => by exact KernelObject.noConfusion)).mp hObj
    obtain ⟨⟨sc, hSc⟩, hState⟩ := hInv.blockedThreadTimeoutConsistent tid tcb scId
      hTcb' hBudget
    exact ⟨⟨sc, (hAgree scId.toObjId (.schedContext sc)
      (fun rr => by exact KernelObject.noConfusion)).mpr hSc⟩, hState⟩
  -- 11. donationChainAcyclic: two `.tcb` hypotheses only.
  · intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
    exact hInv.donationChainAcyclic tid1 tid2 tcb1 tcb2 scId1 scId2
      ((hAgree tid1.toObjId (.tcb tcb1)
        (fun rr => by exact KernelObject.noConfusion)).mp h1)
      ((hAgree tid2.toObjId (.tcb tcb2)
        (fun rr => by exact KernelObject.noConfusion)).mp h2) hB1 hB2
  -- 12. donationOwnerValid: hypothesis `.tcb`; conclusion has a `.schedContext`
  --     witness and an owner `.tcb` witness to transport forward.
  · intro tid tcb scId owner hObj hBind
    have hTcb' := (hAgree tid.toObjId (.tcb tcb)
      (fun rr => by exact KernelObject.noConfusion)).mp hObj
    obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOwner, hOwnerBind, hOwnerIpc⟩⟩ :=
      hInv.donationOwnerValid tid tcb scId owner hTcb' hBind
    refine ⟨⟨sc, (hAgree scId.toObjId (.schedContext sc)
      (fun rr => by exact KernelObject.noConfusion)).mpr hSc, hBound⟩,
      ⟨ownerTcb, (hAgree owner.toObjId (.tcb ownerTcb)
        (fun rr => by exact KernelObject.noConfusion)).mpr hOwner,
        hOwnerBind, hOwnerIpc⟩⟩
  -- 13. passiveServerIdle: hypothesis `.tcb`; goal also reads `st'.scheduler`
  --     (rewritten to `st.scheduler` via `storeObject_scheduler_eq`).
  · intro tid tcb hObj hUnbound hNotInQ hNotCur
    have hTcb' := (hAgree tid.toObjId (.tcb tcb)
      (fun rr => by exact KernelObject.noConfusion)).mp hObj
    rw [hSched] at hNotInQ hNotCur
    exact hInv.passiveServerIdle tid tcb hTcb' hUnbound hNotInQ hNotCur
  -- 14. donationBudgetTransfer: two `.tcb` hypotheses only.
  · intro tid1 tid2 tcb1 tcb2 scId hObj1 hObj2 hNe hSc1 hSc2
    exact hInv.donationBudgetTransfer tid1 tid2 tcb1 tcb2 scId
      ((hAgree tid1.toObjId (.tcb tcb1)
        (fun rr => by exact KernelObject.noConfusion)).mp hObj1)
      ((hAgree tid2.toObjId (.tcb tcb2)
        (fun rr => by exact KernelObject.noConfusion)).mp hObj2) hNe hSc1 hSc2
  -- 15. blockedOnReplyHasTarget: reads `.tcb` only.
  · intro tid tcb endpointId replyTarget hObj hIpc
    exact hInv.blockedOnReplyHasTarget tid tcb endpointId replyTarget
      ((hAgree tid.toObjId (.tcb tcb)
        (fun rr => by exact KernelObject.noConfusion)).mp hObj) hIpc

-- ============================================================================
-- WS-SM SM6.D: storing a `.tcb` that differs from the stored slot's previous
-- TCB only in `replyObject` preserves `ipcInvariantFull`.
--
-- Unlike the `.reply` store above (whose changed slot is foreign to every
-- conjunct), the changed slot here stays a `.tcb`, so the uniform driver is
-- split in two:
--   (a) for every *non-`.tcb`* object kind the pre/post lookups still agree
--       (`tcb_replyObject_store_nonTcb_agree`), exactly as in the `.reply`
--       case; and
--   (b) for `.tcb` lookups the post-store TCB at `id` is
--       `{ tcb with replyObject := v }`, which agrees with `tcb` on every
--       field any conjunct reads (ipcState, pendingMessage,
--       queueNext/Prev/PPrev, schedContextBinding, timeoutBudget) — a
--       structure update of `replyObject` leaves all other projections
--       definitionally equal.  `tcb_replyObject_store_tcb_forward` /
--       `_backward` expose those read-field equalities in each direction.
-- No `ipcInvariantFull` conjunct reads `replyObject`.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: after storing `.tcb { tcb with replyObject := v }` over a slot
that held `.tcb tcb`, the lookup of any *non-`.tcb`* object agrees between pre-
and post-state.  This drives every conjunct that dereferences a notification,
endpoint, cnode, or schedContext: the slot at `id` holds a `.tcb` both before
and after, so neither side can witness a non-`.tcb` kind there, and every other
slot is untouched by `storeObject_objects_ne`. -/
private theorem tcb_replyObject_store_nonTcb_agree
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb : TCB) (v : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb { tcb with replyObject := v }) st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (k : KernelObject), (∀ tt, k ≠ .tcb tt) →
      (st'.objects[s]? = some k ↔ st.objects[s]? = some k) := by
  intro s k hk
  by_cases hs : s = id
  · subst hs
    rw [storeObject_objects_eq st st' s (.tcb { tcb with replyObject := v }) hObjInv hStore,
        hPrev]
    constructor
    · intro h; cases h; exact absurd rfl (hk _)
    · intro h; cases h; exact absurd rfl (hk _)
  · rw [storeObject_objects_ne st st' id s (.tcb { tcb with replyObject := v }) hs hObjInv hStore]

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: a post-store `.tcb` lookup transports back to a pre-store
`.tcb` lookup, agreeing on every field any `ipcInvariantFull` conjunct reads.
At `id` the post-store TCB is `{ tcb with replyObject := v }`, whose
non-`replyObject` projections equal `tcb`'s by `rfl`; elsewhere the TCB is
literally unchanged. -/
private theorem tcb_replyObject_store_tcb_forward
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb : TCB) (v : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb { tcb with replyObject := v }) st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget := by
  intro s tx hObj
  by_cases hs : s = id
  · subst hs
    rw [storeObject_objects_eq st st' s (.tcb { tcb with replyObject := v }) hObjInv hStore] at hObj
    cases hObj
    exact ⟨tcb, hPrev, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [storeObject_objects_ne st st' id s (.tcb { tcb with replyObject := v }) hs hObjInv hStore]
      at hObj
    exact ⟨tx, hObj, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: a pre-store `.tcb` lookup transports forward to a post-store
`.tcb` lookup, agreeing on every read field.  Symmetric counterpart of
`tcb_replyObject_store_tcb_forward`; used to push object witnesses that appear
in conjunct *goals* (queue boundaries, link-integrity duals) forward to the
post-state. -/
private theorem tcb_replyObject_store_tcb_backward
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb : TCB) (v : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb { tcb with replyObject := v }) st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (ty : TCB), st.objects[s]? = some (.tcb ty) →
      ∃ tx, st'.objects[s]? = some (.tcb tx) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget := by
  intro s ty hObj
  by_cases hs : s = id
  · subst hs
    rw [hPrev] at hObj
    cases hObj
    exact ⟨{ tcb with replyObject := v },
      storeObject_objects_eq st st' s (.tcb { tcb with replyObject := v }) hObjInv hStore,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨ty, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [storeObject_objects_ne st st' id s (.tcb { tcb with replyObject := v }) hs hObjInv hStore]
    exact hObj

-- ----------------------------------------------------------------------------
-- Conjunct 2 (`dualQueueSystemInvariant`) support: the three sub-predicates
-- dereference only endpoints and TCBs.  Endpoints transport via the non-`.tcb`
-- iff; `.tcb` lookups transport via the forward/backward field-agreement
-- helpers (queueNext/queuePrev are among the preserved fields, so each queue
-- link carries through unchanged).
-- ----------------------------------------------------------------------------

/-- WS-SM SM6.D: a `QueueNextPath` in the post-state transports back to the
pre-state.  Each constructor carries a `.tcb` lookup and a `queueNext` edge;
the forward field-agreement helper supplies a pre-state `.tcb` with the same
`queueNext`. -/
private theorem tcb_replyObject_store_QueueNextPath_backward
    {st st' : SystemState}
    (hFwd : ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget)
    {a b : SeLe4n.ThreadId} (hPath : QueueNextPath st' a b) :
    QueueNextPath st a b := by
  induction hPath with
  | single src dst tcb hObj hNext =>
      obtain ⟨ty, hStObj, _, _, hQN, _⟩ := hFwd src.toObjId tcb hObj
      exact .single src dst ty hStObj (hQN ▸ hNext)
  | cons src mid dst tcb hObj hNext _ ih =>
      obtain ⟨ty, hStObj, _, _, hQN, _⟩ := hFwd src.toObjId tcb hObj
      exact .cons src mid dst ty hStObj (hQN ▸ hNext) ih

/-- WS-SM SM6.D: `intrusiveQueueWellFormed` for a fixed queue `q` transports
forward across the `replyObject` store.  The head/tail boundary clauses witness
`.tcb` objects whose `queuePrev`/`queueNext` are preserved; the emptiness
clause references only `q` itself, which is unchanged. -/
private theorem tcb_replyObject_store_intrusiveQueueWellFormed_forward
    {st st' : SystemState}
    (hBwd : ∀ (s : SeLe4n.ObjId) (ty : TCB), st.objects[s]? = some (.tcb ty) →
      ∃ tx, st'.objects[s]? = some (.tcb tx) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget)
    {q : IntrusiveQueue} (hWF : intrusiveQueueWellFormed q st) :
    intrusiveQueueWellFormed q st' := by
  obtain ⟨hEmpty, hHead, hTail⟩ := hWF
  refine ⟨hEmpty, ?_, ?_⟩
  · intro hd hHd
    obtain ⟨tcb, hObj, hPrevNone⟩ := hHead hd hHd
    obtain ⟨tx, hStObj, _, _, _, hQP, _⟩ := hBwd hd.toObjId tcb hObj
    exact ⟨tx, hStObj, hQP.trans hPrevNone⟩
  · intro tl hTl
    obtain ⟨tcb, hObj, hNextNone⟩ := hTail tl hTl
    obtain ⟨tx, hStObj, _, _, hQN, _⟩ := hBwd tl.toObjId tcb hObj
    exact ⟨tx, hStObj, hQN.trans hNextNone⟩

/-- WS-SM SM6.D: `tcbQueueLinkIntegrity` transports forward across the
`replyObject` store.  Every lookup it touches is a `.tcb`, and the relevant
links (`queueNext`/`queuePrev`) are preserved fields. -/
private theorem tcb_replyObject_store_tcbQueueLinkIntegrity_forward
    {st st' : SystemState}
    (hFwd : ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget)
    (hBwd : ∀ (s : SeLe4n.ObjId) (ty : TCB), st.objects[s]? = some (.tcb ty) →
      ∃ tx, st'.objects[s]? = some (.tcb tx) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget)
    (hLI : tcbQueueLinkIntegrity st) :
    tcbQueueLinkIntegrity st' := by
  obtain ⟨hFwdLI, hRevLI⟩ := hLI
  refine ⟨?_, ?_⟩
  · intro a tcbA hA b hNext
    obtain ⟨tyA, hStA, _, _, hQNA, _⟩ := hFwd a.toObjId tcbA hA
    obtain ⟨tcbB, hB, hBPrev⟩ := hFwdLI a tyA hStA b (hQNA ▸ hNext)
    obtain ⟨txB, hStB, _, _, _, hQPB, _⟩ := hBwd b.toObjId tcbB hB
    exact ⟨txB, hStB, hQPB.trans hBPrev⟩
  · intro b tcbB hB a hPrevLink
    obtain ⟨tyB, hStB, _, _, _, hQPB, _⟩ := hFwd b.toObjId tcbB hB
    obtain ⟨tcbA, hA, hANext⟩ := hRevLI b tyB hStB a (hQPB ▸ hPrevLink)
    obtain ⟨txA, hStA, _, _, hQNA, _⟩ := hBwd a.toObjId tcbA hA
    exact ⟨txA, hStA, hQNA.trans hANext⟩

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.0): the reusable `ipcInvariantCore` driver behind every TCB
field-store whose changed field is read by *no* structural core conjunct.  Given
the non-`.tcb` kind agreement (`hNT`), the forward/backward read-field agreement
(`hFwd`/`hBwd` over ipcState, pendingMessage, queueNext/Prev/PPrev,
schedContextBinding, timeoutBudget) and the scheduler frame (`hSched`), the store
preserves all 15 structural conjuncts.  Both the `replyObject` store and the
`pendingReceiveReply` store (the server-first stash the #7 fold writes inside
`endpointReceiveDual`) instantiate it via the field-specific agreement helpers,
so the 15-conjunct discharge is proven exactly once. -/
theorem storeObject_tcb_ipcInvariantCore_of_agreements
    (st st' : SystemState)
    (hInv : ipcInvariantCore st)
    (hNT : ∀ (s : SeLe4n.ObjId) (k : KernelObject), (∀ tt, k ≠ .tcb tt) →
      (st'.objects[s]? = some k ↔ st.objects[s]? = some k))
    (hFwd : ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget)
    (hBwd : ∀ (s : SeLe4n.ObjId) (ty : TCB), st.objects[s]? = some (.tcb ty) →
      ∃ tx, st'.objects[s]? = some (.tcb tx) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget)
    (hSched : st'.scheduler = st.scheduler) :
    ipcInvariantCore st' := by
  refine ⟨?c1, ?c2, ?c3, ?c4, ?c5, ?c6, ?c7, ?c8, ?c9, ?c10, ?c11, ?c12, ?c13,
    ?c14, ?c15⟩
  -- 1. ipcInvariant: reads `.notification` only → (a).
  · intro oid ntfn hObj
    exact hInv.ipcInvariant oid ntfn ((hNT oid (.notification ntfn)
      (fun tt => by exact KernelObject.noConfusion)).mp hObj)
  -- 2. dualQueueSystemInvariant: endpoints via (a), TCB links via (b).
  · obtain ⟨hEpWF, hLI, hAcyc⟩ := hInv.dualQueueSystemInvariant
    refine ⟨?_, tcb_replyObject_store_tcbQueueLinkIntegrity_forward hFwd hBwd hLI, ?_⟩
    · intro epId ep hEp
      have hEp' := (hNT epId (.endpoint ep)
        (fun tt => by exact KernelObject.noConfusion)).mp hEp
      have := hEpWF epId ep hEp'
      unfold dualQueueEndpointWellFormed at this ⊢
      rw [hEp'] at this; rw [hEp]
      obtain ⟨hSend, hRecv⟩ := this
      exact ⟨tcb_replyObject_store_intrusiveQueueWellFormed_forward hBwd hSend,
             tcb_replyObject_store_intrusiveQueueWellFormed_forward hBwd hRecv⟩
    · intro tid hPath
      exact hAcyc tid (tcb_replyObject_store_QueueNextPath_backward hFwd hPath)
  -- 3. allPendingMessagesBounded: reads `tcb.pendingMessage` → (b) forward.
  · intro tid tcb msg hObj hMsg
    obtain ⟨ty, hStObj, _, hPM, _⟩ := hFwd tid.toObjId tcb hObj
    exact hInv.allPendingMessagesBounded tid ty msg hStObj (hPM ▸ hMsg)
  -- 4. badgeWellFormed: `.notification` + `.cnode` → (a).
  · obtain ⟨hNB, hCB⟩ := hInv.badgeWellFormed
    refine ⟨?_, ?_⟩
    · intro oid ntfn badge hObj hBadge
      exact hNB oid ntfn badge ((hNT oid (.notification ntfn)
        (fun tt => by exact KernelObject.noConfusion)).mp hObj) hBadge
    · intro oid cn slot cap badge hObj hLook hBadge
      exact hCB oid cn slot cap badge ((hNT oid (.cnode cn)
        (fun tt => by exact KernelObject.noConfusion)).mp hObj) hLook hBadge
  -- 5. waitingThreadsPendingMessageNone: reads `tcb.ipcState`+`pendingMessage` → (b).
  · intro tid tcb hObj
    obtain ⟨ty, hStObj, hIS, hPM, _⟩ := hFwd tid.toObjId tcb hObj
    rw [hIS, hPM]
    exact hInv.waitingThreadsPendingMessageNone tid ty hStObj
  -- 6. endpointQueueNoDup: `.endpoint` hyp via (a); `.tcb` self-loop body via (b).
  · intro oid ep hObj
    have hEp' := (hNT oid (.endpoint ep)
      (fun tt => by exact KernelObject.noConfusion)).mp hObj
    obtain ⟨hSelf, hDisj⟩ := hInv.endpointQueueNoDup oid ep hEp'
    refine ⟨?_, hDisj⟩
    intro tid tcb hTcb
    obtain ⟨ty, hStObj, _, _, hQN, _⟩ := hFwd tid.toObjId tcb hTcb
    rw [hQN]; exact hSelf tid ty hStObj
  -- 7. ipcStateQueueMembershipConsistent: a `.tcb` store, proven directly via (b).
  --    `tcb.ipcState` rewrites to `ty.ipcState`; the three blocking arms transport
  --    the endpoint lookup via (a) and the `prev` queue witness via (b).
  · intro tid tcb hObj
    obtain ⟨ty, hStObj, hIS, _⟩ := hFwd tid.toObjId tcb hObj
    have hbase := hInv.ipcStateQueueMembershipConsistent tid ty hStObj
    rw [hIS]
    cases hq : ty.ipcState with
    | ready => exact True.intro
    | blockedOnNotification _ => exact True.intro
    | blockedOnReply _ _ => exact True.intro
    | blockedOnSend epId =>
        rw [hq] at hbase
        obtain ⟨ep, hEpSt, hcond⟩ := hbase
        refine ⟨ep, (hNT epId (.endpoint ep)
          (fun tt => by exact KernelObject.noConfusion)).mpr hEpSt, ?_⟩
        cases hcond with
        | inl h => exact Or.inl h
        | inr h =>
            obtain ⟨prev, prevTcb, hPrevSt, hQN⟩ := h
            obtain ⟨xx, hStX, _, _, hQNeq, _⟩ := hBwd prev.toObjId prevTcb hPrevSt
            exact Or.inr ⟨prev, xx, hStX, hQNeq.trans hQN⟩
    | blockedOnReceive epId =>
        rw [hq] at hbase
        obtain ⟨ep, hEpSt, hcond⟩ := hbase
        refine ⟨ep, (hNT epId (.endpoint ep)
          (fun tt => by exact KernelObject.noConfusion)).mpr hEpSt, ?_⟩
        cases hcond with
        | inl h => exact Or.inl h
        | inr h =>
            obtain ⟨prev, prevTcb, hPrevSt, hQN⟩ := h
            obtain ⟨xx, hStX, _, _, hQNeq, _⟩ := hBwd prev.toObjId prevTcb hPrevSt
            exact Or.inr ⟨prev, xx, hStX, hQNeq.trans hQN⟩
    | blockedOnCall epId =>
        rw [hq] at hbase
        obtain ⟨ep, hEpSt, hcond⟩ := hbase
        refine ⟨ep, (hNT epId (.endpoint ep)
          (fun tt => by exact KernelObject.noConfusion)).mpr hEpSt, ?_⟩
        cases hcond with
        | inl h => exact Or.inl h
        | inr h =>
            obtain ⟨prev, prevTcb, hPrevSt, hQN⟩ := h
            obtain ⟨xx, hStX, _, _, hQNeq, _⟩ := hBwd prev.toObjId prevTcb hPrevSt
            exact Or.inr ⟨prev, xx, hStX, hQNeq.trans hQN⟩
  -- 8. queueNextBlockingConsistent: two `.tcb` hyps + `queueNext` → (b).
  · intro a b tcbA tcbB hA hB hNext
    obtain ⟨tyA, hStA, hISA, _, hQNA, _⟩ := hFwd a.toObjId tcbA hA
    obtain ⟨tyB, hStB, hISB, _⟩ := hFwd b.toObjId tcbB hB
    have := hInv.queueNextBlockingConsistent a b tyA tyB hStA hStB (hQNA ▸ hNext)
    rw [hISA, hISB]; exact this
  -- 9. queueHeadBlockedConsistent: `.endpoint` via (a) + `.tcb` via (b).
  · intro epId ep hd tcb hEp hHd
    have hEp' := (hNT epId (.endpoint ep)
      (fun tt => by exact KernelObject.noConfusion)).mp hEp
    obtain ⟨ty, hStObj, hIS, _⟩ := hFwd hd.toObjId tcb hHd
    have := hInv.queueHeadBlockedConsistent epId ep hd ty hEp' hStObj
    rw [hIS]; exact this
  -- 10. blockedThreadTimeoutConsistent: hyp `.tcb` via (b); `.schedContext` witness via (a).
  · intro tid tcb scId hObj hBudget
    obtain ⟨ty, hStObj, hIS, _, _, _, _, _, hTB⟩ := hFwd tid.toObjId tcb hObj
    obtain ⟨⟨sc, hSc⟩, hState⟩ := hInv.blockedThreadTimeoutConsistent tid ty scId
      hStObj (hTB ▸ hBudget)
    refine ⟨⟨sc, (hNT scId.toObjId (.schedContext sc)
      (fun tt => by exact KernelObject.noConfusion)).mpr hSc⟩, ?_⟩
    rw [hIS]; exact hState
  -- 11. donationChainAcyclic: two `.tcb` hyps + `schedContextBinding` → (b).
  · intro tid1 tid2 tcb1 tcb2 scId1 scId2 h1 h2 hB1 hB2
    obtain ⟨ty1, hSt1, _, _, _, _, _, hSCB1, _⟩ := hFwd tid1.toObjId tcb1 h1
    obtain ⟨ty2, hSt2, _, _, _, _, _, hSCB2, _⟩ := hFwd tid2.toObjId tcb2 h2
    exact hInv.donationChainAcyclic tid1 tid2 ty1 ty2 scId1 scId2 hSt1 hSt2
      (hSCB1 ▸ hB1) (hSCB2 ▸ hB2)
  -- 12. donationOwnerValid: hyp `.tcb` via (b); `.schedContext` + owner `.tcb` witnesses
  --     pushed forward via (a) and (b).
  · intro tid tcb scId owner hObj hBind
    obtain ⟨ty, hStObj, hIS, _, _, _, _, hSCB, _⟩ := hFwd tid.toObjId tcb hObj
    obtain ⟨⟨sc, hSc, hBound⟩, ⟨ownerTcb, hOwner, hOwnerBind, hOwnerIpc⟩⟩ :=
      hInv.donationOwnerValid tid ty scId owner hStObj (hSCB ▸ hBind)
    obtain ⟨ownerTx, hOwnerSt, hOwnerIS, _, _, _, _, hOwnerSCB, _⟩ :=
      hBwd owner.toObjId ownerTcb hOwner
    refine ⟨⟨sc, (hNT scId.toObjId (.schedContext sc)
      (fun tt => by exact KernelObject.noConfusion)).mpr hSc, hBound⟩,
      ⟨ownerTx, hOwnerSt, ?_, ?_⟩⟩
    · rw [hOwnerSCB]; exact hOwnerBind
    · rw [hOwnerIS]; exact hOwnerIpc
  -- 13. passiveServerIdle: hyp `.tcb` via (b); scheduler reads via `storeObject_scheduler_eq`.
  · intro tid tcb hObj hUnbound hNotInQ hNotCur
    obtain ⟨ty, hStObj, hIS, _, _, _, _, hSCB, _⟩ := hFwd tid.toObjId tcb hObj
    rw [hSched] at hNotInQ hNotCur
    have := hInv.passiveServerIdle tid ty hStObj (hSCB ▸ hUnbound) hNotInQ hNotCur
    rw [hIS]; exact this
  -- 14. donationBudgetTransfer: two `.tcb` hyps + `schedContextBinding` → (b).
  · intro tid1 tid2 tcb1 tcb2 scId hObj1 hObj2 hNe hSc1 hSc2
    obtain ⟨ty1, hSt1, _, _, _, _, _, hSCB1, _⟩ := hFwd tid1.toObjId tcb1 hObj1
    obtain ⟨ty2, hSt2, _, _, _, _, _, hSCB2, _⟩ := hFwd tid2.toObjId tcb2 hObj2
    exact hInv.donationBudgetTransfer tid1 tid2 ty1 ty2 scId hSt1 hSt2 hNe
      (hSCB1 ▸ hSc1) (hSCB2 ▸ hSc2)
  -- 15. blockedOnReplyHasTarget: reads `tcb.ipcState` → (b).
  · intro tid tcb endpointId replyTarget hObj hIpc
    obtain ⟨ty, hStObj, hIS, _⟩ := hFwd tid.toObjId tcb hObj
    exact hInv.blockedOnReplyHasTarget tid ty endpointId replyTarget hStObj (hIS ▸ hIpc)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: storing a `.tcb` that differs from the stored slot's previous TCB
only in `replyObject` preserves `ipcInvariantCore`.  No structural conjunct reads
`replyObject`; every read field (ipcState, pendingMessage, queueNext/Prev/PPrev,
schedContextBinding, timeoutBudget) is unchanged.  Thin instance of
`storeObject_tcb_ipcInvariantCore_of_agreements`. -/
theorem storeObject_tcb_replyObject_preserves_ipcInvariantCore
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb : TCB) (v : Option SeLe4n.ReplyId)
    (hInv : ipcInvariantCore st) (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb { tcb with replyObject := v }) st = .ok ((), st')) :
    ipcInvariantCore st' :=
  storeObject_tcb_ipcInvariantCore_of_agreements st st' hInv
    (tcb_replyObject_store_nonTcb_agree st st' id tcb v hObjInv hPrev hStore)
    (tcb_replyObject_store_tcb_forward st st' id tcb v hObjInv hPrev hStore)
    (tcb_replyObject_store_tcb_backward st st' id tcb v hObjInv hPrev hStore)
    (storeObject_scheduler_eq st st' id (.tcb { tcb with replyObject := v }) hStore)

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.0): non-`.tcb` kind agreement across a `pendingReceiveReply`
store — verbatim dual of `tcb_replyObject_store_nonTcb_agree`. -/
private theorem tcb_pendingReceiveReply_store_nonTcb_agree
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb : TCB) (v : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb { tcb with pendingReceiveReply := v }) st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (k : KernelObject), (∀ tt, k ≠ .tcb tt) →
      (st'.objects[s]? = some k ↔ st.objects[s]? = some k) := by
  intro s k hk
  by_cases hs : s = id
  · subst hs
    rw [storeObject_objects_eq st st' s (.tcb { tcb with pendingReceiveReply := v }) hObjInv hStore,
        hPrev]
    constructor
    · intro h; cases h; exact absurd rfl (hk _)
    · intro h; cases h; exact absurd rfl (hk _)
  · rw [storeObject_objects_ne st st' id s (.tcb { tcb with pendingReceiveReply := v }) hs hObjInv hStore]

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.0): forward read-field agreement across a `pendingReceiveReply`
store — verbatim dual of `tcb_replyObject_store_tcb_forward`. -/
private theorem tcb_pendingReceiveReply_store_tcb_forward
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb : TCB) (v : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb { tcb with pendingReceiveReply := v }) st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget := by
  intro s tx hObj
  by_cases hs : s = id
  · subst hs
    rw [storeObject_objects_eq st st' s (.tcb { tcb with pendingReceiveReply := v }) hObjInv hStore] at hObj
    cases hObj
    exact ⟨tcb, hPrev, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · rw [storeObject_objects_ne st st' id s (.tcb { tcb with pendingReceiveReply := v }) hs hObjInv hStore]
      at hObj
    exact ⟨tx, hObj, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.0): backward read-field agreement across a `pendingReceiveReply`
store — verbatim dual of `tcb_replyObject_store_tcb_backward`. -/
private theorem tcb_pendingReceiveReply_store_tcb_backward
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb : TCB) (v : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb { tcb with pendingReceiveReply := v }) st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (ty : TCB), st.objects[s]? = some (.tcb ty) →
      ∃ tx, st'.objects[s]? = some (.tcb tx) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget := by
  intro s ty hObj
  by_cases hs : s = id
  · subst hs
    rw [hPrev] at hObj
    cases hObj
    exact ⟨{ tcb with pendingReceiveReply := v },
      storeObject_objects_eq st st' s (.tcb { tcb with pendingReceiveReply := v }) hObjInv hStore,
      rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · refine ⟨ty, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    rw [storeObject_objects_ne st st' id s (.tcb { tcb with pendingReceiveReply := v }) hs hObjInv hStore]
    exact hObj

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.0): storing a `.tcb` that differs only in `pendingReceiveReply`
preserves `ipcInvariantCore` — the server-first stash field the #7 receive fold
writes.  No structural conjunct reads it (only the full-invariant
`pendingReceiveReplyWellFormed` does, established separately), so this is the same
read-field-agreement instance as the `replyObject` store. -/
theorem storeObject_tcb_pendingReceiveReply_preserves_ipcInvariantCore
    (st st' : SystemState) (id : SeLe4n.ObjId) (tcb : TCB) (v : Option SeLe4n.ReplyId)
    (hInv : ipcInvariantCore st) (hObjInv : st.objects.invExt)
    (hPrev : st.objects[id]? = some (.tcb tcb))
    (hStore : storeObject id (.tcb { tcb with pendingReceiveReply := v }) st = .ok ((), st')) :
    ipcInvariantCore st' :=
  storeObject_tcb_ipcInvariantCore_of_agreements st st' hInv
    (tcb_pendingReceiveReply_store_nonTcb_agree st st' id tcb v hObjInv hPrev hStore)
    (tcb_pendingReceiveReply_store_tcb_forward st st' id tcb v hObjInv hPrev hStore)
    (tcb_pendingReceiveReply_store_tcb_backward st st' id tcb v hObjInv hPrev hStore)
    (storeObject_scheduler_eq st st' id (.tcb { tcb with pendingReceiveReply := v }) hStore)

-- ============================================================================
-- WS-SM SM6.D: the two reply-linkage operations preserve `ipcInvariantFull`.
--
-- `linkCallerReply` / `consumeCallerReply` (the Call/Reply-path linkage ops)
-- each compose exactly two object stores — a `.reply` store (the B1 mutator)
-- followed by a caller-TCB `replyObject` store — so their preservation chains
-- the two generic frame lemmas above: store A (`…reply…`) on the reply write,
-- store B (`…tcb_replyObject…`) on the TCB write, with `objects.invExt`
-- threaded between by `linkReply_preserves_objects_invExt` /
-- `consumeReply_preserves_objects_invExt`.  The live `.call` / `.reply`
-- dispatch (Phase C-wire) composes these ops after `endpointCall` /
-- `endpointReply`, so this is the preservation it needs.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (PR #822 review): `linkCallerReply` frames every object slot other
than the linked reply (`rid`) and the linking caller (`caller`) — its two stores
(`linkReply` at `rid.toObjId`, the TCB write at `caller.toObjId`) leave all other
slots intact.  The frame the `replyCallerLinkage` establishment reads for untouched
TCBs/Replies. -/
theorem linkCallerReply_objects_frame (st st' : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : linkCallerReply caller rid st = .ok ((), st'))
    (x : SeLe4n.ObjId) (hxR : x ≠ rid.toObjId) (hxC : x ≠ caller.toObjId) :
    st'.objects[x]? = st.objects[x]? := by
  unfold linkCallerReply at hStep
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hFrame1 : st1.objects[x]? = st.objects[x]? := by
      unfold linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hLink; simp at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · exact storeObject_objects_ne st st1 rid.toObjId x _ hxR hObjInv hLink
        · simp at hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · have hInv1 := linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
        rw [storeObject_objects_ne st1 st' caller.toObjId x _ hxC hInv1 hStep, hFrame1]
      · simp at hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (#7.0): `linkCallerReply` preserves the 15 structural conjuncts
(`ipcInvariantCore`).  The reply store changes only `reply.caller` (read by no
core conjunct) and the TCB store changes only `replyObject` (likewise) — so the
generic reply/TCB-field core-preservation lemmas chain directly, with no
caller-blocked precondition (unlike the full-invariant version, which must also
re-establish the 16th `replyCallerLinkage` conjunct).  The `#7` receive fold uses
the structural projections of this on the dequeued-caller link. -/
theorem linkCallerReply_preserves_ipcInvariantCore
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hInv : ipcInvariantCore st) (hObjInv : st.objects.invExt)
    (hStep : linkCallerReply caller rid st = .ok ((), st')) :
    ipcInvariantCore st' := by
  unfold linkCallerReply at hStep
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hObjInv1 : st1.objects.invExt :=
      linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    have hCore1 : ipcInvariantCore st1 := by
      unfold linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hLink; simp at hLink
      | some r =>
        simp only [hGetR] at hLink
        split at hLink
        · exact storeObject_reply_preserves_ipcInvariantCore st st1 rid.toObjId r
            { r with caller := some caller } hInv hObjInv
            ((getReply?_eq_some_iff st rid r).mp hGetR) hLink
        · simp at hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · exact storeObject_tcb_replyObject_preserves_ipcInvariantCore st1 st'
          caller.toObjId tcb (some rid) hCore1 hObjInv1
          ((getTcb?_eq_some_iff st1 caller tcb).mp hT) hStep
      · simp at hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D: `linkCallerReply` frames every object slot other than the consumed
reply (`rid`) and the unblocked caller (`caller`) — symmetric to the link frame. -/
theorem consumeCallerReply_objects_frame (st st' : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : consumeCallerReply caller rid st = .ok ((), st'))
    (x : SeLe4n.ObjId) (hxR : x ≠ rid.toObjId) (hxC : x ≠ caller.toObjId) :
    st'.objects[x]? = st.objects[x]? := by
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hFrame1 : st1.objects[x]? = st.objects[x]? := by
      unfold consumeReply at hCons
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hCons; cases hCons; rfl
      | some r =>
        rw [hGetR] at hCons
        exact storeObject_objects_ne st st1 rid.toObjId x _ hxR hObjInv hCons
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact hFrame1
    | some tcb =>
      simp only [hT] at hStep
      have hInv1 := consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
      rw [storeObject_objects_ne st1 st' caller.toObjId x _ hxC hInv1 hStep, hFrame1]

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (PR #822 review): the success preconditions of `linkCallerReply`:
the reply was **free** (`st.getReply? rid = some r0`, `r0.caller = none`) and the
caller held **no** reply object (`tcbC.replyObject = none`).  Both are the
single-use barriers `linkReply` / the caller-side guard enforce; the
`replyCallerLinkage` establishment reads them to rule out a pre-existing link to
`rid` or from `caller`. -/
theorem linkCallerReply_pre (st st' : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : linkCallerReply caller rid st = .ok ((), st')) :
    (∃ r0, st.getReply? rid = some r0 ∧ r0.caller = none) ∧
    (∃ tcbC, st.getTcb? caller = some tcbC ∧ tcbC.replyObject = none) := by
  unfold linkCallerReply at hStep
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    -- (1) reply free, extracted from `linkReply`'s success branch.
    obtain ⟨r0, hGetR, hFree⟩ : ∃ r0, st.getReply? rid = some r0 ∧ r0.caller = none := by
      unfold linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hLink; simp at hLink
      | some r0 =>
        simp only [hGetR] at hLink
        split at hLink
        · rename_i hF; exact ⟨r0, rfl, by simpa using hF⟩
        · simp at hLink
    -- `linkReply` post: `rid` now holds `r0` with `caller := some caller`.
    have hR1 : st1.getReply? rid = some { r0 with caller := some caller } :=
      linkReply_getReply?_caller_some st rid caller r0 hObjInv hGetR hFree st1 hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · rename_i hRepNone
        -- the caller slot (a TCB) is distinct from the reply slot, so it framed
        -- past the `linkReply` store unchanged: `st.getTcb? caller = some tcb`.
        have hNe : caller.toObjId ≠ rid.toObjId :=
          getTcb?_getReply?_slot_ne st1 caller rid tcb _ hT hR1
        have hFrame : st1.objects[caller.toObjId]? = st.objects[caller.toObjId]? := by
          unfold linkReply at hLink
          simp only [hGetR] at hLink
          rw [if_pos (by simp [hFree])] at hLink
          exact storeObject_objects_ne st st1 rid.toObjId caller.toObjId _ hNe hObjInv hLink
        have hT0 : st.getTcb? caller = some tcb := by
          rw [getTcb?_eq_some_iff] at hT ⊢; rw [← hFrame]; exact hT
        exact ⟨⟨r0, hGetR, hFree⟩, ⟨tcb, hT0, by simpa using hRepNone⟩⟩
      · simp at hStep

-- ============================================================================
-- IPC de-threading D2 — `blockedOnReplyHasReplyObject` frame family
--
-- The third clause of `replyCallerLinkage` reads only each TCB's `(ipcState,
-- replyObject)` pair.  The keystone below frames it through a single `storeObject`;
-- every IPC step (queue-link writes, ready stores, the endpoint store) is a
-- `storeObject` and reuses it, so the folded transitions can *establish* the third
-- clause concretely instead of threading it.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2 (keystone): a single `storeObject` preserves
`blockedOnReplyHasReplyObject` provided the stored object does not introduce a
`.blockedOnReply` TCB lacking a `replyObject` (`hNew`).  Every TCB other than the
stored slot is framed (`storeObject_objects_ne`); the stored slot is discharged by
`hNew`.  All the per-step frames (`storeTcbQueueLinks`, ready stores, the endpoint
store) instantiate this with an `hNew` discharged from the input invariant. -/
theorem storeObject_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (oid : SeLe4n.ObjId) (o : KernelObject)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hNew : ∀ (t : TCB) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        o = .tcb t → t.ipcState = .blockedOnReply ep rt → ∃ rid, t.replyObject = some rid)
    (hStep : storeObject oid o st = .ok ((), st')) :
    blockedOnReplyHasReplyObject st' := by
  intro tid tcb ep rt hTcb hBlk
  by_cases h : tid.toObjId = oid
  · have hLook : st'.objects[oid]? = some o := by
      rw [RHTable_getElem?_eq_get?]
      exact storeObject_inserted_object_lookup st oid o hObjInv st' hStep
    rw [h, hLook] at hTcb
    exact hNew tcb ep rt (Option.some.inj hTcb) hBlk
  · rw [storeObject_objects_ne st st' oid tid.toObjId o h hObjInv hStep] at hTcb
    exact hInv tid tcb ep rt hTcb hBlk

/-- IPC de-threading D2: any object-store-preserving step frames the third clause. -/
theorem blockedOnReplyHasReplyObject_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : blockedOnReplyHasReplyObject st) :
    blockedOnReplyHasReplyObject st' := by
  intro tid tcb ep rt hTcb hBlk
  rw [hObjs] at hTcb
  exact h tid tcb ep rt hTcb hBlk

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: a `storeTcbIpcStateAndMessage` whose new `ipcState` is **not**
`.blockedOnReply` preserves the third clause — the stored TCB leaves the
`.blockedOnReply` domain (so `hNew` is vacuous) and every other TCB is framed.  Covers
the receiver-`.ready` store of the Call/Receive rendezvous. -/
theorem storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hNotBlocked : ∀ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId), ipc ≠ .blockedOnReply ep rt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    blockedOnReplyHasReplyObject st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      refine storeObject_preserves_blockedOnReplyHasReplyObject st st'' tid.toObjId _ hObjInv hInv
        (fun t ep rt ho hb => ?_) hSO
      simp only [KernelObject.tcb.injEq] at ho
      subst ho
      exact absurd hb (hNotBlocked ep rt)

open SeLe4n.Model.SystemState in
/-- Finding F-1: `storeTcbReceiveComplete` preserves the third clause — the stored
TCB is `.ready`, never `.blockedOnReply`, so the keystone discharge is automatic (no
`hNotBlocked` hypothesis needed).  Mirror of
`storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject`. -/
theorem storeTcbReceiveComplete_nonBlocked_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    blockedOnReplyHasReplyObject st' := by
  unfold storeTcbReceiveComplete at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      refine storeObject_preserves_blockedOnReplyHasReplyObject st st'' tid.toObjId _ hObjInv hInv
        (fun t ep rt ho hb => ?_) hSO
      simp only [KernelObject.tcb.injEq] at ho
      subst ho
      simp at hb

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: the `storeTcbIpcState` analogue of the non-blocked frame — a
single `{tcb with ipcState := ipc}` store whose new `ipcState` is not `.blockedOnReply`.
Covers the receiver's `.blockedOnReceive` store on `endpointReceiveDual`'s block path. -/
theorem storeTcbIpcState_nonBlocked_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hNotBlocked : ∀ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId), ipc ≠ .blockedOnReply ep rt)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    blockedOnReplyHasReplyObject st' := by
  unfold storeTcbIpcState at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      refine storeObject_preserves_blockedOnReplyHasReplyObject st st'' tid.toObjId _ hObjInv hInv
        (fun t ep rt ho hb => ?_) hSO
      simp only [KernelObject.tcb.injEq] at ho
      subst ho
      exact absurd hb (hNotBlocked ep rt)

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `storeTcbQueueLinks` writes only queue-link fields
(`tcbWithQueueLinks` preserves `ipcState` / `replyObject`), so it frames the third
clause — `hNew` is discharged from the input invariant at the stored TCB.  Covers the
queue-relink stores inside `endpointQueuePopHead` / `endpointQueueEnqueue`. -/
theorem storeTcbQueueLinks_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    blockedOnReplyHasReplyObject st' := by
  unfold storeTcbQueueLinks at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      refine storeObject_preserves_blockedOnReplyHasReplyObject st st'' tid.toObjId _ hObjInv hInv
        (fun t ep rt ho hb => ?_) hSO
      simp only [KernelObject.tcb.injEq] at ho
      subst ho
      have htcbObj : st.objects[tid.toObjId]? = some (.tcb tcb) :=
        lookupTcb_some_objects st tid tcb hL
      exact hInv tid tcb ep rt htcbObj hb

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: storing an **endpoint** object frames the third clause — no TCB
is written, so the keystone `hNew` is vacuous (`.endpoint ≠ .tcb`).  Covers the endpoint
store inside `endpointQueuePopHead` / `endpointQueueEnqueue`. -/
theorem storeObject_endpoint_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : storeObject oid (.endpoint ep) st = .ok ((), st')) :
    blockedOnReplyHasReplyObject st' :=
  storeObject_preserves_blockedOnReplyHasReplyObject st st' oid (.endpoint ep) hObjInv hInv
    (fun _ _ _ ho _ => by cases ho) hStep

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `pair`-shaped endpoint-store frame, mirroring
`storeObject_preserves_objects_invExt'` so it threads the success branch of
`endpointQueuePopHead` (which keeps the `pair : Unit × SystemState` intact). -/
theorem storeObject_endpoint_preserves_blockedOnReplyHasReplyObject'
    (st : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint) (pair : Unit × SystemState)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStore : storeObject oid (.endpoint ep) st = .ok pair) :
    blockedOnReplyHasReplyObject pair.2 := by
  obtain ⟨⟨⟩, st'⟩ := pair
  exact storeObject_endpoint_preserves_blockedOnReplyHasReplyObject st st' oid ep hObjInv hInv hStore

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `endpointQueuePopHead` frames the third clause.  The dequeue is
one endpoint store (no TCB written — `.endpoint` helper) followed by one or two
`storeTcbQueueLinks` (queue-link frame: `ipcState`/`replyObject` untouched).  Navigation
mirrors `endpointQueuePopHead_preserves_objects_invExt` line-for-line, threading the
predicate alongside `invExt`. -/
theorem endpointQueuePopHead_preserves_blockedOnReplyHasReplyObject
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    blockedOnReplyHasReplyObject st' := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hP1 := storeObject_endpoint_preserves_blockedOnReplyHasReplyObject'
              st endpointId _ pair hObjInv hInv hStore
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact storeTcbQueueLinks_preserves_blockedOnReplyHasReplyObject
                  pair.2 st3 headTid none none none hInv1 hP1 hFinal
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                  have hP2 := storeTcbQueueLinks_preserves_blockedOnReplyHasReplyObject
                    pair.2 st2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext hInv1 hP1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact storeTcbQueueLinks_preserves_blockedOnReplyHasReplyObject
                      st2 st3 headTid none none none hInv2 hP2 hFinal

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `endpointQueueEnqueue` frames the third clause — one endpoint
store (no TCB written) plus one or two `storeTcbQueueLinks` (queue-link frame).
Navigation mirrors `endpointQueueEnqueue_preserves_objects_invExt`. -/
theorem endpointQueueEnqueue_preserves_blockedOnReplyHasReplyObject
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    blockedOnReplyHasReplyObject st' := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hP1 := storeObject_endpoint_preserves_blockedOnReplyHasReplyObject'
                  st endpointId _ pair hObjInv hInv hStore
                intro hStep
                exact storeTcbQueueLinks_preserves_blockedOnReplyHasReplyObject _ _ tid _ _ _ hInv1 hP1 hStep
            | some tailTid =>
              cases hLookupT : lookupTcb st tailTid
              · simp [hLookupT]
              · rename_i tailTcb
                simp only [hLookupT]
                cases hStore : storeObject endpointId _ st
                · simp
                · rename_i pair
                  simp only []
                  have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  have hP1 := storeObject_endpoint_preserves_blockedOnReplyHasReplyObject'
                    st endpointId _ pair hObjInv hInv hStore
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid _ _ (some tid)
                  · simp
                  · rename_i st2
                    simp only []
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    have hP2 := storeTcbQueueLinks_preserves_blockedOnReplyHasReplyObject _ _ tailTid _ _ _ hInv1 hP1 hLink1
                    intro hStep
                    exact storeTcbQueueLinks_preserves_blockedOnReplyHasReplyObject _ _ tid _ _ _ hInv2 hP2 hStep

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: a `storeTcbIpcStateAndMessage` on `self` frames the third clause
for **every TCB other than `self`** — only `self`'s slot is written, so any `tid ≠ self`
is preserved.  Used for the caller's `.blockedOnReply` store inside `endpointCall`, where
the full clause is momentarily false at `self` (no reply linked yet) but holds elsewhere. -/
theorem storeTcbIpcStateAndMessage_off_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (self : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : storeTcbIpcStateAndMessage st self ipc msg = .ok st') :
    ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
      tid ≠ self →
      st'.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.ipcState = .blockedOnReply ep rt →
      ∃ ridv, tcb.replyObject = some ridv := by
  intro tid tcb ep rt hNe hTcb hBlk
  have hFrame : st'.objects[tid.toObjId]? = st.objects[tid.toObjId]? :=
    storeTcbIpcStateAndMessage_preserves_objects_ne st st' self ipc msg tid.toObjId
      (fun h => hNe (ThreadId.toObjId_injective tid self h)) hObjInv hStep
  rw [hFrame] at hTcb
  exact hInv tid tcb ep rt hTcb hBlk

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `linkCallerReply` **establishes** the third clause from the
weaker `hThirdExc` (every TCB *other than* `caller` already carries a reply).  The link
sets `caller.replyObject := some rid`, so the caller's own obligation is discharged; every
other TCB is framed past `linkCallerReply`'s two writes (`caller`, `rid`).  This is the
third-clause-only companion of `linkCallerReply_establishes_replyCallerLinkage` (no
reciprocal hypothesis needed), the seam the `endpointCall` fold composes. -/
theorem linkCallerReply_establishes_blockedOnReplyHasReplyObject (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hThirdExc : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
        (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        tid ≠ caller →
        st.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.ipcState = .blockedOnReply ep rt →
        ∃ ridv, tcb.replyObject = some ridv)
    (hStep : linkCallerReply caller rid st = .ok ((), st')) :
    blockedOnReplyHasReplyObject st' := by
  obtain ⟨tcbC', hGetC', hRepC'⟩ :=
    linkCallerReply_replyObject_some st caller rid hObjInv st' hStep
  have hCallerObj' : st'.objects[caller.toObjId]? = some (.tcb tcbC') :=
    (getTcb?_eq_some_iff st' caller tcbC').mp hGetC'
  obtain ⟨⟨r0, hGetR, hFree⟩, _⟩ :=
    linkCallerReply_pre st st' caller rid hObjInv hStep
  have hR1' : st'.getReply? rid = some { r0 with caller := some caller } :=
    linkCallerReply_getReply?_caller_some st caller rid r0 hObjInv hGetR hFree st' hStep
  have hReplyObj' : st'.objects[rid.toObjId]? = some (.reply { r0 with caller := some caller }) :=
    (getReply?_eq_some_iff st' rid _).mp hR1'
  have hFrame : ∀ x, x ≠ rid.toObjId → x ≠ caller.toObjId →
      st'.objects[x]? = st.objects[x]? :=
    fun x hxR hxC => linkCallerReply_objects_frame st st' caller rid hObjInv hStep x hxR hxC
  intro tid tcb ep rt hTcb hBlk
  by_cases hTC : tid = caller
  · subst hTC
    have htcb : tcbC' = tcb := by
      have := hCallerObj'.symm.trans hTcb; simpa using this
    subst htcb
    exact ⟨rid, hRepC'⟩
  · have htid_ne_caller : tid.toObjId ≠ caller.toObjId :=
      fun h => hTC (ThreadId.toObjId_injective tid caller h)
    have htid_ne_rid : tid.toObjId ≠ rid.toObjId := by
      intro h; rw [h, hReplyObj'] at hTcb; cases hTcb
    rw [hFrame tid.toObjId htid_ne_rid htid_ne_caller] at hTcb
    exact hThirdExc tid tcb ep rt hTC hTcb hBlk

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `linkServerStashedReply` **establishes** the third clause from
`hThirdExc`.  It is `linkCallerReply caller rid` (which discharges the caller's obligation
— `linkCallerReply_establishes_blockedOnReplyHasReplyObject`) followed by the server's
stash-clear store, which writes only `server.pendingReceiveReply` (leaving every TCB's
`ipcState`/`replyObject` intact), so the keystone frames it: any `.blockedOnReply` server
in the post-link state already carries a reply by the clause `linkCallerReply` just
established.  The composition seam for `endpointCall`'s server-waiting rendezvous. -/
theorem linkServerStashedReply_establishes_blockedOnReplyHasReplyObject
    (st st' : SystemState) (caller server : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hThirdExc : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
        (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        tid ≠ caller →
        st.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.ipcState = .blockedOnReply ep rt →
        ∃ ridv, tcb.replyObject = some ridv)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    blockedOnReplyHasReplyObject st' := by
  unfold SystemState.linkServerStashedReply at hStep
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    cases hLink : SystemState.linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hObjInv1 := linkCallerReply_preserves_objects_invExt st st1 caller rid hObjInv hLink
      have hThird1 : blockedOnReplyHasReplyObject st1 :=
        linkCallerReply_establishes_blockedOnReplyHasReplyObject st st1 caller rid hObjInv hThirdExc hLink
      cases hT : st1.getTcb? server with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, hEq⟩ := hStep; subst hEq; exact hThird1
      | some sTcb =>
        simp only [hT] at hStep
        have hServerObj : st1.objects[server.toObjId]? = some (.tcb sTcb) :=
          (getTcb?_eq_some_iff st1 server sTcb).mp hT
        refine storeObject_preserves_blockedOnReplyHasReplyObject st1 st' server.toObjId _
          hObjInv1 hThird1 (fun t ep rt ho hb => ?_) hStep
        simp only [KernelObject.tcb.injEq] at ho
        subst ho
        exact hThird1 server sTcb ep rt hServerObj (by simpa using hb)

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `endpointCall` **establishes** the third clause of
`replyCallerLinkage` (`blockedOnReply ⇒ replyObject`) — concretely, no threaded
post-state hypothesis.  Rendezvous branch: pop (frame) → receiver `.ready` store
(non-blocked frame) → `ensureRunnable` (objects frame) → caller `.blockedOnReply` store
(breaks the clause *only* for `caller`, leaving `hThirdExc`) → `linkServerStashedReply`
(re-establishes it for `caller`, the link is *atomic* with the block) → `removeRunnable`
(objects frame).  Blocking branch: the caller becomes `.blockedOnCall` (never
`.blockedOnReply`), so the clause is framed throughout.  Closes the #7.4 origin gap at the
transition boundary: `endpointCall` cannot strand a `.blockedOnReply` caller without a
backing reply. -/
theorem endpointCall_establishes_blockedOnReplyHasReplyObject
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : blockedOnReplyHasReplyObject st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    blockedOnReplyHasReplyObject st' := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          have hP1 : blockedOnReplyHasReplyObject pair.2.2 :=
            endpointQueuePopHead_preserves_blockedOnReplyHasReplyObject endpointId true st pair.2.2 pair.1 _ hObjInv hInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hMsg
            have hP2 : blockedOnReplyHasReplyObject st2 :=
              storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
                pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hP1 (by simp) hMsg
            have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by rwa [ensureRunnable_preserves_objects]
            have hP3 : blockedOnReplyHasReplyObject (ensureRunnable st2 pair.1) :=
              blockedOnReplyHasReplyObject_of_objects_eq (ensureRunnable_preserves_objects st2 pair.1) hP2
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc] at hStep
              have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) none hObjInvEns hIpc
              have hThirdExc4 := storeTcbIpcStateAndMessage_off_preserves_blockedOnReplyHasReplyObject
                (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) none hObjInvEns hP3 hIpc
              cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
              | error e => simp [hLink] at hStep
              | ok pL =>
                obtain ⟨_, st5⟩ := pL
                simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have hP5 : blockedOnReplyHasReplyObject st5 :=
                  linkServerStashedReply_establishes_blockedOnReplyHasReplyObject st4 st5 caller pair.1 hObjInv4 hThirdExc4 hLink
                exact blockedOnReplyHasReplyObject_of_objects_eq (removeRunnable_preserves_objects st5 caller) hP5
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
          have hP1 : blockedOnReplyHasReplyObject st1 :=
            endpointQueueEnqueue_preserves_blockedOnReplyHasReplyObject endpointId false caller st st1 hObjInv hInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hP2 : blockedOnReplyHasReplyObject st2 :=
              storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
                st1 st2 caller (.blockedOnCall endpointId) (some msg) hObjInv1 hP1 (by simp) hMsg
            exact blockedOnReplyHasReplyObject_of_objects_eq (removeRunnable_preserves_objects st2 caller) hP2

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `endpointReceiveDual` **establishes** the third clause of
`replyCallerLinkage`.  Call path (a `.blockedOnCall` sender dequeued): pop (frame) → sender
`.blockedOnReply` store (breaks the clause only for the sender) → `linkCallerReply`
(re-establishes it for the sender, *atomically*) → receiver `.ready` store (frame).  Send
path: sender/receiver both go `.ready` — framed throughout.  Block path (no sender):
cleanup (frame) → enqueue (frame) → receiver `.blockedOnReceive` store (frame) → stash
store (keystone; the receiver is not `.blockedOnReply`) → `removeRunnable` (frame).  No
branch strands a `.blockedOnReply` thread without a reply. -/
theorem endpointReceiveDual_establishes_blockedOnReplyHasReplyObject
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (hInv : blockedOnReplyHasReplyObject st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st')) :
    blockedOnReplyHasReplyObject st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInvPop : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hP1 : blockedOnReplyHasReplyObject pair.2.2 :=
            endpointQueuePopHead_preserves_blockedOnReplyHasReplyObject endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hInv hPop
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall _ =>
            simp only [hSenderIpc, ite_true] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hThirdExc : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (ep' : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
                  tid ≠ pair.1 → st2.objects[tid.toObjId]? = some (.tcb tcb) →
                  tcb.ipcState = .blockedOnReply ep' rt → ∃ ridv, tcb.replyObject = some ridv :=
                storeTcbIpcStateAndMessage_off_preserves_blockedOnReplyHasReplyObject
                  pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInvPop hP1 hMsg
              cases hReplyId : replyId with
              | none => simp [hReplyId] at hStep
              | some rid =>
                simp only [hReplyId] at hStep
                cases hLink : SystemState.linkCallerReply pair.1 rid st2 with
                | error e => simp [hLink] at hStep
                | ok pLink =>
                  obtain ⟨_, stLinked⟩ := pLink
                  simp only [hLink] at hStep
                  have hObjInvLink : stLinked.objects.invExt :=
                    linkCallerReply_preserves_objects_invExt st2 stLinked pair.1 rid hObjInvMsg hLink
                  have hPLink : blockedOnReplyHasReplyObject stLinked :=
                    linkCallerReply_establishes_blockedOnReplyHasReplyObject st2 stLinked pair.1 rid hObjInvMsg hThirdExc hLink
                  revert hStep
                  cases hPend : storeTcbIpcStateAndMessage stLinked receiver .ready _ with
                  | ok st4 =>
                    exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸
                      storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
                        stLinked st4 receiver .ready _ hObjInvLink hPLink (by simp) hPend
                  | error _ => simp
          | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
            simp only [hSenderIpc] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hP2 : blockedOnReplyHasReplyObject st2 :=
                storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
                  pair.2.2 st2 pair.1 .ready none hObjInvPop hP1 (by simp) hMsg
              have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by rwa [ensureRunnable_preserves_objects]
              have hP3 : blockedOnReplyHasReplyObject (ensureRunnable st2 pair.1) :=
                blockedOnReplyHasReplyObject_of_objects_eq (ensureRunnable_preserves_objects st2 pair.1) hP2
              revert hStep
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready _ with
              | ok st4 =>
                exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸
                  storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
                    (ensureRunnable st2 pair.1) st4 receiver .ready _ hObjInvEns hP3 (by simp) hPend
              | error _ => simp
      | none =>
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hPClean : blockedOnReplyHasReplyObject (cleanupPreReceiveDonation st receiver) :=
            cleanupPreReceiveDonation_preserves_blockedOnReplyHasReplyObject st receiver hObjInv hInv
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInvEnq : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hP1 : blockedOnReplyHasReplyObject st1 :=
              endpointQueueEnqueue_preserves_blockedOnReplyHasReplyObject endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hPClean hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc] at hStep
              have hObjInv2 : st2.objects.invExt :=
                storeTcbIpcState_preserves_objects_invExt st1 st2 receiver _ hObjInvEnq hIpc
              have hP2 : blockedOnReplyHasReplyObject st2 :=
                storeTcbIpcState_nonBlocked_preserves_blockedOnReplyHasReplyObject st1 st2 receiver _ hObjInvEnq hP1 (by simp) hIpc
              cases hGetR : st2.getTcb? receiver with
              | none =>
                simp only [hGetR, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact blockedOnReplyHasReplyObject_of_objects_eq (removeRunnable_preserves_objects st2 receiver) hP2
              | some rTcb =>
                simp only [hGetR] at hStep
                cases hStash : storeObject receiver.toObjId (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                | error e => simp [hStash] at hStep
                | ok pStash =>
                  obtain ⟨_, stStashed⟩ := pStash
                  simp only [hStash, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, hEq⟩ := hStep; subst hEq
                  have hRecvObj : st2.objects[receiver.toObjId]? = some (.tcb rTcb) :=
                    (getTcb?_eq_some_iff st2 receiver rTcb).mp hGetR
                  have hPStash : blockedOnReplyHasReplyObject stStashed := by
                    refine storeObject_preserves_blockedOnReplyHasReplyObject st2 stStashed receiver.toObjId _
                      hObjInv2 hP2 (fun t ep' rt ho hb => ?_) hStash
                    simp only [KernelObject.tcb.injEq] at ho
                    subst ho
                    exact hP2 receiver rTcb ep' rt hRecvObj (by simpa using hb)
                  exact blockedOnReplyHasReplyObject_of_objects_eq (removeRunnable_preserves_objects stStashed receiver) hPStash

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (PR #822 review): `linkCallerReply` **establishes**
`replyCallerLinkage`.  On success the only changed slots are the linked reply
(`rid`, now `caller := some caller`) and the linking caller (`caller`, now
`replyObject := some rid`) — mutually reciprocal — while every other TCB/Reply is
framed past unchanged.  The success preconditions (`linkCallerReply_pre`: the reply
was free, the caller held no reply) rule out a pre-existing link to `rid` or from
`caller`, so the bidirectional invariant re-establishes from `replyCallerLinkage st`. -/
theorem linkCallerReply_establishes_replyCallerLinkage (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hRecip : replyCallerLinkageReciprocal st) (hObjInv : st.objects.invExt)
    (hCallerBlk : ∀ tc, st.getTcb? caller = some tc →
      ∃ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId), tc.ipcState = .blockedOnReply ep rt)
    -- WS-SM SM6.D (#7.4): every OTHER `.blockedOnReply` TCB already carries a reply.
    -- `caller` is excluded: at the link site it is `.blockedOnReply` but not-yet-linked
    -- (`replyObject = none`), so the full third clause is momentarily false there — the
    -- link this step performs is exactly what restores it for `caller`.
    (hThirdExc : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
        (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        tid ≠ caller →
        st.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.ipcState = .blockedOnReply ep rt →
        ∃ ridv, tcb.replyObject = some ridv)
    (hStep : linkCallerReply caller rid st = .ok ((), st')) :
    replyCallerLinkage st' := by
  obtain ⟨⟨r0, hGetR, hFree⟩, tcbC, hGetC, hCFree⟩ :=
    linkCallerReply_pre st st' caller rid hObjInv hStep
  obtain ⟨tcbC', hGetC', hRepC'⟩ :=
    linkCallerReply_replyObject_some st caller rid hObjInv st' hStep
  have hR1' : st'.getReply? rid = some { r0 with caller := some caller } :=
    linkCallerReply_getReply?_caller_some st caller rid r0 hObjInv hGetR hFree st' hStep
  have hCallerObj' : st'.objects[caller.toObjId]? = some (.tcb tcbC') :=
    (getTcb?_eq_some_iff st' caller tcbC').mp hGetC'
  have hReplyObj' : st'.objects[rid.toObjId]? = some (.reply { r0 with caller := some caller }) :=
    (getReply?_eq_some_iff st' rid _).mp hR1'
  have hCallerObj : st.objects[caller.toObjId]? = some (.tcb tcbC) :=
    (getTcb?_eq_some_iff st caller tcbC).mp hGetC
  have hReplyObj : st.objects[rid.toObjId]? = some (.reply r0) :=
    (getReply?_eq_some_iff st rid r0).mp hGetR
  have hFrame : ∀ x, x ≠ rid.toObjId → x ≠ caller.toObjId →
      st'.objects[x]? = st.objects[x]? :=
    fun x hxR hxC => linkCallerReply_objects_frame st st' caller rid hObjInv hStep x hxR hxC
  refine ⟨⟨?fwd, ?bwd⟩, ?third⟩
  · -- forward: a TCB pointing at a reply finds it reciprocating.
    intro tid tcb ridv hTcb hRep
    by_cases hTC : tid = caller
    · subst hTC
      have htcb : tcbC' = tcb := by
        have := hCallerObj'.symm.trans hTcb; simpa using this
      subst htcb
      rw [hRepC'] at hRep
      have : ridv = rid := by simpa using hRep.symm
      subst this
      exact ⟨_, hReplyObj', rfl⟩
    · have htid_ne_caller : tid.toObjId ≠ caller.toObjId :=
        fun h => hTC (ThreadId.toObjId_injective tid caller h)
      have htid_ne_rid : tid.toObjId ≠ rid.toObjId := by
        intro h; rw [h, hReplyObj'] at hTcb; cases hTcb
      rw [hFrame tid.toObjId htid_ne_rid htid_ne_caller] at hTcb
      obtain ⟨r, hr, hrc⟩ := hRecip.1 tid tcb ridv hTcb hRep
      have hridv_ne_rid : ridv.toObjId ≠ rid.toObjId := by
        intro h; rw [h, hReplyObj] at hr
        simp only [Option.some.injEq, KernelObject.reply.injEq] at hr
        subst hr; rw [hFree] at hrc; cases hrc
      have hridv_ne_caller : ridv.toObjId ≠ caller.toObjId := by
        intro h; rw [h, hCallerObj] at hr; cases hr
      rw [← hFrame ridv.toObjId hridv_ne_rid hridv_ne_caller] at hr
      exact ⟨r, hr, hrc⟩
  · -- backward: a reply naming a thread finds the thread pointing back.
    intro ridv r tid hRep hCaller
    by_cases hRR : ridv = rid
    · subst hRR
      rw [hReplyObj'] at hRep
      simp only [Option.some.injEq, KernelObject.reply.injEq] at hRep
      subst hRep
      simp only at hCaller
      have : tid = caller := by simpa using hCaller.symm
      subst this
      -- the linked caller is `blockedOnReply` (precondition + ipcState preserved).
      obtain ⟨ep, rt, hBlk⟩ := hCallerBlk tcbC hGetC
      have hIpc : tcbC'.ipcState = tcbC.ipcState :=
        linkCallerReply_caller_ipcState_preserved st tid ridv tcbC hObjInv hGetC st' tcbC' hStep hGetC'
      exact ⟨tcbC', hCallerObj', hRepC', ep, rt, by rw [hIpc]; exact hBlk⟩
    · have hridv_ne_rid : ridv.toObjId ≠ rid.toObjId :=
        fun h => hRR (SeLe4n.ReplyId.toObjId_injective ridv rid h)
      have hridv_ne_caller : ridv.toObjId ≠ caller.toObjId := by
        intro h; rw [h, hCallerObj'] at hRep; cases hRep
      rw [hFrame ridv.toObjId hridv_ne_rid hridv_ne_caller] at hRep
      obtain ⟨tcb, ht, htr, hBlk⟩ := hRecip.2 ridv r tid hRep hCaller
      have htid_ne_caller : tid.toObjId ≠ caller.toObjId := by
        intro h; rw [h, hCallerObj] at ht
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at ht
        subst ht; rw [hCFree] at htr; cases htr
      have htid_ne_rid : tid.toObjId ≠ rid.toObjId := by
        intro h; rw [h, hReplyObj] at ht; cases ht
      rw [← hFrame tid.toObjId htid_ne_rid htid_ne_caller] at ht
      exact ⟨tcb, ht, htr, hBlk⟩
  · -- third (#7.4): every `.blockedOnReply` TCB at `st'` carries a `replyObject`.
    intro tid tcb ep rt hTcb hBlk
    by_cases hTC : tid = caller
    · -- the just-linked caller now carries `replyObject = some rid`.
      subst hTC
      have htcb : tcbC' = tcb := by
        have := hCallerObj'.symm.trans hTcb; simpa using this
      subst htcb
      exact ⟨rid, hRepC'⟩
    · -- a different TCB is framed past unchanged ⇒ already `.blockedOnReply` at `st`.
      have htid_ne_caller : tid.toObjId ≠ caller.toObjId :=
        fun h => hTC (ThreadId.toObjId_injective tid caller h)
      have htid_ne_rid : tid.toObjId ≠ rid.toObjId := by
        intro h; rw [h, hReplyObj'] at hTcb; cases hTcb
      rw [hFrame tid.toObjId htid_ne_rid htid_ne_caller] at hTcb
      exact hThirdExc tid tcb ep rt hTC hTcb hBlk

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D (PR #822 review / #7.4): `consumeCallerReply` **preserves**
`replyCallerLinkageReciprocal` when invoked on a *mutually linked* pair
(`r0.caller = some caller`).  It clears both halves (`rid.caller := none`,
`caller.replyObject := none`); by reciprocity the back-link is reciprocal
(`caller.replyObject = some rid`), so clearing the pair removes exactly one consistent
edge and frames the rest.

This is deliberately the **reciprocal** half of `replyCallerLinkage`, not the full
invariant: standalone `consumeCallerReply` clears the caller's `replyObject` **without**
unblocking it, so on a still-`.blockedOnReply` caller it would *strand* the third clause
(`blockedOnReply ⇒ replyObject`).  The live `.reply` path unblocks the caller (it leaves
`.blockedOnReply` for `.ready`) **before** the link is torn down, so the fused
reply transition — not this primitive — re-establishes the third clause (the unblocked
caller no longer constrains it).  `consumeCallerReply` is reply-path prep awaiting that
fusion; this lemma carries the part it genuinely preserves on its own. -/
theorem consumeCallerReply_preserves_replyCallerLinkageReciprocal (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (r0 : SeLe4n.Kernel.Reply)
    (hRecip : replyCallerLinkageReciprocal st) (hObjInv : st.objects.invExt)
    (hGetR : st.getReply? rid = some r0) (hLinked : r0.caller = some caller)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    replyCallerLinkageReciprocal st' := by
  have hReplyObj : st.objects[rid.toObjId]? = some (.reply r0) :=
    (getReply?_eq_some_iff st rid r0).mp hGetR
  -- mutual link: the caller points back at `rid` (reciprocity from `hRecip`).
  obtain ⟨tcbC, hCallerObj, hCallerRep, _⟩ := hRecip.2 rid r0 caller hReplyObj hLinked
  have hC_ne : caller.toObjId ≠ rid.toObjId :=
    getTcb?_getReply?_slot_ne st caller rid tcbC r0
      ((getTcb?_eq_some_iff st caller tcbC).mpr hCallerObj) hGetR
  -- the caller TCB survives the consume (reply-less); used to exclude a reply at
  -- the caller slot in the backward direction.
  have hCallerTcb' : ∃ t, st'.objects[caller.toObjId]? = some (.tcb t) := by
    have hStep2 := hStep
    unfold consumeCallerReply at hStep2
    cases hCons : consumeReply rid st with
    | error e => rw [hCons] at hStep2; simp at hStep2
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hCons] at hStep2
      have hObjInv1 := consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
      have hT1 : st1.getTcb? caller = some tcbC := by
        rw [getTcb?_eq_some_iff]
        have hfr : st1.objects[caller.toObjId]? = st.objects[caller.toObjId]? := by
          unfold consumeReply at hCons
          cases hGetR2 : st.getReply? rid with
          | none => rw [hGetR2] at hCons; cases hCons; rfl
          | some r2 =>
            rw [hGetR2] at hCons
            exact storeObject_objects_ne st st1 rid.toObjId caller.toObjId _ hC_ne hObjInv hCons
        rw [hfr]; exact hCallerObj
      rw [hT1] at hStep2
      refine ⟨{ tcbC with replyObject := none }, ?_⟩
      have hLook := storeObject_inserted_object_lookup st1 caller.toObjId
        (.tcb { tcbC with replyObject := none }) hObjInv1 st' hStep2
      rw [RHTable_getElem?_eq_get?]; exact hLook
  -- post-conditions: `rid` now caller-less; any surviving caller TCB reply-less.
  have hR1' : st'.getReply? rid = some { r0 with caller := none } :=
    consumeCallerReply_getReply?_caller_none st caller rid r0 hObjInv hGetR st' hStep
  have hReplyObj' : st'.objects[rid.toObjId]? = some (.reply { r0 with caller := none }) :=
    (getReply?_eq_some_iff st' rid _).mp hR1'
  have hCallerNone' : ∀ tcb', st'.objects[caller.toObjId]? = some (.tcb tcb') →
      tcb'.replyObject = none := by
    intro tcb' hObj
    exact consumeCallerReply_replyObject_none st caller rid hObjInv st' tcb' hStep
      ((getTcb?_eq_some_iff st' caller tcb').mpr hObj)
  have hFrame : ∀ x, x ≠ rid.toObjId → x ≠ caller.toObjId →
      st'.objects[x]? = st.objects[x]? :=
    fun x hxR hxC => consumeCallerReply_objects_frame st st' caller rid hObjInv hStep x hxR hxC
  refine ⟨?fwd, ?bwd⟩
  · intro tid tcb ridv hTcb hRep
    by_cases hTC : tid = caller
    · subst hTC; rw [hCallerNone' tcb hTcb] at hRep; cases hRep
    · have htid_ne_caller : tid.toObjId ≠ caller.toObjId :=
        fun h => hTC (ThreadId.toObjId_injective tid caller h)
      have htid_ne_rid : tid.toObjId ≠ rid.toObjId := by
        intro h; rw [h, hReplyObj'] at hTcb; cases hTcb
      rw [hFrame tid.toObjId htid_ne_rid htid_ne_caller] at hTcb
      obtain ⟨r, hr, hrc⟩ := hRecip.1 tid tcb ridv hTcb hRep
      have hridv_ne_rid : ridv.toObjId ≠ rid.toObjId := by
        intro h; rw [h, hReplyObj] at hr
        simp only [Option.some.injEq, KernelObject.reply.injEq] at hr
        subst hr; rw [hLinked] at hrc
        simp only [Option.some.injEq] at hrc; exact hTC hrc.symm
      have hridv_ne_caller : ridv.toObjId ≠ caller.toObjId := by
        intro h; rw [h, hCallerObj] at hr; cases hr
      rw [← hFrame ridv.toObjId hridv_ne_rid hridv_ne_caller] at hr
      exact ⟨r, hr, hrc⟩
  · intro ridv r tid hRep hCaller
    by_cases hRR : ridv = rid
    · subst hRR; rw [hReplyObj'] at hRep
      simp only [Option.some.injEq, KernelObject.reply.injEq] at hRep
      subst hRep; simp only at hCaller; cases hCaller
    · have hridv_ne_rid : ridv.toObjId ≠ rid.toObjId :=
        fun h => hRR (SeLe4n.ReplyId.toObjId_injective ridv rid h)
      have hridv_ne_caller : ridv.toObjId ≠ caller.toObjId := by
        intro h; obtain ⟨t, ht⟩ := hCallerTcb'; rw [h, ht] at hRep; cases hRep
      rw [hFrame ridv.toObjId hridv_ne_rid hridv_ne_caller] at hRep
      obtain ⟨tcb, ht, htr, hBlk⟩ := hRecip.2 ridv r tid hRep hCaller
      have htid_ne_caller : tid.toObjId ≠ caller.toObjId := by
        intro h; rw [h, hCallerObj] at ht
        simp only [Option.some.injEq, KernelObject.tcb.injEq] at ht
        rw [ht] at hCallerRep; rw [hCallerRep] at htr
        simp only [Option.some.injEq] at htr; exact hRR htr.symm
      have htid_ne_rid : tid.toObjId ≠ rid.toObjId := by
        intro h; rw [h, hReplyObj] at ht; cases ht
      rw [← hFrame tid.toObjId htid_ne_rid htid_ne_caller] at ht
      exact ⟨tcb, ht, htr, hBlk⟩

-- NOTE: `linkCallerReply_preserves_ipcInvariantFull` and
-- `consumeCallerReply_preserves_ipcInvariantFull` are defined further down,
-- after the D3 `pendingReceiveReplyWellFormed` frame family, so their de-threaded
-- forms can derive the 17th conjunct via
-- `linkCallerReply_preserves_pendingReceiveReplyWellFormed` and
-- `consumeCallerReply_preserves_pendingReceiveReplyWellFormed` respectively.

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `endpointSendDual` **preserves** the third clause — it never sets
any TCB to `.blockedOnReply` (rendezvous: receiver `.ready`; blocking: sender
`.blockedOnSend`) and never touches `replyObject`, so the clause is framed throughout.
A preserve case (the `.blockedOnReply` set is never grown), not an establish. -/
theorem endpointSendDual_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : blockedOnReplyHasReplyObject st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    blockedOnReplyHasReplyObject st' := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          have hP1 := endpointQueuePopHead_preserves_blockedOnReplyHasReplyObject endpointId true st pair.2.2 pair.1 _ hObjInv hInv hPop
          cases hMsg : storeTcbReceiveComplete pair.2.2 pair.1 (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hP2 := storeTcbReceiveComplete_nonBlocked_preserves_blockedOnReplyHasReplyObject
              pair.2.2 st2 pair.1 (some msg) hObjInv1 hP1 hMsg
            exact blockedOnReplyHasReplyObject_of_objects_eq (ensureRunnable_preserves_objects st2 pair.1) hP2
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
          have hP1 := endpointQueueEnqueue_preserves_blockedOnReplyHasReplyObject endpointId false sender st st1 hObjInv hInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hP2 := storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
              st1 st2 sender (.blockedOnSend endpointId) (some msg) hObjInv1 hP1 (by simp) hMsg
            exact blockedOnReplyHasReplyObject_of_objects_eq (removeRunnable_preserves_objects st2 sender) hP2

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: storing any **non-TCB** object frames the third clause — the
keystone `hNew` is vacuous since the stored object is never a `.tcb`.  Generalises the
`.endpoint` helper; used by the notification transitions (`.notification` stores). -/
theorem storeObject_nonTcb_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hNonTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st'))
    (hInv : blockedOnReplyHasReplyObject st) :
    blockedOnReplyHasReplyObject st' :=
  storeObject_preserves_blockedOnReplyHasReplyObject st st' id obj hObjInv hInv
    (fun t _ _ ho _ => absurd ho (hNonTcb t)) hStore

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: a `storeTcbIpcState_fromTcb` whose new `ipcState` is not
`.blockedOnReply` frames the third clause (single `{tcb with ipcState := ipc}` store).
Covers the `.blockedOnNotification` block-path store on `notificationWait`. -/
theorem storeTcbIpcState_fromTcb_nonBlocked_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hNotBlocked : ∀ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId), ipc ≠ .blockedOnReply ep rt)
    (hStep : storeTcbIpcState_fromTcb st tid tcb ipc = .ok st') :
    blockedOnReplyHasReplyObject st' := by
  unfold storeTcbIpcState_fromTcb at hStep
  cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
  | error e => simp [hSO] at hStep
  | ok p =>
    obtain ⟨_, st''⟩ := p
    simp only [hSO, Except.ok.injEq] at hStep
    subst hStep
    refine storeObject_preserves_blockedOnReplyHasReplyObject st st'' tid.toObjId _ hObjInv hInv
      (fun t ep rt ho hb => ?_) hSO
    simp only [KernelObject.tcb.injEq] at ho
    subst ho
    exact absurd hb (hNotBlocked ep rt)

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `notificationSignal` **preserves** the third clause — it never
sets any TCB to `.blockedOnReply` (the woken waiter goes `.ready`) and the notification
stores are non-TCB, so the clause is framed.  Mirrors
`notificationSignal_preserves_waitingThreadsPendingMessageNone`. -/
theorem notificationSignal_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    blockedOnReplyHasReplyObject st' := by
  simp only [notificationSignal] at hStep
  split at hStep
  · rename_i ntfn hObj
    cases hWaiters : ntfn.waitingThreads.tail? with
    | some headTail =>
      obtain ⟨waiter, rest⟩ := headTail
      simp only [hWaiters] at hStep
      split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_nonTcb_preserves_blockedOnReplyHasReplyObject
          st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSM =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have hInv2 := storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
            st1 st2 waiter .ready _ hObjInv1 hInv1 (by simp) hSM
          exact blockedOnReplyHasReplyObject_of_objects_eq (ensureRunnable_preserves_objects st2 waiter) hInv2
    | none =>
      simp only [hWaiters] at hStep
      split at hStep
      all_goals
        exact storeObject_nonTcb_preserves_blockedOnReplyHasReplyObject
          st st' notificationId (.notification _) (fun tcb => by simp) hObjInv hStep hInv
  · contradiction
  · contradiction

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `notificationWait` **preserves** the third clause — deliver path
sets the waiter `.ready`, block path sets it `.blockedOnNotification` (neither
`.blockedOnReply`), and the notification stores are non-TCB.  Mirrors
`notificationWait_preserves_waitingThreadsPendingMessageNone`'s split structure. -/
theorem notificationWait_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : notificationWait notificationId waiter st = .ok (badge, st')) :
    blockedOnReplyHasReplyObject st' := by
  simp only [notificationWait] at hStep
  split at hStep
  · rename_i ntfn hObj
    split at hStep
    · -- deliver: pendingBadge = some
      split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_nonTcb_preserves_blockedOnReplyHasReplyObject
          st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSI =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          exact storeTcbIpcState_nonBlocked_preserves_blockedOnReplyHasReplyObject
            st1 st2 waiter .ready hObjInv1 hInv1 (by simp) hSI
    · -- block: pendingBadge = none
      split at hStep
      · contradiction
      · rename_i waiterTcb hLookup
        split at hStep
        · contradiction
        · split at hStep
          · contradiction
          · split at hStep
            next => contradiction
            next st1 hSO =>
              have hInv1 := storeObject_nonTcb_preserves_blockedOnReplyHasReplyObject
                st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
              have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
              split at hStep
              next => contradiction
              next st2 hSI =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                exact blockedOnReplyHasReplyObject_of_objects_eq (removeRunnable_preserves_objects st2 waiter)
                  (storeTcbIpcState_fromTcb_nonBlocked_preserves_blockedOnReplyHasReplyObject
                    st1 st2 waiter waiterTcb (.blockedOnNotification notificationId) hObjInv1 hInv1 (by simp) hSI)
  · contradiction
  · contradiction

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `endpointReply` **preserves** the third clause — it only *unblocks*
the replied-to target (`.blockedOnReply → .ready`) and never sets any TCB to
`.blockedOnReply`, so the `.blockedOnReply` set shrinks and the clause is framed.  (It does
not consume the reply object — that is `consumeCallerReply`.) -/
theorem endpointReply_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    blockedOnReplyHasReplyObject st' := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      cases replyTarget with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp
          | ok st'' =>
            intro hStep
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hP := storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
              st st'' target .ready (some msg) hObjInv hInv (by simp) hMsg
            exact blockedOnReplyHasReplyObject_of_objects_eq (ensureRunnable_preserves_objects st'' target) hP
        · simp at hStep

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `endpointReplyRecv` **preserves** the third clause — it unblocks
the reply target (`.ready`, framed) then runs `endpointReceiveDual`, which *establishes*
the clause (`endpointReceiveDual_establishes_blockedOnReplyHasReplyObject`).  Composes the
unblock frame with the receive-leg establish. -/
theorem endpointReplyRecv_preserves_blockedOnReplyHasReplyObject
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    blockedOnReplyHasReplyObject st' := by
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId expectedReplier =>
      simp only [hIpc] at hStep
      cases expectedReplier with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok stReplied =>
            simp only []
            have hObjInvR := storeTcbIpcStateAndMessage_preserves_objects_invExt st stReplied replyTarget _ _ hObjInv hMsg
            have hPR := storeTcbIpcStateAndMessage_nonBlocked_preserves_blockedOnReplyHasReplyObject
              st stReplied replyTarget .ready (some msg) hObjInv hInv (by simp) hMsg
            have hObjInvE : (ensureRunnable stReplied replyTarget).objects.invExt := by rwa [ensureRunnable_preserves_objects]
            have hPE : blockedOnReplyHasReplyObject (ensureRunnable stReplied replyTarget) :=
              blockedOnReplyHasReplyObject_of_objects_eq (ensureRunnable_preserves_objects stReplied replyTarget) hPR
            cases hRecv : endpointReceiveDual endpointId receiver replyId (ensureRunnable stReplied replyTarget) with
            | error e => simp
            | ok pair =>
              intro hStep
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              exact endpointReceiveDual_establishes_blockedOnReplyHasReplyObject
                (ensureRunnable stReplied replyTarget) pair.2 endpointId receiver pair.1 replyId hPE hObjInvE hRecv
        · simp at hStep

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `ipcUnwrapCaps` (the IPC cap-transfer step) **preserves** the
third clause.  It never creates a TCB — it writes only `receiverRoot`, and only as a CNode
— so every `.tcb` in the post-state maps back to the same `.tcb` in the pre-state
(`ipcUnwrapCaps_tcb_backward`); the clause then transports unchanged. -/
theorem ipcUnwrapCaps_preserves_blockedOnReplyHasReplyObject
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasReplyObject st)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    blockedOnReplyHasReplyObject st' := by
  intro tid tcb ep rt hTcb hBlk
  exact hInv tid tcb ep rt
    (ipcUnwrapCaps_tcb_backward msg senderRoot receiverRoot slotBase grantRight st st' summary
      tid.toObjId tcb hObjInv hStep hTcb) hBlk

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `endpointCallWithCaps` **establishes** the third clause — the base
`endpointCall` establishes it, and the optional `ipcUnwrapCaps` cap-transfer frames it. -/
theorem endpointCallWithCaps_establishes_blockedOnReplyHasReplyObject
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : blockedOnReplyHasReplyObject st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCallWithCaps endpointId caller msg endpointRights
             callerCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    blockedOnReplyHasReplyObject st' := by
  simp only [endpointCallWithCaps] at hStep
  cases hCall : endpointCall endpointId caller msg st with
  | error e => simp [hCall] at hStep
  | ok pair =>
    rcases pair with ⟨_, stMid⟩
    have hPMid := endpointCall_establishes_blockedOnReplyHasReplyObject st stMid endpointId caller msg hInv hObjInv hCall
    have hObjInvMid : stMid.objects.invExt := endpointCall_preserves_objects_invExt st stMid endpointId caller msg hObjInv hCall
    simp [hCall] at hStep
    cases hEp : st.getEndpoint? endpointId with
    | none => simp [hEp] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
    | some ep =>
      simp [hEp] at hStep
      cases hHead : ep.receiveQ.head with
      | none => simp [hHead] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
      | some receiverId =>
        simp [hHead] at hStep
        by_cases hEmpty : msg.caps = #[]
        · simp [hEmpty] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
        · simp [hEmpty] at hStep
          cases hLookup : lookupCspaceRoot stMid receiverId with
          | none => simp [hLookup] at hStep
          | some recvRoot =>
            simp [hLookup] at hStep
            exact ipcUnwrapCaps_preserves_blockedOnReplyHasReplyObject msg callerCspaceRoot recvRoot
              receiverSlotBase _ stMid st' summary hObjInvMid hPMid hStep

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `endpointReceiveDualWithCaps` **establishes** the third clause —
base `endpointReceiveDual` establishes it; the optional `ipcUnwrapCaps` frames it. -/
theorem endpointReceiveDualWithCaps_establishes_blockedOnReplyHasReplyObject
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (endpointRights : AccessRightSet)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId) (summary : CapTransferSummary)
    (hInv : blockedOnReplyHasReplyObject st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDualWithCaps endpointId receiver replyId endpointRights
             receiverCspaceRoot receiverSlotBase st = .ok ((senderId, summary), st')) :
    blockedOnReplyHasReplyObject st' := by
  simp only [endpointReceiveDualWithCaps] at hStep
  cases hRecv : endpointReceiveDual endpointId receiver replyId st with
  | error e => simp [hRecv] at hStep
  | ok pair =>
    rcases pair with ⟨sid, stMid⟩
    have hPMid := endpointReceiveDual_establishes_blockedOnReplyHasReplyObject st stMid endpointId receiver sid replyId hInv hObjInv hRecv
    have hObjInvMid := endpointReceiveDual_preserves_objects_invExt st stMid endpointId receiver sid replyId hObjInv hRecv
    simp [hRecv] at hStep
    cases hTcb : stMid.getTcb? receiver with
    | none => simp [hTcb] at hStep; obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hPMid
    | some receiverTcb =>
      simp [hTcb] at hStep
      cases hMsg : receiverTcb.pendingMessage with
      | none => simp [hMsg] at hStep; obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hPMid
      | some msg =>
        simp [hMsg] at hStep
        split at hStep
        · obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hPMid
        · cases hLookup : lookupCspaceRoot stMid sid with
          | none => simp only [hLookup] at hStep; contradiction
          | some senderRoot =>
            simp only [hLookup] at hStep
            cases hUnwrap : ipcUnwrapCaps msg senderRoot receiverCspaceRoot
                receiverSlotBase (endpointRights.mem .grant) stMid with
            | error e => simp [hUnwrap] at hStep
            | ok pair =>
              rcases pair with ⟨s, stFinal⟩
              simp [hUnwrap] at hStep
              obtain ⟨⟨_, _⟩, rfl⟩ := hStep
              exact ipcUnwrapCaps_preserves_blockedOnReplyHasReplyObject msg senderRoot receiverCspaceRoot
                receiverSlotBase _ stMid stFinal s hObjInvMid hPMid hUnwrap

open SeLe4n.Model.SystemState in
/-- IPC de-threading D2: `endpointSendDualWithCaps` **preserves** the third clause — base
`endpointSendDual` preserves it; the optional `ipcUnwrapCaps` frames it. -/
theorem endpointSendDualWithCaps_preserves_blockedOnReplyHasReplyObject
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : blockedOnReplyHasReplyObject st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
             senderCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    blockedOnReplyHasReplyObject st' := by
  simp only [endpointSendDualWithCaps] at hStep
  cases hSend : endpointSendDual endpointId sender msg st with
  | error e => simp [hSend] at hStep
  | ok pair =>
    rcases pair with ⟨_, stMid⟩
    have hPMid := endpointSendDual_preserves_blockedOnReplyHasReplyObject st stMid endpointId sender msg hInv hObjInv hSend
    have hObjInvMid := endpointSendDual_preserves_objects_invExt st stMid endpointId sender msg hObjInv hSend
    simp [hSend] at hStep
    cases hEp : st.getEndpoint? endpointId with
    | none => simp [hEp] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
    | some ep =>
      simp [hEp] at hStep
      cases hHead : ep.receiveQ.head with
      | none => simp [hHead] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
      | some receiverId =>
        simp [hHead] at hStep
        by_cases hEmpty : msg.caps = #[]
        · simp [hEmpty] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
        · simp [hEmpty] at hStep
          cases hLookup : lookupCspaceRoot stMid receiverId with
          | none => simp [hLookup] at hStep
          | some recvRoot =>
            simp [hLookup] at hStep
            exact ipcUnwrapCaps_preserves_blockedOnReplyHasReplyObject msg senderCspaceRoot recvRoot
              receiverSlotBase _ stMid st' summary hObjInvMid hPMid hStep

-- ============================================================================
-- IPC de-threading D3 — `blockedOnReplyHasTarget` frame family
--
-- `blockedOnReplyHasTarget` reads only each TCB's `ipcState` (a `.blockedOnReply` TCB
-- carries a `some` reply target).  Every IPC `.blockedOnReply` store uses `(some receiver)`,
-- so this clause is *established directly by the store* (no atomic reply link needed —
-- simpler than the third clause).  Frames mirror the `blockedOnReplyHasReplyObject` family.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- D3 keystone: a single `storeObject` preserves `blockedOnReplyHasTarget` provided the
stored object does not introduce a `.blockedOnReply` TCB with a `none` target (`hNew`). -/
theorem storeObject_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (oid : SeLe4n.ObjId) (o : KernelObject)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasTarget st)
    (hNew : ∀ (t : TCB) (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        o = .tcb t → t.ipcState = .blockedOnReply ep rt → rt.isSome)
    (hStep : storeObject oid o st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  intro tid tcb ep rt hTcb hBlk
  by_cases h : tid.toObjId = oid
  · have hLook : st'.objects[oid]? = some o := by
      rw [RHTable_getElem?_eq_get?]
      exact storeObject_inserted_object_lookup st oid o hObjInv st' hStep
    rw [h, hLook] at hTcb
    exact hNew tcb ep rt (Option.some.inj hTcb) hBlk
  · rw [storeObject_objects_ne st st' oid tid.toObjId o h hObjInv hStep] at hTcb
    exact hInv tid tcb ep rt hTcb hBlk

/-- D3: object-store-preserving step frames the clause. -/
theorem blockedOnReplyHasTarget_of_objects_eq {st st' : SystemState}
    (hObjs : st'.objects = st.objects) (h : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget st' := by
  intro tid tcb ep rt hTcb hBlk; rw [hObjs] at hTcb; exact h tid tcb ep rt hTcb hBlk

open SeLe4n.Model.SystemState in
/-- D3: a `storeObject` of a **non-TCB** object frames the clause (vacuous `hNew`). -/
theorem storeObject_nonTcb_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hNonTcb : ∀ tcb, obj ≠ .tcb tcb)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st'))
    (hInv : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget st' :=
  storeObject_preserves_blockedOnReplyHasTarget st st' id obj hObjInv hInv
    (fun t _ _ ho _ => absurd ho (hNonTcb t)) hStore

open SeLe4n.Model.SystemState in
/-- D3: `storeTcbIpcStateAndMessage` frames the clause provided the new `ipcState`, when
`.blockedOnReply`, has a `some` target (`hTargetOk`).  Covers both the receiver `.ready`
store (vacuous) and the caller `.blockedOnReply _ (some r)` store (`some r` is `isSome`). -/
theorem storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasTarget st)
    (hTargetOk : ∀ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId), ipc = .blockedOnReply ep rt → rt.isSome)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    blockedOnReplyHasTarget st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      refine storeObject_preserves_blockedOnReplyHasTarget st st'' tid.toObjId _ hObjInv hInv
        (fun t ep rt ho hb => ?_) hSO
      simp only [KernelObject.tcb.injEq] at ho
      subst ho
      exact hTargetOk ep rt (by simpa using hb)

open SeLe4n.Model.SystemState in
/-- Finding F-1: `storeTcbReceiveComplete` frames the clause — the stored TCB is
`.ready`, never `.blockedOnReply`, so no `hTargetOk` hypothesis is needed.  Mirror of
`storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget`. -/
theorem storeTcbReceiveComplete_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasTarget st)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    blockedOnReplyHasTarget st' := by
  unfold storeTcbReceiveComplete at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      refine storeObject_preserves_blockedOnReplyHasTarget st st'' tid.toObjId _ hObjInv hInv
        (fun t ep rt ho hb => ?_) hSO
      simp only [KernelObject.tcb.injEq] at ho
      subst ho
      simp at hb

open SeLe4n.Model.SystemState in
/-- D3: `storeTcbIpcState` analogue. -/
theorem storeTcbIpcState_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasTarget st)
    (hTargetOk : ∀ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId), ipc = .blockedOnReply ep rt → rt.isSome)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    blockedOnReplyHasTarget st' := by
  unfold storeTcbIpcState at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      refine storeObject_preserves_blockedOnReplyHasTarget st st'' tid.toObjId _ hObjInv hInv
        (fun t ep rt ho hb => ?_) hSO
      simp only [KernelObject.tcb.injEq] at ho
      subst ho
      exact hTargetOk ep rt (by simpa using hb)

open SeLe4n.Model.SystemState in
/-- D3: `storeTcbIpcState_fromTcb` analogue (pre-looked-up TCB). -/
theorem storeTcbIpcState_fromTcb_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasTarget st)
    (hTargetOk : ∀ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId), ipc = .blockedOnReply ep rt → rt.isSome)
    (hStep : storeTcbIpcState_fromTcb st tid tcb ipc = .ok st') :
    blockedOnReplyHasTarget st' := by
  unfold storeTcbIpcState_fromTcb at hStep
  cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
  | error e => simp [hSO] at hStep
  | ok p =>
    obtain ⟨_, st''⟩ := p
    simp only [hSO, Except.ok.injEq] at hStep
    subst hStep
    refine storeObject_preserves_blockedOnReplyHasTarget st st'' tid.toObjId _ hObjInv hInv
      (fun t ep rt ho hb => ?_) hSO
    simp only [KernelObject.tcb.injEq] at ho
    subst ho
    exact hTargetOk ep rt (by simpa using hb)

open SeLe4n.Model.SystemState in
/-- D3: `storeTcbQueueLinks` frames the clause (queue-link writes preserve `ipcState`). -/
theorem storeTcbQueueLinks_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasTarget st)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    blockedOnReplyHasTarget st' := by
  unfold storeTcbQueueLinks at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      refine storeObject_preserves_blockedOnReplyHasTarget st st'' tid.toObjId _ hObjInv hInv
        (fun t ep rt ho hb => ?_) hSO
      simp only [KernelObject.tcb.injEq] at ho
      subst ho
      have htcbObj : st.objects[tid.toObjId]? = some (.tcb tcb) :=
        lookupTcb_some_objects st tid tcb hL
      exact hInv tid tcb ep rt htcbObj hb

open SeLe4n.Model.SystemState in
/-- D3: `pair`-shaped endpoint-store frame (mirrors the `'` shape). -/
theorem storeObject_endpoint_preserves_blockedOnReplyHasTarget'
    (st : SystemState) (oid : SeLe4n.ObjId) (ep : Endpoint) (pair : Unit × SystemState)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasTarget st)
    (hStore : storeObject oid (.endpoint ep) st = .ok pair) :
    blockedOnReplyHasTarget pair.2 := by
  obtain ⟨⟨⟩, st'⟩ := pair
  exact storeObject_nonTcb_preserves_blockedOnReplyHasTarget st st' oid (.endpoint ep)
    (fun _ => by simp) hObjInv hStore hInv

open SeLe4n.Model.SystemState in
/-- D3: `endpointQueuePopHead` frames the clause. -/
theorem endpointQueuePopHead_preserves_blockedOnReplyHasTarget
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasTarget st)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    blockedOnReplyHasTarget st' := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hP1 := storeObject_endpoint_preserves_blockedOnReplyHasTarget'
              st endpointId _ pair hObjInv hInv hStore
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact storeTcbQueueLinks_preserves_blockedOnReplyHasTarget
                  pair.2 st3 headTid none none none hInv1 hP1 hFinal
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                  have hP2 := storeTcbQueueLinks_preserves_blockedOnReplyHasTarget
                    pair.2 st2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext hInv1 hP1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact storeTcbQueueLinks_preserves_blockedOnReplyHasTarget
                      st2 st3 headTid none none none hInv2 hP2 hFinal

open SeLe4n.Model.SystemState in
/-- D3: `endpointQueueEnqueue` frames the clause. -/
theorem endpointQueueEnqueue_preserves_blockedOnReplyHasTarget
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hInv : blockedOnReplyHasTarget st)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    blockedOnReplyHasTarget st' := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hP1 := storeObject_endpoint_preserves_blockedOnReplyHasTarget'
                  st endpointId _ pair hObjInv hInv hStore
                intro hStep
                exact storeTcbQueueLinks_preserves_blockedOnReplyHasTarget _ _ tid _ _ _ hInv1 hP1 hStep
            | some tailTid =>
              cases hLookupT : lookupTcb st tailTid
              · simp [hLookupT]
              · rename_i tailTcb
                simp only [hLookupT]
                cases hStore : storeObject endpointId _ st
                · simp
                · rename_i pair
                  simp only []
                  have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  have hP1 := storeObject_endpoint_preserves_blockedOnReplyHasTarget'
                    st endpointId _ pair hObjInv hInv hStore
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid _ _ (some tid)
                  · simp
                  · rename_i st2
                    simp only []
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    have hP2 := storeTcbQueueLinks_preserves_blockedOnReplyHasTarget _ _ tailTid _ _ _ hInv1 hP1 hLink1
                    intro hStep
                    exact storeTcbQueueLinks_preserves_blockedOnReplyHasTarget _ _ tid _ _ _ hInv2 hP2 hStep

open SeLe4n.Model.SystemState in
/-- D3: `linkCallerReply` frames the clause (it never writes any TCB's `ipcState`). -/
theorem linkCallerReply_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  intro tid tcb ep rt hTcb hBlk
  obtain ⟨tcb0, hTcb0, hIpc⟩ := linkCallerReply_tcb_ipcState_backward st st' caller rid tid tcb hObjInv hStep hTcb
  exact hInv tid tcb0 ep rt hTcb0 (hIpc.trans hBlk)

open SeLe4n.Model.SystemState in
/-- D3: `linkServerStashedReply` frames the clause (no `ipcState` write). -/
theorem linkServerStashedReply_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (caller server : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  intro tid tcb ep rt hTcb hBlk
  obtain ⟨tcb0, hTcb0, hIpc⟩ := linkServerStashedReply_tcb_ipcState_backward st st' caller server tid tcb hObjInv hStep hTcb
  exact hInv tid tcb0 ep rt hTcb0 (hIpc.trans hBlk)

open SeLe4n.Model.SystemState in
/-- D3: `cleanupPreReceiveDonation` frames the clause (preserves every `ipcState`). -/
theorem cleanupPreReceiveDonation_preserves_blockedOnReplyHasTarget
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st) :
    blockedOnReplyHasTarget (cleanupPreReceiveDonation st receiver) := by
  intro tid tcb ep rt hTcb hBlk
  obtain ⟨tcb0, hTcb0, hIpc⟩ := cleanupPreReceiveDonation_tcb_ipcState_backward st receiver hObjInv tid tcb hTcb
  exact hInv tid tcb0 ep rt hTcb0 (hIpc.trans hBlk)

open SeLe4n.Model.SystemState in
/-- D3: `endpointCall` **establishes** the clause — every `.blockedOnReply` store uses
`(some receiver)`; the link/queue/scheduler steps frame it. -/
theorem endpointCall_establishes_blockedOnReplyHasTarget
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : blockedOnReplyHasTarget st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          have hP1 := endpointQueuePopHead_preserves_blockedOnReplyHasTarget endpointId true st pair.2.2 pair.1 _ hObjInv hInv hPop
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObjInv1 hMsg
            have hP2 := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
              pair.2.2 st2 pair.1 .ready (some msg) hObjInv1 hP1 (by intro ep rt h; cases h) hMsg
            have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by rwa [ensureRunnable_preserves_objects]
            have hP3 := blockedOnReplyHasTarget_of_objects_eq (ensureRunnable_preserves_objects st2 pair.1) hP2
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc] at hStep
              have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt (ensureRunnable st2 pair.1) st4 caller _ _ hObjInvEns hIpc
              have hP4 := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
                (ensureRunnable st2 pair.1) st4 caller (.blockedOnReply endpointId (some pair.1)) none hObjInvEns hP3 (by rintro ep rt h; cases h; rfl) hIpc
              cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
              | error e => simp [hLink] at hStep
              | ok pL =>
                obtain ⟨_, st5⟩ := pL
                simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                have hP5 := linkServerStashedReply_preserves_blockedOnReplyHasTarget st4 st5 caller pair.1 hObjInv4 hP4 hLink
                exact blockedOnReplyHasTarget_of_objects_eq (removeRunnable_preserves_objects st5 caller) hP5
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
          have hP1 := endpointQueueEnqueue_preserves_blockedOnReplyHasTarget endpointId false caller st st1 hObjInv hInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hP2 := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
              st1 st2 caller (.blockedOnCall endpointId) (some msg) hObjInv1 hP1 (by intro ep rt h; cases h) hMsg
            exact blockedOnReplyHasTarget_of_objects_eq (removeRunnable_preserves_objects st2 caller) hP2

open SeLe4n.Model.SystemState in
/-- D3: `endpointReceiveDual` **establishes** the clause. -/
theorem endpointReceiveDual_establishes_blockedOnReplyHasTarget
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (hInv : blockedOnReplyHasTarget st)
    (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st')) :
    blockedOnReplyHasTarget st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInvPop : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hP1 := endpointQueuePopHead_preserves_blockedOnReplyHasTarget endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hInv hPop
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall _ =>
            simp only [hSenderIpc, ite_true] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hP2 := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
                pair.2.2 st2 pair.1 (.blockedOnReply endpointId (some receiver)) none hObjInvPop hP1 (by rintro ep rt h; cases h; rfl) hMsg
              cases hReplyId : replyId with
              | none => simp [hReplyId] at hStep
              | some rid =>
                simp only [hReplyId] at hStep
                cases hLink : SystemState.linkCallerReply pair.1 rid st2 with
                | error e => simp [hLink] at hStep
                | ok pLink =>
                  obtain ⟨_, stLinked⟩ := pLink
                  simp only [hLink] at hStep
                  have hObjInvLink : stLinked.objects.invExt :=
                    linkCallerReply_preserves_objects_invExt st2 stLinked pair.1 rid hObjInvMsg hLink
                  have hPLink := linkCallerReply_preserves_blockedOnReplyHasTarget st2 stLinked pair.1 rid hObjInvMsg hP2 hLink
                  revert hStep
                  cases hPend : storeTcbIpcStateAndMessage stLinked receiver .ready _ with
                  | ok st4 =>
                    exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸
                      storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
                        stLinked st4 receiver .ready _ hObjInvLink hPLink (by intro ep rt h; cases h) hPend
                  | error _ => simp
          | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
            simp only [hSenderIpc] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hP2 := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
                pair.2.2 st2 pair.1 .ready none hObjInvPop hP1 (by intro ep rt h; cases h) hMsg
              have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by rwa [ensureRunnable_preserves_objects]
              have hP3 := blockedOnReplyHasTarget_of_objects_eq (ensureRunnable_preserves_objects st2 pair.1) hP2
              revert hStep
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready _ with
              | ok st4 =>
                exact fun h => (Prod.mk.inj (Except.ok.inj h)).2 ▸
                  storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
                    (ensureRunnable st2 pair.1) st4 receiver .ready _ hObjInvEns hP3 (by intro ep rt h; cases h) hPend
              | error _ => simp
      | none =>
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hPClean := cleanupPreReceiveDonation_preserves_blockedOnReplyHasTarget st receiver hObjInv hInv
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInvEnq : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hP1 := endpointQueueEnqueue_preserves_blockedOnReplyHasTarget endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hPClean hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc] at hStep
              have hObjInv2 : st2.objects.invExt :=
                storeTcbIpcState_preserves_objects_invExt st1 st2 receiver _ hObjInvEnq hIpc
              have hP2 := storeTcbIpcState_preserves_blockedOnReplyHasTarget st1 st2 receiver _ hObjInvEnq hP1 (by intro ep rt h; cases h) hIpc
              cases hGetR : st2.getTcb? receiver with
              | none =>
                simp only [hGetR, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact blockedOnReplyHasTarget_of_objects_eq (removeRunnable_preserves_objects st2 receiver) hP2
              | some rTcb =>
                simp only [hGetR] at hStep
                cases hStash : storeObject receiver.toObjId (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                | error e => simp [hStash] at hStep
                | ok pStash =>
                  obtain ⟨_, stStashed⟩ := pStash
                  simp only [hStash, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, hEq⟩ := hStep; subst hEq
                  have hRecvObj : st2.objects[receiver.toObjId]? = some (.tcb rTcb) :=
                    (getTcb?_eq_some_iff st2 receiver rTcb).mp hGetR
                  have hPStash : blockedOnReplyHasTarget stStashed := by
                    refine storeObject_preserves_blockedOnReplyHasTarget st2 stStashed receiver.toObjId _
                      hObjInv2 hP2 (fun t ep' rt ho hb => ?_) hStash
                    simp only [KernelObject.tcb.injEq] at ho
                    subst ho
                    exact hP2 receiver rTcb ep' rt hRecvObj (by simpa using hb)
                  exact blockedOnReplyHasTarget_of_objects_eq (removeRunnable_preserves_objects stStashed receiver) hPStash

open SeLe4n.Model.SystemState in
/-- D3: `endpointSendDual` frames the clause (never sets `.blockedOnReply`). -/
theorem endpointSendDual_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : blockedOnReplyHasTarget st) (hObjInv : st.objects.invExt)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          have hP1 := endpointQueuePopHead_preserves_blockedOnReplyHasTarget endpointId true st pair.2.2 pair.1 _ hObjInv hInv hPop
          cases hMsg : storeTcbReceiveComplete pair.2.2 pair.1 (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hP2 := storeTcbReceiveComplete_preserves_blockedOnReplyHasTarget
              pair.2.2 st2 pair.1 (some msg) hObjInv1 hP1 hMsg
            exact blockedOnReplyHasTarget_of_objects_eq (ensureRunnable_preserves_objects st2 pair.1) hP2
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
          have hP1 := endpointQueueEnqueue_preserves_blockedOnReplyHasTarget endpointId false sender st st1 hObjInv hInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hP2 := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
              st1 st2 sender (.blockedOnSend endpointId) (some msg) hObjInv1 hP1 (by intro ep rt h; cases h) hMsg
            exact blockedOnReplyHasTarget_of_objects_eq (removeRunnable_preserves_objects st2 sender) hP2

open SeLe4n.Model.SystemState in
/-- D3: `notificationSignal` frames the clause. -/
theorem notificationSignal_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  simp only [notificationSignal] at hStep
  split at hStep
  · rename_i ntfn hObj
    cases hWaiters : ntfn.waitingThreads.tail? with
    | some headTail =>
      obtain ⟨waiter, rest⟩ := headTail
      simp only [hWaiters] at hStep
      split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_nonTcb_preserves_blockedOnReplyHasTarget
          st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSM =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have hInv2 := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
            st1 st2 waiter .ready _ hObjInv1 hInv1 (by intro ep rt h; cases h) hSM
          exact blockedOnReplyHasTarget_of_objects_eq (ensureRunnable_preserves_objects st2 waiter) hInv2
    | none =>
      simp only [hWaiters] at hStep
      split at hStep
      all_goals
        exact storeObject_nonTcb_preserves_blockedOnReplyHasTarget
          st st' notificationId (.notification _) (fun tcb => by simp) hObjInv hStep hInv
  · contradiction
  · contradiction

open SeLe4n.Model.SystemState in
/-- D3: `notificationWait` frames the clause. -/
theorem notificationWait_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st)
    (hStep : notificationWait notificationId waiter st = .ok (badge, st')) :
    blockedOnReplyHasTarget st' := by
  simp only [notificationWait] at hStep
  split at hStep
  · rename_i ntfn hObj
    split at hStep
    · split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_nonTcb_preserves_blockedOnReplyHasTarget
          st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSI =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          exact storeTcbIpcState_preserves_blockedOnReplyHasTarget
            st1 st2 waiter .ready hObjInv1 hInv1 (by intro ep rt h; cases h) hSI
    · split at hStep
      · contradiction
      · rename_i waiterTcb hLookup
        split at hStep
        · contradiction
        · split at hStep
          · contradiction
          · split at hStep
            next => contradiction
            next st1 hSO =>
              have hInv1 := storeObject_nonTcb_preserves_blockedOnReplyHasTarget
                st st1 notificationId (.notification _) (fun tcb => by simp) hObjInv hSO hInv
              have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
              split at hStep
              next => contradiction
              next st2 hSI =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                exact blockedOnReplyHasTarget_of_objects_eq (removeRunnable_preserves_objects st2 waiter)
                  (storeTcbIpcState_fromTcb_preserves_blockedOnReplyHasTarget
                    st1 st2 waiter waiterTcb (.blockedOnNotification notificationId) hObjInv1 hInv1 (by intro ep rt h; cases h) hSI)
  · contradiction
  · contradiction

open SeLe4n.Model.SystemState in
/-- D3: `endpointReply` frames the clause (unblock to `.ready`). -/
theorem endpointReply_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      cases replyTarget with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp
          | ok st'' =>
            intro hStep
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hP := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
              st st'' target .ready (some msg) hObjInv hInv (by intro ep rt h; cases h) hMsg
            exact blockedOnReplyHasTarget_of_objects_eq (ensureRunnable_preserves_objects st'' target) hP
        · simp at hStep

open SeLe4n.Model.SystemState in
/-- D3: `endpointReplyRecv` frames the clause (unblock then receive-establish). -/
theorem endpointReplyRecv_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId expectedReplier =>
      simp only [hIpc] at hStep
      cases expectedReplier with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok stReplied =>
            simp only []
            have hObjInvR := storeTcbIpcStateAndMessage_preserves_objects_invExt st stReplied replyTarget _ _ hObjInv hMsg
            have hPR := storeTcbIpcStateAndMessage_preserves_blockedOnReplyHasTarget
              st stReplied replyTarget .ready (some msg) hObjInv hInv (by intro ep rt h; cases h) hMsg
            have hObjInvE : (ensureRunnable stReplied replyTarget).objects.invExt := by rwa [ensureRunnable_preserves_objects]
            have hPE := blockedOnReplyHasTarget_of_objects_eq (ensureRunnable_preserves_objects stReplied replyTarget) hPR
            cases hRecv : endpointReceiveDual endpointId receiver replyId (ensureRunnable stReplied replyTarget) with
            | error e => simp
            | ok pair =>
              intro hStep
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              exact endpointReceiveDual_establishes_blockedOnReplyHasTarget
                (ensureRunnable stReplied replyTarget) pair.2 endpointId receiver pair.1 replyId hPE hObjInvE hRecv
        · simp at hStep

open SeLe4n.Model.SystemState in
/-- D3: `ipcUnwrapCaps` frames the clause (it never creates a TCB — `ipcUnwrapCaps_tcb_backward`). -/
theorem ipcUnwrapCaps_preserves_blockedOnReplyHasTarget
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st = .ok (summary, st')) :
    blockedOnReplyHasTarget st' := by
  intro tid tcb ep rt hTcb hBlk
  exact hInv tid tcb ep rt
    (ipcUnwrapCaps_tcb_backward msg senderRoot receiverRoot slotBase grantRight st st' summary
      tid.toObjId tcb hObjInv hStep hTcb) hBlk

open SeLe4n.Model.SystemState in
/-- D3: `endpointCallWithCaps` establishes the clause. -/
theorem endpointCallWithCaps_establishes_blockedOnReplyHasTarget
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : blockedOnReplyHasTarget st) (hObjInv : st.objects.invExt)
    (hStep : endpointCallWithCaps endpointId caller msg endpointRights
             callerCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    blockedOnReplyHasTarget st' := by
  simp only [endpointCallWithCaps] at hStep
  cases hCall : endpointCall endpointId caller msg st with
  | error e => simp [hCall] at hStep
  | ok pair =>
    rcases pair with ⟨_, stMid⟩
    have hPMid := endpointCall_establishes_blockedOnReplyHasTarget st stMid endpointId caller msg hInv hObjInv hCall
    have hObjInvMid : stMid.objects.invExt := endpointCall_preserves_objects_invExt st stMid endpointId caller msg hObjInv hCall
    simp [hCall] at hStep
    cases hEp : st.getEndpoint? endpointId with
    | none => simp [hEp] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
    | some ep =>
      simp [hEp] at hStep
      cases hHead : ep.receiveQ.head with
      | none => simp [hHead] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
      | some receiverId =>
        simp [hHead] at hStep
        by_cases hEmpty : msg.caps = #[]
        · simp [hEmpty] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
        · simp [hEmpty] at hStep
          cases hLookup : lookupCspaceRoot stMid receiverId with
          | none => simp [hLookup] at hStep
          | some recvRoot =>
            simp [hLookup] at hStep
            exact ipcUnwrapCaps_preserves_blockedOnReplyHasTarget msg callerCspaceRoot recvRoot
              receiverSlotBase _ stMid st' summary hObjInvMid hPMid hStep

open SeLe4n.Model.SystemState in
/-- D3: `endpointReceiveDualWithCaps` establishes the clause. -/
theorem endpointReceiveDualWithCaps_establishes_blockedOnReplyHasTarget
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (endpointRights : AccessRightSet)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId) (summary : CapTransferSummary)
    (hInv : blockedOnReplyHasTarget st) (hObjInv : st.objects.invExt)
    (hStep : endpointReceiveDualWithCaps endpointId receiver replyId endpointRights
             receiverCspaceRoot receiverSlotBase st = .ok ((senderId, summary), st')) :
    blockedOnReplyHasTarget st' := by
  simp only [endpointReceiveDualWithCaps] at hStep
  cases hRecv : endpointReceiveDual endpointId receiver replyId st with
  | error e => simp [hRecv] at hStep
  | ok pair =>
    rcases pair with ⟨sid, stMid⟩
    have hPMid := endpointReceiveDual_establishes_blockedOnReplyHasTarget st stMid endpointId receiver sid replyId hInv hObjInv hRecv
    have hObjInvMid := endpointReceiveDual_preserves_objects_invExt st stMid endpointId receiver sid replyId hObjInv hRecv
    simp [hRecv] at hStep
    cases hTcb : stMid.getTcb? receiver with
    | none => simp [hTcb] at hStep; obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hPMid
    | some receiverTcb =>
      simp [hTcb] at hStep
      cases hMsg : receiverTcb.pendingMessage with
      | none => simp [hMsg] at hStep; obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hPMid
      | some msg =>
        simp [hMsg] at hStep
        split at hStep
        · obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hPMid
        · cases hLookup : lookupCspaceRoot stMid sid with
          | none => simp only [hLookup] at hStep; contradiction
          | some senderRoot =>
            simp only [hLookup] at hStep
            cases hUnwrap : ipcUnwrapCaps msg senderRoot receiverCspaceRoot
                receiverSlotBase (endpointRights.mem .grant) stMid with
            | error e => simp [hUnwrap] at hStep
            | ok pair =>
              rcases pair with ⟨s, stFinal⟩
              simp [hUnwrap] at hStep
              obtain ⟨⟨_, _⟩, rfl⟩ := hStep
              exact ipcUnwrapCaps_preserves_blockedOnReplyHasTarget msg senderRoot receiverCspaceRoot
                receiverSlotBase _ stMid stFinal s hObjInvMid hPMid hUnwrap

open SeLe4n.Model.SystemState in
/-- D3: `endpointSendDualWithCaps` frames the clause. -/
theorem endpointSendDualWithCaps_preserves_blockedOnReplyHasTarget
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : blockedOnReplyHasTarget st) (hObjInv : st.objects.invExt)
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
             senderCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    blockedOnReplyHasTarget st' := by
  simp only [endpointSendDualWithCaps] at hStep
  cases hSend : endpointSendDual endpointId sender msg st with
  | error e => simp [hSend] at hStep
  | ok pair =>
    rcases pair with ⟨_, stMid⟩
    have hPMid := endpointSendDual_preserves_blockedOnReplyHasTarget st stMid endpointId sender msg hInv hObjInv hSend
    have hObjInvMid := endpointSendDual_preserves_objects_invExt st stMid endpointId sender msg hObjInv hSend
    simp [hSend] at hStep
    cases hEp : st.getEndpoint? endpointId with
    | none => simp [hEp] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
    | some ep =>
      simp [hEp] at hStep
      cases hHead : ep.receiveQ.head with
      | none => simp [hHead] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
      | some receiverId =>
        simp [hHead] at hStep
        by_cases hEmpty : msg.caps = #[]
        · simp [hEmpty] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
        · simp [hEmpty] at hStep
          cases hLookup : lookupCspaceRoot stMid receiverId with
          | none => simp [hLookup] at hStep
          | some recvRoot =>
            simp [hLookup] at hStep
            exact ipcUnwrapCaps_preserves_blockedOnReplyHasTarget msg senderCspaceRoot recvRoot
              receiverSlotBase _ stMid st' summary hObjInvMid hPMid hStep

open SeLe4n.Model.SystemState in
/-- D3: `consumeReply` frames the clause (a non-TCB reply store, or a no-op). -/
theorem consumeReply_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st)
    (hStep : SystemState.consumeReply rid st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  unfold SystemState.consumeReply at hStep
  cases hGet : st.getReply? rid with
  | none =>
    simp only [hGet, Except.ok.injEq, Prod.mk.injEq] at hStep
    obtain ⟨_, rfl⟩ := hStep; exact hInv
  | some r =>
    simp only [hGet] at hStep
    exact storeObject_nonTcb_preserves_blockedOnReplyHasTarget st st' rid.toObjId (.reply _)
      (fun _ => by simp) hObjInv hStep hInv

open SeLe4n.Model.SystemState in
/-- D3: `consumeCallerReply` frames the clause — it clears `reply.caller` and the caller's
`replyObject` (never `ipcState`).  Unlike the third clause, this is *preservable* here. -/
theorem consumeCallerReply_preserves_blockedOnReplyHasTarget
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : blockedOnReplyHasTarget st)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    blockedOnReplyHasTarget st' := by
  unfold SystemState.consumeCallerReply at hStep
  cases hConsume : SystemState.consumeReply rid st with
  | error e => simp [hConsume] at hStep
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    have hP1 := consumeReply_preserves_blockedOnReplyHasTarget st st1 rid hObjInv hInv hConsume
    have hObjInv1 := consumeReply_preserves_objects_invExt st st1 rid hObjInv hConsume
    simp only [hConsume] at hStep
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨_, rfl⟩ := hStep; exact hP1
    | some tcb =>
      simp only [hT] at hStep
      refine storeObject_preserves_blockedOnReplyHasTarget st1 st' caller.toObjId _ hObjInv1 hP1
        (fun t ep rt ho hb => ?_) hStep
      simp only [KernelObject.tcb.injEq] at ho
      subst ho
      have hCallerObj := (getTcb?_eq_some_iff st1 caller tcb).mp hT
      exact hP1 caller tcb ep rt hCallerObj (by simpa using hb)

-- ============================================================================
-- IPC de-threading D3 — `pendingReceiveReplyWellFormed` frame family.
--
-- `pendingReceiveReplyWellFormed` is the **2-clause coupling** conjunct:
--   C1: every TCB with `pendingReceiveReply = some rid` is `.blockedOnReceive`
--       AND the Reply `rid` is present with `caller = none`;
--   C2: the stash is **injective** (at most one blocked receiver per `rid`).
-- C1 reads *both* the TCB store (`getTcb?`) and the Reply store (`getReply?`);
-- C2 couples two TCBs.  The keystones below split by stored-object kind.  The
-- crucial fact making them tractable without a separate kind-stability
-- invariant: a Reply slot and a TCB slot that *coincide* (raw `ObjId.ofNat`)
-- hold disjoint kinds (`.reply` ≠ `.tcb`), so the two accessor facts contradict
-- — hence a TCB store frames every Reply lookup, and vice versa.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- D3 keystone (TCB store): storing `.tcb newTcb` at `tid₀.toObjId` (which held a TCB,
`hOld`) preserves `pendingReceiveReplyWellFormed`, given the new TCB's stash is
well-formed in the pre-state (`hNewC1`: blocked-on-receive + a present free Reply) and
fresh (`hNewC2`: no other thread already stashes it).  Reply lookups frame because a
Reply slot cannot coincide with the stored TCB slot. -/
theorem storeObject_tcb_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (tid₀ : SeLe4n.ThreadId) (oldTcb newTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hOld : st.getTcb? tid₀ = some oldTcb)
    (hInv : pendingReceiveReplyWellFormed st)
    (hNewC1 : ∀ (rid : SeLe4n.ReplyId), newTcb.pendingReceiveReply = some rid →
        (∃ ep, newTcb.ipcState = .blockedOnReceive ep) ∧
        (∃ r, st.getReply? rid = some r ∧ r.caller = none))
    (hNewC2 : ∀ (rid : SeLe4n.ReplyId), newTcb.pendingReceiveReply = some rid →
        ∀ (tid' : SeLe4n.ThreadId) (tcb' : TCB), tid' ≠ tid₀ →
          st.getTcb? tid' = some tcb' → tcb'.pendingReceiveReply ≠ some rid)
    (hStep : storeObject tid₀.toObjId (.tcb newTcb) st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  have hStoredTcb : st'.getTcb? tid₀ = some newTcb := by
    rw [getTcb?_eq_some_iff]
    exact storeObject_objects_eq st st' tid₀.toObjId (.tcb newTcb) hObjInv hStep
  have hFrameTcb : ∀ (tid : SeLe4n.ThreadId), tid ≠ tid₀ → st'.getTcb? tid = st.getTcb? tid := by
    intro tid hne
    unfold getTcb?
    rw [storeObject_objects_ne st st' tid₀.toObjId tid.toObjId (.tcb newTcb)
        (fun h => hne (ThreadId.toObjId_injective tid tid₀ h)) hObjInv hStep]
  have hFrameReply : ∀ (rid : SeLe4n.ReplyId) (r : Reply), st.getReply? rid = some r →
      st'.getReply? rid = some r := by
    intro rid r hr
    have hrObj : st.objects[rid.toObjId]? = some (.reply r) := (getReply?_eq_some_iff st rid r).mp hr
    have hne : rid.toObjId ≠ tid₀.toObjId := by
      intro heq
      have hTcbObj : st.objects[tid₀.toObjId]? = some (.tcb oldTcb) :=
        (getTcb?_eq_some_iff st tid₀ oldTcb).mp hOld
      rw [← heq] at hTcbObj
      rw [hrObj] at hTcbObj
      simp at hTcbObj
    rw [getReply?_eq_some_iff,
      storeObject_objects_ne st st' tid₀.toObjId rid.toObjId (.tcb newTcb) hne hObjInv hStep]
    exact hrObj
  refine ⟨?_, ?_⟩
  · intro tid tcb rid hTcb hStash
    by_cases h : tid = tid₀
    · subst h
      rw [hStoredTcb] at hTcb
      obtain rfl := Option.some.inj hTcb
      obtain ⟨hBlk, r, hr, hrcaller⟩ := hNewC1 rid hStash
      exact ⟨hBlk, r, hFrameReply rid r hr, hrcaller⟩
    · rw [hFrameTcb tid h] at hTcb
      obtain ⟨hBlk, r, hr, hrcaller⟩ := hInv.1 tid tcb rid hTcb hStash
      exact ⟨hBlk, r, hFrameReply rid r hr, hrcaller⟩
  · intro tid₁ tid₂ tcb₁ tcb₂ rid hTcb₁ hTcb₂ hStash₁ hStash₂
    by_cases h1 : tid₁ = tid₀ <;> by_cases h2 : tid₂ = tid₀
    · rw [h1, h2]
    · subst h1
      rw [hStoredTcb] at hTcb₁; obtain rfl := Option.some.inj hTcb₁
      rw [hFrameTcb tid₂ h2] at hTcb₂
      exact absurd hStash₂ (hNewC2 rid hStash₁ tid₂ tcb₂ h2 hTcb₂)
    · subst h2
      rw [hStoredTcb] at hTcb₂; obtain rfl := Option.some.inj hTcb₂
      rw [hFrameTcb tid₁ h1] at hTcb₁
      exact absurd hStash₁ (hNewC2 rid hStash₂ tid₁ tcb₁ h1 hTcb₁)
    · rw [hFrameTcb tid₁ h1] at hTcb₁
      rw [hFrameTcb tid₂ h2] at hTcb₂
      exact hInv.2 tid₁ tid₂ tcb₁ tcb₂ rid hTcb₁ hTcb₂ hStash₁ hStash₂

open SeLe4n.Model.SystemState in
/-- D3 keystone (Reply store): storing `.reply newR` at `rid₀.toObjId` (which held a Reply,
`hOld`) preserves `pendingReceiveReplyWellFormed`.  TCBs are unchanged (a TCB slot cannot
coincide with the stored Reply slot — `.tcb` ≠ `.reply`), so C2 and C1's blocked-half
frame; C1's "free Reply" half needs the stored Reply to be free **iff** it is the one a
blocked receiver stashes (`hNewFree`). -/
theorem storeObject_reply_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (rid₀ : SeLe4n.ReplyId) (oldR newR : Reply)
    (hObjInv : st.objects.invExt)
    (hOld : st.getReply? rid₀ = some oldR)
    (hInv : pendingReceiveReplyWellFormed st)
    (hNewFree : (∃ (tid : SeLe4n.ThreadId) (tcb : TCB),
        st.getTcb? tid = some tcb ∧ tcb.pendingReceiveReply = some rid₀) → newR.caller = none)
    (hStep : storeObject rid₀.toObjId (.reply newR) st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  have hFrameTcb : ∀ (tid : SeLe4n.ThreadId), st'.getTcb? tid = st.getTcb? tid := by
    intro tid
    by_cases hEq : tid.toObjId = rid₀.toObjId
    · have hst' : st'.objects[tid.toObjId]? = some (.reply newR) := by
        rw [hEq]; exact storeObject_objects_eq st st' rid₀.toObjId (.reply newR) hObjInv hStep
      have hst : st.objects[tid.toObjId]? = some (.reply oldR) := by
        rw [hEq]; exact (getReply?_eq_some_iff st rid₀ oldR).mp hOld
      unfold getTcb?; rw [hst', hst]
    · unfold getTcb?
      rw [storeObject_objects_ne st st' rid₀.toObjId tid.toObjId (.reply newR) hEq hObjInv hStep]
  refine ⟨?_, ?_⟩
  · intro tid tcb rid hTcb hStash
    rw [hFrameTcb tid] at hTcb
    obtain ⟨hBlk, r, hr, hrcaller⟩ := hInv.1 tid tcb rid hTcb hStash
    refine ⟨hBlk, ?_⟩
    by_cases hEq : rid = rid₀
    · subst hEq
      exact ⟨newR, by rw [getReply?_eq_some_iff];
                      exact storeObject_objects_eq st st' rid.toObjId (.reply newR) hObjInv hStep,
             hNewFree ⟨tid, tcb, hTcb, hStash⟩⟩
    · refine ⟨r, ?_, hrcaller⟩
      have hrObj : st.objects[rid.toObjId]? = some (.reply r) := (getReply?_eq_some_iff st rid r).mp hr
      rw [getReply?_eq_some_iff,
        storeObject_objects_ne st st' rid₀.toObjId rid.toObjId (.reply newR)
          (fun h => hEq (ReplyId.toObjId_injective rid rid₀ h)) hObjInv hStep]
      exact hrObj
  · intro tid₁ tid₂ tcb₁ tcb₂ rid hTcb₁ hTcb₂ hStash₁ hStash₂
    rw [hFrameTcb tid₁] at hTcb₁
    rw [hFrameTcb tid₂] at hTcb₂
    exact hInv.2 tid₁ tid₂ tcb₁ tcb₂ rid hTcb₁ hTcb₂ hStash₁ hStash₂

open SeLe4n.Model.SystemState in
/-- D3 keystone (neither TCB nor Reply): storing a non-TCB, non-Reply object at a slot that
did **not** hold a Reply (`hOldNonReply`) frames the clause.  A store may *remove* a TCB
(if `oid` held one), but that only drops a constraint; no TCB is added, and Replies are
untouched. -/
theorem storeObject_nonTcbReply_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (oid : SeLe4n.ObjId) (o : KernelObject)
    (hNonTcb : ∀ t, o ≠ .tcb t) (hNonReply : ∀ r, o ≠ .reply r)
    (hOldNonReply : ∀ r, st.objects[oid]? ≠ some (.reply r))
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hStep : storeObject oid o st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  have frame : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
      st'.getTcb? tid = some tcb → st.getTcb? tid = some tcb := by
    intro tid tcb hTcb
    have hTidNe : tid.toObjId ≠ oid := by
      intro hEq
      have hstore : st'.objects[tid.toObjId]? = some o := by
        rw [hEq]; exact storeObject_objects_eq st st' oid o hObjInv hStep
      rw [getTcb?_eq_some_iff] at hTcb; rw [hstore] at hTcb
      exact (hNonTcb tcb) (Option.some.inj hTcb)
    rw [getTcb?_eq_some_iff] at hTcb ⊢
    rwa [storeObject_objects_ne st st' oid tid.toObjId o hTidNe hObjInv hStep] at hTcb
  refine ⟨?_, ?_⟩
  · intro tid tcb rid hTcb hStash
    have hTcbSt := frame tid tcb hTcb
    obtain ⟨hBlk, r, hr, hrcaller⟩ := hInv.1 tid tcb rid hTcbSt hStash
    refine ⟨hBlk, r, ?_, hrcaller⟩
    have hrObj : st.objects[rid.toObjId]? = some (.reply r) := (getReply?_eq_some_iff st rid r).mp hr
    have hRidNe : rid.toObjId ≠ oid := by
      intro hEq; rw [hEq] at hrObj; exact (hOldNonReply r) hrObj
    rw [getReply?_eq_some_iff, storeObject_objects_ne st st' oid rid.toObjId o hRidNe hObjInv hStep]
    exact hrObj
  · intro tid₁ tid₂ tcb₁ tcb₂ rid hTcb₁ hTcb₂ hStash₁ hStash₂
    exact hInv.2 tid₁ tid₂ tcb₁ tcb₂ rid (frame tid₁ tcb₁ hTcb₁) (frame tid₂ tcb₂ hTcb₂) hStash₁ hStash₂

open SeLe4n.Model.SystemState in
/-- D3: `storeTcbIpcStateAndMessage` (writes `ipcState` + `pendingMessage`; leaves
`pendingReceiveReply` untouched) preserves `pendingReceiveReplyWellFormed`, provided the new
`ipcState` keeps any stashing thread `.blockedOnReceive` (`hStashOk`).  The Reply and the
stash itself frame through the keystone; freshness is the pre-state injectivity. -/
theorem storeTcbIpcStateAndMessage_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hStashOk : ∀ (tcb : TCB) (rid : SeLe4n.ReplyId), st.getTcb? tid = some tcb →
        tcb.pendingReceiveReply = some rid → ∃ ep, ipc = .blockedOnReceive ep)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    pendingReceiveReplyWellFormed st' := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      have hOld : st.getTcb? tid = some tcb :=
        (getTcb?_eq_some_iff st tid tcb).mpr (lookupTcb_some_objects st tid tcb hL)
      refine storeObject_tcb_preserves_pendingReceiveReplyWellFormed st st'' tid tcb
        { tcb with ipcState := ipc, pendingMessage := msg } hObjInv hOld hInv ?_ ?_ hSO
      · intro rid hStash
        have hStashOld : tcb.pendingReceiveReply = some rid := hStash
        obtain ⟨_, hFree⟩ := hInv.1 tid tcb rid hOld hStashOld
        exact ⟨hStashOk tcb rid hOld hStashOld, hFree⟩
      · intro rid hStash tid' tcb' hne hTcb' hStash'
        have hStashOld : tcb.pendingReceiveReply = some rid := hStash
        exact hne (hInv.2 tid' tid tcb' tcb rid hTcb' hOld hStash' hStashOld)

open SeLe4n.Model.SystemState in
/-- Finding F-1: `storeTcbReceiveComplete` (writes `ipcState := .ready`,
`pendingMessage`, **and clears** `pendingReceiveReply := none`) preserves
`pendingReceiveReplyWellFormed` **unconditionally** — the stored TCB carries no
stash (`pendingReceiveReply = none`), so both keystone obligations are vacuous (no
`hStashOk` precondition is required).  This is exactly the C1-repair the non-`Call`
receive-completion wakes need: a thread woken to `.ready` no longer stashes a reply,
restoring clause C1 ("only `.blockedOnReceive` threads stash"). -/
theorem storeTcbReceiveComplete_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hStep : storeTcbReceiveComplete st tid msg = .ok st') :
    pendingReceiveReplyWellFormed st' := by
  unfold storeTcbReceiveComplete at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      have hOld : st.getTcb? tid = some tcb :=
        (getTcb?_eq_some_iff st tid tcb).mpr (lookupTcb_some_objects st tid tcb hL)
      refine storeObject_tcb_preserves_pendingReceiveReplyWellFormed st st'' tid tcb
        { tcb with ipcState := .ready, pendingMessage := msg, pendingReceiveReply := none } hObjInv hOld hInv ?_ ?_ hSO
      · intro rid hStash; simp at hStash
      · intro rid hStash; simp at hStash

open SeLe4n.Model.SystemState in
/-- D3: `storeTcbIpcState` analogue of the above (`ipcState` only). -/
theorem storeTcbIpcState_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hStashOk : ∀ (tcb : TCB) (rid : SeLe4n.ReplyId), st.getTcb? tid = some tcb →
        tcb.pendingReceiveReply = some rid → ∃ ep, ipc = .blockedOnReceive ep)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    pendingReceiveReplyWellFormed st' := by
  unfold storeTcbIpcState at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      have hOld : st.getTcb? tid = some tcb :=
        (getTcb?_eq_some_iff st tid tcb).mpr (lookupTcb_some_objects st tid tcb hL)
      refine storeObject_tcb_preserves_pendingReceiveReplyWellFormed st st'' tid tcb
        { tcb with ipcState := ipc } hObjInv hOld hInv ?_ ?_ hSO
      · intro rid hStash
        have hStashOld : tcb.pendingReceiveReply = some rid := hStash
        obtain ⟨_, hFree⟩ := hInv.1 tid tcb rid hOld hStashOld
        exact ⟨hStashOk tcb rid hOld hStashOld, hFree⟩
      · intro rid hStash tid' tcb' hne hTcb' hStash'
        have hStashOld : tcb.pendingReceiveReply = some rid := hStash
        exact hne (hInv.2 tid' tid tcb' tcb rid hTcb' hOld hStash' hStashOld)

open SeLe4n.Model.SystemState in
/-- D3: `storeTcbQueueLinks` (queue-link writes; `ipcState` and `pendingReceiveReply`
unchanged) preserves `pendingReceiveReplyWellFormed` unconditionally. -/
theorem storeTcbQueueLinks_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (prev : Option SeLe4n.ThreadId) (pprev : Option QueuePPrev) (next : Option SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hStep : storeTcbQueueLinks st tid prev pprev next = .ok st') :
    pendingReceiveReplyWellFormed st' := by
  unfold storeTcbQueueLinks at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb (tcbWithQueueLinks tcb prev pprev next)) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      have hOld : st.getTcb? tid = some tcb :=
        (getTcb?_eq_some_iff st tid tcb).mpr (lookupTcb_some_objects st tid tcb hL)
      refine storeObject_tcb_preserves_pendingReceiveReplyWellFormed st st'' tid tcb
        (tcbWithQueueLinks tcb prev pprev next) hObjInv hOld hInv ?_ ?_ hSO
      · intro rid hStash
        have hStashOld : tcb.pendingReceiveReply = some rid := by simpa using hStash
        obtain ⟨hBlk, hFree⟩ := hInv.1 tid tcb rid hOld hStashOld
        exact ⟨by simpa using hBlk, hFree⟩
      · intro rid hStash tid' tcb' hne hTcb' hStash'
        have hStashOld : tcb.pendingReceiveReply = some rid := by simpa using hStash
        exact hne (hInv.2 tid' tid tcb' tcb rid hTcb' hOld hStash' hStashOld)

open SeLe4n.Model.SystemState in
/-- D3: a TCB store that leaves `ipcState` and `pendingReceiveReply` unchanged preserves the
clause unconditionally (covers e.g. the caller-TCB `replyObject` write in `linkCallerReply`). -/
theorem storeObject_tcb_preserveFields_pendingReceiveReplyWellFormed
    (st st' : SystemState) (tid₀ : SeLe4n.ThreadId) (oldTcb newTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hOld : st.getTcb? tid₀ = some oldTcb)
    (hSameIpc : newTcb.ipcState = oldTcb.ipcState)
    (hSameStash : newTcb.pendingReceiveReply = oldTcb.pendingReceiveReply)
    (hInv : pendingReceiveReplyWellFormed st)
    (hStep : storeObject tid₀.toObjId (.tcb newTcb) st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  refine storeObject_tcb_preserves_pendingReceiveReplyWellFormed st st' tid₀ oldTcb newTcb
    hObjInv hOld hInv ?_ ?_ hStep
  · intro rid hStash
    rw [hSameStash] at hStash
    obtain ⟨hBlk, hFree⟩ := hInv.1 tid₀ oldTcb rid hOld hStash
    rw [hSameIpc]; exact ⟨hBlk, hFree⟩
  · intro rid hStash tid' tcb' hne hTcb' hStash'
    rw [hSameStash] at hStash
    exact hne (hInv.2 tid' tid₀ tcb' oldTcb rid hTcb' hOld hStash' hStash)

open SeLe4n.Model.SystemState in
/-- D3: `consumeReply` (clears `reply.caller` to `none`) preserves the clause — the stored
reply is free, so the Reply keystone's `hNewFree` holds outright. -/
theorem consumeReply_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hStep : SystemState.consumeReply rid st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold SystemState.consumeReply at hStep
  cases hGet : st.getReply? rid with
  | none =>
    simp only [hGet, Except.ok.injEq, Prod.mk.injEq] at hStep
    obtain ⟨_, rfl⟩ := hStep; exact hInv
  | some r =>
    simp only [hGet] at hStep
    exact storeObject_reply_preserves_pendingReceiveReplyWellFormed st st' rid r
      { r with caller := none } hObjInv hGet hInv (fun _ => rfl) hStep

open SeLe4n.Model.SystemState in
/-- D3: `linkReply` (sets `reply.caller := some caller`) preserves the clause provided **no**
blocked receiver stashes `rid` (`hNotStashed`) — otherwise linking would leave a stashed
reply non-free, violating C1. -/
theorem linkReply_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (rid : SeLe4n.ReplyId) (caller : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hNotStashed : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
        st.getTcb? tid = some tcb → tcb.pendingReceiveReply ≠ some rid)
    (hStep : linkReply rid caller st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold linkReply at hStep
  cases hGet : st.getReply? rid with
  | none => rw [hGet] at hStep; simp at hStep
  | some r =>
    rw [hGet] at hStep
    cases hFree : r.caller.isNone with
    | false => simp [hFree] at hStep
    | true =>
      simp only [hFree, if_true] at hStep
      refine storeObject_reply_preserves_pendingReceiveReplyWellFormed st st' rid r
        { r with caller := some caller } hObjInv hGet hInv ?_ hStep
      intro hex
      obtain ⟨tid, tcb, hTcb, hStash⟩ := hex
      exact absurd hStash (hNotStashed tid tcb hTcb)

open SeLe4n.Model.SystemState in
/-- D3: `linkCallerReply` (sets `reply.caller := some caller` via `linkReply`, then the
inverse forward link `caller.replyObject := some rid` on the caller TCB) preserves the clause
provided **no** blocked receiver stashes `rid` (`hNotStashed`).  The `.reply` write is
`linkReply` (delegates to `linkReply_preserves_pendingReceiveReplyWellFormed`); the trailing
caller-TCB store touches only `replyObject`, leaving `ipcState`/`pendingReceiveReply`
unchanged, so it frames the clause via `storeObject_tcb_preserveFields_…`. -/
theorem linkCallerReply_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hNotStashed : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
        st.getTcb? tid = some tcb → tcb.pendingReceiveReply ≠ some rid)
    (hStep : linkCallerReply caller rid st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold linkCallerReply at hStep
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hStep
    have hObjInv1 : st1.objects.invExt :=
      linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    -- C1/C2 preserved through the `.reply` link.
    have hInv1 : pendingReceiveReplyWellFormed st1 :=
      linkReply_preserves_pendingReceiveReplyWellFormed st st1 rid caller hObjInv hInv
        hNotStashed hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      split at hStep
      · -- caller-TCB `replyObject := some rid` write: preserves ipcState + stash.
        exact storeObject_tcb_preserveFields_pendingReceiveReplyWellFormed st1 st'
          caller tcb { tcb with replyObject := some rid } hObjInv1 hT rfl rfl hInv1 hStep
      · simp at hStep

open SeLe4n.Model.SystemState in
/-- D3: **establishing** a stash — storing a TCB whose only stash is `some rid` establishes
the clause, given the TCB is `.blockedOnReceive` (`hNewBlk`), the Reply `rid` is present and
free (`hFree`), and `rid` is not already stashed by any thread (`hFresh`).  This is the
server-first receive path (`pendingReceiveReply := some rid`). -/
theorem storeObject_establishStash_pendingReceiveReplyWellFormed
    (st st' : SystemState) (tid₀ : SeLe4n.ThreadId) (oldTcb newTcb : TCB) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hOld : st.getTcb? tid₀ = some oldTcb)
    (hNewStash : newTcb.pendingReceiveReply = some rid)
    (hNewBlk : ∃ ep, newTcb.ipcState = .blockedOnReceive ep)
    (hFree : ∃ r, st.getReply? rid = some r ∧ r.caller = none)
    (hFresh : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
        st.getTcb? tid = some tcb → tcb.pendingReceiveReply ≠ some rid)
    (hInv : pendingReceiveReplyWellFormed st)
    (hStep : storeObject tid₀.toObjId (.tcb newTcb) st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  refine storeObject_tcb_preserves_pendingReceiveReplyWellFormed st st' tid₀ oldTcb newTcb
    hObjInv hOld hInv ?_ ?_ hStep
  · intro rid' hStash'
    rw [hNewStash] at hStash'
    obtain rfl := Option.some.inj hStash'
    exact ⟨hNewBlk, hFree⟩
  · intro rid' hStash' tid' tcb' _hne hTcb' hStash''
    rw [hNewStash] at hStash'
    obtain rfl := Option.some.inj hStash'
    exact absurd hStash'' (hFresh tid' tcb' hTcb')

open SeLe4n.Model.SystemState in
/-- D3 (stash/ipcState backward): a `storeTcbIpcStateAndMessage st tid ipc msg` write keeps
**every** TCB's `pendingReceiveReply` (it rewrites only `ipcState`/`pendingMessage`), and
leaves every non-target TCB's `ipcState` intact.  Pulls a post-state TCB read back to a
pre-state TCB carrying the same stash. -/
theorem storeTcbIpcStateAndMessage_getTcb?_backward
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st')
    (y : SeLe4n.ThreadId) (tcY : TCB) (hY : st'.getTcb? y = some tcY) :
    ∃ tc0, st.getTcb? y = some tc0 ∧ tc0.pendingReceiveReply = tcY.pendingReceiveReply ∧
      (y ≠ tid → tc0.ipcState = tcY.ipcState) := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hL : lookupTcb st tid with
  | none => simp [hL] at hStep
  | some tcb =>
    simp only [hL] at hStep
    cases hSO : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hSO] at hStep
    | ok p =>
      obtain ⟨_, st''⟩ := p
      simp only [hSO, Except.ok.injEq] at hStep
      subst hStep
      have hOld : st.objects[tid.toObjId]? = some (.tcb tcb) := lookupTcb_some_objects st tid tcb hL
      by_cases hYt : y = tid
      · subst hYt
        have hStored : st''.objects[y.toObjId]? = some (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) :=
          storeObject_objects_eq st st'' y.toObjId _ hObjInv hSO
        rw [getTcb?_eq_some_iff, hStored] at hY
        obtain rfl := KernelObject.tcb.inj (Option.some.inj hY)
        exact ⟨tcb, (getTcb?_eq_some_iff st y tcb).mpr hOld, rfl, fun h => absurd rfl h⟩
      · have hNe : y.toObjId ≠ tid.toObjId := fun h => hYt (ThreadId.toObjId_injective y tid h)
        have hFrame : st''.objects[y.toObjId]? = st.objects[y.toObjId]? :=
          storeObject_objects_ne st st'' tid.toObjId y.toObjId _ hNe hObjInv hSO
        rw [getTcb?_eq_some_iff, hFrame] at hY
        exact ⟨tcY, (getTcb?_eq_some_iff st y tcY).mpr hY, rfl, fun _ => rfl⟩

open SeLe4n.Model.SystemState in
/-- D3 (crux frame): `linkServerStashedReply caller server` preserves
`pendingReceiveReplyWellFormed` from the **post-deliver** state, where the `server`
is `.ready` but still carries the stash `rid` it set on its earlier server-first
`Recv` — a state that *violates* C1 for the server alone.  The composite (i) links
that stash `rid` to the freshly-blocked `caller` (`linkCallerReply`) and (ii) clears
the server's stash, with the **net effect** that `rid` is linked-but-unstashed and
the server is stash-free — so the C1 violation is repaired.  Rather than the full
pre-state PRR (false here), the precondition is **PRR-minus-the-server**:

- `hC1Other`: C1 for every thread *other than* `server` (every non-server thread that
  stashes a reply is `.blockedOnReceive` and that reply is present + free);
- `hC2`: C2 (stash injectivity) holds globally;

both of which hold at the post-deliver state because the deliver/block stores only
move `ipcState`/`pendingMessage` (never a stash field) and the caller — known not to
be `.blockedOnReceive` — stashes nothing.  The crucial fact discharging C1 at the
post-state: by `hC2`, the `server` is the **unique** staser of `rid`, so once its
stash is cleared *no* surviving thread stashes `rid`, and the link cannot strand any
blocked receiver. -/
theorem linkServerStashedReply_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (caller server : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt)
    (hC1Other : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB) (rid' : SeLe4n.ReplyId),
        tid ≠ server → st.getTcb? tid = some tcb → tcb.pendingReceiveReply = some rid' →
        (∃ ep, tcb.ipcState = .blockedOnReceive ep) ∧
        (∃ r, st.getReply? rid' = some r ∧ r.caller = none))
    (hC2 : ∀ (tid₁ tid₂ : SeLe4n.ThreadId) (tcb₁ tcb₂ : TCB) (rid' : SeLe4n.ReplyId),
        st.getTcb? tid₁ = some tcb₁ → st.getTcb? tid₂ = some tcb₂ →
        tcb₁.pendingReceiveReply = some rid' → tcb₂.pendingReceiveReply = some rid' →
        tid₁ = tid₂)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold SystemState.linkServerStashedReply at hStep
  -- Extract the server's stashed reply `rid` (the def's read).
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    -- The server stashes `rid` at `st`.
    obtain ⟨sTcb0, hServer0, hServerStash0⟩ : ∃ sTcb0, st.getTcb? server = some sTcb0 ∧
        sTcb0.pendingReceiveReply = some rid := by
      cases hG : st.getTcb? server with
      | none => rw [hG] at hStash; simp at hStash
      | some sTcb0 => rw [hG] at hStash; exact ⟨sTcb0, rfl, by simpa using hStash⟩
    cases hLink : SystemState.linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hObjInv1 : st1.objects.invExt :=
        linkCallerReply_preserves_objects_invExt st st1 caller rid hObjInv hLink
      -- `rid` was present and free at `st` (`linkCallerReply` succeeded).
      obtain ⟨⟨r0, hGetR0, hFreeR0⟩, _⟩ :=
        linkCallerReply_pre st st1 caller rid hObjInv hLink
      -- After the link, `rid` carries `caller := some caller`.
      have hR1 : st1.getReply? rid = some { r0 with caller := some caller } :=
        linkCallerReply_getReply?_caller_some st caller rid r0 hObjInv hGetR0 hFreeR0 st1 hLink
      have hReplyObj1 : st1.objects[rid.toObjId]? = some (.reply { r0 with caller := some caller }) :=
        (getReply?_eq_some_iff st1 rid _).mp hR1
      -- `linkCallerReply` frames every slot other than `rid` and `caller`.
      have hFrame1 : ∀ x, x ≠ rid.toObjId → x ≠ caller.toObjId →
          st1.objects[x]? = st.objects[x]? :=
        fun x hxR hxC => linkCallerReply_objects_frame st st1 caller rid hObjInv hLink x hxR hxC
      -- `rid`'s slot is a Reply, so it is distinct from any thread's TCB slot.
      have hRidNeTcb : ∀ (t : SeLe4n.ThreadId) (tc : TCB), st1.getTcb? t = some tc →
          t.toObjId ≠ rid.toObjId := by
        intro t tc hT heq
        rw [getTcb?_eq_some_iff, heq, hReplyObj1] at hT; cases hT
      -- `linkCallerReply` writes only `rid`'s reply and the caller's `replyObject`, so
      -- **every** TCB keeps its `ipcState` and `pendingReceiveReply` across the link.
      -- The caller's `st1` TCB is exactly `{ tcbC0 with replyObject := some rid }`.
      have hCallerSt1 : ∃ tcbC0, st.getTcb? caller = some tcbC0 ∧
          st1.getTcb? caller = some { tcbC0 with replyObject := some rid } := by
        -- Unfold the link: `linkReply` writes only `rid.toObjId`, leaving the caller TCB
        -- untouched; then the trailing store writes `{ that-TCB with replyObject := some rid }`.
        unfold SystemState.linkCallerReply at hLink
        cases hLR : linkReply rid caller st with
        | error e => simp [hLR] at hLink
        | ok pLR =>
          obtain ⟨_, stLR⟩ := pLR
          simp only [hLR] at hLink
          have hObjInvLR : stLR.objects.invExt :=
            linkReply_preserves_objects_invExt st stLR rid caller hObjInv hLR
          -- `linkReply` is a single `storeObject` at `rid.toObjId` (its success branch).
          have hLRstore : storeObject rid.toObjId (.reply { r0 with caller := some caller }) st
              = .ok ((), stLR) := by
            unfold linkReply at hLR
            simp only [hGetR0] at hLR
            rw [if_pos (by simp [hFreeR0])] at hLR
            exact hLR
          cases hT : stLR.getTcb? caller with
          | none => simp [hT] at hLink
          | some tcbLR =>
            simp only [hT] at hLink
            split at hLink
            · -- the caller's TCB slot is distinct from `rid.toObjId`, so it frames past
              -- `linkReply`: `st.getTcb? caller = some tcbLR`.
              have hRLR : stLR.getReply? rid = some { r0 with caller := some caller } := by
                rw [getReply?_eq_some_iff]
                exact storeObject_objects_eq st stLR rid.toObjId _ hObjInv hLRstore
              have hCR : caller.toObjId ≠ rid.toObjId :=
                getTcb?_getReply?_slot_ne stLR caller rid tcbLR _ hT hRLR
              have hCallerStLR : stLR.getTcb? caller = st.getTcb? caller := by
                unfold getTcb?
                rw [storeObject_objects_ne st stLR rid.toObjId caller.toObjId _ hCR hObjInv hLRstore]
              refine ⟨tcbLR, by rw [← hCallerStLR]; exact hT, ?_⟩
              rw [getTcb?_eq_some_iff, RHTable_getElem?_eq_get?]
              exact storeObject_inserted_object_lookup stLR caller.toObjId
                (.tcb { tcbLR with replyObject := some rid }) hObjInvLR st1 hLink
            · simp at hLink
      obtain ⟨tcbC0, hGetC0, hGetC1⟩ := hCallerSt1
      -- A `linkCallerReply` TCB read at `st1` pulls back to `st` with the same
      -- `ipcState` and the same `pendingReceiveReply`.
      have hTcbBack : ∀ (tid : SeLe4n.ThreadId) (tc1 : TCB), st1.getTcb? tid = some tc1 →
          ∃ tc0, st.getTcb? tid = some tc0 ∧ tc0.ipcState = tc1.ipcState ∧
            tc0.pendingReceiveReply = tc1.pendingReceiveReply := by
        intro tid tc1 hT1
        by_cases hC : tid = caller
        · subst hC
          rw [hGetC1] at hT1; obtain rfl := Option.some.inj hT1
          exact ⟨tcbC0, hGetC0, rfl, rfl⟩
        · refine ⟨tc1, ?_, rfl, rfl⟩
          have hNe : tid.toObjId ≠ caller.toObjId :=
            fun h => hC (ThreadId.toObjId_injective tid caller h)
          have hFrame := hFrame1 tid.toObjId (hRidNeTcb tid tc1 hT1) hNe
          rw [getTcb?_eq_some_iff] at hT1 ⊢
          rwa [hFrame] at hT1
      -- And forward: a TCB at `st` other than the caller is unchanged at `st1`; the
      -- caller maps to `{ tcbC0 with replyObject := some rid }`.
      have hTcbFwdStash : ∀ (tid : SeLe4n.ThreadId) (tc0 : TCB), st.getTcb? tid = some tc0 →
          ∃ tc1, st1.getTcb? tid = some tc1 ∧ tc1.pendingReceiveReply = tc0.pendingReceiveReply := by
        intro tid tc0 hT0
        by_cases hC : tid = caller
        · subst hC; rw [hGetC0] at hT0; obtain rfl := Option.some.inj hT0
          exact ⟨{ tcbC0 with replyObject := some rid }, hGetC1, rfl⟩
        · have hNe : tid.toObjId ≠ caller.toObjId :=
            fun h => hC (ThreadId.toObjId_injective tid caller h)
          have hRidNe0 : tid.toObjId ≠ rid.toObjId := by
            intro heq
            have hRidObj : st.objects[rid.toObjId]? = some (.reply r0) :=
              (getReply?_eq_some_iff st rid r0).mp hGetR0
            rw [← heq, (getTcb?_eq_some_iff st tid tc0).mp hT0] at hRidObj; cases hRidObj
          refine ⟨tc0, ?_, rfl⟩
          rw [getTcb?_eq_some_iff] at hT0 ⊢
          rwa [hFrame1 tid.toObjId hRidNe0 hNe]
      -- ── The final server-stash-clear store ──────────────────────────────────
      -- `rid` is *not* stashed by any thread at `st1`: the server is its unique staser
      -- at `st` (by `hC2`), and stashes are unchanged across the link.
      have hNoStashRidSt1 : ∀ (tid : SeLe4n.ThreadId) (tc : TCB),
          st1.getTcb? tid = some tc → tc.pendingReceiveReply = some rid → tid = server := by
        intro tid tc hT1 hStashRid
        obtain ⟨tc0, hT0, _, hStash0⟩ := hTcbBack tid tc hT1
        exact hC2 tid server tc0 sTcb0 rid hT0 hServer0 (hStash0.trans hStashRid) hServerStash0
      cases hT : st1.getTcb? server with
      | none =>
        -- no server TCB at `st1` → the store is a no-op; `st' = st1`.  But the server
        -- exists at `st` (`hServer0`) and is preserved by the link, contradiction.
        obtain ⟨tc1, hT1', _⟩ := hTcbFwdStash server sTcb0 hServer0
        rw [hT] at hT1'; cases hT1'
      | some sTcb1 =>
        simp only [hT] at hStep
        -- `st'` is `st1` with the server's stash cleared.
        have hStore : storeObject server.toObjId (.tcb { sTcb1 with pendingReceiveReply := none }) st1
            = .ok ((), st') := hStep
        -- The cleared server-TCB has no stash → its C1/C2 obligations are vacuous; and the
        -- *other* TCBs' C1 follows from `hC1Other` (via `hTcbBack`), with `rid`'s freeness
        -- repaired because the only surviving stash of any reply is at a *different* reply.
        have hServer1Obj : st1.getTcb? server = some sTcb1 := hT
        refine ⟨?_, ?_⟩
        · -- C1 at `st'`.
          intro tid tcb ridX hTcbX hStashX
          -- back the `st'` TCB through the server-clear store to `st1`.
          by_cases hTS : tid = server
          · -- the stored server TCB has `pendingReceiveReply = none`.
            have hStoredServer : st'.getTcb? server = some { sTcb1 with pendingReceiveReply := none } := by
              rw [getTcb?_eq_some_iff]
              exact storeObject_objects_eq st1 st' server.toObjId _ hObjInv1 hStore
            rw [hTS, hStoredServer] at hTcbX; obtain rfl := Option.some.inj hTcbX
            simp at hStashX
          · -- `tid ≠ server`: the server-clear store frames `tid`'s slot.
            have hNeObj : tid.toObjId ≠ server.toObjId :=
              fun h => hTS (ThreadId.toObjId_injective tid server h)
            have hTcb1 : st1.getTcb? tid = some tcb := by
              rw [getTcb?_eq_some_iff] at hTcbX ⊢
              rwa [storeObject_objects_ne st1 st' server.toObjId tid.toObjId _ hNeObj hObjInv1 hStore] at hTcbX
            -- pull back to `st` to apply `hC1Other`.
            obtain ⟨tc0, hT0, hIpc0, hStash0⟩ := hTcbBack tid tcb hTcb1
            have hStashX0 : tc0.pendingReceiveReply = some ridX := hStash0.trans hStashX
            obtain ⟨hBlk0, ⟨rr, hGetRR, hRRfree⟩⟩ := hC1Other tid tc0 ridX hTS hT0 hStashX0
            refine ⟨hIpc0 ▸ hBlk0, ?_⟩
            -- `ridX ≠ rid` (else `tid = server` by uniqueness, contra `hTS`).
            have hRidXne : ridX ≠ rid := by
              intro hEqR; subst hEqR
              exact hTS (hNoStashRidSt1 tid tcb hTcb1 hStashX)
            -- `ridX`'s reply is unchanged from `st` → `st1` → `st'` (it is neither `rid`
            -- nor a TCB slot, so both stores frame it).
            have hRidXneObjSt : ridX.toObjId ≠ rid.toObjId :=
              fun h => hRidXne (ReplyId.toObjId_injective ridX rid h)
            have hRidXneCaller : ridX.toObjId ≠ caller.toObjId := by
              intro hEq
              -- the caller is a TCB at `st`; a Reply slot ≠ a TCB slot.
              have hCallerObj : st.objects[caller.toObjId]? = some (.tcb tcbC0) :=
                (getTcb?_eq_some_iff st caller tcbC0).mp hGetC0
              have hRRobj : st.objects[ridX.toObjId]? = some (.reply rr) :=
                (getReply?_eq_some_iff st ridX rr).mp hGetRR
              rw [hEq, hCallerObj] at hRRobj; cases hRRobj
            have hRidXneServer : ridX.toObjId ≠ server.toObjId := by
              intro hEq
              have hServerObj : st.objects[server.toObjId]? = some (.tcb sTcb0) :=
                (getTcb?_eq_some_iff st server sTcb0).mp hServer0
              have hRRobj : st.objects[ridX.toObjId]? = some (.reply rr) :=
                (getReply?_eq_some_iff st ridX rr).mp hGetRR
              rw [hEq, hServerObj] at hRRobj; cases hRRobj
            refine ⟨rr, ?_, hRRfree⟩
            -- frame `ridX` across the link (≠ rid, ≠ caller) and the server-clear (≠ server).
            have hRR1 : st1.getReply? ridX = some rr := by
              have hRRobj : st.objects[ridX.toObjId]? = some (.reply rr) :=
                (getReply?_eq_some_iff st ridX rr).mp hGetRR
              rw [getReply?_eq_some_iff, hFrame1 ridX.toObjId hRidXneObjSt hRidXneCaller]; exact hRRobj
            rw [getReply?_eq_some_iff,
              storeObject_objects_ne st1 st' server.toObjId ridX.toObjId _ hRidXneServer hObjInv1 hStore]
            exact (getReply?_eq_some_iff st1 ridX rr).mp hRR1
        · -- C2 at `st'`: two stashers must both be `≠ server` (the cleared server stashes
          -- nothing), and a non-server stash is unchanged from `st1`, where uniqueness holds.
          intro tid₁ tid₂ tcb₁ tcb₂ ridX hT₁ hT₂ hStash₁ hStash₂
          have hStored : st'.getTcb? server = some { sTcb1 with pendingReceiveReply := none } := by
            rw [getTcb?_eq_some_iff]
            exact storeObject_objects_eq st1 st' server.toObjId _ hObjInv1 hStore
          have backToSt1 : ∀ (t : SeLe4n.ThreadId) (tc : TCB), st'.getTcb? t = some tc →
              tc.pendingReceiveReply = some ridX → st1.getTcb? t = some tc ∧ t ≠ server := by
            intro t tc hT' hS'
            by_cases hTS : t = server
            · subst hTS; rw [hStored] at hT'; obtain rfl := Option.some.inj hT'
              simp at hS'
            · have hNeObj : t.toObjId ≠ server.toObjId :=
                fun h => hTS (ThreadId.toObjId_injective t server h)
              refine ⟨?_, hTS⟩
              rw [getTcb?_eq_some_iff] at hT' ⊢
              rwa [storeObject_objects_ne st1 st' server.toObjId t.toObjId _ hNeObj hObjInv1 hStore] at hT'
          obtain ⟨hT1₁, _⟩ := backToSt1 tid₁ tcb₁ hT₁ hStash₁
          obtain ⟨hT1₂, _⟩ := backToSt1 tid₂ tcb₂ hT₂ hStash₂
          -- pull both back to `st` and apply `hC2`.
          obtain ⟨tc0₁, hT0₁, _, hStash0₁⟩ := hTcbBack tid₁ tcb₁ hT1₁
          obtain ⟨tc0₂, hT0₂, _, hStash0₂⟩ := hTcbBack tid₂ tcb₂ hT1₂
          exact hC2 tid₁ tid₂ tc0₁ tc0₂ ridX hT0₁ hT0₂ (hStash0₁.trans hStash₁) (hStash0₂.trans hStash₂)


-- ============================================================================
-- IPC de-threading D3 — per-transition `pendingReceiveReplyWellFormed` lemmas.
--
-- These mirror the `*_{preserves,establishes}_blockedOnReplyHasTarget` proofs
-- above, but discharge the `pendingReceiveReplyWellFormed` frame-family
-- obligations (`hStashOk` / `hNotStashed` / freshness) rather than the
-- `blockedOnReply`-target ones.  The key discharge pattern: a TCB store that
-- moves a thread to a *non-`.blockedOnReceive`* `ipcState` (`.ready`,
-- `.blockedOnSend`, …) frames C1 only if that thread did **not** stash a reply
-- in the pre-state; PRR's own C1 (stash ⇒ `.blockedOnReceive`) discharges this
-- whenever the proof's case-split already fixes the thread's pre-state to a
-- non-`.blockedOnReceive` constructor.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- D3: a TCB store moving `tid` out of `.blockedOnReceive` (the new `ipcState`
is *not* `.blockedOnReceive`) frames `pendingReceiveReplyWellFormed`, **provided**
`tid`'s *pre-state* `ipcState` is not `.blockedOnReceive` — then C1 of `hInv`
forces `tid` not to stash, so the `storeTcbIpcStateAndMessage` keystone's
`hStashOk` obligation is vacuous.  This is the canonical "wake / re-block a
non-receiving thread" frame. -/
theorem storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (ipc : ThreadIpcState) (msg : Option IpcMessage)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hPreNotRecv : ∀ (tcb : TCB), st.getTcb? tid = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    pendingReceiveReplyWellFormed st' := by
  refine storeTcbIpcStateAndMessage_preserves_pendingReceiveReplyWellFormed
    st st' tid ipc msg hObjInv hInv ?_ hStep
  intro tcb rid hTcb hStash
  -- `tid` stashes `rid` ⇒ (C1) `tid` is `.blockedOnReceive`, contradicting `hPreNotRecv`.
  obtain ⟨⟨ep, hBlk⟩, _⟩ := hInv.1 tid tcb rid hTcb hStash
  exact absurd hBlk (hPreNotRecv tcb hTcb ep)

open SeLe4n.Model.SystemState in
/-- D3: `storeTcbIpcState` analogue of
`storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed`. -/
theorem storeTcbIpcState_notReceiving_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hPreNotRecv : ∀ (tcb : TCB), st.getTcb? tid = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    pendingReceiveReplyWellFormed st' := by
  refine storeTcbIpcState_preserves_pendingReceiveReplyWellFormed
    st st' tid ipc hObjInv hInv ?_ hStep
  intro tcb rid hTcb hStash
  obtain ⟨⟨ep, hBlk⟩, _⟩ := hInv.1 tid tcb rid hTcb hStash
  exact absurd hBlk (hPreNotRecv tcb hTcb ep)

open SeLe4n.Model.SystemState in
/-- D3: storing `.endpoint ep` at a slot that **previously held an endpoint**
(`hOldEp`) frames `pendingReceiveReplyWellFormed` (an endpoint is neither a TCB
nor a Reply, and the old slot was not a Reply either). -/
theorem storeObject_endpoint_preserves_pendingReceiveReplyWellFormed'
    (st : SystemState) (oid : SeLe4n.ObjId) (ep oldEp : Endpoint) (pair : Unit × SystemState)
    (hObjInv : st.objects.invExt)
    (hOldEp : st.objects[oid]? = some (.endpoint oldEp))
    (hInv : pendingReceiveReplyWellFormed st)
    (hStore : storeObject oid (.endpoint ep) st = .ok pair) :
    pendingReceiveReplyWellFormed pair.2 := by
  obtain ⟨⟨⟩, st'⟩ := pair
  exact storeObject_nonTcbReply_preserves_pendingReceiveReplyWellFormed st st' oid (.endpoint ep)
    (fun t => by simp) (fun r => by simp)
    (fun r h => by rw [hOldEp] at h; simp at h)
    hObjInv hInv hStore

open SeLe4n.Model.SystemState in
/-- D3: `endpointQueuePopHead` frames `pendingReceiveReplyWellFormed` (an endpoint
store, then queue-link writes — neither touches `pendingReceiveReply`/`ipcState`
or a Reply's `caller`). -/
theorem endpointQueuePopHead_preserves_pendingReceiveReplyWellFormed
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (rTid : SeLe4n.ThreadId) (rTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (rTid, rTcb, st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold endpointQueuePopHead at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : (if isReceiveQ then ep.receiveQ else ep.sendQ).head with
      | none => simp [hHead] at hStep
      | some headTid =>
        simp only [hHead] at hStep
        cases hLookup : lookupTcb st headTid with
        | none => simp [hLookup] at hStep
        | some tcb =>
          simp only [hLookup] at hStep
          revert hStep
          cases hStore : storeObject endpointId _ st with
          | error e => simp
          | ok pair =>
            have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
            have hP1 := storeObject_endpoint_preserves_pendingReceiveReplyWellFormed'
              st endpointId _ ep pair hObjInv hObj hInv hStore
            cases hNext : tcb.queueNext with
            | none =>
              simp only []
              cases hFinal : storeTcbQueueLinks pair.2 headTid none none none with
              | error e => simp
              | ok st3 =>
                simp only [Except.ok.injEq, Prod.mk.injEq]
                intro ⟨_, _, rfl⟩
                exact storeTcbQueueLinks_preserves_pendingReceiveReplyWellFormed
                  pair.2 st3 headTid none none none hInv1 hP1 hFinal
            | some nextTid =>
              simp only []
              cases hLookupNext : lookupTcb pair.2 nextTid with
              | none => simp
              | some nextTcb =>
                simp only []
                cases hLink : storeTcbQueueLinks pair.2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext with
                | error e => simp
                | ok st2 =>
                  simp only []
                  have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ nextTid _ _ _ hInv1 hLink
                  have hP2 := storeTcbQueueLinks_preserves_pendingReceiveReplyWellFormed
                    pair.2 st2 nextTid none (some QueuePPrev.endpointHead) nextTcb.queueNext hInv1 hP1 hLink
                  cases hFinal : storeTcbQueueLinks st2 headTid none none none with
                  | error e => simp
                  | ok st3 =>
                    simp only [Except.ok.injEq, Prod.mk.injEq]
                    intro ⟨_, _, rfl⟩
                    exact storeTcbQueueLinks_preserves_pendingReceiveReplyWellFormed
                      st2 st3 headTid none none none hInv2 hP2 hFinal

open SeLe4n.Model.SystemState in
/-- D3: `endpointQueueEnqueue` frames `pendingReceiveReplyWellFormed`. -/
theorem endpointQueueEnqueue_preserves_pendingReceiveReplyWellFormed
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (tid : SeLe4n.ThreadId)
    (st st' : SystemState)
    (hObjInv : st.objects.invExt)
    (hInv : pendingReceiveReplyWellFormed st)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ tid st = .ok st') :
    pendingReceiveReplyWellFormed st' := by
  unfold endpointQueueEnqueue at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hLookup : lookupTcb st tid with
      | none => simp [hLookup] at hStep
      | some tcb =>
        simp only [hLookup] at hStep
        split at hStep
        · simp at hStep
        · split at hStep
          · simp at hStep
          · revert hStep
            cases (if isReceiveQ then ep.receiveQ else ep.sendQ).tail with
            | none =>
              cases hStore : storeObject endpointId _ st with
              | error e => simp
              | ok pair =>
                simp only []
                have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                have hP1 := storeObject_endpoint_preserves_pendingReceiveReplyWellFormed'
                  st endpointId _ ep pair hObjInv hObj hInv hStore
                intro hStep
                exact storeTcbQueueLinks_preserves_pendingReceiveReplyWellFormed _ _ tid _ _ _ hInv1 hP1 hStep
            | some tailTid =>
              cases hLookupT : lookupTcb st tailTid
              · simp [hLookupT]
              · rename_i tailTcb
                simp only [hLookupT]
                cases hStore : storeObject endpointId _ st
                · simp
                · rename_i pair
                  simp only []
                  have hInv1 := storeObject_preserves_objects_invExt' st endpointId _ pair hObjInv hStore
                  have hP1 := storeObject_endpoint_preserves_pendingReceiveReplyWellFormed'
                    st endpointId _ ep pair hObjInv hObj hInv hStore
                  cases hLink1 : storeTcbQueueLinks pair.2 tailTid _ _ (some tid)
                  · simp
                  · rename_i st2
                    simp only []
                    have hInv2 := storeTcbQueueLinks_preserves_objects_invExt _ _ tailTid _ _ _ hInv1 hLink1
                    have hP2 := storeTcbQueueLinks_preserves_pendingReceiveReplyWellFormed _ _ tailTid _ _ _ hInv1 hP1 hLink1
                    intro hStep
                    exact storeTcbQueueLinks_preserves_pendingReceiveReplyWellFormed _ _ tid _ _ _ hInv2 hP2 hStep

open SeLe4n.Model.SystemState in
/-- D3: `endpointReply` frames `pendingReceiveReplyWellFormed`.  It unblocks the
`.blockedOnReply` target to `.ready`; that target — being `.blockedOnReply` in
the pre-state — does not stash, so the wake frames C1.  `ensureRunnable` is an
object-store no-op. -/
theorem endpointReply_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      cases replyTarget with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp
          | ok st'' =>
            intro hStep
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            have hP := storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
              st st'' target .ready (some msg) hObjInv hInv ?_ hMsg
            · exact pendingReceiveReplyWellFormed_of_objects_eq
                (ensureRunnable_preserves_objects st'' target) hP
            · intro tcb' hTcb' ep h
              have hLookEq : st.getTcb? target = some tcb :=
                (getTcb?_eq_some_iff st target tcb).mpr (lookupTcb_some_objects st target tcb hLookup)
              rw [hLookEq] at hTcb'
              obtain rfl := Option.some.inj hTcb'
              rw [hIpc] at h; cases h
        · simp at hStep

-- ============================================================================
-- IPC de-threading D3 — `endpointReceiveDual` establish-stash freshness transport.
--
-- The receive no-sender branch establishes a fresh server-first stash
-- (`pendingReceiveReply := some rid`) via `storeObject_establishStash_…`, whose
-- preconditions name `rid` as *present-free-and-unstashed*.  The Call rendezvous
-- branch links the same `rid` via `linkCallerReply_preserves_…`, whose
-- `hNotStashed` is the *unstashed* half.  Both preconditions are facts about the
-- transition's *pre-state* `st` (discharged upstream by the receive syscall's
-- reply-cap validation) that must be carried forward to the store site through
-- the intervening steps (cleanup → enqueue → storeTcbIpcState; or popHead →
-- storeTcbIpcStateAndMessage).  Those steps write only TCB queue-links / ipcState
-- / schedContext and the endpoint object — never a `.reply`, never any thread's
-- `pendingReceiveReply` — so each frames the bundled freshness fact below.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- D3 freshness bundle: a Reply id `rid` is *present, free, and unstashed* in `st`.
This is exactly the conjunction of `storeObject_establishStash_…`'s `hFree`/`hFresh`
hypotheses (and `linkCallerReply_preserves_…`'s `hNotStashed`). -/
def replyIdEstablishFresh (st : SystemState) (rid : SeLe4n.ReplyId) : Prop :=
  (∃ r, st.getReply? rid = some r ∧ r.caller = none) ∧
  (∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
    st.getTcb? tid = some tcb → tcb.pendingReceiveReply ≠ some rid)

open SeLe4n.Model.SystemState in
/-- D3: a single `storeObject` of a `.tcb` whose `pendingReceiveReply` equals the
old TCB's stash (`hStashEq`) frames `replyIdEstablishFresh` — the reply slot
`rid.toObjId` is untouched (a TCB store cannot write a reply, and the old slot
held a TCB), and every post-state TCB's stash agrees with a pre-state TCB's. -/
theorem storeObject_tcb_preserveStash_replyIdEstablishFresh
    (st st' : SystemState) (tid₀ : SeLe4n.ThreadId) (oldTcb newTcb : TCB)
    (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hOld : st.objects[tid₀.toObjId]? = some (.tcb oldTcb))
    (hStashEq : newTcb.pendingReceiveReply = oldTcb.pendingReceiveReply)
    (hFresh : replyIdEstablishFresh st rid)
    (hStep : storeObject tid₀.toObjId (.tcb newTcb) st = .ok ((), st')) :
    replyIdEstablishFresh st' rid := by
  obtain ⟨⟨r, hr, hrc⟩, hUnstashed⟩ := hFresh
  refine ⟨⟨r, ?_, hrc⟩, ?_⟩
  · -- reply slot untouched: `rid.toObjId ≠ tid₀.toObjId` (reply vs tcb kind).
    have hrObj : st.objects[rid.toObjId]? = some (.reply r) := (getReply?_eq_some_iff st rid r).mp hr
    have hNe : rid.toObjId ≠ tid₀.toObjId := by
      intro hEq; rw [hEq, hOld] at hrObj; cases hrObj
    rw [getReply?_eq_some_iff, storeObject_objects_ne st st' tid₀.toObjId rid.toObjId _ hNe hObjInv hStep]
    exact hrObj
  · -- stash agreement: a post TCB stashing `rid` maps to a pre TCB stashing `rid`.
    intro tid tcb hTcb hStash
    rw [getTcb?_eq_some_iff] at hTcb
    by_cases hEq : tid.toObjId = tid₀.toObjId
    · rw [hEq, storeObject_objects_eq st st' tid₀.toObjId _ hObjInv hStep] at hTcb
      simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb
      subst hTcb
      rw [hStashEq] at hStash
      exact hUnstashed tid₀ oldTcb ((getTcb?_eq_some_iff st tid₀ oldTcb).mpr hOld) hStash
    · rw [storeObject_objects_ne st st' tid₀.toObjId tid.toObjId _ hEq hObjInv hStep] at hTcb
      exact hUnstashed tid tcb ((getTcb?_eq_some_iff st tid tcb).mpr hTcb) hStash

open SeLe4n.Model.SystemState in
/-- D3: `storeTcbIpcState` frames `replyIdEstablishFresh` (it writes only
`ipcState`, leaving the stash intact). -/
theorem storeTcbIpcState_preserves_replyIdEstablishFresh
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hFresh : replyIdEstablishFresh st rid)
    (hStep : storeTcbIpcState st tid ipc = .ok st') :
    replyIdEstablishFresh st' rid := by
  unfold storeTcbIpcState at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep
      subst hEq
      exact storeObject_tcb_preserveStash_replyIdEstablishFresh st pair.2 tid tcb
        { tcb with ipcState := ipc } rid hObjInv
        (lookupTcb_some_objects st tid tcb hTcb) rfl hFresh hStore

open SeLe4n.Model.SystemState in
/-- D3: `storeTcbIpcStateAndMessage` frames `replyIdEstablishFresh` (writes
`ipcState` + `pendingMessage`, leaving the stash intact). -/
theorem storeTcbIpcStateAndMessage_preserves_replyIdEstablishFresh
    (st st' : SystemState) (tid : SeLe4n.ThreadId) (ipc : ThreadIpcState)
    (msg : Option IpcMessage) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hFresh : replyIdEstablishFresh st rid)
    (hStep : storeTcbIpcStateAndMessage st tid ipc msg = .ok st') :
    replyIdEstablishFresh st' rid := by
  unfold storeTcbIpcStateAndMessage at hStep
  cases hTcb : lookupTcb st tid with
  | none => simp [hTcb] at hStep
  | some tcb =>
    simp only [hTcb] at hStep
    cases hStore : storeObject tid.toObjId (.tcb { tcb with ipcState := ipc, pendingMessage := msg }) st with
    | error e => simp [hStore] at hStep
    | ok pair =>
      simp only [hStore] at hStep
      have hEq : pair.snd = st' := Except.ok.inj hStep
      subst hEq
      exact storeObject_tcb_preserveStash_replyIdEstablishFresh st pair.2 tid tcb
        { tcb with ipcState := ipc, pendingMessage := msg } rid hObjInv
        (lookupTcb_some_objects st tid tcb hTcb) rfl hFresh hStore

open SeLe4n.Model.SystemState in
/-- D3: `endpointQueueEnqueue` frames `replyIdEstablishFresh`.  Reply preserved
(the enqueue writes only the endpoint object + queue links); stash preserved
backward via `endpointQueueEnqueue_tcb_pendingReceiveReply_backward`. -/
theorem endpointQueueEnqueue_preserves_replyIdEstablishFresh
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (enqueueTid : SeLe4n.ThreadId)
    (st st' : SystemState) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hFresh : replyIdEstablishFresh st rid)
    (hStep : endpointQueueEnqueue endpointId isReceiveQ enqueueTid st = .ok st') :
    replyIdEstablishFresh st' rid := by
  obtain ⟨⟨r, hr, hrc⟩, hUnstashed⟩ := hFresh
  refine ⟨⟨r, ?_, hrc⟩, ?_⟩
  · -- the enqueue exact-preserves the reply slot at `rid.toObjId`.
    rw [getReply?_eq_some_iff,
        endpointQueueEnqueue_preserves_reply endpointId isReceiveQ enqueueTid st st' rid.toObjId r
          ((getReply?_eq_some_iff st rid r).mp hr) hObjInv hStep]
  · intro tid tcb hTcb hStash
    rw [getTcb?_eq_some_iff] at hTcb
    obtain ⟨tcb0, hTcb0, hStashEq⟩ := endpointQueueEnqueue_tcb_pendingReceiveReply_backward
      endpointId isReceiveQ enqueueTid st st' tid tcb hObjInv hStep hTcb
    exact hUnstashed tid tcb0 ((getTcb?_eq_some_iff st tid tcb0).mpr hTcb0) (hStashEq.trans hStash)

open SeLe4n.Model.SystemState in
/-- D3: `endpointQueuePopHead` frames `replyIdEstablishFresh` (the rendezvous
branch dequeues a sender — writes only the endpoint object + queue links). -/
theorem endpointQueuePopHead_preserves_replyIdEstablishFresh
    (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (st st' : SystemState) (tid₀ : SeLe4n.ThreadId) (tcb₀ : TCB) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hFresh : replyIdEstablishFresh st rid)
    (hStep : endpointQueuePopHead endpointId isReceiveQ st = .ok (tid₀, tcb₀, st')) :
    replyIdEstablishFresh st' rid := by
  obtain ⟨⟨r, hr, hrc⟩, hUnstashed⟩ := hFresh
  refine ⟨⟨r, ?_, hrc⟩, ?_⟩
  · rw [getReply?_eq_some_iff,
        endpointQueuePopHead_preserves_reply endpointId isReceiveQ st st' tid₀ tcb₀ rid.toObjId r
          ((getReply?_eq_some_iff st rid r).mp hr) hObjInv hStep]
  · intro tid tcb hTcb hStash
    rw [getTcb?_eq_some_iff] at hTcb
    obtain ⟨tcb0, hTcb0, hStashEq⟩ := endpointQueuePopHead_tcb_pendingReceiveReply_backward
      endpointId isReceiveQ st st' tid₀ tcb₀ tid tcb hObjInv hStep hTcb
    exact hUnstashed tid tcb0 ((getTcb?_eq_some_iff st tid tcb0).mpr hTcb0) (hStashEq.trans hStash)

open SeLe4n.Model.SystemState in
/-- D3: `cleanupPreReceiveDonation` frames `replyIdEstablishFresh` (it is a no-op
or a single `returnDonatedSchedContext`, which writes only schedContext +
schedContextBinding — never a reply, never a stash). -/
theorem cleanupPreReceiveDonation_preserves_replyIdEstablishFresh
    (st : SystemState) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hFresh : replyIdEstablishFresh st rid) :
    replyIdEstablishFresh (cleanupPreReceiveDonation st receiver) rid := by
  obtain ⟨⟨r, hr, hrc⟩, hUnstashed⟩ := hFresh
  refine ⟨⟨r, ?_, hrc⟩, ?_⟩
  · rw [getReply?_eq_some_iff,
        cleanupPreReceiveDonation_preserves_reply st receiver rid.toObjId r
          ((getReply?_eq_some_iff st rid r).mp hr) hObjInv]
  · intro tid tcb hTcb hStash
    rw [getTcb?_eq_some_iff] at hTcb
    obtain ⟨tcb0, hTcb0, hStashEq⟩ :=
      cleanupPreReceiveDonation_tcb_pendingReceiveReply_backward st receiver hObjInv tid tcb hTcb
    exact hUnstashed tid tcb0 ((getTcb?_eq_some_iff st tid tcb0).mpr hTcb0) (hStashEq.trans hStash)

open SeLe4n.Model.SystemState in
/-- D3 (Step 2): `cleanupPreReceiveDonation` frames `pendingReceiveReplyWellFormed`.
It is a no-op or a single `returnDonatedSchedContext`, which writes only a
SchedContext's `boundThread` and two TCBs' `schedContextBinding` — never a TCB's
`ipcState`/`pendingReceiveReply` nor a `.reply` object — so both C1 (stash ⇒
`.blockedOnReceive` ∧ reply-present-free) and C2 (stash injective) frame backward
through `cleanupPreReceiveDonation_tcb_{ipcState,pendingReceiveReply}_backward` +
`cleanupPreReceiveDonation_preserves_reply`. -/
theorem cleanupPreReceiveDonation_preserves_pendingReceiveReplyWellFormed
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st) :
    pendingReceiveReplyWellFormed (cleanupPreReceiveDonation st receiver) := by
  refine ⟨?_, ?_⟩
  · -- C1
    intro tid tcb rid hTcb hStash
    rw [getTcb?_eq_some_iff] at hTcb
    obtain ⟨tcb0, hTcb0, hIpcEq⟩ :=
      cleanupPreReceiveDonation_tcb_ipcState_backward st receiver hObjInv tid tcb hTcb
    obtain ⟨tcb0', hTcb0', hStashEq⟩ :=
      cleanupPreReceiveDonation_tcb_pendingReceiveReply_backward st receiver hObjInv tid tcb hTcb
    -- both backward witnesses are the *same* pre-state TCB at `tid.toObjId`.
    have hSame : tcb0 = tcb0' := by
      rw [hTcb0] at hTcb0'
      simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hTcb0'
    subst hSame
    obtain ⟨⟨ep, hBlk⟩, r, hr, hrc⟩ :=
      hInv.1 tid tcb0 rid ((getTcb?_eq_some_iff st tid tcb0).mpr hTcb0) (hStashEq.trans hStash)
    refine ⟨⟨ep, hIpcEq ▸ hBlk⟩, r, ?_, hrc⟩
    rw [getReply?_eq_some_iff]
    exact cleanupPreReceiveDonation_preserves_reply st receiver rid.toObjId r
      ((getReply?_eq_some_iff st rid r).mp hr) hObjInv
  · -- C2 (injectivity)
    intro tid₁ tid₂ tcb₁ tcb₂ rid hTcb₁ hTcb₂ hStash₁ hStash₂
    rw [getTcb?_eq_some_iff] at hTcb₁ hTcb₂
    obtain ⟨tcbA, hTcbA, hStashEqA⟩ :=
      cleanupPreReceiveDonation_tcb_pendingReceiveReply_backward st receiver hObjInv tid₁ tcb₁ hTcb₁
    obtain ⟨tcbB, hTcbB, hStashEqB⟩ :=
      cleanupPreReceiveDonation_tcb_pendingReceiveReply_backward st receiver hObjInv tid₂ tcb₂ hTcb₂
    exact hInv.2 tid₁ tid₂ tcbA tcbB rid
      ((getTcb?_eq_some_iff st tid₁ tcbA).mpr hTcbA) ((getTcb?_eq_some_iff st tid₂ tcbB).mpr hTcbB)
      (hStashEqA.trans hStash₁) (hStashEqB.trans hStash₂)

open SeLe4n.Model.SystemState in
/-- D3: `endpointSendDual` frames `pendingReceiveReplyWellFormed`.  Rendezvous
branch: the receiver is completed via `storeTcbReceiveComplete`, which *clears*
its stash (unconditional frame).  Blocking branch: the sender is enqueued and set
`.blockedOnSend`; that write frames C1 provided the sender was not a stashing
`.blockedOnReceive` thread (`hSenderNotRecv` — a real precondition of the send
syscall: the scheduler only dispatches `.ready` threads).  Threading
`hSenderNotRecv` replaces the post-state `pendingReceiveReplyWellFormed st'`. -/
theorem endpointSendDual_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold endpointSendDual at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | some _ =>
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          have hP1 := endpointQueuePopHead_preserves_pendingReceiveReplyWellFormed endpointId true st pair.2.2 pair.1 _ hObjInv hInv hPop
          cases hMsg : storeTcbReceiveComplete pair.2.2 pair.1 (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hP2 := storeTcbReceiveComplete_preserves_pendingReceiveReplyWellFormed
              pair.2.2 st2 pair.1 (some msg) hObjInv1 hP1 hMsg
            exact pendingReceiveReplyWellFormed_of_objects_eq (ensureRunnable_preserves_objects st2 pair.1) hP2
      | none =>
        cases hEnq : endpointQueueEnqueue endpointId false sender st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false sender st st1 hObjInv hEnq
          have hP1 := endpointQueueEnqueue_preserves_pendingReceiveReplyWellFormed endpointId false sender st st1 hObjInv hInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 sender (.blockedOnSend endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hP2 := storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
              st1 st2 sender (.blockedOnSend endpointId) (some msg) hObjInv1 hP1 ?_ hMsg
            · exact pendingReceiveReplyWellFormed_of_objects_eq (removeRunnable_preserves_objects st2 sender) hP2
            · -- the enqueue preserves the sender's `ipcState`; carry `hSenderNotRecv` to `st1`.
              intro tcb' hTcb' ep' h
              obtain ⟨tcb0, hTcb0, hIpcEq⟩ := endpointQueueEnqueue_tcb_ipcState_backward
                endpointId false sender st st1 sender tcb' hObjInv hEnq
                ((getTcb?_eq_some_iff st1 sender tcb').mp hTcb')
              exact hSenderNotRecv tcb0 ((getTcb?_eq_some_iff st sender tcb0).mpr hTcb0) ep' (hIpcEq.trans h)

open SeLe4n.Model.SystemState in
/-- D3 (de-threaded crux): `endpointCall` **preserves** `pendingReceiveReplyWellFormed`.
The blocking branch moves the caller to `.blockedOnCall` (a non-`.blockedOnReceive`
store) — framed, given the caller does not stash (which `hCallerNotRecv` + C1 force).
The server-waiting branch delivers the message to the dequeued server (keeping its
stash `rid`), blocks the caller, then `linkServerStashedReply` links `rid` to the caller
and clears the server's stash — the `linkServerStashedReply` frame above closes it from
the **post-pop** PRR, with `hC1Other`/`hC2` discharged by object-framing the deliver/block
stores (which only touch `ipcState`/`pendingMessage`, never a stash).  `hCallerNotRecv`
(the caller is not `.blockedOnReceive`) prevents the caller's block-store from creating a
second C1 violation.  Needs the pre-state PRR, **not** `hReplyIdValid` —
`endpointCall` establishes no fresh stash. -/
theorem endpointCall_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold endpointCall at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.receiveQ.head with
      | none =>
        -- Blocking branch: caller enqueues then becomes `.blockedOnCall`.
        cases hEnq : endpointQueueEnqueue endpointId false caller st with
        | error e => simp [hHead, hEnq] at hStep
        | ok st1 =>
          simp only [hHead, hEnq] at hStep
          have hObjInv1 := endpointQueueEnqueue_preserves_objects_invExt endpointId false caller st st1 hObjInv hEnq
          have hP1 := endpointQueueEnqueue_preserves_pendingReceiveReplyWellFormed endpointId false caller st st1 hObjInv hInv hEnq
          cases hMsg : storeTcbIpcStateAndMessage st1 caller (.blockedOnCall endpointId) (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg, Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, hEq⟩ := hStep; subst hEq
            have hP2 := storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
              st1 st2 caller (.blockedOnCall endpointId) (some msg) hObjInv1 hP1 ?_ hMsg
            · exact pendingReceiveReplyWellFormed_of_objects_eq (removeRunnable_preserves_objects st2 caller) hP2
            · -- caller's `ipcState` is preserved by the enqueue; carry `hCallerNotRecv` to `st1`.
              intro tcb' hTcb' ep' h
              obtain ⟨tcb0, hTcb0, hIpcEq⟩ := endpointQueueEnqueue_tcb_ipcState_backward
                endpointId false caller st st1 caller tcb' hObjInv hEnq
                ((getTcb?_eq_some_iff st1 caller tcb').mp hTcb')
              exact hCallerNotRecv tcb0 ((getTcb?_eq_some_iff st caller tcb0).mpr hTcb0) ep' (hIpcEq.trans h)
      | some _ =>
        -- Server-waiting branch.
        cases hPop : endpointQueuePopHead endpointId true st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInv1 := endpointQueuePopHead_preserves_objects_invExt endpointId true st pair.2.2 pair.1 _ hObjInv hPop
          have hP1 : pendingReceiveReplyWellFormed pair.2.2 :=
            endpointQueuePopHead_preserves_pendingReceiveReplyWellFormed endpointId true st pair.2.2 pair.1 _ hObjInv hInv hPop
          -- `hCallerNotRecv` transported to the post-pop state `pair.2.2`.
          have hCallerNotRecv1 : ∀ (tcb : TCB), pair.2.2.getTcb? caller = some tcb →
              ∀ ep', tcb.ipcState ≠ .blockedOnReceive ep' := by
            intro tcb hTcb ep' hBlk
            obtain ⟨tcb0, hTcb0, hIpc0⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId true st pair.2.2 pair.1 caller tcb hObjInv hPop ((getTcb?_eq_some_iff pair.2.2 caller tcb).mp hTcb)
            exact hCallerNotRecv tcb0 ((getTcb?_eq_some_iff st caller tcb0).mpr hTcb0) ep' (hIpc0 ▸ hBlk)
          cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready (some msg) with
          | error e => simp [hMsg] at hStep
          | ok st2 =>
            simp only [hMsg] at hStep
            have hObjInv2 := storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ _ hObjInv1 hMsg
            have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by rwa [ensureRunnable_preserves_objects]
            cases hIpc : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) caller (.blockedOnReply endpointId (some pair.1)) none with
            | error e => simp [hIpc] at hStep
            | ok st4 =>
              simp only [hIpc] at hStep
              have hObjInv4 := storeTcbIpcStateAndMessage_preserves_objects_invExt (ensureRunnable st2 pair.1) st4 caller _ _ hObjInvEns hIpc
              cases hLink : SystemState.linkServerStashedReply caller pair.1 st4 with
              | error e => simp [hLink] at hStep
              | ok pL =>
                obtain ⟨_, st5⟩ := pL
                simp only [hLink, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                -- Back-frame TCB reads from `st4` to the post-pop state `pair.2.2`,
                -- carrying the stash unchanged through deliver/ensureRunnable/block.
                have hBackTcb : ∀ (y : SeLe4n.ThreadId) (tcY : TCB), st4.getTcb? y = some tcY →
                    ∃ tc0, pair.2.2.getTcb? y = some tc0 ∧
                      tc0.pendingReceiveReply = tcY.pendingReceiveReply ∧
                      (y ≠ pair.1 → y ≠ caller → tc0.ipcState = tcY.ipcState) := by
                  intro y tcY hY4
                  -- st4 → ensureRunnable st2 (block store, target `caller`).
                  obtain ⟨tcE, hTcE, hStashE, hIpcE⟩ :=
                    storeTcbIpcStateAndMessage_getTcb?_backward (ensureRunnable st2 pair.1) st4 caller _ none hObjInvEns hIpc y tcY hY4
                  -- ensureRunnable st2 → st2 (objects-eq).
                  have hTc2 : st2.getTcb? y = some tcE := by
                    unfold getTcb? at hTcE ⊢; rwa [ensureRunnable_preserves_objects] at hTcE
                  -- st2 → pair.2.2 (deliver store, target `pair.1`).
                  obtain ⟨tc0, hTc0, hStash0, hIpc0⟩ :=
                    storeTcbIpcStateAndMessage_getTcb?_backward pair.2.2 st2 pair.1 _ (some msg) hObjInv1 hMsg y tcE hTc2
                  refine ⟨tc0, hTc0, hStash0.trans hStashE, ?_⟩
                  intro hyP hyC
                  rw [hIpc0 hyP, hIpcE hyC]
                -- The deliver/block stores' target slots each held a TCB pre-store.
                have hDelivTarget : ∃ t, pair.2.2.objects[pair.1.toObjId]? = some (.tcb t) := by
                  unfold storeTcbIpcStateAndMessage at hMsg
                  cases hL : lookupTcb pair.2.2 pair.1 with
                  | none => simp [hL] at hMsg
                  | some t => exact ⟨t, lookupTcb_some_objects pair.2.2 pair.1 t hL⟩
                have hBlockTarget : ∃ t, (ensureRunnable st2 pair.1).objects[caller.toObjId]? = some (.tcb t) := by
                  unfold storeTcbIpcStateAndMessage at hIpc
                  cases hL : lookupTcb (ensureRunnable st2 pair.1) caller with
                  | none => simp [hL] at hIpc
                  | some t => exact ⟨t, lookupTcb_some_objects (ensureRunnable st2 pair.1) caller t hL⟩
                -- `getReply?` frames from `pair.2.2` through both stores (targets are TCBs).
                have hReplyFrame : ∀ (r' : SeLe4n.ReplyId) (rr : Reply),
                    pair.2.2.getReply? r' = some rr → st4.getReply? r' = some rr := by
                  intro r' rr hR
                  have hRobj : pair.2.2.objects[r'.toObjId]? = some (.reply rr) := (getReply?_eq_some_iff pair.2.2 r' rr).mp hR
                  -- distinctness of a Reply slot from each TCB target slot.
                  have hNe2 : r'.toObjId ≠ pair.1.toObjId := by
                    intro hEq
                    obtain ⟨t1, ht1⟩ := hDelivTarget
                    rw [hEq, ht1] at hRobj; cases hRobj
                  rw [getReply?_eq_some_iff]
                  -- frame across deliver (≠ pair.1) then ensureRunnable then block.
                  have hStep1 : st2.objects[r'.toObjId]? = pair.2.2.objects[r'.toObjId]? :=
                    storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ (some msg) r'.toObjId hNe2 hObjInv1 hMsg
                  have hStep2 : (ensureRunnable st2 pair.1).objects[r'.toObjId]? = st2.objects[r'.toObjId]? := by
                    rw [ensureRunnable_preserves_objects]
                  have hNe4 : r'.toObjId ≠ caller.toObjId := by
                    intro hEq
                    obtain ⟨tc0c, hcObj⟩ := hBlockTarget
                    have hRobj2 : (ensureRunnable st2 pair.1).objects[r'.toObjId]? = some (.reply rr) := by
                      rw [hStep2, hStep1]; exact hRobj
                    rw [hEq, hcObj] at hRobj2; cases hRobj2
                  have hStep3 : st4.objects[r'.toObjId]? = (ensureRunnable st2 pair.1).objects[r'.toObjId]? :=
                    storeTcbIpcStateAndMessage_preserves_objects_ne (ensureRunnable st2 pair.1) st4 caller _ none r'.toObjId hNe4 hObjInvEns hIpc
                  rw [hStep3, hStep2, hStep1]; exact hRobj
                -- Apply the `linkServerStashedReply` frame from the post-pop PRR `hP1`.
                refine linkServerStashedReply_preserves_pendingReceiveReplyWellFormed st4 st5 caller pair.1 hObjInv4 ?_ ?_ hLink
                · -- hC1Other at `st4`.
                  intro tid tcb ridX hTNeServer hT4 hStash4
                  obtain ⟨tc0, hTc0, hStash0, hIpc0⟩ := hBackTcb tid tcb hT4
                  have hStashX0 : tc0.pendingReceiveReply = some ridX := hStash0.trans hStash4
                  -- tid ≠ caller (else caller stashes at `pair.2.2`, contra `hCallerNotRecv1` via C1).
                  have hTNeCaller : tid ≠ caller := by
                    intro hEqC; subst hEqC
                    obtain ⟨hBlk0, _⟩ := hP1.1 tid tc0 ridX hTc0 hStashX0
                    obtain ⟨epx, hepx⟩ := hBlk0
                    exact hCallerNotRecv1 tc0 hTc0 epx hepx
                  obtain ⟨hBlk0, hFreeReply0⟩ := hP1.1 tid tc0 ridX hTc0 hStashX0
                  refine ⟨?_, ?_⟩
                  · -- tid `.blockedOnReceive` at `st4` (ipcState unchanged: tid ≠ pair.1, ≠ caller).
                    rw [← hIpc0 hTNeServer hTNeCaller]; exact hBlk0
                  · obtain ⟨rr, hGetRR, hRRfree⟩ := hFreeReply0
                    exact ⟨rr, hReplyFrame ridX rr hGetRR, hRRfree⟩
                · -- hC2 at `st4`.
                  intro tid₁ tid₂ tcb₁ tcb₂ ridX hT4₁ hT4₂ hStash4₁ hStash4₂
                  obtain ⟨tc0₁, hTc0₁, hStash0₁, _⟩ := hBackTcb tid₁ tcb₁ hT4₁
                  obtain ⟨tc0₂, hTc0₂, hStash0₂, _⟩ := hBackTcb tid₂ tcb₂ hT4₂
                  exact hP1.2 tid₁ tid₂ tc0₁ tc0₂ ridX hTc0₁ hTc0₂ (hStash0₁.trans hStash4₁) (hStash0₂.trans hStash4₂)

open SeLe4n.Model.SystemState in
/-- D3: `consumeCallerReply` frames `pendingReceiveReplyWellFormed`.  It clears
`reply.caller := none` (frees a reply — only relaxes C1's "free" half) and the
caller's `replyObject := none` (touches neither `ipcState` nor
`pendingReceiveReply`). -/
theorem consumeCallerReply_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold SystemState.consumeCallerReply at hStep
  cases hConsume : SystemState.consumeReply rid st with
  | error e => simp [hConsume] at hStep
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    have hP1 := consumeReply_preserves_pendingReceiveReplyWellFormed st st1 rid hObjInv hInv hConsume
    have hObjInv1 := consumeReply_preserves_objects_invExt st st1 rid hObjInv hConsume
    simp only [hConsume] at hStep
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨_, rfl⟩ := hStep; exact hP1
    | some tcb =>
      simp only [hT] at hStep
      exact storeObject_tcb_preserveFields_pendingReceiveReplyWellFormed st1 st' caller tcb
        { tcb with replyObject := none } hObjInv1 hT rfl rfl hP1 hStep

open SeLe4n.Model.SystemState in
/-- D3: `notificationWait` frames `pendingReceiveReplyWellFormed`.  It stores the
notification object (non-TCB, non-Reply) then writes the *waiter* — the calling
thread — to `.ready` (badge path) or `.blockedOnNotification` (block path).
Neither target is `.blockedOnReceive`, so the only way the write could break C1
is if the caller were already a stashing `.blockedOnReceive` thread; the
precondition `hWaiterNotRecv` (the calling thread is not mid-receive-stash — a
real precondition of the wait syscall, the scheduler only dispatches `.ready`
threads) rules that out.  Threading it replaces the post-state
`pendingReceiveReplyWellFormed st'` hypothesis. -/
theorem notificationWait_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hWaiterNotRecv : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : notificationWait notificationId waiter st = .ok (badge, st')) :
    pendingReceiveReplyWellFormed st' := by
  simp only [notificationWait] at hStep
  split at hStep
  · rename_i ntfn hObj
    -- `hWaiterNotRecv` framed through any notification-object store at `notificationId`
    -- (the waiter slot holds a TCB, never a notification, so it is untouched).
    have hFrameWaiter : ∀ (n : Notification) (st1 : SystemState),
        storeObject notificationId (.notification n) st = .ok ((), st1) →
        ∀ (tcb : TCB), st1.getTcb? waiter = some tcb → ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep := by
      intro n st1 hSO tcb hTcb ep
      have hNe : waiter.toObjId ≠ notificationId := by
        intro hEq
        rw [getTcb?_eq_some_iff, hEq,
          storeObject_objects_eq st st1 notificationId (.notification n) hObjInv hSO] at hTcb
        simp at hTcb
      have hTcbSt : st.getTcb? waiter = some tcb := by
        rw [getTcb?_eq_some_iff] at hTcb ⊢
        rwa [storeObject_objects_ne st st1 notificationId waiter.toObjId (.notification n) hNe hObjInv hSO] at hTcb
      exact hWaiterNotRecv tcb hTcbSt ep
    split at hStep
    · split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_nonTcbReply_preserves_pendingReceiveReplyWellFormed
          st st1 notificationId (.notification _) (fun t => by simp) (fun r => by simp)
          (fun r => by rw [hObj]; simp) hObjInv hInv hSO
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSI =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          exact storeTcbIpcState_notReceiving_preserves_pendingReceiveReplyWellFormed
            st1 st2 waiter .ready hObjInv1 hInv1 (hFrameWaiter _ st1 hSO) hSI
    · split at hStep
      · contradiction
      · rename_i waiterTcb hLookup
        split at hStep
        · contradiction
        · split at hStep
          · contradiction
          · split at hStep
            next => contradiction
            next st1 hSO =>
              have hInv1 := storeObject_nonTcbReply_preserves_pendingReceiveReplyWellFormed
                st st1 notificationId (.notification _) (fun t => by simp) (fun r => by simp)
                (fun r => by rw [hObj]; simp) hObjInv hInv hSO
              have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
              split at hStep
              next => contradiction
              next st2 hSI =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                -- The notification store frames the waiter's TCB, so the pre-store lookup
                -- value `waiterTcb` is still the value in `st1`.
                have hLookup1 : lookupTcb st1 waiter = some waiterTcb :=
                  lookupTcb_preserved_by_storeObject_notification hLookup hObj hObjInv hSO
                rw [storeTcbIpcState_fromTcb_eq hLookup1] at hSI
                exact pendingReceiveReplyWellFormed_of_objects_eq
                  (removeRunnable_preserves_objects st2 waiter)
                  (storeTcbIpcState_notReceiving_preserves_pendingReceiveReplyWellFormed
                    st1 st2 waiter (.blockedOnNotification notificationId) hObjInv1 hInv1
                    (hFrameWaiter _ st1 hSO) hSI)
  · contradiction
  · contradiction

open SeLe4n.Model.SystemState in
/-- D3: `notificationSignal` frames `pendingReceiveReplyWellFormed`.  It stores the
notification object (non-TCB, non-Reply — frames the clause) then wakes the head
waiter to `.ready`.  That waiter is a notification-queue member, so
`notificationWaiterConsistent` pins its pre-state `ipcState` to
`.blockedOnNotification` (≠ `.blockedOnReceive`) ⇒ it does not stash ⇒ the wake
frames C1.  `notificationWaiterConsistent st` is the *pre-state* invariant the
callers carry (a real system invariant of the notification subsystem); threading
it replaces the post-state `pendingReceiveReplyWellFormed st'` hypothesis. -/
theorem notificationSignal_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hNWC : notificationWaiterConsistent st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  simp only [notificationSignal] at hStep
  split at hStep
  · rename_i ntfn hObj
    cases hWaiters : ntfn.waitingThreads.tail? with
    | some headTail =>
      obtain ⟨waiter, rest⟩ := headTail
      simp only [hWaiters] at hStep
      split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_nonTcbReply_preserves_pendingReceiveReplyWellFormed
          st st1 notificationId (.notification _) (fun t => by simp) (fun r => by simp)
          (fun r => by rw [hObj]; simp) hObjInv hInv hSO
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        -- The waiter is the head of `ntfn.waitingThreads`, hence `.blockedOnNotification`.
        have hValEq : ntfn.waitingThreads.val = waiter :: rest.val :=
          (SeLe4n.NoDupList.tail?_eq_some_iff ntfn.waitingThreads waiter rest).mp hWaiters
        have hWaiterMem : waiter ∈ ntfn.waitingThreads := by
          show waiter ∈ ntfn.waitingThreads.val
          rw [hValEq]; exact List.mem_cons_self
        obtain ⟨wTcb, hWTcb, hWIpc⟩ := hNWC notificationId ntfn waiter hObj hWaiterMem
        split at hStep
        next => contradiction
        next st2 hSM =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have hInv2 := storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
            st1 st2 waiter .ready _ hObjInv1 hInv1 ?_ hSM
          · exact pendingReceiveReplyWellFormed_of_objects_eq
              (ensureRunnable_preserves_objects st2 waiter) hInv2
          · intro tcb' hTcb' ep h
            -- `waiter`'s TCB is unchanged by the notification store: derive its pre-state.
            have hNe : waiter.toObjId ≠ notificationId := by
              intro hEq; rw [hEq] at hWTcb; rw [hObj] at hWTcb; simp at hWTcb
            have hWTcb1 : st1.getTcb? waiter = some wTcb := by
              rw [getTcb?_eq_some_iff,
                storeObject_objects_ne st st1 notificationId waiter.toObjId _ hNe hObjInv hSO]
              exact hWTcb
            rw [hWTcb1] at hTcb'; obtain rfl := Option.some.inj hTcb'
            rw [hWIpc] at h; cases h
    | none =>
      simp only [hWaiters] at hStep
      split at hStep
      all_goals
        exact storeObject_nonTcbReply_preserves_pendingReceiveReplyWellFormed
          st st' notificationId (.notification _) (fun t => by simp) (fun r => by simp)
          (fun r => by rw [hObj]; simp) hObjInv hInv hStep
  · contradiction
  · contradiction

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D / #7.4: `linkCallerReply` preserves `ipcInvariantFull`.  It is the
reply store (`linkReply`, success ⇒ slot held `.reply r`, writes
`.reply { r with caller := some caller }`) followed by the caller-TCB
`replyObject := some rid` store; store A frames the first, store B the second.

The preconditions are the **intermediate-state** invariants the fold actually has at the
link site (post-blocking-store, pre-link): `ipcInvariantCore`, reply-link reciprocity
(`replyCallerLinkageReciprocal`), and the third clause for every blockedOnReply caller
**other** than `caller` (`hThirdExc`).  Taking the full `ipcInvariantFull st` would be
*vacuous* here — its third clause would force `caller.replyObject` to already be set, which
contradicts `linkCallerReply`'s fail-closed precondition that the caller holds no reply.

IPC de-threading D3 (de-threaded): the 17th conjunct is **derived** via
`linkCallerReply_preserves_pendingReceiveReplyWellFormed` from the *pre-state* PRR
(`hPRR`) rather than threaded on the post-state.  Linking a reply that some blocked
receiver still stashes would break C1's "free Reply" half, so the de-thread carries the
`hNotStashed` side-condition (no blocked receiver stashes `rid`) — which the fold's caller
discharges from `replyIsStashed` at the link site. -/
theorem linkCallerReply_preserves_ipcInvariantFull
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hCore : ipcInvariantCore st)
    (hRecip : replyCallerLinkageReciprocal st) (hObjInv : st.objects.invExt)
    (hCallerBlk : ∀ tc, st.getTcb? caller = some tc →
      ∃ (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId), tc.ipcState = .blockedOnReply ep rt)
    (hThirdExc : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
        (ep : SeLe4n.ObjId) (rt : Option SeLe4n.ThreadId),
        tid ≠ caller →
        st.objects[tid.toObjId]? = some (.tcb tcb) →
        tcb.ipcState = .blockedOnReply ep rt →
        ∃ ridv, tcb.replyObject = some ridv)
    (hPRR : pendingReceiveReplyWellFormed st)
    (hNotStashed : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB),
        st.getTcb? tid = some tcb → tcb.pendingReceiveReply ≠ some rid)
    (hStep : linkCallerReply caller rid st = .ok ((), st')) :
    ipcInvariantFull st' := by
  refine ipcInvariantFull_of_core_replyCallerLinkage ?core ?link
    (linkCallerReply_preserves_pendingReceiveReplyWellFormed st st' caller rid hObjInv
      hPRR hNotStashed hStep)
  case link =>
    exact linkCallerReply_establishes_replyCallerLinkage st st' caller rid
      hRecip hObjInv hCallerBlk hThirdExc hStep
  case core =>
    unfold linkCallerReply at hStep
    cases hLink : linkReply rid caller st with
    | error e => simp [hLink] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hLink] at hStep
      have hObjInv1 : st1.objects.invExt :=
        linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
      have hCore1 : ipcInvariantCore st1 := by
        unfold linkReply at hLink
        cases hGetR : st.getReply? rid with
        | none => rw [hGetR] at hLink; simp at hLink
        | some r =>
          simp only [hGetR] at hLink
          split at hLink
          · exact storeObject_reply_preserves_ipcInvariantCore st st1 rid.toObjId r
              { r with caller := some caller } hCore hObjInv
              ((getReply?_eq_some_iff st rid r).mp hGetR) hLink
          · simp at hLink
      cases hT : st1.getTcb? caller with
      | none => simp [hT] at hStep
      | some tcb =>
        simp only [hT] at hStep
        split at hStep
        · exact storeObject_tcb_replyObject_preserves_ipcInvariantCore st1 st'
            caller.toObjId tcb (some rid) hCore1 hObjInv1
            ((getTcb?_eq_some_iff st1 caller tcb).mp hT) hStep
        · simp at hStep

open SeLe4n.Model.SystemState in
/-- WS-SM SM6.D / #7.4: `consumeCallerReply` preserves `ipcInvariantFull` on a *mutually
linked* pair (`r0.caller = some caller`).  Structural core: the reply store
(`consumeReply`) then the caller-TCB `replyObject := none` store, both via
`ipcInvariantCore`.  Reply linkage (`hRCL'`) is threaded as a post-state hypothesis,
exactly as for the live IPC transitions: standalone consume clears `caller.replyObject`
without unblocking it, so the strengthened `replyCallerLinkage` (third clause:
`blockedOnReply ⇒ replyObject`) is re-established by the *fused* reply transition that
unblocks the caller, not by the link-teardown primitive in isolation.  Its reciprocal
half is `consumeCallerReply_preserves_replyCallerLinkageReciprocal`.  IPC de-threading D3
(de-threaded): the 17th conjunct is **derived** via
`consumeCallerReply_preserves_pendingReceiveReplyWellFormed` rather than threaded. -/
theorem consumeCallerReply_preserves_ipcInvariantFull
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (r0 : SeLe4n.Kernel.Reply)
    (hInv : ipcInvariantFull st) (hObjInv : st.objects.invExt)
    (hGetR0 : st.getReply? rid = some r0) (hLinked : r0.caller = some caller)
    (hRCL' : replyCallerLinkage st')
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    ipcInvariantFull st' := by
  refine ipcInvariantFull_of_core_replyCallerLinkage ?core hRCL'
    (consumeCallerReply_preserves_pendingReceiveReplyWellFormed st st' caller rid hObjInv
      hInv.pendingReceiveReplyWellFormed hStep)
  case core =>
    unfold consumeCallerReply at hStep
    cases hCons : consumeReply rid st with
    | error e => simp [hCons] at hStep
    | ok p1 =>
      obtain ⟨_, st1⟩ := p1
      simp only [hCons] at hStep
      have hObjInv1 : st1.objects.invExt :=
        consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
      have hCore1 : ipcInvariantCore st1 := by
        unfold consumeReply at hCons
        cases hGetR : st.getReply? rid with
        | none =>
          simp only [hGetR, Except.ok.injEq, Prod.mk.injEq, true_and] at hCons
          rw [← hCons]; exact hInv.toCore
        | some r =>
          simp only [hGetR] at hCons
          exact storeObject_reply_preserves_ipcInvariantCore st st1 rid.toObjId r
            { r with caller := none } hInv.toCore hObjInv
            ((getReply?_eq_some_iff st rid r).mp hGetR) hCons
      cases hT : st1.getTcb? caller with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
        rw [← hStep]; exact hCore1
      | some tcb =>
        simp only [hT] at hStep
        exact storeObject_tcb_replyObject_preserves_ipcInvariantCore st1 st'
          caller.toObjId tcb none hCore1 hObjInv1
          ((getTcb?_eq_some_iff st1 caller tcb).mp hT) hStep

-- ============================================================================
-- IPC de-threading D2 — de-threaded `ipcInvariantFull` bundle theorems
--
-- `endpointReceiveDual` / `endpointCall` no longer thread the full
-- `replyCallerLinkage st'`.  They thread only the reciprocal half
-- (`replyCallerLinkageReciprocal st'`, threaded pre-#7.4) and **establish** the third
-- clause (`blockedOnReplyHasReplyObject st'`) concretely from the pre-state via the
-- `*_establishes_blockedOnReplyHasReplyObject` theorems above — closing the #7.4 origin
-- gap at the transition boundary.  Placed here (rather than next to the other bundle
-- theorems) to follow the establish theorems they depend on.
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- IPC de-threading D3 (the establish): `endpointReceiveDual` **establishes**
`pendingReceiveReplyWellFormed`.

* **No-sender branch** — the receiver blocks and the server-supplied `replyId`
  (when present, named present-free-and-unstashed by `hReplyIdValid`) is stashed.
  The stash-write discharges PRR via `storeObject_establishStash_…`, fed by the
  freshness fact `replyIdEstablishFresh` carried forward through cleanup → enqueue
  → `storeTcbIpcState` (none of which touch a reply's `caller` or any thread's
  stash).
* **Rendezvous branch** — a waiting sender is dequeued and the message delivered.
  No stash is established; the receiver- and sender-completions move threads to
  `.ready` / `.blockedOnReply` (never `.blockedOnReceive`), so PRR frames provided
  those threads were not mid-receive-stash.  The dequeued head is a `sendQ` head,
  hence `.blockedOnSend` / `.blockedOnCall` (`hQHBC : queueHeadBlockedConsistent` —
  trivially available in the bundle), never `.blockedOnReceive`.  The completing
  receiver is the running thread (`hReceiverNotRecv`, a real precondition — needed
  only when the receiver is *not* the dequeued sender; when it is, the sender
  completion already left it `.ready` / `.blockedOnReply`).  A `Call` rendezvous
  additionally links `replyId` to the dequeued caller;
  `linkCallerReply_preserves_…`'s `hNotStashed` is the *unstashed* half of
  `hReplyIdValid` carried to the link site. -/
theorem endpointReceiveDual_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver : SeLe4n.ThreadId) (senderId : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hQHBC : queueHeadBlockedConsistent st)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold endpointReceiveDual at hStep
  cases hObj : st.objects[endpointId]? with
  | none => simp [hObj] at hStep
  | some obj => cases obj with
    | tcb _ | cnode _ | notification _ | vspaceRoot _ | untyped _ | schedContext _ | reply _ =>
        simp [hObj] at hStep
    | endpoint ep =>
      simp only [hObj] at hStep
      cases hHead : ep.sendQ.head with
      | some _ =>
        -- Rendezvous branch.
        cases hPop : endpointQueuePopHead endpointId false st with
        | error e => simp [hHead, hPop] at hStep
        | ok pair =>
          simp only [hHead, hPop] at hStep
          have hObjInvPop : pair.2.2.objects.invExt :=
            endpointQueuePopHead_preserves_objects_invExt endpointId false st pair.2.2 pair.1 pair.2.1 hObjInv hPop
          have hP1 : pendingReceiveReplyWellFormed pair.2.2 :=
            endpointQueuePopHead_preserves_pendingReceiveReplyWellFormed endpointId false st pair.2.2 pair.1 _ hObjInv hInv hPop
          -- `pair.2.1` is the dequeued head's *pre-state* TCB; by `queueHeadBlockedConsistent`
          -- a sendQ head is `.blockedOnSend`/`.blockedOnCall`, never `.blockedOnReceive`.
          have hHeadPre : st.objects[pair.1.toObjId]? = some (.tcb pair.2.1) :=
            endpointQueuePopHead_returns_pre_tcb endpointId false st ep pair.1 pair.2.1 pair.2.2 hObj hPop
          have hHeadIsHead : ep.sendQ.head = some pair.1 := by
            have := endpointQueuePopHead_returns_head endpointId false st ep pair.1 pair.2.2 hObj hPop
            simpa using this
          have hHeadNotRecv : ∀ ep', pair.2.1.ipcState ≠ .blockedOnReceive ep' := by
            intro ep' hBlk
            rcases (hQHBC endpointId ep pair.1 pair.2.1 hObj hHeadPre).2 hHeadIsHead with h | h <;>
              rw [hBlk] at h <;> cases h
          -- the dequeued head's ipcState is preserved by PopHead (only queue links change).
          have hHeadNotRecvPop : ∀ (tcb : TCB), pair.2.2.getTcb? pair.1 = some tcb →
              ∀ ep', tcb.ipcState ≠ .blockedOnReceive ep' := by
            intro tcb hTcb ep' hBlk
            obtain ⟨tcb0, hTcb0, hIpc0⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId false st pair.2.2 pair.1 pair.1 tcb hObjInv hPop ((getTcb?_eq_some_iff pair.2.2 pair.1 tcb).mp hTcb)
            rw [hHeadPre] at hTcb0
            simp only [Option.some.injEq, KernelObject.tcb.injEq] at hTcb0
            subst hTcb0
            exact hHeadNotRecv ep' (hIpc0 ▸ hBlk)
          cases hSenderIpc : pair.2.1.ipcState with
          | blockedOnCall _ =>
            -- Call path: sender → `.blockedOnReply`, link reply, complete receiver.
            simp only [hSenderIpc, ite_true] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 (.blockedOnReply endpointId (some receiver)) none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hP2 : pendingReceiveReplyWellFormed st2 :=
                storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
                  pair.2.2 st2 pair.1 _ none hObjInvPop hP1 hHeadNotRecvPop hMsg
              cases hReplyId : replyId with
              | none => simp [hReplyId] at hStep
              | some rid =>
                simp only [hReplyId] at hStep
                cases hLink : SystemState.linkCallerReply pair.1 rid st2 with
                | error e => simp [hLink] at hStep
                | ok pLink =>
                  obtain ⟨_, stLinked⟩ := pLink
                  simp only [hLink] at hStep
                  have hObjInvLink : stLinked.objects.invExt :=
                    linkCallerReply_preserves_objects_invExt st2 stLinked pair.1 rid hObjInvMsg hLink
                  -- transport the unstashed-freshness of `rid` from `st` to `st2`.
                  have hFreshSt : replyIdEstablishFresh st rid := hReplyIdValid rid hReplyId
                  have hFreshPop : replyIdEstablishFresh pair.2.2 rid :=
                    endpointQueuePopHead_preserves_replyIdEstablishFresh endpointId false st pair.2.2 pair.1 pair.2.1 rid hObjInv hFreshSt hPop
                  have hFresh2 : replyIdEstablishFresh st2 rid :=
                    storeTcbIpcStateAndMessage_preserves_replyIdEstablishFresh pair.2.2 st2 pair.1 _ none rid hObjInvPop hFreshPop hMsg
                  have hPLink : pendingReceiveReplyWellFormed stLinked :=
                    linkCallerReply_preserves_pendingReceiveReplyWellFormed st2 stLinked pair.1 rid hObjInvMsg hP2 hFresh2.2 hLink
                  revert hStep
                  cases hPend : storeTcbIpcStateAndMessage stLinked receiver .ready _ with
                  | ok st4 =>
                    intro h
                    obtain ⟨_, hEq⟩ := Prod.mk.inj (Except.ok.inj h); subst hEq
                    -- receiver-completion frames PRR: receiver not `.blockedOnReceive` at `stLinked`.
                    refine storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
                      stLinked st4 receiver .ready _ hObjInvLink hPLink ?_ hPend
                    intro tcb hTcb ep' hBlk
                    -- back `stLinked` → `st2` (linkCallerReply preserves the receiver's ipcState).
                    obtain ⟨tcbL, hTcbL, hIpcL⟩ := linkCallerReply_tcb_ipcState_backward st2 stLinked pair.1 rid receiver tcb hObjInvMsg hLink ((getTcb?_eq_some_iff stLinked receiver tcb).mp hTcb)
                    by_cases hRS : receiver = pair.1
                    · -- receiver = dequeued sender: at `st2` it is `.blockedOnReply` (sender-store).
                      have hIpcAt : tcbL.ipcState = .blockedOnReply endpointId (some receiver) :=
                        storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 _ none hObjInvPop hMsg tcbL (hRS ▸ hTcbL)
                      rw [← hIpcL, hIpcAt] at hBlk; cases hBlk
                    · -- receiver ≠ sender: the receiver slot is untouched by the sender-store.
                      have hNeObj : receiver.toObjId ≠ pair.1.toObjId :=
                        fun h => hRS (ThreadId.toObjId_injective receiver pair.1 h)
                      have hTcbPop : pair.2.2.objects[receiver.toObjId]? = some (.tcb tcbL) := by
                        rwa [storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ none receiver.toObjId hNeObj hObjInvPop hMsg] at hTcbL
                      obtain ⟨tcb0, hTcb0, hIpc0⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId false st pair.2.2 pair.1 receiver tcbL hObjInv hPop hTcbPop
                      exact hReceiverNotRecv tcb0 ((getTcb?_eq_some_iff st receiver tcb0).mpr hTcb0) ep' (by rw [hIpc0, hIpcL]; exact hBlk)
                  | error _ => simp
          | ready | blockedOnSend _ | blockedOnReceive _ | blockedOnNotification _ | blockedOnReply _ _ =>
            -- Send path: sender → `.ready`, complete receiver.
            simp only [hSenderIpc] at hStep
            cases hMsg : storeTcbIpcStateAndMessage pair.2.2 pair.1 .ready none with
            | error e => simp [hMsg] at hStep
            | ok st2 =>
              simp only [hMsg] at hStep
              have hObjInvMsg : st2.objects.invExt :=
                storeTcbIpcStateAndMessage_preserves_objects_invExt pair.2.2 st2 pair.1 _ none hObjInvPop hMsg
              have hP2 : pendingReceiveReplyWellFormed st2 :=
                storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
                  pair.2.2 st2 pair.1 _ none hObjInvPop hP1 hHeadNotRecvPop hMsg
              have hObjInvEns : (ensureRunnable st2 pair.1).objects.invExt := by rwa [ensureRunnable_preserves_objects]
              have hP3 : pendingReceiveReplyWellFormed (ensureRunnable st2 pair.1) :=
                pendingReceiveReplyWellFormed_of_objects_eq (ensureRunnable_preserves_objects st2 pair.1) hP2
              revert hStep
              cases hPend : storeTcbIpcStateAndMessage (ensureRunnable st2 pair.1) receiver .ready _ with
              | ok st4 =>
                intro h
                obtain ⟨_, hEq⟩ := Prod.mk.inj (Except.ok.inj h); subst hEq
                refine storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
                  (ensureRunnable st2 pair.1) st4 receiver .ready _ hObjInvEns hP3 ?_ hPend
                intro tcb hTcb ep' hBlk
                have hTcbEns : st2.objects[receiver.toObjId]? = some (.tcb tcb) := by
                  have := (getTcb?_eq_some_iff (ensureRunnable st2 pair.1) receiver tcb).mp hTcb
                  rwa [ensureRunnable_preserves_objects] at this
                by_cases hRS : receiver = pair.1
                · -- receiver = dequeued sender: the sender-store left it `.ready`.
                  have hIpcAt : tcb.ipcState = .ready :=
                    storeTcbIpcStateAndMessage_ipcState_eq pair.2.2 st2 pair.1 _ none hObjInvPop hMsg tcb (hRS ▸ hTcbEns)
                  rw [hIpcAt] at hBlk; cases hBlk
                · have hNeObj : receiver.toObjId ≠ pair.1.toObjId :=
                    fun h => hRS (ThreadId.toObjId_injective receiver pair.1 h)
                  have hTcbPop : pair.2.2.objects[receiver.toObjId]? = some (.tcb tcb) := by
                    rwa [storeTcbIpcStateAndMessage_preserves_objects_ne pair.2.2 st2 pair.1 _ none receiver.toObjId hNeObj hObjInvPop hMsg] at hTcbEns
                  obtain ⟨tcb0, hTcb0, hIpc0⟩ := endpointQueuePopHead_tcb_ipcState_backward endpointId false st pair.2.2 pair.1 receiver tcb hObjInv hPop hTcbPop
                  exact hReceiverNotRecv tcb0 ((getTcb?_eq_some_iff st receiver tcb0).mpr hTcb0) ep' (by rw [hIpc0]; exact hBlk)
              | error _ => simp
      | none =>
        -- No-sender branch: cleanup → enqueue → block → establish stash.
        cases hChecked : cleanupPreReceiveDonationChecked st receiver with
        | error _ => simp [hHead, hChecked] at hStep
        | ok stClean =>
          have hBridge : stClean = cleanupPreReceiveDonation st receiver :=
            (cleanupPreReceiveDonationChecked_ok_eq_cleanup st stClean receiver hChecked).symm
          simp only [hHead, hChecked] at hStep
          rw [hBridge] at hStep
          have hObjInvClean := cleanupPreReceiveDonation_preserves_objects_invExt st receiver hObjInv
          have hPClean : pendingReceiveReplyWellFormed (cleanupPreReceiveDonation st receiver) :=
            cleanupPreReceiveDonation_preserves_pendingReceiveReplyWellFormed st receiver hObjInv hInv
          cases hEnq : endpointQueueEnqueue endpointId true receiver (cleanupPreReceiveDonation st receiver) with
          | error e => simp [hEnq] at hStep
          | ok st1 =>
            simp only [hEnq] at hStep
            have hObjInvEnq : st1.objects.invExt :=
              endpointQueueEnqueue_preserves_objects_invExt endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hEnq
            have hP1 : pendingReceiveReplyWellFormed st1 :=
              endpointQueueEnqueue_preserves_pendingReceiveReplyWellFormed endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 hObjInvClean hPClean hEnq
            cases hIpc : storeTcbIpcState st1 receiver (.blockedOnReceive endpointId) with
            | error e => simp [hIpc] at hStep
            | ok st2 =>
              simp only [hIpc] at hStep
              have hObjInv2 : st2.objects.invExt :=
                storeTcbIpcState_preserves_objects_invExt st1 st2 receiver _ hObjInvEnq hIpc
              have hP2 : pendingReceiveReplyWellFormed st2 :=
                storeTcbIpcState_preserves_pendingReceiveReplyWellFormed st1 st2 receiver _ hObjInvEnq hP1
                  (fun _tcb _rid _hTcb _hStash => ⟨endpointId, rfl⟩) hIpc
              cases hGetR : st2.getTcb? receiver with
              | none =>
                simp only [hGetR, Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, hEq⟩ := hStep; subst hEq
                exact pendingReceiveReplyWellFormed_of_objects_eq (removeRunnable_preserves_objects st2 receiver) hP2
              | some rTcb =>
                simp only [hGetR] at hStep
                cases hStash : storeObject receiver.toObjId (.tcb { rTcb with pendingReceiveReply := replyId }) st2 with
                | error e => simp [hStash] at hStep
                | ok pStash =>
                  obtain ⟨_, stStashed⟩ := pStash
                  simp only [hStash, Except.ok.injEq, Prod.mk.injEq] at hStep
                  obtain ⟨_, hEq⟩ := hStep; subst hEq
                  have hRecvObj : st2.objects[receiver.toObjId]? = some (.tcb rTcb) :=
                    (getTcb?_eq_some_iff st2 receiver rTcb).mp hGetR
                  -- the receiver is now `.blockedOnReceive` (the prior store set it).
                  have hRecvBlk : rTcb.ipcState = .blockedOnReceive endpointId :=
                    storeTcbIpcState_ipcState_eq st1 st2 receiver _ hObjInvEnq hIpc rTcb hRecvObj
                  have hPStash : pendingReceiveReplyWellFormed stStashed := by
                    cases hReplyId : replyId with
                    | none =>
                      -- stash cleared to `none`: C1/C2 obligations are vacuous (no new stash).
                      refine storeObject_tcb_preserves_pendingReceiveReplyWellFormed
                        st2 stStashed receiver rTcb { rTcb with pendingReceiveReply := replyId }
                        hObjInv2 hGetR hP2 ?_ ?_ hStash
                      · intro rid hStashSome; rw [hReplyId] at hStashSome; cases hStashSome
                      · intro rid hStashSome; rw [hReplyId] at hStashSome; cases hStashSome
                    | some rid =>
                      -- establish a fresh stash; transport freshness of `rid` to `st2`.
                      have hFreshSt : replyIdEstablishFresh st rid := hReplyIdValid rid hReplyId
                      have hFreshClean : replyIdEstablishFresh (cleanupPreReceiveDonation st receiver) rid :=
                        cleanupPreReceiveDonation_preserves_replyIdEstablishFresh st receiver rid hObjInv hFreshSt
                      have hFreshEnq : replyIdEstablishFresh st1 rid :=
                        endpointQueueEnqueue_preserves_replyIdEstablishFresh endpointId true receiver (cleanupPreReceiveDonation st receiver) st1 rid hObjInvClean hFreshClean hEnq
                      have hFresh2 : replyIdEstablishFresh st2 rid :=
                        storeTcbIpcState_preserves_replyIdEstablishFresh st1 st2 receiver _ rid hObjInvEnq hFreshEnq hIpc
                      obtain ⟨⟨r, hr, hrc⟩, hUnstashed⟩ := hFresh2
                      refine storeObject_establishStash_pendingReceiveReplyWellFormed
                        st2 stStashed receiver rTcb _ rid hObjInv2 hGetR ?_ ?_ ⟨r, hr, hrc⟩ hUnstashed hP2 hStash
                      · simp [hReplyId]
                      · exact ⟨endpointId, by rw [hRecvBlk]⟩
                  exact pendingReceiveReplyWellFormed_of_objects_eq (removeRunnable_preserves_objects stStashed receiver) hPStash

open SeLe4n.Model.SystemState in
/-- D3 (Step 4): `ipcUnwrapCaps` frames `pendingReceiveReplyWellFormed`.  Cap transfer
writes only CNode slots at `receiverRoot` (and CDT lifecycle fields) — never a `.reply`
object and never any TCB's `pendingReceiveReply`.  So C1 (stash ⇒ `.blockedOnReceive`
∧ reply-present-free) and C2 (injective) transport backward through the full-TCB
preservation `ipcUnwrapCaps_tcb_backward`, and C1's reply-present half forward through
`ipcUnwrapCaps_preserves_reply_objects`. -/
theorem ipcUnwrapCaps_preserves_pendingReceiveReplyWellFormed
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    pendingReceiveReplyWellFormed st' := by
  refine ⟨?_, ?_⟩
  · -- C1
    intro tid tcb rid hTcb hStash
    have hTcbSt : st.objects[tid.toObjId]? = some (.tcb tcb) :=
      ipcUnwrapCaps_tcb_backward msg senderRoot receiverRoot slotBase grantRight st st' summary
        tid.toObjId tcb hObjInv hStep ((getTcb?_eq_some_iff st' tid tcb).mp hTcb)
    obtain ⟨hBlk, r, hr, hrc⟩ := hInv.1 tid tcb rid ((getTcb?_eq_some_iff st tid tcb).mpr hTcbSt) hStash
    refine ⟨hBlk, r, ?_, hrc⟩
    rw [getReply?_eq_some_iff]
    exact ipcUnwrapCaps_preserves_reply_objects msg senderRoot receiverRoot slotBase grantRight
      st st' summary rid.toObjId r ((getReply?_eq_some_iff st rid r).mp hr) hObjInv hStep
  · -- C2 (injectivity)
    intro tid₁ tid₂ tcb₁ tcb₂ rid hTcb₁ hTcb₂ hStash₁ hStash₂
    have hTcbSt₁ : st.objects[tid₁.toObjId]? = some (.tcb tcb₁) :=
      ipcUnwrapCaps_tcb_backward msg senderRoot receiverRoot slotBase grantRight st st' summary
        tid₁.toObjId tcb₁ hObjInv hStep ((getTcb?_eq_some_iff st' tid₁ tcb₁).mp hTcb₁)
    have hTcbSt₂ : st.objects[tid₂.toObjId]? = some (.tcb tcb₂) :=
      ipcUnwrapCaps_tcb_backward msg senderRoot receiverRoot slotBase grantRight st st' summary
        tid₂.toObjId tcb₂ hObjInv hStep ((getTcb?_eq_some_iff st' tid₂ tcb₂).mp hTcb₂)
    exact hInv.2 tid₁ tid₂ tcb₁ tcb₂ rid ((getTcb?_eq_some_iff st tid₁ tcb₁).mpr hTcbSt₁)
      ((getTcb?_eq_some_iff st tid₂ tcb₂).mpr hTcbSt₂) hStash₁ hStash₂

open SeLe4n.Model.SystemState in
/-- D3 (Step 5): `endpointReplyRecv` **establishes** `pendingReceiveReplyWellFormed`.
The reply leg (`storeTcbIpcStateAndMessage replyTarget .ready (some msg)` + `ensureRunnable`)
frames PRR and transports the establish-preconditions (`replyIdEstablishFresh`,
`hReceiverNotRecv`, `queueHeadBlockedConsistent`) to the intermediate state, where the
folded `endpointReceiveDual` establishes the clause. -/
theorem endpointReplyRecv_preserves_pendingReceiveReplyWellFormed
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hQHBC : queueHeadBlockedConsistent st)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    pendingReceiveReplyWellFormed st' := by
  unfold endpointReplyRecv at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st replyTarget with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId expectedReplier =>
      simp only [hIpc] at hStep
      cases expectedReplier with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st replyTarget .ready (some msg) with
          | error e => simp
          | ok stReplied =>
            simp only []
            have hObjInvR := storeTcbIpcStateAndMessage_preserves_objects_invExt st stReplied replyTarget _ _ hObjInv hMsg
            -- the reply leg frames PRR (`replyTarget` was `.blockedOnReply`, not stashing).
            have hPR : pendingReceiveReplyWellFormed stReplied :=
              storeTcbIpcStateAndMessage_notReceiving_preserves_pendingReceiveReplyWellFormed
                st stReplied replyTarget .ready (some msg) hObjInv hInv
                (fun t hT ep hBlk => by
                  have hTObj := (getTcb?_eq_some_iff st replyTarget t).mp hT
                  rw [lookupTcb_some_objects st replyTarget tcb hLookup] at hTObj
                  obtain rfl : t = tcb := by
                    simpa only [Option.some.injEq, KernelObject.tcb.injEq] using hTObj.symm
                  rw [hIpc] at hBlk; cases hBlk) hMsg
            have hObjInvE : (ensureRunnable stReplied replyTarget).objects.invExt := by rwa [ensureRunnable_preserves_objects]
            have hPE : pendingReceiveReplyWellFormed (ensureRunnable stReplied replyTarget) :=
              pendingReceiveReplyWellFormed_of_objects_eq (ensureRunnable_preserves_objects stReplied replyTarget) hPR
            -- `replyTarget` is `.blockedOnReply`, hence not a queue head — transport `hQHBC`.
            have hNotHead : ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
                st.objects[epId']? = some (.endpoint ep') →
                ep'.receiveQ.head ≠ some replyTarget ∧ ep'.sendQ.head ≠ some replyTarget := by
              intro epId' ep' hEp'
              have hRTObj : st.objects[replyTarget.toObjId]? = some (.tcb tcb) :=
                lookupTcb_some_objects st replyTarget tcb hLookup
              refine ⟨fun hHd => ?_, fun hHd => ?_⟩
              · have := (hQHBC epId' ep' replyTarget tcb hEp' hRTObj).1 hHd; rw [hIpc] at this; cases this
              · rcases (hQHBC epId' ep' replyTarget tcb hEp' hRTObj).2 hHd with h | h <;> rw [hIpc] at h <;> cases h
            have hQHBCR : queueHeadBlockedConsistent stReplied :=
              storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent st stReplied replyTarget
                _ _ hQHBC hObjInv hMsg hNotHead
            have hQHBCE : queueHeadBlockedConsistent (ensureRunnable stReplied replyTarget) :=
              ensureRunnable_preserves_queueHeadBlockedConsistent stReplied replyTarget hQHBCR
            -- transport `replyIdEstablishFresh` to the intermediate state.
            have hReplyIdValidE : ∀ rid, replyId = some rid →
                replyIdEstablishFresh (ensureRunnable stReplied replyTarget) rid := by
              intro rid hRid
              have hF0 := hReplyIdValid rid hRid
              have hFR := storeTcbIpcStateAndMessage_preserves_replyIdEstablishFresh st stReplied
                replyTarget _ _ rid hObjInv hF0 hMsg
              obtain ⟨⟨r, hr, hrc⟩, hUn⟩ := hFR
              refine ⟨⟨r, ?_, hrc⟩, ?_⟩
              · rw [getReply?_eq_some_iff] at hr ⊢; rwa [ensureRunnable_preserves_objects]
              · intro tid t hT hS
                rw [getTcb?_eq_some_iff] at hT; rw [ensureRunnable_preserves_objects] at hT
                exact hUn tid t ((getTcb?_eq_some_iff stReplied tid t).mpr hT) hS
            -- transport `hReceiverNotRecv` to the intermediate state.
            have hReceiverNotRecvE : ∀ (t : TCB),
                (ensureRunnable stReplied replyTarget).getTcb? receiver = some t →
                ∀ ep, t.ipcState ≠ .blockedOnReceive ep := by
              intro t hT ep hBlk
              rw [getTcb?_eq_some_iff, ensureRunnable_preserves_objects] at hT
              by_cases hRR : receiver = replyTarget
              · -- receiver = replyTarget: the reply store left it `.ready`.
                have hIpcAt := storeTcbIpcStateAndMessage_ipcState_eq st stReplied replyTarget _ _ hObjInv hMsg t (hRR ▸ hT)
                rw [hIpcAt] at hBlk; cases hBlk
              · have hNeObj : receiver.toObjId ≠ replyTarget.toObjId :=
                  fun h => hRR (ThreadId.toObjId_injective receiver replyTarget h)
                have hTSt : st.objects[receiver.toObjId]? = some (.tcb t) := by
                  rwa [storeTcbIpcStateAndMessage_preserves_objects_ne st stReplied replyTarget _ _ receiver.toObjId hNeObj hObjInv hMsg] at hT
                exact hReceiverNotRecv t ((getTcb?_eq_some_iff st receiver t).mpr hTSt) ep hBlk
            cases hRecv : endpointReceiveDual endpointId receiver replyId (ensureRunnable stReplied replyTarget) with
            | error e => simp
            | ok pair =>
              intro hStep
              simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
              obtain ⟨_, rfl⟩ := hStep
              exact endpointReceiveDual_preserves_pendingReceiveReplyWellFormed
                (ensureRunnable stReplied replyTarget) pair.2 endpointId receiver pair.1 replyId
                hObjInvE hPE hReplyIdValidE hReceiverNotRecvE hQHBCE hRecv
        · simp at hStep

open SeLe4n.Model.SystemState in
/-- D3 (Step 5): `endpointReceiveDualWithCaps` **establishes** `pendingReceiveReplyWellFormed`
— the base `endpointReceiveDual` establishes it (carrying `hReplyIdValid` / `hReceiverNotRecv`
/ `hQHBC`), and the optional `ipcUnwrapCaps` cap-transfer frames it. -/
theorem endpointReceiveDualWithCaps_preserves_pendingReceiveReplyWellFormed
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId) (endpointRights : AccessRightSet)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hQHBC : queueHeadBlockedConsistent st)
    (hStep : endpointReceiveDualWithCaps endpointId receiver replyId endpointRights
             receiverCspaceRoot receiverSlotBase st = .ok ((senderId, summary), st')) :
    pendingReceiveReplyWellFormed st' := by
  simp only [endpointReceiveDualWithCaps] at hStep
  cases hRecv : endpointReceiveDual endpointId receiver replyId st with
  | error e => simp [hRecv] at hStep
  | ok pair =>
    rcases pair with ⟨sid, stMid⟩
    have hPMid := endpointReceiveDual_preserves_pendingReceiveReplyWellFormed st stMid endpointId
      receiver sid replyId hObjInv hInv hReplyIdValid hReceiverNotRecv hQHBC hRecv
    have hObjInvMid := endpointReceiveDual_preserves_objects_invExt st stMid endpointId receiver sid replyId hObjInv hRecv
    simp [hRecv] at hStep
    cases hTcb : stMid.getTcb? receiver with
    | none => simp [hTcb] at hStep; obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hPMid
    | some receiverTcb =>
      simp [hTcb] at hStep
      cases hMsg : receiverTcb.pendingMessage with
      | none => simp [hMsg] at hStep; obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hPMid
      | some msg =>
        simp [hMsg] at hStep
        split at hStep
        · obtain ⟨⟨_, _⟩, rfl⟩ := hStep; exact hPMid
        · cases hLookup : lookupCspaceRoot stMid sid with
          | none => simp only [hLookup] at hStep; contradiction
          | some senderRoot =>
            simp only [hLookup] at hStep
            cases hUnwrap : ipcUnwrapCaps msg senderRoot receiverCspaceRoot
                receiverSlotBase (endpointRights.mem .grant) stMid with
            | error e => simp [hUnwrap] at hStep
            | ok pairU =>
              rcases pairU with ⟨s, stFinal⟩
              simp [hUnwrap] at hStep
              obtain ⟨⟨_, _⟩, rfl⟩ := hStep
              exact ipcUnwrapCaps_preserves_pendingReceiveReplyWellFormed msg senderRoot receiverCspaceRoot
                receiverSlotBase _ stMid stFinal s hObjInvMid hPMid hUnwrap

open SeLe4n.Model.SystemState in
/-- D3: `endpointSendDualWithCaps` preserves `pendingReceiveReplyWellFormed` — the base
`endpointSendDual` frames it (`hSenderNotRecv`), and the optional cap-transfer leg
(`ipcUnwrapCaps`) frames it. -/
theorem endpointSendDualWithCaps_preserves_pendingReceiveReplyWellFormed
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
             senderCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    pendingReceiveReplyWellFormed st' := by
  simp only [endpointSendDualWithCaps] at hStep
  cases hSend : endpointSendDual endpointId sender msg st with
  | error e => simp [hSend] at hStep
  | ok pair =>
    rcases pair with ⟨_, stMid⟩
    have hPMid := endpointSendDual_preserves_pendingReceiveReplyWellFormed st stMid endpointId
      sender msg hObjInv hInv hSenderNotRecv hSend
    have hObjInvMid := endpointSendDual_preserves_objects_invExt st stMid endpointId sender msg hObjInv hSend
    simp [hSend] at hStep
    cases hEp : st.getEndpoint? endpointId with
    | none => simp [hEp] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
    | some ep =>
      simp [hEp] at hStep
      cases hHead : ep.receiveQ.head with
      | none => simp [hHead] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
      | some receiverId =>
        simp [hHead] at hStep
        by_cases hEmpty : msg.caps = #[]
        · simp [hEmpty] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
        · simp [hEmpty] at hStep
          cases hLookup : lookupCspaceRoot stMid receiverId with
          | none => simp [hLookup] at hStep
          | some recvRoot =>
            simp [hLookup] at hStep
            exact ipcUnwrapCaps_preserves_pendingReceiveReplyWellFormed msg senderCspaceRoot recvRoot
              receiverSlotBase _ stMid st' summary hObjInvMid hPMid hStep

open SeLe4n.Model.SystemState in
/-- D3: `endpointCallWithCaps` preserves `pendingReceiveReplyWellFormed` — the base
`endpointCall` frames it (`hCallerNotRecv`; no fresh stash is established, so the
pre-state PRR suffices), and the optional cap-transfer leg (`ipcUnwrapCaps`) frames it. -/
theorem endpointCallWithCaps_preserves_pendingReceiveReplyWellFormed
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt) (hInv : pendingReceiveReplyWellFormed st)
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointCallWithCaps endpointId caller msg endpointRights
             callerCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    pendingReceiveReplyWellFormed st' := by
  simp only [endpointCallWithCaps] at hStep
  cases hCall : endpointCall endpointId caller msg st with
  | error e => simp [hCall] at hStep
  | ok pair =>
    rcases pair with ⟨_, stMid⟩
    have hPMid := endpointCall_preserves_pendingReceiveReplyWellFormed st stMid endpointId
      caller msg hObjInv hInv hCallerNotRecv hCall
    have hObjInvMid := endpointCall_preserves_objects_invExt st stMid endpointId caller msg hObjInv hCall
    simp [hCall] at hStep
    cases hEp : st.getEndpoint? endpointId with
    | none => simp [hEp] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
    | some ep =>
      simp [hEp] at hStep
      cases hHead : ep.receiveQ.head with
      | none => simp [hHead] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
      | some receiverId =>
        simp [hHead] at hStep
        by_cases hEmpty : msg.caps = #[]
        · simp [hEmpty] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hPMid
        · simp [hEmpty] at hStep
          cases hLookup : lookupCspaceRoot stMid receiverId with
          | none => simp [hLookup] at hStep
          | some recvRoot =>
            simp [hLookup] at hStep
            exact ipcUnwrapCaps_preserves_pendingReceiveReplyWellFormed msg callerCspaceRoot recvRoot
              receiverSlotBase _ stMid st' summary hObjInvMid hPMid hStep

-- ============================================================================
-- IPC de-threading D4: transition-level `queueNextBlockingConsistent` frames
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- Generic backward transfer: if every post-state TCB has a pre-state TCB at the
same slot with the **same** `ipcState` and `queueNext`, then
`queueNextBlockingConsistent` transfers from `st` to `st'`. The workhorse for the
reply-path helpers (which only touch `reply.caller` / `tcb.replyObject` /
`tcb.pendingReceiveReply` / `tcb.schedContextBinding`, never `ipcState`/`queueNext`). -/
theorem queueNextBlockingConsistent_of_tcb_links_backward
    (st st' : SystemState)
    (hBack : ∀ (y : SeLe4n.ThreadId) (tcb' : TCB),
      st'.objects[y.toObjId]? = some (.tcb tcb') →
      ∃ tcb, st.objects[y.toObjId]? = some (.tcb tcb) ∧
        tcb.ipcState = tcb'.ipcState ∧ tcb.queueNext = tcb'.queueNext)
    (hInv : queueNextBlockingConsistent st) :
    queueNextBlockingConsistent st' := by
  intro a b tcbA tcbB hA hB hN
  obtain ⟨tcbA0, hA0, hIpcA, hQNA⟩ := hBack a tcbA hA
  obtain ⟨tcbB0, hB0, hIpcB, _⟩ := hBack b tcbB hB
  have hN0 : tcbA0.queueNext = some b := by rw [hQNA]; exact hN
  have := hInv a b tcbA0 tcbB0 hA0 hB0 hN0
  -- `queueNextBlockingMatch` depends only on the two ipcStates.
  rw [hIpcA, hIpcB] at this; exact this

open SeLe4n.Model.SystemState in
/-- `storeObject` of a Reply object preserves `queueNextBlockingConsistent`
(a Reply is never a TCB, so no TCB's `ipcState`/`queueNext` changes). -/
theorem storeObject_reply_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (rid : SeLe4n.ReplyId) (r : SeLe4n.Kernel.Reply)
    (hObjInv : st.objects.invExt)
    (hInv : queueNextBlockingConsistent st)
    (hStore : storeObject rid.toObjId (.reply r) st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  refine queueNextBlockingConsistent_of_tcb_links_backward st st' ?_ hInv
  intro y tcb' hY
  have hEqAt : st'.objects[rid.toObjId]? = some (.reply r) :=
    storeObject_objects_eq st st' rid.toObjId (.reply r) hObjInv hStore
  by_cases hEq : y.toObjId = rid.toObjId
  · rw [hEq, hEqAt] at hY; cases hY
  · rw [storeObject_objects_ne st st' rid.toObjId y.toObjId (.reply r) hEq hObjInv hStore] at hY
    exact ⟨tcb', hY, rfl, rfl⟩

open SeLe4n.Model.SystemState in
/-- D4: `consumeReply` frames `queueNextBlockingConsistent` (stores a Reply object,
or is a no-op when the reply is absent). -/
theorem consumeReply_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : SystemState.consumeReply rid st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  unfold SystemState.consumeReply at hStep
  cases hGet : st.getReply? rid with
  | none => simp only [hGet, Except.ok.injEq, Prod.mk.injEq] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInv
  | some r =>
    simp only [hGet] at hStep
    exact storeObject_reply_preserves_queueNextBlockingConsistent st st' rid _ hObjInv hInv hStep

open SeLe4n.Model.SystemState in
/-- D4: `linkReply` frames `queueNextBlockingConsistent` (stores a Reply object). -/
theorem linkReply_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (rid : SeLe4n.ReplyId) (caller : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : SystemState.linkReply rid caller st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  unfold SystemState.linkReply at hStep
  cases hGet : st.getReply? rid with
  | none => simp [hGet] at hStep
  | some r =>
    simp only [hGet] at hStep
    by_cases hFree : r.caller.isNone
    · simp only [hFree, if_true] at hStep
      exact storeObject_reply_preserves_queueNextBlockingConsistent st st' rid _ hObjInv hInv hStep
    · simp [hFree] at hStep

open SeLe4n.Model.SystemState in
/-- `storeObject` of a TCB that preserves `ipcState` and `queueNext` frames
`queueNextBlockingConsistent`.  Used by the reply-cap link/unlink stores
(`replyObject` writes) which touch neither field. -/
theorem storeObject_tcb_preserveLinks_queueNextBlockingConsistent
    (st st' : SystemState) (tid₀ : SeLe4n.ThreadId) (oldTcb newTcb : TCB)
    (hObjInv : st.objects.invExt)
    (hOld : st.objects[tid₀.toObjId]? = some (.tcb oldTcb))
    (hSameIpc : newTcb.ipcState = oldTcb.ipcState)
    (hSameNext : newTcb.queueNext = oldTcb.queueNext)
    (hInv : queueNextBlockingConsistent st)
    (hStep : storeObject tid₀.toObjId (.tcb newTcb) st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  refine queueNextBlockingConsistent_of_tcb_links_backward st st' ?_ hInv
  intro y tcb' hY
  have hEqAt : st'.objects[tid₀.toObjId]? = some (.tcb newTcb) :=
    storeObject_objects_eq st st' tid₀.toObjId (.tcb newTcb) hObjInv hStep
  by_cases hEq : y.toObjId = tid₀.toObjId
  · rw [hEq, hEqAt] at hY; cases hY
    exact ⟨oldTcb, hEq ▸ hOld, hSameIpc.symm, hSameNext.symm⟩
  · rw [storeObject_objects_ne st st' tid₀.toObjId y.toObjId (.tcb newTcb) hEq hObjInv hStep] at hY
    exact ⟨tcb', hY, rfl, rfl⟩

open SeLe4n.Model.SystemState in
/-- D4: `linkCallerReply` frames `queueNextBlockingConsistent`.  Composes a
`linkReply` (Reply store) with a `caller.replyObject` write (preserves
`ipcState`/`queueNext`). -/
theorem linkCallerReply_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  unfold SystemState.linkCallerReply at hStep
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    have hInv1 := linkReply_preserves_queueNextBlockingConsistent st st1 rid caller hObjInv hInv hLink
    have hObjInv1 := linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    simp only [hLink] at hStep
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      by_cases hRO : tcb.replyObject.isNone
      · simp only [hRO, if_true] at hStep
        exact storeObject_tcb_preserveLinks_queueNextBlockingConsistent st1 st' caller tcb
          { tcb with replyObject := some rid } hObjInv1
          ((getTcb?_eq_some_iff st1 caller tcb).mp hT) rfl rfl hInv1 hStep
      · simp [hRO] at hStep

open SeLe4n.Model.SystemState in
/-- D4: `consumeCallerReply` frames `queueNextBlockingConsistent`.  Composes a
`consumeReply` (Reply store) with an optional `caller.replyObject := none` write. -/
theorem consumeCallerReply_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  unfold SystemState.consumeCallerReply at hStep
  cases hConsume : SystemState.consumeReply rid st with
  | error e => simp [hConsume] at hStep
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    have hInv1 := consumeReply_preserves_queueNextBlockingConsistent st st1 rid hObjInv hInv hConsume
    have hObjInv1 := consumeReply_preserves_objects_invExt st st1 rid hObjInv hConsume
    simp only [hConsume] at hStep
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨_, rfl⟩ := hStep; exact hInv1
    | some tcb =>
      simp only [hT] at hStep
      exact storeObject_tcb_preserveLinks_queueNextBlockingConsistent st1 st' caller tcb
        { tcb with replyObject := none } hObjInv1
        ((getTcb?_eq_some_iff st1 caller tcb).mp hT) rfl rfl hInv1 hStep

open SeLe4n.Model.SystemState in
/-- D4: `linkServerStashedReply` frames `queueNextBlockingConsistent`.  Composes a
`linkCallerReply` with a `server.pendingReceiveReply := none` write (preserves
`ipcState`/`queueNext`). -/
theorem linkServerStashedReply_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (caller server : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : SystemState.linkServerStashedReply caller server st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  unfold SystemState.linkServerStashedReply at hStep
  cases hStash : (st.getTcb? server).bind (·.pendingReceiveReply) with
  | none => simp [hStash] at hStep
  | some rid =>
    simp only [hStash] at hStep
    cases hLink : SystemState.linkCallerReply caller rid st with
    | error e => simp [hLink] at hStep
    | ok p =>
      obtain ⟨⟨⟩, st1⟩ := p
      have hInv1 := linkCallerReply_preserves_queueNextBlockingConsistent st st1 caller rid hObjInv hInv hLink
      have hObjInv1 := linkCallerReply_preserves_objects_invExt st st1 caller rid hObjInv hLink
      simp only [hLink] at hStep
      cases hT : st1.getTcb? server with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
        obtain ⟨_, rfl⟩ := hStep; exact hInv1
      | some sTcb =>
        simp only [hT] at hStep
        exact storeObject_tcb_preserveLinks_queueNextBlockingConsistent st1 st' server sTcb
          { sTcb with pendingReceiveReply := none } hObjInv1
          ((getTcb?_eq_some_iff st1 server sTcb).mp hT) rfl rfl hInv1 hStep

open SeLe4n.Model.SystemState in
/-- D4: `cleanupPreReceiveDonation` frames `queueNextBlockingConsistent`.  It either
no-ops or runs `returnDonatedSchedContext`, whose stores preserve every TCB's
`ipcState`/`queueNext` (`returnDonatedSchedContext_tcb_queue_backward`). -/
theorem cleanupPreReceiveDonation_preserves_queueNextBlockingConsistent
    (st : SystemState) (receiver : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st) :
    queueNextBlockingConsistent (cleanupPreReceiveDonation st receiver) := by
  unfold cleanupPreReceiveDonation
  cases hL : lookupTcb st receiver with
  | none => exact hInv
  | some recvTcb =>
    simp only []
    cases hB : recvTcb.schedContextBinding with
    | donated scId originalOwner =>
      simp only []
      cases hR : returnDonatedSchedContext st receiver scId originalOwner with
      | error e => exact hInv
      | ok st' =>
        simp only []
        refine queueNextBlockingConsistent_of_tcb_links_backward st st' ?_ hInv
        intro y tcb' hY
        obtain ⟨tcb, hTcb, hQN, _, hIpc, _⟩ :=
          returnDonatedSchedContext_tcb_queue_backward st st' receiver scId originalOwner hObjInv hR y.toObjId tcb' hY
        exact ⟨tcb, hTcb, hIpc, hQN⟩
    | unbound => exact hInv
    | bound _ => exact hInv

open SeLe4n.Model.SystemState in
/-- D4: `ipcUnwrapCaps` frames `queueNextBlockingConsistent`.  Every post-state TCB
equals its pre-state (the cap-transfer touches only a CNode), so `ipcState` and
`queueNext` are unchanged (`ipcUnwrapCaps_tcb_backward`). -/
theorem ipcUnwrapCaps_preserves_queueNextBlockingConsistent
    (msg : IpcMessage) (senderRoot receiverRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot) (grantRight : Bool)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : ipcUnwrapCaps msg senderRoot receiverRoot slotBase grantRight st
             = .ok (summary, st')) :
    queueNextBlockingConsistent st' := by
  refine queueNextBlockingConsistent_of_tcb_links_backward st st' ?_ hInv
  intro y tcb' hY
  exact ⟨tcb', ipcUnwrapCaps_tcb_backward msg senderRoot receiverRoot slotBase grantRight
    st st' summary y.toObjId tcb' hObjInv hStep hY, rfl, rfl⟩

-- ============================================================================
-- D4: transition-level frames for the cleanly-composing transitions
-- (no enqueue-to-blocking-state; see file note on the deferred transitions).
-- ============================================================================

open SeLe4n.Model.SystemState in
/-- D4: `endpointReply` frames `queueNextBlockingConsistent`.  It moves the
`.blockedOnReply` target to `.ready` (vacuously link-compatible both ways) then
`ensureRunnable` (object no-op). -/
theorem endpointReply_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      cases replyTarget with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp
          | ok st'' =>
            intro hStep
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            exact queueNextBlockingConsistent_of_objects_eq st'' (ensureRunnable st'' target)
              (fun x => by rw [ensureRunnable_preserves_objects])
              (storeTcbIpcStateAndMessage_ready_preserves_queueNextBlockingConsistent
                st st'' target (some msg) hInv hObjInv hMsg)
        · simp at hStep

open SeLe4n.Model.SystemState in
/-- D4: `endpointReply` frames `queueHeadBlockedConsistent`.  The `.blockedOnReply`
target is not an endpoint queue head (heads are `.blockedOnSend`/`Receive`/`Call`),
so the `.ready` write frames heads via `hNotHead`. -/
theorem endpointReply_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hObjInv : st.objects.invExt) (hInv : queueHeadBlockedConsistent st)
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    queueHeadBlockedConsistent st' := by
  unfold endpointReply at hStep
  simp only [show ¬(maxMessageRegisters < msg.registers.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  simp only [show ¬(maxExtraCaps < msg.caps.size) from by
    intro h; simp [h] at hStep, ↓reduceIte] at hStep
  cases hLookup : lookupTcb st target with
  | none => simp [hLookup] at hStep
  | some tcb =>
    simp only [hLookup] at hStep
    rw [storeTcbIpcStateAndMessage_fromTcb_eq hLookup] at hStep
    cases hIpc : tcb.ipcState with
    | ready => simp [hIpc] at hStep
    | blockedOnSend _ => simp [hIpc] at hStep
    | blockedOnReceive _ => simp [hIpc] at hStep
    | blockedOnNotification _ => simp [hIpc] at hStep
    | blockedOnCall _ => simp [hIpc] at hStep
    | blockedOnReply epId replyTarget =>
      simp only [hIpc] at hStep
      cases replyTarget with
      | none => simp at hStep
      | some expected =>
        simp only at hStep
        split at hStep
        · revert hStep
          cases hMsg : storeTcbIpcStateAndMessage st target .ready (some msg) with
          | error e => simp
          | ok st'' =>
            intro hStep
            simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
            obtain ⟨_, rfl⟩ := hStep
            -- `target` is `.blockedOnReply`, so not an endpoint head; discharge `hNotHead`.
            have hTargetObj : st.objects[target.toObjId]? = some (.tcb tcb) :=
              lookupTcb_some_objects st target tcb hLookup
            have hNotHead : ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
                st.objects[epId']? = some (.endpoint ep') →
                ep'.receiveQ.head ≠ some target ∧ ep'.sendQ.head ≠ some target := by
              intro epId' ep' hEp'
              refine ⟨fun hHd => ?_, fun hHd => ?_⟩
              · have := (hInv epId' ep' target tcb hEp' hTargetObj).1 hHd; rw [hIpc] at this; cases this
              · rcases (hInv epId' ep' target tcb hEp' hTargetObj).2 hHd with h | h <;> rw [hIpc] at h <;> cases h
            exact ensureRunnable_preserves_queueHeadBlockedConsistent st'' target
              (storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent
                st st'' target .ready (some msg) hInv hObjInv hMsg hNotHead)
        · simp at hStep

open SeLe4n.Model.SystemState in
/-- `storeObject` of a Reply object preserves `queueHeadBlockedConsistent`. -/
theorem storeObject_reply_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (rid : SeLe4n.ReplyId) (r : SeLe4n.Kernel.Reply)
    (hObjInv : st.objects.invExt) (hInv : queueHeadBlockedConsistent st)
    (hStore : storeObject rid.toObjId (.reply r) st = .ok ((), st')) :
    queueHeadBlockedConsistent st' :=
  storeObject_nonEndpointNonTcb_preserves_queueHeadBlockedConsistent
    st st' rid.toObjId (.reply r) hObjInv (fun _ => by simp) (fun _ => by simp) hInv hStore

open SeLe4n.Model.SystemState in
/-- D4: `consumeReply` frames `queueHeadBlockedConsistent`. -/
theorem consumeReply_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : queueHeadBlockedConsistent st)
    (hStep : SystemState.consumeReply rid st = .ok ((), st')) :
    queueHeadBlockedConsistent st' := by
  unfold SystemState.consumeReply at hStep
  cases hGet : st.getReply? rid with
  | none => simp only [hGet, Except.ok.injEq, Prod.mk.injEq] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hInv
  | some r =>
    simp only [hGet] at hStep
    exact storeObject_reply_preserves_queueHeadBlockedConsistent st st' rid _ hObjInv hInv hStep

open SeLe4n.Model.SystemState in
/-- D4: `linkReply` frames `queueHeadBlockedConsistent`. -/
theorem linkReply_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (rid : SeLe4n.ReplyId) (caller : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (hInv : queueHeadBlockedConsistent st)
    (hStep : SystemState.linkReply rid caller st = .ok ((), st')) :
    queueHeadBlockedConsistent st' := by
  unfold SystemState.linkReply at hStep
  cases hGet : st.getReply? rid with
  | none => simp [hGet] at hStep
  | some r =>
    simp only [hGet] at hStep
    by_cases hFree : r.caller.isNone
    · simp only [hFree, if_true] at hStep
      exact storeObject_reply_preserves_queueHeadBlockedConsistent st st' rid _ hObjInv hInv hStep
    · simp [hFree] at hStep

open SeLe4n.Model.SystemState in
/-- D4: `linkCallerReply` frames `queueHeadBlockedConsistent` (Reply store + a
`caller.replyObject` write that preserves `ipcState`). -/
theorem linkCallerReply_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : queueHeadBlockedConsistent st)
    (hStep : SystemState.linkCallerReply caller rid st = .ok ((), st')) :
    queueHeadBlockedConsistent st' := by
  unfold SystemState.linkCallerReply at hStep
  cases hLink : SystemState.linkReply rid caller st with
  | error e => simp [hLink] at hStep
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    have hInv1 := linkReply_preserves_queueHeadBlockedConsistent st st1 rid caller hObjInv hInv hLink
    have hObjInv1 := linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    simp only [hLink] at hStep
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hStep
    | some tcb =>
      simp only [hT] at hStep
      by_cases hRO : tcb.replyObject.isNone
      · simp only [hRO, if_true] at hStep
        exact storeObject_tcb_preserveIpc_preserves_queueHeadBlockedConsistent st1 st' caller tcb
          { tcb with replyObject := some rid } hObjInv1
          ((getTcb?_eq_some_iff st1 caller tcb).mp hT) rfl hInv1 hStep
      · simp [hRO] at hStep

open SeLe4n.Model.SystemState in
/-- D4: `consumeCallerReply` frames `queueHeadBlockedConsistent`. -/
theorem consumeCallerReply_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt) (hInv : queueHeadBlockedConsistent st)
    (hStep : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    queueHeadBlockedConsistent st' := by
  unfold SystemState.consumeCallerReply at hStep
  cases hConsume : SystemState.consumeReply rid st with
  | error e => simp [hConsume] at hStep
  | ok p =>
    obtain ⟨⟨⟩, st1⟩ := p
    have hInv1 := consumeReply_preserves_queueHeadBlockedConsistent st st1 rid hObjInv hInv hConsume
    have hObjInv1 := consumeReply_preserves_objects_invExt st st1 rid hObjInv hConsume
    simp only [hConsume] at hStep
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq] at hStep
      obtain ⟨_, rfl⟩ := hStep; exact hInv1
    | some tcb =>
      simp only [hT] at hStep
      exact storeObject_tcb_preserveIpc_preserves_queueHeadBlockedConsistent st1 st' caller tcb
        { tcb with replyObject := none } hObjInv1
        ((getTcb?_eq_some_iff st1 caller tcb).mp hT) rfl hInv1 hStep

open SeLe4n.Model.SystemState in
/-- D4: `notificationWait` frames `queueNextBlockingConsistent`.  Stores the
notification object (non-endpoint, non-TCB) then writes the *waiter* to `.ready`
(badge path) or `.blockedOnNotification` (block path) — both vacuously
link-compatible (a `.ready` / `.blockedOnNotification` thread matches anything). -/
theorem notificationWait_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (badge : Option SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : notificationWait notificationId waiter st = .ok (badge, st')) :
    queueNextBlockingConsistent st' := by
  simp only [notificationWait] at hStep
  split at hStep
  · rename_i ntfn hObj
    split at hStep
    · split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_non_ep_non_tcb_preserves_queueNextBlockingConsistent
          st st1 notificationId (.notification _) hInv hObjInv (fun _ => by simp)
          (fun tcb => by rw [hObj]; simp) hSO
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSI =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          exact storeTcbIpcState_preserves_queueNextBlockingConsistent_ready
            st1 st2 waiter hObjInv1 hInv1 hSI
    · split at hStep
      · contradiction
      · rename_i waiterTcb hLookup
        split at hStep
        · contradiction
        · split at hStep
          · contradiction
          · split at hStep
            next => contradiction
            next st1 hSO =>
              have hInv1 := storeObject_non_ep_non_tcb_preserves_queueNextBlockingConsistent
                st st1 notificationId (.notification _) hInv hObjInv (fun _ => by simp)
                (fun tcb => by rw [hObj]; simp) hSO
              have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
              split at hStep
              next => contradiction
              next st2 hSI =>
                simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
                obtain ⟨_, rfl⟩ := hStep
                have hLookup1 : lookupTcb st1 waiter = some waiterTcb :=
                  lookupTcb_preserved_by_storeObject_notification hLookup hObj hObjInv hSO
                rw [storeTcbIpcState_fromTcb_eq hLookup1] at hSI
                exact queueNextBlockingConsistent_of_objects_eq st2 (removeRunnable st2 waiter)
                  (fun x => by rw [removeRunnable_preserves_objects])
                  (storeTcbIpcState_blockedOnNotification_preserves_queueNextBlockingConsistent
                    st1 st2 waiter notificationId hObjInv1 hInv1 hSI)
  · contradiction
  · contradiction

open SeLe4n.Model.SystemState in
/-- D4: `notificationSignal` frames `queueNextBlockingConsistent`.  Stores the
notification object (non-endpoint, non-TCB) then wakes the head waiter to `.ready`
(badge-merge branch only re-stores the notification). -/
theorem notificationSignal_preserves_queueNextBlockingConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hInv : queueNextBlockingConsistent st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    queueNextBlockingConsistent st' := by
  simp only [notificationSignal] at hStep
  split at hStep
  · rename_i ntfn hObj
    cases hWaiters : ntfn.waitingThreads.tail? with
    | some headTail =>
      obtain ⟨waiter, rest⟩ := headTail
      simp only [hWaiters] at hStep
      split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_non_ep_non_tcb_preserves_queueNextBlockingConsistent
          st st1 notificationId (.notification _) hInv hObjInv (fun _ => by simp)
          (fun tcb => by rw [hObj]; simp) hSO
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        split at hStep
        next => contradiction
        next st2 hSM =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          exact queueNextBlockingConsistent_of_objects_eq st2 (ensureRunnable st2 waiter)
            (fun x => by rw [ensureRunnable_preserves_objects])
            (storeTcbIpcStateAndMessage_ready_preserves_queueNextBlockingConsistent
              st1 st2 waiter _ hInv1 hObjInv1 hSM)
    | none =>
      simp only [hWaiters] at hStep
      exact storeObject_non_ep_non_tcb_preserves_queueNextBlockingConsistent
        st st' notificationId (.notification _) hInv hObjInv (fun _ => by simp)
        (fun tcb => by rw [hObj]; simp) hStep
  · contradiction
  · contradiction

open SeLe4n.Model.SystemState in
/-- D4: `notificationSignal` frames `queueHeadBlockedConsistent`.  The notification
store frames endpoints/TCBs; the woken head waiter is a notification-queue member,
hence `.blockedOnNotification` (`notificationWaiterConsistent`), so it is not an
endpoint queue head ⇒ the `.ready` write discharges `hNotHead`. -/
theorem notificationSignal_preserves_queueHeadBlockedConsistent
    (st st' : SystemState) (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hObjInv : st.objects.invExt) (hInv : queueHeadBlockedConsistent st)
    (hNWC : notificationWaiterConsistent st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    queueHeadBlockedConsistent st' := by
  simp only [notificationSignal] at hStep
  split at hStep
  · rename_i ntfn hObj
    cases hWaiters : ntfn.waitingThreads.tail? with
    | some headTail =>
      obtain ⟨waiter, rest⟩ := headTail
      simp only [hWaiters] at hStep
      split at hStep
      next => contradiction
      next st1 hSO =>
        have hInv1 := storeObject_nonEndpointNonTcb_preserves_queueHeadBlockedConsistent
          st st1 notificationId (.notification _) hObjInv (fun _ => by simp) (fun _ => by simp) hInv hSO
        have hObjInv1 := storeObject_preserves_objects_invExt st st1 notificationId _ hObjInv hSO
        -- The waiter is the head of `ntfn.waitingThreads`, hence `.blockedOnNotification`.
        have hValEq : ntfn.waitingThreads.val = waiter :: rest.val :=
          (SeLe4n.NoDupList.tail?_eq_some_iff ntfn.waitingThreads waiter rest).mp hWaiters
        have hWaiterMem : waiter ∈ ntfn.waitingThreads := by
          show waiter ∈ ntfn.waitingThreads.val
          rw [hValEq]; exact List.mem_cons_self
        obtain ⟨wTcb, hWTcb, hWIpc⟩ := hNWC notificationId ntfn waiter hObj hWaiterMem
        split at hStep
        next => contradiction
        next st2 hSM =>
          simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
          obtain ⟨_, rfl⟩ := hStep
          -- The waiter's TCB is unchanged by the notification store: derive its `st1` ipcState.
          have hNe : waiter.toObjId ≠ notificationId := by
            intro hEq; rw [hEq] at hWTcb; rw [hObj] at hWTcb; simp at hWTcb
          have hWTcb1 : st1.objects[waiter.toObjId]? = some (.tcb wTcb) := by
            rw [storeObject_objects_ne st st1 notificationId waiter.toObjId _ hNe hObjInv hSO]; exact hWTcb
          have hNotHead : ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
              st1.objects[epId']? = some (.endpoint ep') →
              ep'.receiveQ.head ≠ some waiter ∧ ep'.sendQ.head ≠ some waiter := by
            intro epId' ep' hEp'
            refine ⟨fun hHd => ?_, fun hHd => ?_⟩
            · have := (hInv1 epId' ep' waiter wTcb hEp' hWTcb1).1 hHd; rw [hWIpc] at this; cases this
            · rcases (hInv1 epId' ep' waiter wTcb hEp' hWTcb1).2 hHd with h | h <;> rw [hWIpc] at h <;> cases h
          exact ensureRunnable_preserves_queueHeadBlockedConsistent st2 waiter
            (storeTcbIpcStateAndMessage_preserves_queueHeadBlockedConsistent
              st1 st2 waiter .ready _ hInv1 hObjInv1 hSM hNotHead)
    | none =>
      simp only [hWaiters] at hStep
      exact storeObject_nonEndpointNonTcb_preserves_queueHeadBlockedConsistent
        st st' notificationId (.notification _) hObjInv (fun _ => by simp) (fun _ => by simp) hInv hStep
  · contradiction
  · contradiction

/-- IPC de-threading D2 (de-threaded): `endpointReceiveDual` preserves `ipcInvariantFull`,
**establishing** the `replyCallerLinkage` third clause rather than threading it.
`allPendingMessagesBounded` / `badgeWellFormed` derived internally. -/
theorem endpointReceiveDual_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver senderId : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (st st' : SystemState)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointReceiveDual endpointId receiver replyId st = .ok (senderId, st')) :
    ipcInvariantFull st' :=
  ⟨endpointReceiveDual_preserves_ipcInvariant st st' endpointId receiver senderId replyId hInv.1 hObjInv hStep,
   hDualQueue',
   endpointReceiveDual_preserves_allPendingMessagesBounded endpointId receiver senderId replyId st st' hInv.2.2.1 hObjInv hStep,
   endpointReceiveDual_preserves_badgeWellFormed endpointId receiver senderId replyId st st' hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI', hDBT',
   endpointReceiveDual_establishes_blockedOnReplyHasTarget st st' endpointId receiver senderId replyId hInv.blockedOnReplyHasTarget hObjInv hStep,
   ⟨hRCLRecip', endpointReceiveDual_establishes_blockedOnReplyHasReplyObject st st' endpointId
      receiver senderId replyId hInv.replyCallerLinkage.2 hObjInv hStep⟩,
   -- IPC de-threading D3: **establish** PRR from the pre-state (was threaded `hPRR'`).
   endpointReceiveDual_preserves_pendingReceiveReplyWellFormed st st' endpointId receiver senderId
     replyId hObjInv hInv.pendingReceiveReplyWellFormed hReplyIdValid hReceiverNotRecv
     hInv.queueHeadBlockedConsistent hStep⟩

/-- IPC de-threading D2 (de-threaded): `endpointCall` preserves `ipcInvariantFull`,
**establishing** the `replyCallerLinkage` third clause rather than threading it.
`allPendingMessagesBounded` / `badgeWellFormed` derived internally. -/
theorem endpointCall_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointCall endpointId caller msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointCall_preserves_ipcInvariant st st' endpointId caller msg hInv.1 hObjInv hStep,
   hDualQueue',
   endpointCall_preserves_allPendingMessagesBounded st st' endpointId caller msg hInv.2.2.1 hObjInv hStep,
   endpointCall_preserves_badgeWellFormed st st' endpointId caller msg hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI', hDBT',
   endpointCall_establishes_blockedOnReplyHasTarget st st' endpointId caller msg hInv.blockedOnReplyHasTarget hObjInv hStep,
   ⟨hRCLRecip', endpointCall_establishes_blockedOnReplyHasReplyObject st st' endpointId caller msg
      hInv.replyCallerLinkage.2 hObjInv hStep⟩,
   -- IPC de-threading D3: **establish** PRR from the pre-state (was threaded `hPRR'`).
   endpointCall_preserves_pendingReceiveReplyWellFormed st st' endpointId caller msg hObjInv
     hInv.pendingReceiveReplyWellFormed hCallerNotRecv hStep⟩

/-- IPC de-threading D2 (de-threaded): `endpointSendDual` preserves `ipcInvariantFull`,
*preserving* the `replyCallerLinkage` third clause (framed — `endpointSendDual` never
introduces a `.blockedOnReply` thread) rather than threading it.
`allPendingMessagesBounded` / `badgeWellFormed` derived internally. -/
theorem endpointSendDual_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (sender : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointSendDual endpointId sender msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointSendDual_preserves_ipcInvariant st st' endpointId sender msg hInv.1 hObjInv hStep,
   hDualQueue',
   endpointSendDual_preserves_allPendingMessagesBounded st st' endpointId sender msg hInv.2.2.1 hObjInv hStep,
   endpointSendDual_preserves_badgeWellFormed st st' endpointId sender msg hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI', hDBT',
   endpointSendDual_preserves_blockedOnReplyHasTarget st st' endpointId sender msg hInv.blockedOnReplyHasTarget hObjInv hStep,
   ⟨hRCLRecip', endpointSendDual_preserves_blockedOnReplyHasReplyObject st st' endpointId sender msg
      hInv.replyCallerLinkage.2 hObjInv hStep⟩,
   endpointSendDual_preserves_pendingReceiveReplyWellFormed st st' endpointId sender msg hObjInv
     hInv.pendingReceiveReplyWellFormed hSenderNotRecv hStep⟩

/-- IPC de-threading D2 (de-threaded): `notificationSignal` preserves `ipcInvariantFull`,
*preserving* the `replyCallerLinkage` third clause (framed) rather than threading it.
All four core components derived internally. -/
theorem notificationSignal_preserves_ipcInvariantFull
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hNWC : notificationWaiterConsistent st)
    (hStep : notificationSignal notificationId badge st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨notificationSignal_preserves_ipcInvariant st st' notificationId badge hInv.1 hObjInv hStep,
   notificationSignal_preserves_dualQueueSystemInvariant st st' notificationId badge hInv.2.1 hObjInv hStep,
   notificationSignal_preserves_allPendingMessagesBounded st st' notificationId badge hInv.2.2.1 hObjInv hStep,
   notificationSignal_preserves_badgeWellFormed st st' notificationId badge hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC',
   -- IPC de-threading D4: queueNext/headBlocked **established** from the pre-state.
   notificationSignal_preserves_queueNextBlockingConsistent st st' notificationId badge hObjInv hInv.queueNextBlockingConsistent hStep,
   notificationSignal_preserves_queueHeadBlockedConsistent st st' notificationId badge hObjInv hInv.queueHeadBlockedConsistent hNWC hStep,
   hBlockedTimeout', donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI', hDBT',
   notificationSignal_preserves_blockedOnReplyHasTarget st st' notificationId badge hObjInv hInv.blockedOnReplyHasTarget hStep,
   ⟨hRCLRecip', notificationSignal_preserves_blockedOnReplyHasReplyObject st st' notificationId badge
      hObjInv hInv.replyCallerLinkage.2 hStep⟩,
   notificationSignal_preserves_pendingReceiveReplyWellFormed st st' notificationId badge hObjInv
     hInv.pendingReceiveReplyWellFormed hNWC hStep⟩

/-- IPC de-threading D2 (de-threaded): `notificationWait` preserves `ipcInvariantFull`,
*preserving* the `replyCallerLinkage` third clause (framed) rather than threading it.
All four core components derived internally. -/
theorem notificationWait_preserves_ipcInvariantFull
    (st st' : SystemState)
    (notificationId : SeLe4n.ObjId) (waiter : SeLe4n.ThreadId)
    (result : Option SeLe4n.Badge)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    -- IPC de-threading D4: `queueHeadBlockedConsistent` remains threaded —
    -- `notificationWait` may re-block a thread that the carried preconditions do
    -- not exclude from being an endpoint queue head (see file note).
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hWaiterNotRecv : ∀ (tcb : TCB), st.getTcb? waiter = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : notificationWait notificationId waiter st = .ok (result, st')) :
    ipcInvariantFull st' :=
  ⟨notificationWait_preserves_ipcInvariant st st' notificationId waiter result hInv.1 hObjInv hStep,
   notificationWait_preserves_dualQueueSystemInvariant st st' notificationId waiter result hInv.2.1 hObjInv hStep,
   notificationWait_preserves_allPendingMessagesBounded st st' notificationId waiter result hInv.2.2.1 hObjInv hStep,
   notificationWait_preserves_badgeWellFormed st st' notificationId waiter result hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC',
   -- IPC de-threading D4: queueNext **established** from the pre-state.
   notificationWait_preserves_queueNextBlockingConsistent st st' notificationId waiter result hObjInv hInv.queueNextBlockingConsistent hStep,
   hQHBC', hBlockedTimeout', donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI', hDBT',
   notificationWait_preserves_blockedOnReplyHasTarget st st' notificationId waiter result hObjInv hInv.blockedOnReplyHasTarget hStep,
   ⟨hRCLRecip', notificationWait_preserves_blockedOnReplyHasReplyObject st st' notificationId waiter
      result hObjInv hInv.replyCallerLinkage.2 hStep⟩,
   notificationWait_preserves_pendingReceiveReplyWellFormed st st' notificationId waiter result hObjInv
     hInv.pendingReceiveReplyWellFormed hWaiterNotRecv hStep⟩

/-- IPC de-threading D2 (de-threaded): `endpointReply` preserves `ipcInvariantFull`,
*preserving* the `replyCallerLinkage` third clause (framed — the reply only unblocks the
target) rather than threading it.  All four core components derived internally. -/
theorem endpointReply_preserves_ipcInvariantFull
    (st st' : SystemState)
    (replier target : SeLe4n.ThreadId) (msg : IpcMessage)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hStep : endpointReply replier target msg st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReply_preserves_ipcInvariant st st' replier target msg hInv.1 hObjInv hStep,
   endpointReply_preserves_dualQueueSystemInvariant replier target msg st st' hObjInv hStep hInv.2.1,
   endpointReply_preserves_allPendingMessagesBounded st st' replier target msg hInv.2.2.1 hObjInv hStep,
   endpointReply_preserves_badgeWellFormed st st' replier target msg hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC',
   -- IPC de-threading D4: queueNext/headBlocked **established** from the pre-state.
   endpointReply_preserves_queueNextBlockingConsistent st st' replier target msg hObjInv hInv.queueNextBlockingConsistent hStep,
   endpointReply_preserves_queueHeadBlockedConsistent st st' replier target msg hObjInv hInv.queueHeadBlockedConsistent hStep,
   -- IPC de-threading D7: `donationChainAcyclic` is **derived** from the (still-threaded)
   -- post-state `donationOwnerValid` via the subsumption lemma — no separate `hDCA'`.
   hBlockedTimeout', donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI', hDBT',
   endpointReply_preserves_blockedOnReplyHasTarget st st' replier target msg hObjInv hInv.blockedOnReplyHasTarget hStep,
   ⟨hRCLRecip', endpointReply_preserves_blockedOnReplyHasReplyObject st st' replier target msg
      hObjInv hInv.replyCallerLinkage.2 hStep⟩,
   endpointReply_preserves_pendingReceiveReplyWellFormed st st' replier target msg hObjInv hInv.pendingReceiveReplyWellFormed hStep⟩

/-- IPC de-threading D2 (de-threaded): `endpointReplyRecv` preserves `ipcInvariantFull`,
*preserving* the `replyCallerLinkage` third clause (the unblock frames it, the receive leg
establishes it) rather than threading it.  `allPendingMessagesBounded` / `badgeWellFormed`
derived internally. -/
theorem endpointReplyRecv_preserves_ipcInvariantFull
    (st st' : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver replyTarget : SeLe4n.ThreadId) (msg : IpcMessage)
    (replyId : Option SeLe4n.ReplyId)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointReplyRecv endpointId receiver replyTarget msg replyId st = .ok ((), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReplyRecv_preserves_ipcInvariant st st' endpointId receiver replyTarget msg hInv.1 hObjInv replyId hStep,
   hDualQueue',
   endpointReplyRecv_preserves_allPendingMessagesBounded st st' endpointId receiver replyTarget msg replyId hInv.2.2.1 hObjInv hStep,
   endpointReplyRecv_preserves_badgeWellFormed st st' endpointId receiver replyTarget msg replyId hInv.2.2.2.1 hObjInv hStep,
   hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI', hDBT',
   endpointReplyRecv_preserves_blockedOnReplyHasTarget st st' endpointId receiver replyTarget msg replyId hObjInv hInv.blockedOnReplyHasTarget hStep,
   ⟨hRCLRecip', endpointReplyRecv_preserves_blockedOnReplyHasReplyObject st st' endpointId receiver
      replyTarget msg replyId hObjInv hInv.replyCallerLinkage.2 hStep⟩,
   -- IPC de-threading D3: **establish** PRR from the pre-state (was threaded `hPRR'`).
   endpointReplyRecv_preserves_pendingReceiveReplyWellFormed st st' endpointId receiver replyTarget
     msg replyId hObjInv hInv.pendingReceiveReplyWellFormed hReplyIdValid hReceiverNotRecv
     hInv.queueHeadBlockedConsistent hStep⟩

/-- IPC de-threading D2 (de-threaded): `endpointSendDualWithCaps` preserves
`ipcInvariantFull`, *preserving* the `replyCallerLinkage` third clause rather than
threading it. -/
theorem endpointSendDualWithCaps_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
             senderCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    ipcInvariantFull st' :=
  ⟨endpointSendDualWithCaps_preserves_ipcInvariant endpointId sender msg
     endpointRights senderCspaceRoot receiverSlotBase st st' summary hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge', hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI', hDBT',
   endpointSendDualWithCaps_preserves_blockedOnReplyHasTarget endpointId sender msg endpointRights senderCspaceRoot receiverSlotBase st st' summary hInv.blockedOnReplyHasTarget hObjInv hStep,
   ⟨hRCLRecip', endpointSendDualWithCaps_preserves_blockedOnReplyHasReplyObject endpointId sender msg
      endpointRights senderCspaceRoot receiverSlotBase st st' summary hInv.replyCallerLinkage.2 hObjInv hStep⟩,
   -- IPC de-threading D3: **preserve** PRR from the pre-state (was threaded `hPRR'`).
   endpointSendDualWithCaps_preserves_pendingReceiveReplyWellFormed endpointId sender msg endpointRights
     senderCspaceRoot receiverSlotBase st st' summary hObjInv hInv.pendingReceiveReplyWellFormed
     hSenderNotRecv hStep⟩

/-- IPC de-threading D2 (de-threaded): `endpointReceiveDualWithCaps` preserves
`ipcInvariantFull`, **establishing** the `replyCallerLinkage` third clause (via the base
receive establish + the cap-transfer frame) rather than threading it. -/
theorem endpointReceiveDualWithCaps_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (receiver : SeLe4n.ThreadId)
    (replyId : Option SeLe4n.ReplyId)
    (endpointRights : AccessRightSet)
    (receiverCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (senderId : SeLe4n.ThreadId) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hReplyIdValid : ∀ rid, replyId = some rid → replyIdEstablishFresh st rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointReceiveDualWithCaps endpointId receiver replyId endpointRights
             receiverCspaceRoot receiverSlotBase st = .ok ((senderId, summary), st')) :
    ipcInvariantFull st' :=
  ⟨endpointReceiveDualWithCaps_preserves_ipcInvariant endpointId receiver replyId endpointRights
     receiverCspaceRoot receiverSlotBase st st' senderId summary hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge', hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI', hDBT',
   endpointReceiveDualWithCaps_establishes_blockedOnReplyHasTarget endpointId receiver replyId endpointRights receiverCspaceRoot receiverSlotBase st st' senderId summary hInv.blockedOnReplyHasTarget hObjInv hStep,
   ⟨hRCLRecip', endpointReceiveDualWithCaps_establishes_blockedOnReplyHasReplyObject endpointId receiver
      replyId endpointRights receiverCspaceRoot receiverSlotBase st st' senderId summary hInv.replyCallerLinkage.2 hObjInv hStep⟩,
   -- IPC de-threading D3: **establish** PRR from the pre-state (was threaded `hPRR'`).
   endpointReceiveDualWithCaps_preserves_pendingReceiveReplyWellFormed endpointId receiver replyId
     endpointRights receiverCspaceRoot receiverSlotBase st st' senderId summary hObjInv
     hInv.pendingReceiveReplyWellFormed hReplyIdValid hReceiverNotRecv
     hInv.queueHeadBlockedConsistent hStep⟩

/-- IPC de-threading D2 (de-threaded): `endpointCallWithCaps` preserves `ipcInvariantFull`,
**establishing** the `replyCallerLinkage` third clause (via the base call establish + the
cap-transfer frame) rather than threading it. -/
theorem endpointCallWithCaps_preserves_ipcInvariantFull
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (callerCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary)
    (hInv : ipcInvariantFull st)
    (hObjInv : st.objects.invExt)
    (hDualQueue' : dualQueueSystemInvariant st')
    (hBounded' : allPendingMessagesBounded st')
    (hBadge' : badgeWellFormed st')
    (hWtpmn' : waitingThreadsPendingMessageNone st')
    (hNoDup' : endpointQueueNoDup st')
    (hQMC' : ipcStateQueueMembershipConsistent st')
    (hQNBC' : queueNextBlockingConsistent st')
    (hQHBC' : queueHeadBlockedConsistent st')
    (hBlockedTimeout' : blockedThreadTimeoutConsistent st')
    (hDOV' : donationOwnerValid st')
    (hPSI' : passiveServerIdle st')
    (hDBT' : donationBudgetTransfer st')
    (hRCLRecip' : replyCallerLinkageReciprocal st')
    (hCallerNotRecv : ∀ (tcb : TCB), st.getTcb? caller = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hStep : endpointCallWithCaps endpointId caller msg endpointRights
             callerCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    ipcInvariantFull st' :=
  ⟨endpointCallWithCaps_preserves_ipcInvariant endpointId caller msg
     endpointRights callerCspaceRoot receiverSlotBase st st' summary hInv.1 hObjInv hStep,
   hDualQueue', hBounded', hBadge', hWtpmn', hNoDup', hQMC', hQNBC', hQHBC', hBlockedTimeout', donationOwnerValid_implies_donationChainAcyclic st' hDOV', hDOV', hPSI', hDBT',
   endpointCallWithCaps_establishes_blockedOnReplyHasTarget endpointId caller msg endpointRights callerCspaceRoot receiverSlotBase st st' summary hInv.blockedOnReplyHasTarget hObjInv hStep,
   ⟨hRCLRecip', endpointCallWithCaps_establishes_blockedOnReplyHasReplyObject endpointId caller msg
      endpointRights callerCspaceRoot receiverSlotBase st st' summary hInv.replyCallerLinkage.2 hObjInv hStep⟩,
   -- IPC de-threading D3: **establish** PRR from the pre-state (was threaded `hPRR'`).
   endpointCallWithCaps_preserves_pendingReceiveReplyWellFormed endpointId caller msg endpointRights
     callerCspaceRoot receiverSlotBase st st' summary hObjInv hInv.pendingReceiveReplyWellFormed
     hCallerNotRecv hStep⟩

end SeLe4n.Kernel
