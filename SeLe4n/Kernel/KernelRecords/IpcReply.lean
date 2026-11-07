-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcCall

/-!
# The reply keeps the records

WS-ZA ZA6.37.  A reply makes its target `.ready` out of `.blockedOnReply`, a
parked state, so the reply leg keeps every *other* thread's fault record parked
(`RecordsStepOff`) and leaves the target's fault record where it was.  The plain
reply answers a target carrying no fault (`replyTransferOnCoreChecked` routes a
faulted one to the fault reply), so it is a `RecordsStep`; the fault reply
clears the record it answers, so it is one too.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsFrame

/-- A reply stored over a slot that held a reply when the frame began. -/
theorem storeReplyOver {st s s' : SystemState} (F : RecordsFrame st s) {k : SeLe4n.ObjId}
    {r r' : Reply} (hR : st.objects[k]? = some (.reply r))
    (h : SeLe4n.Model.storeObject k (.reply r') s = .ok ((), s')) : RecordsFrame st s' :=
  F.trans (storeObject_noView F.invExt h rfl (by rw [F.views, hR]; rfl))

theorem storeReplyOverId {st s s' : SystemState} (F : RecordsFrame st s) {rid : SeLe4n.ReplyId}
    {r r' : Reply} (hR : st.getReply? rid = some r)
    (h : SeLe4n.Model.storeObject rid.toObjId (.reply r') s = .ok ((), s')) : RecordsFrame st s' :=
  storeReplyOver F ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) h

theorem cutFrameBelow?_reply {st : SystemState} {rid above below : SeLe4n.ReplyId} {r b : Reply}
    (h : cutFrameBelow? st rid r above = some (below, b)) : st.getReply? below = some b := by
  unfold cutFrameBelow? at h
  split at h
  · cases h
  · split at h
    · cases h
    · split at h
      · cases h
      · rename_i b' hb; split at h
        · cases h
        · cases h; exact hb

theorem cutReplyFrameOut {st st' : SystemState} {rid : SeLe4n.ReplyId}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.cutReplyFrameOut st rid = .ok st') :
    RecordsFrame st st' := by
  rcases cutReplyFrameOut_cases h with rfl | ⟨r, above, a, hR, -, hA, -, hS⟩ |
      ⟨r, below, b, hR, -, -, hB, -, hS⟩
  · exact refl hInv
  · rcases cutReplyFrameStores_cases hS with ⟨s1, -, h1, h2⟩ |
        ⟨below, b, s1, s2, hc, h1, h2, h3⟩
    · exact storeReplyOverId (storeReplyOverId (refl hInv) hA h1) hR h2
    · exact storeReplyOverId (storeReplyOverId (storeReplyOverId (refl hInv) hA h1)
        (cutFrameBelow?_reply hc) h2) hR h3
  · obtain ⟨s1, h1, h2⟩ := severReplyFrameBelowStores_cases hS
    exact storeReplyOverId (storeReplyOverId (refl hInv) hB h1) hR h2

theorem cutReplyFrameOutOrSelf (st : SystemState) (rid : SeLe4n.ReplyId)
    (hInv : st.objects.invExt) : RecordsFrame st (_root_.SeLe4n.Kernel.cutReplyFrameOutOrSelf st rid) := by
  rcases cutReplyFrameOutOrSelf_cases st rid with h | h
  · rw [h]; exact refl hInv
  · exact cutReplyFrameOut hInv h

theorem consumeReply {st st' : SystemState} {rid : SeLe4n.ReplyId} (hInv : st.objects.invExt)
    (h : SystemState.consumeReply rid st = .ok ((), st')) : RecordsFrame st st' := by
  unfold SystemState.consumeReply at h
  split at h
  · rename_i r hR; exact storeReplyAt hInv hR h
  · cases h; exact refl hInv

theorem consumeCallerReply {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {st st' : SystemState}
    (hInv : st.objects.invExt) (h : SystemState.consumeCallerReply caller rid st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold SystemState.consumeCallerReply at h
  cases h1 : SystemState.consumeReply rid st with
  | error e => simp [h1] at h
  | ok p =>
    obtain ⟨⟨⟩, s1⟩ := p
    simp only [h1] at h
    have F1 := consumeReply hInv h1
    cases hT : s1.getTcb? caller with
    | none => simp only [hT] at h; cases h; exact F1
    | some tcb =>
      simp only [hT] at h
      exact F1.trans (storeObject F1.invExt h
        (by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT]; rfl) (fun _ h => by cases h))

theorem removeCallerReplyFrame {caller : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.removeCallerReplyFrame caller rid st = .ok ((), st')) :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.removeCallerReplyFrame at h
  have F1 := cutReplyFrameOutOrSelf st rid hInv
  exact F1.trans (consumeCallerReply F1.invExt h)

/-- The returned context settled: its release link purged and placed. -/
theorem settleReturnedContext (st : SystemState) (c : CoreId) (scId : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) :
    RecordsFrame st (SchedContextOps.settleReturnedContext st c scId) :=
  of_agreeOffReleaseLinks (SchedContextOps.settleReturnedContext_agree st c scId)
    (by
      have h := congrArg SystemState.asidTable
        (SchedContextOps.settleReturnedContext_releaseOnlyWrite st c scId).1
      exact h)
    (SchedContextOps.settleReturnedContext_objects_invExt st c scId hInv)
    (by
      have h := congrArg (fun x : SystemState => x.machine.physicalAddressWidth)
        (SchedContextOps.settleReturnedContext_releaseOnlyWrite st c scId).1
      exact h)

theorem descheduleAt (st : SystemState) (t : SeLe4n.ThreadId) (p : Option CoreId)
    (hInv : st.objects.invExt) : RecordsFrame st (_root_.SeLe4n.Kernel.descheduleAt st t p) := by
  unfold _root_.SeLe4n.Kernel.descheduleAt
  split
  · exact removeRunnableOnCore _ _ _ hInv
  · exact refl hInv

theorem descheduleAtPlacement (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.descheduleAtPlacement st t) :=
  descheduleAt _ _ _ hInv

theorem returnUnheldSchedContext {st st' : SystemState} {scId : SeLe4n.SchedContextId}
    {owner : SeLe4n.ThreadId} {newOwner? : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.returnUnheldSchedContext st scId owner newOwner? = .ok st') :
    RecordsFrame st st' := by
  obtain ⟨sc, head?, ot, s1, s2, s3, hSc, -, -, -, -, hS1, hS2, hL, hS3, rfl⟩ :=
    returnUnheldSchedContext_ok_storeChain st st' scId owner newOwner? h
  have F1 := storeSchedContext hInv hSc hS1
  have F2 := F1.trans (storeDonationHeadPop F1.invExt hS2)
  have F3 := F2.trans (storeTcbBinding F2.invExt hL hS3)
  exact F3.trans (markKeyChangeFrom _ _ _ F3.invExt)

theorem severUnheldSchedContext {st st' : SystemState} {scId : SeLe4n.SchedContextId}
    {newOwner? : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.severUnheldSchedContext st scId newOwner? = .ok st') :
    RecordsFrame st st' := by
  obtain ⟨sc, head?, s1, hSc, -, -, hS1, hS2⟩ := severUnheldSchedContext_ok_storeChain h
  have F1 := storeSchedContext hInv hSc hS1
  exact F1.trans (storeDonationHeadPop F1.invExt hS2)

theorem popUnheldReplyHead {st st' : SystemState} {rid : SeLe4n.ReplyId} {target : SeLe4n.ThreadId}
    {home : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.popUnheldReplyHead st rid target home = .ok st') :
    RecordsFrame st st' := by
  rcases popUnheldReplyHead_objects_frame h with ⟨-, rfl⟩ | ⟨_, _, st1, -, -, hP, rfl⟩ |
      ⟨_, _, -, -, hS⟩
  · exact refl hInv
  · have F := returnUnheldSchedContext hInv hP
    exact F.trans (settleReturnedContext _ _ _ F.invExt)
  · exact severUnheldSchedContext hInv hS

/-- **The reply's donation return keeps every record view.** -/
theorem applyReplyDonationOnCore {st st' : SystemState} {rid : SeLe4n.ReplyId}
    {targetVtid : SeLe4n.ValidThreadId} {ownerHome : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.applyReplyDonationOnCore st rid targetVtid ownerHome = .ok st') :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.applyReplyDonationOnCore at h
  dsimp only at h
  split at h
  · exact popUnheldReplyHead hInv h
  · split at h
    · split at h
      · cases h
      · rename_i st1 hRet
        cases h
        have F1 := returnDonatedSchedContextResolved hInv hRet
        refine F1.trans ((settleReturnedContext _ _ _ F1.invExt).trans
          (descheduleAtPlacement _ _ ?_))
        exact SchedContextOps.settleReturnedContext_objects_invExt _ _ _ F1.invExt
    · cases h

end RecordsFrame

-- ============================================================================
-- The step off one thread
-- ============================================================================

/-- A thread carrying no fault record, read on a state. -/
def NoFaultAt (st : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∀ x, st.getTcb? t = some x → x.pendingFault = none

theorem NoFaultAt.frame {st st' : SystemState} (F : RecordsFrame st st') {t : SeLe4n.ThreadId}
    (h : NoFaultAt st t) : NoFaultAt st' t := fun x hx => by
  obtain ⟨y, hy, hv⟩ := F.getTcb?_view hx
  have hf : y.pendingFault.isSome = x.pendingFault.isSome := congrArg TcbRecordView.faulted hv
  rw [h y hy] at hf
  cases hx' : x.pendingFault with
  | none => rfl
  | some _ => rw [hx'] at hf; cases hf

/-- **A step that keeps the address-space records and every fault record parked
except, perhaps, thread `t`'s**: the reply leg, which unparks its target. -/
structure RecordsStepOff (t : SeLe4n.ThreadId) (st st' : SystemState) : Prop where
  rootViews : ∀ k : SeLe4n.ObjId, rootViewOf st'.objects[k]? = rootViewOf st.objects[k]?
  asid : st'.asidTable = st.asidTable
  invExt : st'.objects.invExt
  others : ∀ u tcb', u.toObjId ≠ t.toObjId → st'.getTcb? u = some tcb' → tcb'.pendingFault.isSome →
    (∀ tcb, st.getTcb? u = some tcb → tcb.pendingFault.isSome → tcb.faultParked) → tcb'.faultParked
  width : st'.machine.physicalAddressWidth = st.machine.physicalAddressWidth

namespace RecordsStepOff

theorem of_step {t : SeLe4n.ThreadId} {st st' : SystemState} (S : RecordsStep st st') :
    RecordsStepOff t st st' :=
  ⟨S.rootViews, S.asid, S.invExt, fun u tcb' _ hT hF H => S.faults u tcb' hT hF H, S.width⟩

theorem trans {t : SeLe4n.ThreadId} {a b c : SystemState} (h₁ : RecordsStepOff t a b)
    (h₂ : RecordsStepOff t b c) : RecordsStepOff t a c :=
  ⟨fun k => (h₂.rootViews k).trans (h₁.rootViews k), h₂.asid.trans h₁.asid, h₂.invExt,
    fun u tcb' hne hT hF H => h₂.others u tcb' hne hT hF (fun x hx hxF => h₁.others u x hne hx hxF H),
    h₂.width.trans h₁.width⟩

/-- Closed by a state where the thread carries no fault record. -/
theorem close {t : SeLe4n.ThreadId} {st st' : SystemState} (S : RecordsStepOff t st st')
    (hT : NoFaultAt st' t) : RecordsStep st st' :=
  ⟨S.rootViews, S.asid, S.invExt, fun u tcb' hU hF H => by
    by_cases hk : u.toObjId = t.toObjId
    · have hu : u = t := SeLe4n.ThreadId.toObjId_injective _ _ hk
      subst hu; rw [hT tcb' hU] at hF; cases hF
    · exact S.others u tcb' hk hU hF H, S.width⟩

/-- A store of thread `t`'s TCB over its TCB. -/
theorem storeObject_self {st st' : SystemState} {t : SeLe4n.ThreadId} {x y : TCB}
    (hInv : st.objects.invExt) (hOld : st.objects[t.toObjId]? = some (.tcb x))
    (h : storeObject t.toObjId (.tcb y) st = .ok ((), st')) : RecordsStepOff t st st' := by
  refine ⟨fun k => ?_, ?_, storeObject_preserves_objects_invExt st st' _ _ hInv h, ?_,
    by rw [storeObject_machine_eq st st' _ _ h]⟩
  · by_cases hk : k = t.toObjId
    · subst hk; rw [storeObject_objects_eq st st' _ _ hInv h, hOld]; rfl
    · rw [storeObject_objects_ne st st' _ k _ hk hInv h]
  · rw [storeObject_asidTable_non_vspaceRoot st st' _ _ (fun _ => by simp) h, hOld]
  · intro u tcb' hne hT hF H
    have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    rw [storeObject_objects_ne st st' _ _ _ hne hInv h] at hO
    exact H tcb' ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hO) hF

end RecordsStepOff

/-- **The reply leg's step**: off its target always, and a records step from a
state where the target carries no fault record. -/
def ReplyLegStep (t : SeLe4n.ThreadId) (st st' : SystemState) : Prop :=
  RecordsStepOff t st st' ∧ (NoFaultAt st t → RecordsStep st st')

namespace ReplyLegStep

theorem of_step {t : SeLe4n.ThreadId} {st st' : SystemState} (S : RecordsStep st st') :
    ReplyLegStep t st st' := ⟨.of_step S, fun _ => S⟩

theorem trans_step {t : SeLe4n.ThreadId} {a b c : SystemState} (A : ReplyLegStep t a b)
    (S : RecordsStep b c) : ReplyLegStep t a c :=
  ⟨A.1.trans (.of_step S), fun h => (A.2 h).trans S⟩

theorem frame_trans {t : SeLe4n.ThreadId} {a b c : SystemState} (F : RecordsFrame a b)
    (A : ReplyLegStep t b c) : ReplyLegStep t a c :=
  ⟨(RecordsStepOff.of_step (.of_frame F)).trans A.1,
    fun h => (RecordsStep.of_frame F).trans (A.2 (h.frame F))⟩

/-- The target's TCB stored over its TCB with its fault record kept. -/
theorem storeObject_self {st st' : SystemState} {t : SeLe4n.ThreadId} {x y : TCB}
    (hInv : st.objects.invExt) (hOld : st.objects[t.toObjId]? = some (.tcb x))
    (h : storeObject t.toObjId (.tcb y) st = .ok ((), st')) (hpf : y.pendingFault = x.pendingFault) :
    ReplyLegStep t st st' :=
  ⟨.storeObject_self hInv hOld h, fun hN => RecordsStep.storeObject_tcb hInv hOld h
    (TcbStaysParked.of_noFault (by
      rw [hpf]; exact hN x ((SystemState.getTcb?_eq_some_iff _ _ _).mpr hOld)))⟩

/-- **The per-core reply leg.** -/
theorem endpointReplyOnCore {replier target : SeLe4n.ThreadId} {msg : IpcMessage} {c : CoreId}
    {st : SystemState} (hInv : st.objects.invExt) :
    ReplyLegStep target st (_root_.SeLe4n.Kernel.endpointReplyOnCore replier target msg c st).1 := by
  have hRefl : ReplyLegStep target st st := of_step (RecordsStep.refl hInv)
  unfold _root_.SeLe4n.Kernel.endpointReplyOnCore
  split
  · exact hRefl
  split
  · exact hRefl
  · rename_i tcb hL
    have hO := lookupTcb_some_objects _ _ _ hL
    split
    · split
      · exact hRefl
      · rename_i st1 hS
        unfold storeTcbIpcStateAndMessage_fromTcb at hS
        revert hS
        cases hSt : SeLe4n.Model.storeObject target.toObjId
            (.tcb (TCB.setIpcState { tcb with pendingMessage := some msg } .ready)) st with
        | error _ => intro h; cases h
        | ok p =>
          obtain ⟨⟨⟩, s⟩ := p
          intro h
          have he := Except.ok.inj h
          subst he
          have A1 := storeObject_self hInv hO hSt (by simp)
          have F2 := RecordsFrame.wakeThread s target c A1.1.invExt (fun y hy => by
            rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr
              (storeObject_objects_eq st s _ _ hInv hSt)] at hy
            cases hy; simp)
          have A2 := A1.trans_step (.of_frame F2)
          split
          · exact A2.trans_step (RecordsStep.unlinkReplyWaiterOpt _ _ _ F2.invExt)
          · split
            · rename_i st2 hR
              have F3 := RecordsFrame.removeCallerReplyFrame F2.invExt hR
              exact (A2.trans_step (.of_frame F3)).trans_step
                (RecordsStep.unlinkReplyWaiterOpt _ _ _ F3.invExt)
            · exact hRefl
    · exact hRefl


theorem endpointReplyCrossCoreDispatch {replier target : SeLe4n.ThreadId} {msg : IpcMessage}
    {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    ReplyLegStep target st
      (_root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch replier target msg c st).1 := by
  have hRefl : ReplyLegStep target st st := of_step (RecordsStep.refl hInv)
  unfold _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch
  have A := endpointReplyOnCore (replier := replier) (target := target) (msg := msg) (c := c) hInv
  generalize _root_.SeLe4n.Kernel.endpointReplyOnCore replier target msg c st = r at A
  obtain ⟨st1, res⟩ := r
  dsimp only at A ⊢
  cases res with
  | error _ => exact hRefl
  | ok sgi =>
    dsimp only
    repeat' split
    all_goals first
      | exact hRefl
      | exact A
      | exact A.trans_step (.of_frame (RecordsFrame.propagatePipChainCrossCore _ _ _ _ A.1.invExt))
      | (rename_i hD
         have F := RecordsFrame.applyReplyDonationOnCore A.1.invExt hD
         exact A.trans_step (.of_frame (F.trans
           (RecordsFrame.propagatePipChainCrossCore _ _ _ _ F.invExt))))
      | (rename_i hD
         exact A.trans_step (.of_frame (RecordsFrame.applyReplyDonationOnCore A.1.invExt hD)))

theorem endpointReplyCrossCoreDispatchChecked {ctx : LabelingContext}
    {replier target : SeLe4n.ThreadId} {msg : IpcMessage} {c : CoreId} {st : SystemState}
    (hInv : st.objects.invExt) :
    ReplyLegStep target st
      (_root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked ctx replier target msg c st).1 := by
  unfold _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked
  split
  · exact endpointReplyCrossCoreDispatch hInv
  · exact of_step (RecordsStep.refl hInv)

end ReplyLegStep

namespace RecordsStep

/-- The decoded outcome applied: a restart or an abandon, each clearing the
fault record it answers. -/
theorem faultReplyApplyOnCore (st : SystemState) (t : SeLe4n.ThreadId)
    (outcome : Architecture.FaultReplyOutcome) (hInv : st.objects.invExt) :
    RecordsStep st (_root_.SeLe4n.Kernel.faultReplyApplyOnCore st t outcome) ∧
      NoFaultAt (_root_.SeLe4n.Kernel.faultReplyApplyOnCore st t outcome) t := by
  unfold _root_.SeLe4n.Kernel.faultReplyApplyOnCore
  split
  · unfold applyFaultRestart
    refine ⟨updateTcb st t hInv (fun x _ => TcbStaysParked.of_noFault
      (TCB.pendingFault_setPendingFault _ none)), fun y hy => ?_⟩
    rw [SystemState.updateTcb_getTcb?_self _ _ _ hInv] at hy
    cases hT : st.getTcb? t with
    | none => rw [hT] at hy; cases hy
    | some x => rw [hT] at hy; cases hy; exact TCB.pendingFault_setPendingFault _ none
  · unfold faultAbandonOnCore
    have F := RecordsFrame.removeRunnableOnCore st t (faultAbandonCore st t) hInv
    refine ⟨(of_frame F).trans (updateTcb _ t F.invExt
      (fun x _ => TcbStaysParked.of_noFault
        (TCB.pendingFault_setPendingFault _ none))), fun y hy => ?_⟩
    rw [SystemState.updateTcb_getTcb?_self _ _ _ F.invExt] at hy
    cases hT : (removeRunnableOnCore st t (faultAbandonCore st t)).getTcb? t with
    | none => rw [hT] at hy; cases hy
    | some x => rw [hT] at hy; cases hy; exact TCB.pendingFault_setPendingFault _ none

/-- **The fault reply keeps the records**: the reply chain unparks the faulted
thread and the outcome clears its record. -/
theorem faultReplyOnCore {replier faulted : SeLe4n.ThreadId} {mi : MessageInfo}
    {regs : Array SeLe4n.RegValue} {c : CoreId} {st : SystemState} (hInv : st.objects.invExt) :
    RecordsStep st (_root_.SeLe4n.Kernel.faultReplyOnCore replier faulted mi regs c st).1 := by
  unfold _root_.SeLe4n.Kernel.faultReplyOnCore
  split
  · exact refl hInv
  · split
    · exact refl hInv
    · dsimp only
      have A := ReplyLegStep.endpointReplyCrossCoreDispatch (replier := replier) (target := faulted)
        (msg := IpcMessage.empty) (c := c) hInv
      generalize _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatch replier faulted
        IpcMessage.empty c st = r at A
      obtain ⟨st1, res⟩ := r
      dsimp only at A ⊢
      cases res with
      | error _ => exact refl hInv
      | ok sgi =>
        dsimp only
        obtain ⟨S, hN⟩ := faultReplyApplyOnCore st1 faulted _ A.1.invExt
        exact (A.1.trans (.of_step S)).close hN

/-- **The reply transfer keeps the records**: a faulted caller through the fault
reply, any other through the checked reply leg from a state where it carries no
fault record. -/
theorem replyTransferOnCoreChecked {ctx : LabelingContext} {replier callerTid : SeLe4n.ThreadId}
    {mi : MessageInfo} {regs : Array SeLe4n.RegValue} {msg : IpcMessage} {c : CoreId}
    {st st' : SystemState} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.replyTransferOnCoreChecked ctx replier callerTid mi regs msg c st
      = .ok ((), st')) : RecordsStep st st' := by
  unfold _root_.SeLe4n.Kernel.replyTransferOnCoreChecked at h
  split at h
  · have S := faultReplyOnCore (replier := replier) (faulted := callerTid) (mi := mi)
      (regs := regs) (c := c) hInv
    generalize _root_.SeLe4n.Kernel.faultReplyOnCore replier callerTid mi regs c st = r at S h
    obtain ⟨st1, res⟩ := r
    cases res with
    | error _ => cases h
    | ok _ => cases h; exact S
  · rename_i hNF
    have hN : NoFaultAt st callerTid := fun x hx => by
      unfold threadHasPendingFault at hNF
      rw [hx] at hNF
      simpa using hNF
    have A := ReplyLegStep.endpointReplyCrossCoreDispatchChecked (ctx := ctx) (replier := replier)
      (target := callerTid) (msg := msg) (c := c) hInv
    generalize _root_.SeLe4n.Kernel.endpointReplyCrossCoreDispatchChecked ctx replier callerTid
      msg c st = r at A h
    obtain ⟨st1, res⟩ := r
    cases res with
    | error _ => cases h
    | ok _ =>
      cases h
      have S := A.2 hN
      exact S.trans (of_frame (RecordsFrame.stageDeliveredMessage _ _ _ S.invExt))

end RecordsStep


end SeLe4n.Kernel
