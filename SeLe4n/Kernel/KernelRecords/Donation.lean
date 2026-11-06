-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.KernelRecords.IpcPrimitives
import SeLe4n.Kernel.SchedContext.ReplenishAffinity
import SeLe4n.Kernel.IPC.CrossCore.ReplyWaitersPreservation

/-!
# The donation writes keep the records' reads

WS-ZA ZA6.37.  Handing a donated scheduling context back writes the context, the
reply stack's head, and two threads' binding codes, then raises reschedule
flags; a replenishment migration moves the context's release link.  None of it
is a thread's record view, a root, or the ASID table, so each is a
`RecordsFrame`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

namespace RecordsFrame

/-- The release-link edits write contexts and the scheduler only. -/
theorem _root_.SeLe4n.Model.SystemState.releaseRemoveOn_asidTable (st : SystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) : (st.releaseRemoveOn c s).asidTable = st.asidTable := by
  unfold SystemState.releaseRemoveOn SystemState.releaseUnlinkOn
  split
  · dsimp only; split <;> rfl
  · rfl

theorem _root_.SeLe4n.Model.SystemState.releaseInsertOn_asidTable (st : SystemState) (c : CoreId)
    (s : SeLe4n.SchedContextId) (t : Nat) : (st.releaseInsertOn c s t).asidTable = st.asidTable := by
  unfold SystemState.releaseInsertOn SystemState.releaseInsertFresh SystemState.releaseLinkIn
  split
  · rfl
  · dsimp only; split <;> rfl

/-- A key-change mark raises reschedule flags only. -/
theorem markKeyChangeFrom (pre st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : RecordsFrame st (_root_.SeLe4n.Kernel.markKeyChangeFrom pre st t) :=
  of_objects_eq hInv (markKeyChangeFrom_objects pre st t) (markKeyChangeFrom_asidTable pre st t)

/-- A reply re-linked by its id. -/
theorem storeReplyAt {st st' : SystemState} {rid : SeLe4n.ReplyId} {r r' : Reply}
    (hInv : st.objects.invExt) (hR : st.getReply? rid = some r)
    (h : SeLe4n.Model.storeObject rid.toObjId (.reply r') st = .ok ((), st')) :
    RecordsFrame st st' :=
  storeReply hInv ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) h

theorem storeDonationHeadClear {st st' : SystemState} {rid? : Option SeLe4n.ReplyId}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.storeDonationHeadClear rid? st = .ok st') :
    RecordsFrame st st' := by
  cases rid? with
  | none => cases h; exact refl hInv
  | some rid =>
    rw [storeDonationHeadClear_some] at h
    revert h
    cases hR : st.getReply? rid with
    | none => intro h; cases h
    | some r =>
      dsimp only
      cases hS : SeLe4n.Model.storeObject rid.toObjId (.reply { r with prev := none, next := none }) st with
      | error e => intro h; cases h
      | ok p => intro h; cases h; exact storeReplyAt hInv hR hS

theorem storeReplyReHead {st st' : SystemState} {scId : SeLe4n.SchedContextId}
    {rid? : Option SeLe4n.ReplyId}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.storeReplyReHead scId rid? st = .ok st') :
    RecordsFrame st st' := by
  cases rid? with
  | none => cases h; exact refl hInv
  | some rid =>
    rw [storeReplyReHead_some] at h
    revert h
    cases hR : st.getReply? rid with
    | none => intro h; cases h
    | some r =>
      dsimp only
      cases hS : SeLe4n.Model.storeObject rid.toObjId (.reply { r with next := some (.head scId) }) st with
      | error e => intro h; cases h
      | ok p => intro h; cases h; exact storeReplyAt hInv hR hS

theorem storeDonationHeadPop {st st' : SystemState} {scId : SeLe4n.SchedContextId}
    {head? : Option (SeLe4n.ReplyId × Reply)}
    (hInv : st.objects.invExt) (h : _root_.SeLe4n.Kernel.storeDonationHeadPop scId head? st = .ok st') :
    RecordsFrame st st' := by
  rcases storeDonationHeadPop_cases h with ⟨-, rfl⟩ | ⟨rid, r, s1, -, h1, h2⟩
  · exact refl hInv
  · have F1 := storeDonationHeadClear hInv h1
    exact F1.trans (storeReplyReHead F1.invExt h2)

/-- A thread's binding codes rewritten. -/
theorem storeTcbBinding {st st' : SystemState} {t : SeLe4n.ThreadId} {x : TCB} {c o : Nat}
    (hInv : st.objects.invExt) (hL : lookupTcb st t = some x)
    (h : SeLe4n.Model.storeObject t.toObjId
      (.tcb { x with scBindingScCode := c, scBindingOwnerCode := o }) st = .ok ((), st')) :
    RecordsFrame st st' :=
  storeObject hInv h (by rw [lookupTcb_some_objects st t x hL]; rfl) (fun _ h => by cases h)

/-- **The donation return keeps every record view.** -/
theorem returnDonatedSchedContext {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId}
    {newOwner? : Option SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.returnDonatedSchedContext st serverTid scId originalOwner newOwner?
      = .ok st') : RecordsFrame st st' := by
  obtain ⟨sc, head?, clientTcb, serverTcb, s1, s2, s3, s4,
    hSc, _, _, _, hS1, hClear, hL1, hS3, hL2, hS4, hEq⟩ :=
    returnDonatedSchedContext_ok_storeChain st st' serverTid scId originalOwner newOwner? h
  have F1 := storeSchedContext hInv hSc hS1
  have F2 := F1.trans (storeDonationHeadPop F1.invExt hClear)
  have F3 := F2.trans (storeTcbBinding F2.invExt hL1 hS3)
  have F4 := F3.trans (storeTcbBinding F3.invExt hL2 hS4)
  exact F4.congr (by rw [hEq]) (by rw [hEq])

theorem returnDonatedSchedContextResolved {st st' : SystemState} {serverTid : SeLe4n.ThreadId}
    {scId : SeLe4n.SchedContextId} {originalOwner : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.returnDonatedSchedContextResolved st serverTid scId originalOwner
      = .ok st') : RecordsFrame st st' := by
  obtain ⟨_, -, hR⟩ := returnDonatedSchedContextResolved_ok_decompose h
  exact returnDonatedSchedContext hInv hR

theorem cleanupPreReceiveDonationChecked {st st' : SystemState} {receiver : SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.cleanupPreReceiveDonationChecked st receiver = .ok st') :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.cleanupPreReceiveDonationChecked at h
  split at h
  · cases h; exact refl hInv
  · split at h
    · exact returnDonatedSchedContextResolved hInv h
    · cases h; exact refl hInv

/-- The replenishment migration moves a release link only. -/
theorem migrateSchedContextReplenishment (st : SystemState) (scId : SeLe4n.SchedContextId)
    (fromCore toCore : CoreId) (hInv : st.objects.invExt) :
    RecordsFrame st (_root_.SeLe4n.Kernel.migrateSchedContextReplenishment st scId fromCore toCore) :=
  of_agreeOffReleaseLinks (migrateSchedContextReplenishment_agree st scId fromCore toCore)
    (by
      unfold _root_.SeLe4n.Kernel.migrateSchedContextReplenishment
      split
      · rfl
      · dsimp only; split
        · show (((st.releaseRemoveOn fromCore scId).releaseInsertOn toCore scId _)).asidTable = _
          rw [SystemState.releaseInsertOn_asidTable, SystemState.releaseRemoveOn_asidTable]
        · rfl)
    (migrateSchedContextReplenishment_preserves_objects_invExt st scId fromCore toCore hInv)

theorem cleanupPreReceiveDonationMigrated {st st' : SystemState} {receiver : SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.cleanupPreReceiveDonationMigrated st receiver = .ok st') :
    RecordsFrame st st' := by
  obtain ⟨stClean, hC, rfl⟩ := cleanupPreReceiveDonationMigrated_ok_decompose h
  have F1 := cleanupPreReceiveDonationChecked hInv hC
  unfold preReceiveReturnMigration
  split
  · exact F1.trans (migrateSchedContextReplenishment _ _ _ _ F1.invExt)
  · exact F1

/-- **The priority-inheritance chain walk keeps every record view**: it writes
threads' boosts and run links, and the scheduler. -/
theorem propagatePipChainCrossCore (st : SystemState) (t : SeLe4n.ThreadId) (ec : CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    RecordsFrame st (PriorityInheritance.propagatePipChainCrossCore st t ec fuel).1 := by
  refine ⟨fun k => ?_, asid_of_onlyObjectsScheduler
    (propagatePipChainCrossCore_onlyObjectsSchedulerDiffer fuel st t ec),
    PriorityInheritance.propagatePipChainCrossCore_preserves_objects_invExt st t ec fuel hInv⟩
  rcases PriorityInheritance.propagatePipChainCrossCore_objects_pointwise fuel st t ec hInv k with
    e | ⟨pre, post, hPre, hPost, -⟩
  · rw [e]
  · obtain ⟨tcb, p, hT, hw⟩ := PriorityInheritance.propagatePipChainCrossCore_tcb_backward st t ec
      fuel hInv ⟨k.val⟩ post hPost
    have hk : (⟨k.val⟩ : SeLe4n.ThreadId).toObjId = k := rfl
    rw [hk, hPre] at hT; cases hT
    have hR := congrFun (propagatePipChainCrossCore_replyViews_eq st t ec fuel hInv) k
    unfold SystemState.replyViews SystemState.getObject? at hR
    simp only [RHTable_getElem?_eq_get?] at hR
    rw [← RHTable_getElem?_eq_get?, ← RHTable_getElem?_eq_get?, hPost, hPre] at hR
    simp only [objReplyView_tcb, Option.some.injEq] at hR
    rw [hPost, hPre, recordViewOf_tcb, recordViewOf_tcb]
    unfold TCB.recordView
    rw [hR, TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hw,
      TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState hw,
      TCB.proj_eq_of_withoutRunLinks_eq (fun x => x.pendingFault.isSome) hw]

/-- A store of an object with no record view over a slot with none. -/
theorem storeObject_noView {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (ho : recordViewOf (some o) = none) (hk : recordViewOf st.objects[k]? = none) :
    RecordsFrame st st' :=
  storeObject hInv h (ho.trans hk.symm) (fun r hr => by subst hr; simp [recordViewOf] at ho)

/-- The frame push writes two replies. -/
theorem storeDonationFramePush {st st' : SystemState} {scId : SeLe4n.SchedContextId}
    {pushRid : SeLe4n.ReplyId} {pushReply : Reply} {oldHead? : Option SeLe4n.ReplyId}
    (hInv : st.objects.invExt) (hk : recordViewOf st.objects[pushRid.toObjId]? = none)
    (h : _root_.SeLe4n.Kernel.storeDonationFramePush scId pushRid pushReply oldHead? st = .ok st') :
    RecordsFrame st st' := by
  obtain ⟨-, s1, h1, hRest⟩ := storeDonationFramePush_cases h
  have F1 := storeObject_noView hInv h1 rfl hk
  rcases hRest with ⟨-, rfl⟩ | ⟨old, oldR, -, hR, h2⟩
  · exact F1
  · exact F1.trans (storeReplyAt F1.invExt hR h2)

/-- **The donation lend keeps every record view.** -/
theorem donateSchedContext {st st' : SystemState} {clientTid serverTid : SeLe4n.ThreadId}
    {clientScId : SeLe4n.SchedContextId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.donateSchedContext st clientTid serverTid clientScId = .ok st') :
    RecordsFrame st st' := by
  obtain ⟨sc, donorTcb, clientTcb, serverTcb, pushRid, pushReply, s1, s2, s3, s4,
    hSc, -, -, hFrame, hS1, hS2, hL1, hS3, hL2, hS4, hEq⟩ :=
    donateSchedContext_ok_storeChain st st' clientTid serverTid clientScId h
  have F1 := storeSchedContext hInv ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc) hS1
  have hRep := (SystemState.getReply?_eq_some_iff _ _ _).mp
    (donationPushFrame?_ok st donorTcb pushRid pushReply hFrame).2.1
  have F2 := F1.trans (storeDonationFramePush F1.invExt
    (by rw [F1.views, hRep]; rfl) hS2)
  have F3 := F2.trans (storeObject F2.invExt hS3
    (by rw [lookupTcb_some_objects _ _ _ hL1]; rfl) (fun _ h => by cases h))
  have F4 := F3.trans (storeObject F3.invExt hS4
    (by rw [lookupTcb_some_objects _ _ _ hL2]; rfl) (fun _ h => by cases h))
  exact F4.congr (by rw [hEq]) (by rw [hEq])

theorem applyCallDonation {st st' : SystemState} {callerVtid receiverVtid : SeLe4n.ValidThreadId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.applyCallDonation st callerVtid receiverVtid = .ok st') :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.applyCallDonation at h
  dsimp only at h
  repeat' split at h
  all_goals first
    | (cases h; exact refl hInv)
    | (cases h; rename_i hD; exact donateSchedContext hInv hD)
    | (cases h; done)

theorem applyCallDonationOnCore {st st' : SystemState}
    {callerVtid receiverVtid : SeLe4n.ValidThreadId} {donorHome doneeHome : CoreId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome
      = .ok st') : RecordsFrame st st' := by
  obtain ⟨st1, hDon, hArm⟩ := applyCallDonationOnCore_ok_decompose _ _ _ _ _ _ h
  have F1 := applyCallDonation hInv hDon
  rcases hArm with ⟨_, rfl⟩ | ⟨scId, _, rfl⟩
  · exact F1
  · exact F1.trans (migrateSchedContextReplenishment _ _ _ _ F1.invExt)

theorem applyRendezvousCallDonation {st st' : SystemState} {receiver donor : SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.applyRendezvousCallDonation st receiver donor = .ok st') :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.applyRendezvousCallDonation at h
  split at h
  · exact applyCallDonationOnCore hInv h
  · cases h

theorem applyReceiveRendezvousDonation {st st' : SystemState} {receiver dequeued : SeLe4n.ThreadId}
    (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.applyReceiveRendezvousDonation st receiver dequeued = .ok st') :
    RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.applyReceiveRendezvousDonation at h
  split at h
  · exact applyRendezvousCallDonation hInv h
  · cases h; exact refl hInv

/-- The receive rendezvous' hand-off: the lend, then the chain walk. -/
theorem applyReceiveRendezvousHandoff {st st' : SystemState} {receiver dequeued : SeLe4n.ThreadId}
    {ec : CoreId} (hInv : st.objects.invExt)
    (h : _root_.SeLe4n.Kernel.applyReceiveRendezvousHandoff st receiver dequeued ec = .ok st') :
    RecordsFrame st st' := by
  obtain ⟨stDon, hDon, rfl⟩ := applyReceiveRendezvousHandoff_ok_decompose _ _ _ _ _ h
  have F := applyReceiveRendezvousDonation hInv hDon
  split
  · exact F.trans (propagatePipChainCrossCore _ _ _ _ F.invExt)
  · exact F

end RecordsFrame

end SeLe4n.Kernel
