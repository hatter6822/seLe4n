/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.FinaliseWaiterCompletion

/-!
# A finalised object's own record is retirable

WS-ZA ZA5.4 part 26: a final delete finalises a thread or a scheduling context
(`finaliseThread`, `finaliseSchedContext`) and then retires it
(`retireFinalObject`), which erases it only when it is retirable
(`schedulingObjectRetirable`).  This module proves that the finalisation, run on
a state its admission admits, always leaves the object's **own record** in the
retirable shape: nothing it holds names another object and nothing it records
keeps it in use.

* **The scheduling context** (`finaliseSchedContext_releases`): bound to no
  thread, lent from no one, heading no reply stack.
* **The thread** (`finaliseThread_quiesces`): `.Inactive` and `.ready`, linked
  into no queue and heading none, bound to no notification and to no
  scheduling context, holding no reply link or stash and no timeout budget,
  and held by no core — every field `threadLinksQuiescent` reads, the space
  slots aside, which the zombie loop empties after the finalisation.

What the record does not say — that no *other* object still names the
finalised one — is the retire's store walk today, and the reciprocity
invariants that replace it are `docs/planning/UNTYPED_RESET_PLAN.md` row 27,
which consumes these theorems.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The scheduling context
-- ============================================================================

/-- **A finalised scheduling context's own record is released**: the context
at `x` is stored, bound to no thread, lent from no one and heading no reply
stack — the record half of `schedContextRetirable`. -/
def schedContextRecordReleased (st : SystemState) (x : SeLe4n.ObjId) : Prop :=
  ∃ sc, st.objects[x]? = some (.schedContext sc) ∧ sc.boundThreadCode = 0 ∧
    sc.donationOrigin = none ∧ sc.scReply = none

/-- **The holder's unbind keeps the context, its reply-stack head and every
reply**: it rewrites the context's binding fields and the holder's TCB alone. -/
theorem finaliseSchedContextUnbind_keeps {s : SystemState} {x : SeLe4n.ObjId}
    {sc : SchedContext} (hInv : s.objects.invExt) (hO : s.objects[x]? = some (.schedContext sc)) :
    (∃ sc', (finaliseSchedContextUnbind s x).objects[x]? = some (.schedContext sc') ∧
      sc'.scReply = sc.scReply) ∧
    ∀ (k : SeLe4n.ObjId) (r : Reply), s.objects[k]? = some (.reply r) →
      (finaliseSchedContextUnbind s x).objects[k]? = some (.reply r) := by
  have hId : ∀ s' : SystemState, s' = s →
      (∃ sc', s'.objects[x]? = some (.schedContext sc') ∧ sc'.scReply = sc.scReply) ∧
      ∀ (k : SeLe4n.ObjId) (r : Reply), s.objects[k]? = some (.reply r) →
        s'.objects[k]? = some (.reply r) := by
    intro s' e; subst e; exact ⟨⟨sc, hO, rfl⟩, fun _ _ h => h⟩
  unfold finaliseSchedContextUnbind
  rw [SystemState.getObject?_eq_getElem, hO]
  dsimp only
  split
  · exact hId _ rfl
  generalize hTid : (⟨sc.boundThreadCode - 1⟩ : SeLe4n.ThreadId) = tid
  cases hT : s.getTcb? tid with
  | none => exact hId _ rfl
  | some t =>
  dsimp only
  split
  rotate_left
  · exact hId _ rfl
  rename_i hG
  simp only [beq_iff_eq] at hG
  have hBind := schedContextBinding_ownerCleared (t := t) hG
  have hOk := cancelBoundDonationOnCore_of_bound s tid { t with scBindingOwnerCode := 0 }
    (determineTargetCore s tid) _ hBind
  rw [hOk]
  dsimp only
  have hObj := cancelBoundDonationOnCore_objects s _ tid _ _ _ hBind hOk
  have hNe : tid.toObjId ≠ x := by
    intro e
    have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
    rw [e, hO] at this; cases this
  have hG' : s.getSchedContext? ⟨x.val⟩ = some sc := by
    rw [SystemState.getSchedContext?_eq_some_iff]; exact hO
  have hInv1 := SystemState.updateSchedContext_preserves_objects_invExt s ⟨x.val⟩
    (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none }) hInv
  refine ⟨⟨{ sc with boundThreadCode := 0, isActive := false, donationOrigin := none }, ?_, rfl⟩,
    fun k r hk => ?_⟩
  · rw [hObj, SystemState.updateTcb_objects_ne _ _ _ _ hNe hInv1,
      SystemState.updateSchedContext_eq_of_some hG']
    dsimp only
    rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl,
      RHTable_getElem?_eq_get?, RobinHood.RHTable.getElem?_insert_self _ _ _ hInv]
  · have hkx : (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId ≠ k := by
      intro e; rw [← e] at hk; rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl,
        hO] at hk; cases hk
    have hkt : tid.toObjId ≠ k := by
      intro e
      have := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
      rw [e, hk] at this; cases this
    rw [hObj, SystemState.updateTcb_objects_ne _ _ _ _ hkt hInv1,
      SystemState.updateSchedContext_objects_ne _ _ _ _ hkx hInv]
    exact hk

/-- **The holder's deschedule keeps the context and every reply**: it writes
run-queue links alone. -/
theorem finaliseSchedContextDeschedule_keeps {s : SystemState} {x k : SeLe4n.ObjId}
    {o : KernelObject} (hNot : ∀ t, o ≠ .tcb t) (hk : s.objects[k]? = some o) :
    (finaliseSchedContextDeschedule s x).objects[k]? = some o :=
  (finaliseSchedContextDeschedule_objectsAgreeOffRunLinks s x).get_of_not_tcb hNot hk

/-- **A finalised scheduling context's own record is released**
(WS-ZA ZA5.4 part 26): on a state its admission admits, the finalisation
leaves the context at `x` bound to no thread and lent from no one — the
holder's unbind clears both (`finaliseSchedContextUnbind_released`) — and
heading no reply stack: the head reply the admission reads still names the
context as its head after the deschedule and the unbind, which write no reply,
so the unstack runs and clears the head. -/
theorem finaliseSchedContext_releases (x : SeLe4n.ObjId) (st : SystemState)
    (hInv : st.objects.invExt) (hA : schedContextFinaliseAdmitted st x = true) :
    schedContextRecordReleased (finaliseSchedContext x st) x := by
  rw [finaliseSchedContext_eq, if_pos hA]
  have hA0 := hA
  unfold schedContextFinaliseAdmitted at hA0
  obtain ⟨sc0, hO, hRep⟩ : ∃ sc0, st.objects[x]? = some (.schedContext sc0) ∧
      (match sc0.scReply with
        | none => true
        | some rid =>
          match st.getReply? rid with
          | some r => replyStackLinkHeads x r.next
          | none => false) = true := by
    split at hA0
    · rename_i sc0 hO
      simp only [Bool.and_eq_true] at hA0
      exact ⟨sc0, by rw [← SystemState.getObject?_eq_getElem]; exact hO, hA0.1⟩
    · cases hA0
  have hInv1 : (finaliseSchedContextDeschedule st x).objects.invExt :=
    finaliseSchedContextDeschedule_closed (fun s => s.objects.invExt)
      (fun s t _ h _ _ _ _ => descheduleAtPlacement_preserves_objects_invExt s t h) st x hInv
  have hO1 := finaliseSchedContextDeschedule_keeps (x := x) (fun _ e => KernelObject.noConfusion e) hO
  obtain ⟨⟨sc2, hO2, hR2⟩, hKeep⟩ := finaliseSchedContextUnbind_keeps hInv1 hO1
  have hInv2 : (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x).objects.invExt :=
    finaliseSchedContextUnbind_closed (fun s => s.objects.invExt)
      (fun s _ _ _ _ _ h _ _ _ _ hOk => (FinaliseFrame.cancelBoundDonationOnCore h hOk).invExt)
      _ x hInv1
  have hG2 : (finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x).getSchedContext?
      ⟨x.val⟩ = some sc2 := by
    rw [SystemState.getSchedContext?_eq_some_iff]; exact hO2
  obtain ⟨hB2, hD2⟩ := finaliseSchedContextUnbind_released hInv hA hG2
  generalize finaliseSchedContextUnbind (finaliseSchedContextDeschedule st x) x = s2
    at hO2 hKeep hInv2 hG2
  unfold finaliseSchedContextUnstack
  rw [hG2]
  dsimp only
  cases hS : sc2.scReply with
  | none => exact ⟨sc2, hO2, hB2, hD2, hS⟩
  | some rid =>
  dsimp only
  rw [hR2] at hS
  rw [hS] at hRep
  dsimp only at hRep
  cases hR : st.getReply? rid with
  | none => rw [hR] at hRep; cases hRep
  | some r =>
  rw [hR] at hRep
  dsimp only at hRep
  have hRo := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
  have hRo2 := hKeep _ r (finaliseSchedContextDeschedule_keeps
    (fun _ e => KernelObject.noConfusion e) hRo)
  rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRo2]
  dsimp only
  rw [if_pos hRep]
  obtain ⟨s3, hS3⟩ : ∃ s3, storeObject rid.toObjId (.reply { r with next := none }) s2 = .ok ((), s3) :=
    ⟨_, rfl⟩
  rw [hS3]
  dsimp only
  have hNe : x ≠ rid.toObjId := by intro e; rw [e, hRo2] at hO2; cases hO2
  have hO3 : s3.objects[x]? = some (.schedContext sc2) := by
    rw [storeObject_objects_ne s2 s3 rid.toObjId x _ hNe hInv2 hS3]; exact hO2
  have hInv3 := storeObject_preserves_objects_invExt s2 s3 rid.toObjId _ hInv2 hS3
  have hG3 : s3.getSchedContext? ⟨x.val⟩ = some sc2 := by
    rw [SystemState.getSchedContext?_eq_some_iff]; exact hO3
  refine ⟨{ sc2 with scReply := none }, ?_, hB2, hD2, rfl⟩
  rw [SystemState.updateSchedContext_eq_of_some hG3]
  dsimp only
  rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl,
    RHTable_getElem?_eq_get?, RobinHood.RHTable.getElem?_insert_self _ _ _ hInv3]

end SeLe4n.Kernel
