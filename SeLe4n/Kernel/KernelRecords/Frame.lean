-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.Architecture.PageTeardownClears

/-!
# The records every kernel entry carries, and the frame that keeps them

WS-ZA ZA6.37.  Three invariants describe records the kernel keeps beside the
objects they relate, and each reads a small view of the store:

* the reply-waiter queues (`SystemState.replyWaitersConsistent`) read every
  TCB's reply view (`TCB.replyView`);
* the fault records (`SystemState.faultRecordParked`: a thread carrying a fault
  is fault-blocked or `.Inactive`) read every TCB's IPC state, thread state and
  whether it carries a fault;
* the address-space records (`teardownWellFormed`: the object and ASID tables
  well formed and the VSpace bundle) read the ASID table and the VSpace roots.

`SystemState.kernelRecordsSound` is the three together.  A step that keeps every
slot's record view (`recordViewOf`) and the ASID table keeps it
(`RecordsFrame.preserves`), whatever else it writes: a CNode, an endpoint, a
notification, a scheduling context, a register file, a run-queue link, the
scheduler record.  The steps that write a view — the IPC arms, the cancellations,
the suspend and resume, the fault delivery, the retype, the VSpace writes and the
teardown — keep it by their own theorems, and a kernel entry chains the two
kinds as a `RecordsStage`.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The views
-- ============================================================================

/-- What the carried records read of one TCB: its reply view, its IPC state, its
thread state, and whether it carries a fault. -/
structure TcbRecordView where
  reply : ReplyView
  ipc : ThreadIpcState
  state : ThreadState
  faulted : Bool

/-- A TCB's record view. -/
def _root_.SeLe4n.Model.TCB.recordView (t : TCB) : TcbRecordView :=
  ⟨t.replyView, t.ipcState, t.threadState, t.pendingFault.isSome⟩

/-- What the carried records read of one object slot: a TCB's record view, or a
VSpace root whole; nothing of any other object. -/
def recordViewOf : Option KernelObject → Option (TcbRecordView ⊕ VSpaceRoot)
  | some (.tcb t) => some (.inl t.recordView)
  | some (.vspaceRoot r) => some (.inr r)
  | _ => none

@[simp] theorem recordViewOf_tcb (t : TCB) :
    recordViewOf (some (.tcb t)) = some (.inl t.recordView) := rfl

@[simp] theorem recordViewOf_vspaceRoot (r : VSpaceRoot) :
    recordViewOf (some (.vspaceRoot r)) = some (.inr r) := rfl

/-- **The records every kernel entry carries.** -/
def _root_.SeLe4n.Model.SystemState.kernelRecordsSound (st : SystemState) : Prop :=
  teardownWellFormed st ∧ st.replyWaitersConsistent ∧ st.faultRecordParked

namespace KernelRecords

theorem objects_invExt {st : SystemState} (h : st.kernelRecordsSound) : st.objects.invExt :=
  h.1.1

/-- A slot whose view is a TCB's holds a TCB with that view. -/
theorem tcb_of_view {o : Option KernelObject} {v : TcbRecordView}
    (h : recordViewOf o = some (.inl v)) : ∃ t, o = some (.tcb t) ∧ t.recordView = v := by
  cases o with
  | none => cases h
  | some o =>
    cases o <;> simp only [recordViewOf, Option.some.injEq, reduceCtorEq, Sum.inl.injEq] at h
    exact ⟨_, rfl, h⟩

/-- A slot whose view is a root holds that root. -/
theorem root_of_view {o : Option KernelObject} {r : VSpaceRoot}
    (h : recordViewOf o = some (.inr r)) : o = some (.vspaceRoot r) := by
  cases o with
  | none => cases h
  | some o =>
    cases o <;> simp only [recordViewOf, Option.some.injEq, reduceCtorEq, Sum.inr.injEq] at h
    rw [h]

/-- The reply view of a slot is read off its record view. -/
theorem objReplyView_eq_of_view {a b : Option KernelObject}
    (h : recordViewOf a = recordViewOf b) : objReplyView a = objReplyView b := by
  cases ha : recordViewOf a with
  | none =>
    have hb : recordViewOf b = none := h ▸ ha
    have hNa : objReplyView a = none := by
      cases a with
      | none => rfl
      | some o => cases o <;> simp_all [recordViewOf, objReplyView]
    have hNb : objReplyView b = none := by
      cases b with
      | none => rfl
      | some o => cases o <;> simp_all [recordViewOf, objReplyView]
    rw [hNa, hNb]
  | some v =>
    rw [ha] at h
    cases v with
    | inl v =>
      obtain ⟨ta, rfl, hva⟩ := tcb_of_view ha
      obtain ⟨tb, rfl, hvb⟩ := tcb_of_view h.symm
      have : ta.replyView = tb.replyView := by
        have := congrArg TcbRecordView.reply (hva.trans hvb.symm); exact this
      simp [objReplyView, this]
    | inr r =>
      rw [root_of_view ha, root_of_view h.symm]

end KernelRecords


-- ============================================================================
-- §2  The frame
-- ============================================================================

/-- **A step that keeps the records' reads**: every slot's record view and the
ASID table, with the store's invariant. -/
structure RecordsFrame (st st' : SystemState) : Prop where
  views : ∀ k : SeLe4n.ObjId, recordViewOf st'.objects[k]? = recordViewOf st.objects[k]?
  asid : st'.asidTable = st.asidTable
  invExt : st'.objects.invExt

namespace RecordsFrame

theorem refl {st : SystemState} (hInv : st.objects.invExt) : RecordsFrame st st :=
  ⟨fun _ => rfl, rfl, hInv⟩

theorem trans {a b c : SystemState} (h₁ : RecordsFrame a b) (h₂ : RecordsFrame b c) :
    RecordsFrame a c :=
  ⟨fun k => (h₂.views k).trans (h₁.views k), h₂.asid.trans h₁.asid, h₂.invExt⟩

theorem of_objects_eq {st st' : SystemState} (hInv : st.objects.invExt)
    (hO : st'.objects = st.objects) (hA : st'.asidTable = st.asidTable) : RecordsFrame st st' :=
  ⟨fun k => by rw [hO], hA, hO ▸ hInv⟩

theorem of_eq {st st' : SystemState} (hInv : st.objects.invExt) (h : st' = st) :
    RecordsFrame st st' := by subst h; exact refl hInv

/-- A state with another's objects and ASID table is in the same frame. -/
theorem congr {st s s' : SystemState} (h : RecordsFrame st s) (hO : s'.objects = s.objects)
    (hA : s'.asidTable = s.asidTable) : RecordsFrame st s' :=
  ⟨fun k => by rw [hO]; exact h.views k, hA.trans h.asid, hO ▸ h.invExt⟩

/-- The record views of every thread are the frame's. -/
theorem getTcb?_view {st st' : SystemState} (F : RecordsFrame st st') {t : SeLe4n.ThreadId}
    {tcb' : TCB} (h : st'.getTcb? t = some tcb') :
    ∃ tcb, st.getTcb? t = some tcb ∧ tcb.recordView = tcb'.recordView := by
  have hO := (SystemState.getTcb?_eq_some_iff _ _ _).mp h
  have hv := F.views t.toObjId
  rw [hO, recordViewOf_tcb] at hv
  obtain ⟨tcb, hT, hEq⟩ := KernelRecords.tcb_of_view hv.symm
  exact ⟨tcb, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT, hEq⟩

theorem replyViews {st st' : SystemState} (F : RecordsFrame st st') :
    st'.replyViews = st.replyViews := by
  funext k
  unfold SystemState.replyViews SystemState.getObject?
  simp only [RHTable_getElem?_eq_get?]
  exact KernelRecords.objReplyView_eq_of_view (F.views k)

theorem roots {st st' : SystemState} (F : RecordsFrame st st') (oid : SeLe4n.ObjId)
    (r : VSpaceRoot) :
    st'.objects[oid]? = some (.vspaceRoot r) ↔ st.objects[oid]? = some (.vspaceRoot r) := by
  have hv := F.views oid
  constructor
  · intro h; rw [h, recordViewOf_vspaceRoot] at hv; exact KernelRecords.root_of_view hv.symm
  · intro h; rw [h, recordViewOf_vspaceRoot] at hv; exact KernelRecords.root_of_view hv

theorem faultRecordParked {st st' : SystemState} (F : RecordsFrame st st')
    (h : st.faultRecordParked) : st'.faultRecordParked := by
  intro t tcb' hT hF
  obtain ⟨tcb, hT0, hv⟩ := F.getTcb?_view hT
  simp only [TCB.recordView, TcbRecordView.mk.injEq] at hv
  obtain ⟨-, hIpc, hTs, hFl⟩ := hv
  rw [← hIpc, ← hTs]
  exact h t tcb hT0 (hFl ▸ hF)

/-- **A step that keeps the records' reads keeps the records.** -/
theorem preserves {st st' : SystemState} (F : RecordsFrame st st')
    (h : st.kernelRecordsSound) : st'.kernelRecordsSound :=
  ⟨teardownWellFormed_of_roots_eq F.invExt F.asid F.roots h.1,
   SystemState.replyWaitersConsistent.of_views F.replyViews h.2.1,
   F.faultRecordParked h.2.2⟩

end RecordsFrame

-- ============================================================================
-- §3  The stage
-- ============================================================================

/-- **A step that carries the records**: the unit a kernel entry chains. -/
def RecordsStage (st st' : SystemState) : Prop :=
  st.kernelRecordsSound → st'.kernelRecordsSound

namespace RecordsStage

theorem refl (st : SystemState) : RecordsStage st st := id

theorem trans {a b c : SystemState} (h₁ : RecordsStage a b) (h₂ : RecordsStage b c) :
    RecordsStage a c := h₂ ∘ h₁

theorem of_frame {st st' : SystemState} (F : RecordsFrame st st') : RecordsStage st st' :=
  F.preserves

theorem of_eq {st st' : SystemState} (h : st' = st) : RecordsStage st st' := h ▸ refl st

end RecordsStage


-- ============================================================================
-- §4  The primitive writes
-- ============================================================================

namespace RecordsFrame

/-- A raw insert whose object keeps its slot's view, over a slot that held no
root (the ASID table is untouched). -/
theorem insert {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hV : recordViewOf (some o) = recordViewOf st.objects[k]?) :
    RecordsFrame st { st with objects := st.objects.insert k o } := by
  refine ⟨fun x => ?_, rfl, RHTable_insert_preserves_invExt _ _ _ hInv⟩
  show recordViewOf (st.objects.insert k o)[x]? = _
  simp only [RHTable_getElem?_eq_get?] at hV ⊢
  by_cases hx : k = x
  · subst hx; rw [RobinHood.RHTable.getElem?_insert_self _ _ _ hInv]; exact hV
  · rw [RobinHood.RHTable.getElem?_insert_ne _ _ _ _ (fun hb => hx (eq_of_beq hb)) hInv]

/-- A store whose object keeps its slot's view and is no root. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (h : storeObject k o st = .ok ((), st'))
    (hV : recordViewOf (some o) = recordViewOf st.objects[k]?)
    (hNR : ∀ r, o ≠ .vspaceRoot r) : RecordsFrame st st' := by
  refine ⟨fun x => ?_, ?_, storeObject_preserves_objects_invExt st st' k o hInv h⟩
  · by_cases hx : x = k
    · subst hx; rw [storeObject_objects_eq st st' x o hInv h]; exact hV
    · rw [storeObject_objects_ne st st' k x o hx hInv h]
  · rw [storeObject_asidTable_non_vspaceRoot st st' k o hNR h]
    split
    · rename_i r hr
      rw [hr, recordViewOf_vspaceRoot] at hV
      cases o <;> simp [recordViewOf] at hV
      exact absurd rfl (hNR _)
    · rfl

/-- A typed rewrite whose object keeps its slot's view. -/
theorem rewriteObject {st : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hAdm : st.rewriteAdmissible k o) (hInv : st.objects.invExt)
    (hV : recordViewOf (some o) = recordViewOf st.objects[k]?) :
    RecordsFrame st (st.rewriteObject k o hAdm) :=
  insert hInv hV

/-- **A TCB write that keeps every record view.** -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).recordView = x.recordView) :
    RecordsFrame st (st.updateTcb t f) := by
  cases hT : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hT]; exact refl hInv
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hT]
    exact insert hInv (by rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT]; simp [hf])

/-- The checked TCB write, when it keeps every record view. -/
theorem modifyTcb {st st' : SystemState} {t : SeLe4n.ThreadId} {f : TCB → TCB}
    (hInv : st.objects.invExt) (hf : ∀ x, (f x).recordView = x.recordView)
    (h : _root_.SeLe4n.Kernel.modifyTcb st t f = .ok st') : RecordsFrame st st' := by
  unfold _root_.SeLe4n.Kernel.modifyTcb at h
  split at h
  · cases h
  · rename_i tcb hL
    split at h
    · cases h
    · rename_i st1 hS
      cases h
      have hT : st.objects[t.toObjId]? = some (.tcb tcb) := lookupTcb_some_objects st t tcb hL
      exact storeObject hInv hS (by rw [hT]; simp [hf]) (fun _ => by simp)

end RecordsFrame


-- ============================================================================
-- §5  The erasure frames
-- ============================================================================

namespace RecordsFrame

/-- **Two stores equal modulo an erasure the record views ignore** have the same
views. -/
theorem views_of_erasure {E : KernelObject → KernelObject}
    (hE : ∀ o o', E o = E o' → recordViewOf (some o) = recordViewOf (some o'))
    {st st' : SystemState} (h : ∀ x : SeLe4n.ObjId,
      (st'.objects[x]?).map E = (st.objects[x]?).map E) :
    ∀ k : SeLe4n.ObjId, recordViewOf st'.objects[k]? = recordViewOf st.objects[k]? := by
  intro k
  have hk := h k
  cases ha : st'.objects[k]? <;> cases hb : st.objects[k]? <;> rw [ha, hb] at hk <;>
    simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hk
  all_goals first | rfl | exact hE _ _ hk

theorem erasure_taint (o o' : KernelObject) (h : o.eraseTaint = o'.eraseTaint) :
    recordViewOf (some o) = recordViewOf (some o') := by
  cases o <;> cases o' <;>
    simp only [KernelObject.eraseTaint, KernelObject.withTaintWords, reduceCtorEq,
      KernelObject.tcb.injEq, KernelObject.vspaceRoot.injEq] at h ⊢ <;>
    first | rfl | (subst h; rfl) | skip
  rename_i t t'
  have := congrArg TCB.recordView h
  simpa [TCB.recordView, TCB.withTaintWords] using this

theorem erasure_yield (o o' : KernelObject) (h : o.withoutYield = o'.withoutYield) :
    recordViewOf (some o) = recordViewOf (some o') := by
  cases o <;> cases o' <;>
    simp only [KernelObject.withoutYield, reduceCtorEq, KernelObject.tcb.injEq,
      KernelObject.vspaceRoot.injEq] at h ⊢ <;>
    first | rfl | (subst h; rfl) | skip
  rename_i t t'
  have := congrArg TCB.recordView h
  simpa [TCB.recordView] using this

theorem erasure_release (o o' : KernelObject) (h : o.withoutRelease = o'.withoutRelease) :
    recordViewOf (some o) = recordViewOf (some o') := by
  cases o <;> cases o' <;>
    simp only [KernelObject.withoutRelease, reduceCtorEq, KernelObject.tcb.injEq,
      KernelObject.vspaceRoot.injEq] at h ⊢ <;>
    first | rfl | (subst h; rfl)

theorem of_agreeOffTaint {st st' : SystemState} (h : st.objectsAgreeOffTaint st')
    (hA : st'.asidTable = st.asidTable) (hInv : st'.objects.invExt) : RecordsFrame st st' :=
  ⟨views_of_erasure erasure_taint h, hA, hInv⟩

theorem of_agreeOffYield {st st' : SystemState} (h : SystemState.objectsAgreeOffYield st' st)
    (hA : st'.asidTable = st.asidTable) (hInv : st'.objects.invExt) : RecordsFrame st st' :=
  ⟨views_of_erasure erasure_yield h, hA, hInv⟩

theorem of_agreeOffReleaseLinks {st st' : SystemState}
    (h : SystemState.objectsAgreeOffReleaseLinks st' st)
    (hA : st'.asidTable = st.asidTable) (hInv : st'.objects.invExt) : RecordsFrame st st' :=
  ⟨views_of_erasure erasure_release h, hA, hInv⟩

/-- Two slots agreeing off the run links, with the same reply view, have the same
record view: the run links clear the reply links, so the reply view is read on
its own. -/
theorem view_of_runLinks {a b : Option KernelObject}
    (hw : a.map KernelObject.withoutRunLinks = b.map KernelObject.withoutRunLinks)
    (hr : objReplyView a = objReplyView b) : recordViewOf a = recordViewOf b := by
  cases a <;> cases b <;>
    simp only [Option.map_none, Option.map_some, Option.some.injEq, reduceCtorEq] at hw ⊢
  all_goals try rfl
  · rename_i o o'
    cases o <;> cases o' <;>
      simp only [KernelObject.withoutRunLinks, reduceCtorEq, KernelObject.tcb.injEq,
        KernelObject.vspaceRoot.injEq] at hw ⊢ <;>
      first | rfl | (subst hw; rfl) | skip
    rename_i t t'
    simp only [objReplyView, Option.some.injEq] at hr
    show some (Sum.inl t.recordView) = some (Sum.inl t'.recordView)
    unfold TCB.recordView
    rw [hr, TCB.proj_eq_of_withoutRunLinks_eq TCB.ipcState hw,
      TCB.proj_eq_of_withoutRunLinks_eq TCB.threadState hw,
      TCB.proj_eq_of_withoutRunLinks_eq (fun x => x.pendingFault.isSome) hw]

theorem of_agreeOffRunLinks {st st' : SystemState} (h : st'.objectsAgreeOffRunLinks st)
    (hR : st'.replyViews = st.replyViews)
    (hA : st'.asidTable = st.asidTable) (hInv : st'.objects.invExt) : RecordsFrame st st' := by
  refine ⟨fun k => view_of_runLinks (h k) ?_, hA, hInv⟩
  have := congrFun hR k
  unfold SystemState.replyViews SystemState.getObject? at this
  simpa only [RHTable_getElem?_eq_get?] using this

end RecordsFrame

end SeLe4n.Kernel
