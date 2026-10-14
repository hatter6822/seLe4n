/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.Scheduler.RunQueueThreadLinks
import SeLe4n.Kernel.RobinHood.Invariant.InPlaceCommute

/-!
# TCB writes in place commute

WS-ZA ZA4.7.  On an object table with no resize due, every TCB write is
`mapTcbInPlace` (`updateTcb_eq_mapTcbInPlace`) and every object update is a
slot write (`modifyObject_eq_mapValueAt`).  A write at one thread then commutes
with a write at another (`mapTcbInPlace_swap`), and with a write at the same
thread to fields it leaves alone.  The reads see a written thread through its
write (`getTcb?_mapTcbInPlace`) and every other kind's object as it was.
-/

namespace SeLe4n.Model.SystemState

open SeLe4n.Kernel SeLe4n.Kernel.RobinHood SeLe4n.Kernel.LinkedQueue

theorem mapTcbObject_eq_mapTcb (f : TCB → TCB) : mapTcbObject f = KernelObject.mapTcb f := by
  funext o; cases o <;> rfl

@[simp] theorem mapTcbInPlace_noResizeDue (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) :
    (st.mapTcbInPlace t g).objects.noResizeDue ↔ st.objects.noResizeDue := Iff.rfl

theorem mapTcbInPlace_objectIndex (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB) :
    (st.mapTcbInPlace t g).objectIndex = st.objectIndex := rfl

theorem mapTcbInPlace_mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) (f g : TCB → TCB) :
    (st.mapTcbInPlace t f).mapTcbInPlace t g = st.mapTcbInPlace t (g ∘ f) := by
  unfold mapTcbInPlace
  dsimp only
  rw [RHTable.mapValueAt_mapValueAt]
  congr 2
  funext o; cases o <;> rfl

/-- **Two TCB writes commute** when they are at two threads, or at one thread
through updates that commute. -/
theorem mapTcbInPlace_swap (st : SystemState) {r x : SeLe4n.ThreadId} (g f : TCB → TCB)
    (hc : x = r → ∀ t, f (g t) = g (f t)) :
    (st.mapTcbInPlace r g).mapTcbInPlace x f = (st.mapTcbInPlace x f).mapTcbInPlace r g := by
  by_cases hx : x = r
  · subst hx
    rw [mapTcbInPlace_mapTcbInPlace, mapTcbInPlace_mapTcbInPlace]
    congr 1
    funext t; exact hc rfl t
  · unfold mapTcbInPlace
    dsimp only
    rw [RHTable.mapValueAt_comm _ _ _
      (fun h => hx (SeLe4n.ThreadId.toObjId_injective _ _ h))]

theorem updateTcbAtCode_swap (st : SystemState) {r : SeLe4n.ThreadId} (k : Nat)
    (g f : TCB → TCB) (hc : decode k = r → ∀ t, f (g t) = g (f t)) :
    (st.mapTcbInPlace r g).updateTcbAtCode k f = (st.updateTcbAtCode k f).mapTcbInPlace r g := by
  unfold updateTcbAtCode
  split
  · rfl
  · exact mapTcbInPlace_swap st g f hc

/-- An object-table slot write at a key other than the thread's, or at the
thread's through an update that commutes with its write, commutes with it. -/
theorem mapTcbInPlace_swap_objects (st : SystemState) (r : SeLe4n.ThreadId) (g : TCB → TCB)
    (x : SeLe4n.ObjId) (F : KernelObject → KernelObject)
    (hc : x = r.toObjId → ∀ o, F (KernelObject.mapTcb g o) = KernelObject.mapTcb g (F o)) :
    { st.mapTcbInPlace r g with objects := (st.mapTcbInPlace r g).objects.mapValueAt x F } =
      ({ st with objects := st.objects.mapValueAt x F } : SystemState).mapTcbInPlace r g := by
  unfold mapTcbInPlace
  dsimp only
  by_cases hx : x = r.toObjId
  · subst hx
    rw [RHTable.mapValueAt_mapValueAt, RHTable.mapValueAt_mapValueAt]
    congr 2
    funext o; exact hc rfl o
  · rw [RHTable.mapValueAt_comm _ _ _ hx]

private theorem objects_get?_of_getTcb? {st : SystemState} {x : SeLe4n.ThreadId} {t : TCB}
    (h : st.getTcb? x = some t) : st.objects.get? x.toObjId = some (.tcb t) := by
  have := (getTcb?_eq_some_iff st x t).mp h
  simpa only [RHTable_getElem?_eq_get?] using this

/-- **Under no resize, a TCB update is a write in place.** -/
theorem updateTcb_eq_mapTcbInPlace (st : SystemState) (x : SeLe4n.ThreadId) (f : TCB → TCB)
    (hNo : st.objects.noResizeDue) : st.updateTcb x f = st.mapTcbInPlace x f := by
  cases h : st.getTcb? x with
  | some t =>
    rw [updateTcb_eq_of_some h]
    unfold mapTcbInPlace
    have hg := objects_get?_of_getTcb? h
    rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? hNo hg)]
    congr 1
    exact RHTable.mapValueAt_congr hg rfl
  | none =>
    rw [updateTcb_eq_self_of_none h]
    unfold mapTcbInPlace
    cases hg : st.objects.get? x.toObjId with
    | none => rw [RHTable.mapValueAt_of_get?_none hg]
    | some o =>
      have hid : KernelObject.mapTcb f o = id o := by
        cases o with
        | tcb t =>
          exfalso
          have : st.getTcb? x = some t :=
            (getTcb?_eq_some_iff st x t).mpr (by simpa only [RHTable_getElem?_eq_get?] using hg)
          rw [h] at this; cases this
        | _ => rfl
      rw [RHTable.mapValueAt_congr hg hid, RHTable.mapValueAt_id]

/-- **Under no resize, an object update is a slot write.** -/
theorem modifyObject_eq_mapValueAt (st : SystemState) (x : SeLe4n.ObjId)
    (F : KernelObject → KernelObject) (hNo : st.objects.noResizeDue) :
    st.modifyObject x F = { st with objects := st.objects.mapValueAt x F } := by
  unfold modifyObject
  rw [RHTable.modify_eq_mapValueAt _ _ hNo]

theorem getTcb?_mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId) (g : TCB → TCB)
    (y : SeLe4n.ThreadId) :
    (st.mapTcbInPlace t g).getTcb? y = if t = y then (st.getTcb? y).map g else st.getTcb? y := by
  split
  · next h => subst h; exact mapTcbInPlace_getTcb?_self st t g
  · next h =>
    exact mapTcbInPlace_getTcb?_ne st t g y (fun e => h (SeLe4n.ThreadId.toObjId_injective _ _ e))

@[simp] theorem getReply?_mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) (rid : SeLe4n.ReplyId) :
    (st.mapTcbInPlace t g).getReply? rid = st.getReply? rid := by
  unfold getReply?
  rw [objects_mapTcbInPlace]
  by_cases h : t.toObjId == rid.toObjId
  · rw [if_pos h]
    cases st.objects[rid.toObjId]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rw [if_neg h]

@[simp] theorem getEndpoint?_mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) (id : SeLe4n.ObjId) :
    (st.mapTcbInPlace t g).getEndpoint? id = st.getEndpoint? id := by
  unfold getEndpoint?
  rw [objects_mapTcbInPlace]
  by_cases h : t.toObjId == id
  · rw [if_pos h]
    cases st.objects[id]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rw [if_neg h]

@[simp] theorem getSchedContext?_mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) (sc : SeLe4n.SchedContextId) :
    (st.mapTcbInPlace t g).getSchedContext? sc = st.getSchedContext? sc := by
  unfold getSchedContext?
  rw [objects_mapTcbInPlace]
  by_cases h : t.toObjId == sc.toObjId
  · rw [if_pos h]
    cases st.objects[sc.toObjId]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rw [if_neg h]

@[simp] theorem getNotification?_mapTcbInPlace (st : SystemState) (t : SeLe4n.ThreadId)
    (g : TCB → TCB) (id : SeLe4n.ObjId) :
    (st.mapTcbInPlace t g).getNotification? id = st.getNotification? id := by
  unfold getNotification?
  rw [objects_mapTcbInPlace]
  by_cases h : t.toObjId == id
  · rw [if_pos h]
    cases st.objects[id]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rw [if_neg h]

end SeLe4n.Model.SystemState
