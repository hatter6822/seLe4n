-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# A scheduling context bound to a notification

seL4-MCS binds a scheduling context to a notification (`schedContext_bindNtfn`):
the notification names the context (`ntfnSchedContext`,
`Notification.schedContextCode`) and the context names the notification
(`scNotification`, `SchedContext.notificationCode`).  `SchedContext_Bind` on a
notification capability sets both ends, and `SchedContext_Unbind` and the
finalisation of either object clear them (`schedContext_unbindNtfn`,
`schedContextMaybeUnbindNtfn`).

Each write here is a scalar field of the object's own slot, so the bind
allocates nothing.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The notification object with its scheduling-context link set to `code`;
any other object as it is. -/
@[inline] def mapNotificationSchedContext (code : Nat) : KernelObject → KernelObject
  | .notification n => .notification { n with schedContextCode := code }
  | o => o

/-- **seL4-MCS's `schedContext_bindNtfn`**: context `s` names notification `n`
and `n` names `s`, each in its slot. -/
def bindNotificationSchedLink (st : SystemState) (s : SeLe4n.SchedContextId)
    (n : SeLe4n.ObjId) : SystemState :=
  (st.updateSchedContext s (fun sc => { sc with notificationCode := n.val + 1 })).modifyObject n
    (mapNotificationSchedContext (s.val + 1))

/-- **seL4-MCS's `decodeSchedContext_Bind` and `invokeSchedContext_Bind` on a
notification capability**: refused `illegalState` (seL4's `IllegalOperation`)
when the context is already bound to a notification or the notification to a
context; otherwise both ends are linked (`bindNotificationSchedLink`). -/
def schedContextBindNotification (vScId : SeLe4n.ValidObjId) (ntfnId : SeLe4n.ObjId) :
    Kernel Unit :=
  fun st =>
    match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
    | none => .error .objectNotFound
    | some sc =>
      if sc.notificationCode != 0 then .error .illegalState else
      match st.getNotification? ntfnId with
      | none => .error .objectNotFound
      | some ntfn =>
        if ntfn.schedContextCode != 0 then .error .illegalState else
        .ok ((), bindNotificationSchedLink st (SeLe4n.SchedContextId.ofObjId vScId.val) ntfnId)

/-- **Whether `schedContextBindNotification` succeeds**: the context and the
notification present, each bound to no notification or context. -/
@[inline] def schedContextBindNotificationAdmitted (st : SystemState)
    (vScId : SeLe4n.ValidObjId) (ntfnId : SeLe4n.ObjId) : Bool :=
  match st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => false
  | some sc =>
    if sc.notificationCode != 0 then false else
    match st.getNotification? ntfnId with
    | none => false
    | some ntfn => ntfn.schedContextCode == 0

/-- An admitted bind succeeds with the link written on both ends. -/
theorem schedContextBindNotification_of_admitted (st : SystemState) (vScId : SeLe4n.ValidObjId)
    (ntfnId : SeLe4n.ObjId) (h : schedContextBindNotificationAdmitted st vScId ntfnId = true) :
    schedContextBindNotification vScId ntfnId st =
      .ok ((), bindNotificationSchedLink st (SeLe4n.SchedContextId.ofObjId vScId.val) ntfnId) := by
  unfold schedContextBindNotificationAdmitted at h
  unfold schedContextBindNotification
  cases hS : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => simp [hS] at h
  | some sc =>
    simp only [hS] at h ⊢
    by_cases hC : (sc.notificationCode != 0) = true
    · simp [hC] at h
    · simp only [hC, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hN : st.getNotification? ntfnId with
      | none => simp [hN] at h
      | some ntfn =>
        simp only [hN] at h ⊢
        have h0 : ntfn.schedContextCode = 0 := by simpa using h
        simp [h0]

/-- A bind that succeeds was admitted, and wrote the link on both ends. -/
theorem schedContextBindNotification_ok_admitted {st st' : SystemState}
    {vScId : SeLe4n.ValidObjId} {ntfnId : SeLe4n.ObjId}
    (h : schedContextBindNotification vScId ntfnId st = .ok ((), st')) :
    schedContextBindNotificationAdmitted st vScId ntfnId = true ∧
      st' = bindNotificationSchedLink st (SeLe4n.SchedContextId.ofObjId vScId.val) ntfnId := by
  unfold schedContextBindNotification at h
  unfold schedContextBindNotificationAdmitted
  cases hS : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => simp [hS] at h
  | some sc =>
    simp only [hS] at h ⊢
    by_cases hC : (sc.notificationCode != 0) = true
    · simp [hC] at h
    · simp only [hC, Bool.false_eq_true, ↓reduceIte] at h ⊢
      cases hN : st.getNotification? ntfnId with
      | none => simp [hN] at h
      | some ntfn =>
        simp only [hN] at h ⊢
        by_cases h0 : (ntfn.schedContextCode != 0) = true
        · simp [h0] at h
        · simp only [h0, Bool.false_eq_true, ↓reduceIte, Except.ok.injEq, Prod.mk.injEq,
            true_and] at h
          exact ⟨by simpa using h0, h.symm⟩

/-- **The notification's link written in its slot** is the insert of the
notification with that link. -/
theorem modifyObject_mapNotificationSchedContext_eq {st : SystemState} {n : SeLe4n.ObjId}
    {ntfn : Notification} (h : st.objects[n]? = some (.notification ntfn)) (code : Nat) :
    st.modifyObject n (mapNotificationSchedContext code) =
      { st with objects := st.objects.insert n (.notification { ntfn with schedContextCode := code }) } := by
  unfold SystemState.modifyObject
  rw [SeLe4n.Kernel.RobinHood.RHTable.modify_of_get? h]
  rfl

/-- **What an admitted bind reads**: the context bound to no notification and
the notification bound to no context. -/
theorem schedContextBindNotificationAdmitted_facts {st : SystemState}
    {vScId : SeLe4n.ValidObjId} {ntfnId : SeLe4n.ObjId}
    (h : schedContextBindNotificationAdmitted st vScId ntfnId = true) :
    ∃ sc ntfn, st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) = some sc ∧
      sc.notificationCode = 0 ∧ st.getNotification? ntfnId = some ntfn ∧
      ntfn.schedContextCode = 0 := by
  unfold schedContextBindNotificationAdmitted at h
  cases hS : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vScId.val) with
  | none => simp [hS] at h
  | some sc =>
    simp only [hS] at h
    by_cases hC : (sc.notificationCode != 0) = true
    · simp [hC] at h
    · simp only [hC, Bool.false_eq_true, ↓reduceIte] at h
      cases hN : st.getNotification? ntfnId with
      | none => simp [hN] at h
      | some ntfn =>
        simp only [hN] at h
        exact ⟨sc, ntfn, rfl, by simpa using hC, rfl, by simpa using h⟩

/-- **The bind's two writes as two inserts**: the context's link rewritten in its
slot, then the notification's, which the first write leaves where it was. -/
theorem bindNotificationSchedLink_eq {st : SystemState} {s : SeLe4n.SchedContextId}
    {n : SeLe4n.ObjId} {sc : SchedContext} {ntfn : Notification}
    (hS : st.getSchedContext? s = some sc) (hN : st.getNotification? n = some ntfn)
    (hInv : st.objects.invExt) :
    let st1 := st.updateSchedContext s (fun sc => { sc with notificationCode := n.val + 1 })
    st1.objects[n]? = some (.notification ntfn) ∧
      bindNotificationSchedLink st s n =
        { st1 with
          objects := st1.objects.insert n (.notification { ntfn with schedContextCode := s.val + 1 }) } := by
  intro st1
  have hSraw := (SystemState.getSchedContext?_eq_some_iff st s sc).mp hS
  have hNraw := (SystemState.getNotification?_eq_some_iff st n ntfn).mp hN
  have hNe : s.toObjId ≠ n := by
    intro e; rw [e, hNraw] at hSraw; cases hSraw
  have h1 : st1.objects[n]? = some (.notification ntfn) := by
    rw [SystemState.updateSchedContext_objects_ne _ _ _ _ hNe hInv]; exact hNraw
  exact ⟨h1, modifyObject_mapNotificationSchedContext_eq h1 _⟩

end SeLe4n.Kernel
