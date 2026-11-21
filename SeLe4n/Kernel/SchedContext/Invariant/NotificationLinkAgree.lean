-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.NotificationLink

/-!
# The notification link agrees in both directions

WS-SX SX8.3: seL4-MCS keeps a notification's `ntfnSchedContext` and its
context's `scNotification` naming each other (`schedContext_bindNtfn` sets
both, `schedContext_unbindNtfn` clears both).  `notificationLinksAgree` is that
pairing over the object store: slot `n` names context `s`
(`Notification.schedContextCode`) exactly when slot `s` names notification `n`
(`SchedContext.notificationCode`), the template of `yieldLinksAgree`.

The writers of either word keep it: the bind on a notification, which links
two clear ends, and the unbind read from either end, which clears both ends of
a link it finds.  A step that keeps every slot's two codes keeps it too
(`notificationLinksAgree_of_kept`), which is every other transition's case:
the donation and the return write a thread's binding and the context's bound
thread, never either link word.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- The notification-link codes a slot holds: a notification's link to its
context first, a context's link to its notification second; `0` for none and
for every other object. -/
def objNotificationLinkCodes : Option KernelObject → Nat × Nat
  | some (.notification n) => (n.schedContextCode, 0)
  | some (.schedContext sc) => (0, sc.notificationCode)
  | _ => (0, 0)

/-- One of a slot's two codes is `0`: a slot holds a notification or a
context, never both. -/
theorem objNotificationLinkCodes_fst_or_snd (o : Option KernelObject) :
    (objNotificationLinkCodes o).1 = 0 ∨ (objNotificationLinkCodes o).2 = 0 := by
  rcases o with _ | o
  · exact Or.inl rfl
  · cases o <;> simp [objNotificationLinkCodes]

/-- **The notification link agrees in both directions**: slot `n` names `s` as
its scheduling context exactly when slot `s` names `n` as its notification. -/
def notificationLinksAgree (st : SystemState) : Prop :=
  ∀ n s : SeLe4n.ObjId,
    (objNotificationLinkCodes st.objects[n]?).1 = s.val + 1 ↔
      (objNotificationLinkCodes st.objects[s]?).2 = n.val + 1

/-- Every slot's two codes kept. -/
def NotificationLinksKept (st' st : SystemState) : Prop :=
  ∀ k : SeLe4n.ObjId,
    objNotificationLinkCodes st'.objects[k]? = objNotificationLinkCodes st.objects[k]?

namespace NotificationLinksKept

theorem refl (st : SystemState) : NotificationLinksKept st st := fun _ => rfl

theorem trans {a b d : SystemState} (h₁ : NotificationLinksKept a b)
    (h₂ : NotificationLinksKept b d) : NotificationLinksKept a d := fun k => (h₁ k).trans (h₂ k)

theorem symm {st st' : SystemState} (h : NotificationLinksKept st' st) :
    NotificationLinksKept st st' := fun k => (h k).symm

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    NotificationLinksKept st' st := fun k => by rw [h]

/-- Two stores agreeing up to a rewrite that keeps every object's link codes
keep the codes. -/
theorem of_map {st st' : SystemState} (g : KernelObject → KernelObject)
    (hg : ∀ o, objNotificationLinkCodes (some (g o)) = objNotificationLinkCodes (some o))
    (h : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).map g = (st.objects[k]?).map g) :
    NotificationLinksKept st' st := fun k => by
  have e := h k
  revert e
  cases st'.objects[k]? <;> cases st.objects[k]? <;> intro e
  · rfl
  · cases e
  · cases e
  · rename_i a b
    simp only [Option.map_some, Option.some.injEq] at e
    rw [← hg a, e, hg b]

/-- An insert whose object holds its slot's link codes keeps the codes. -/
theorem insert {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k o)
    (h : objNotificationLinkCodes (some o) = objNotificationLinkCodes st.objects[k]?) :
    NotificationLinksKept st' st := fun x => by
  rw [hO]
  by_cases hx : x = k
  · subst hx
    have e : (st.objects.insert x o)[x]? = some o :=
      RobinHood.RHTable.getElem?_insert_self st.objects x o hInv
    rw [e]; exact h
  · have e : (st.objects.insert k o)[x]? = st.objects[x]? :=
      RobinHood.RHTable.getElem?_insert_ne st.objects k x o
        (by intro h'; exact hx (eq_of_beq h').symm) hInv
    rw [e]

/-- A store whose object holds its slot's link codes keeps the codes. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (h : objNotificationLinkCodes (some o) = objNotificationLinkCodes st.objects[k]?) :
    NotificationLinksKept st' st := by
  unfold SeLe4n.Model.storeObject at hS; cases hS
  exact .insert hInv rfl h

/-- A thread update keeps the codes: a thread holds neither link word. -/
theorem updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) (g : TCB → TCB)
    (hInv : st.objects.invExt) : NotificationLinksKept (st.updateTcb tid g) st := fun k => by
  by_cases hk : tid.toObjId = k
  · subst hk
    cases hT : st.getTcb? tid with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT]
    | some t =>
      have h' := SystemState.updateTcb_getTcb?_self st tid g hInv
      rw [hT] at h'
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT, (SystemState.getTcb?_eq_some_iff _ _ _).mp h']
      rfl
  · rw [SystemState.updateTcb_objects_ne _ _ _ _ hk hInv]

/-- A context update keeping the context's notification code keeps the codes. -/
theorem updateSchedContext (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hg : ∀ sc, (g sc).notificationCode = sc.notificationCode := by intro _; rfl) :
    NotificationLinksKept (st.updateSchedContext s g) st := fun k => by
  by_cases hk : s.toObjId = k
  · subst hk
    cases hS : st.getSchedContext? s with
    | none => rw [SystemState.updateSchedContext_eq_self_of_none hS]
    | some sc =>
      have h' := SystemState.updateSchedContext_getSchedContext?_self st s g hInv
      rw [hS] at h'
      rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS,
        (SystemState.getSchedContext?_eq_some_iff _ _ _).mp h']
      simp only [objNotificationLinkCodes, hg]
  · rw [SystemState.updateSchedContext_objects_ne _ _ _ _ hk hInv]

/-- **A write confined to reply objects keeps the codes**: every slot not
holding a reply is kept, and a reply stays a reply.  A reply holds neither link
word, so the donation stack's pushes and pops are of this shape. -/
theorem of_replyWrite {st st' : SystemState}
    (hNR : ∀ k : SeLe4n.ObjId, (∀ r : Reply, st.objects[k]? ≠ some (.reply r)) →
      st'.objects[k]? = st.objects[k]?)
    (hR : ∀ (k : SeLe4n.ObjId) (r : Reply), st.objects[k]? = some (.reply r) →
      ∃ r', st'.objects[k]? = some (.reply r')) :
    NotificationLinksKept st' st := fun k => by
  by_cases h : ∃ r : Reply, st.objects[k]? = some (.reply r)
  · obtain ⟨r, hr⟩ := h
    obtain ⟨r', hr'⟩ := hR k r hr
    rw [hr, hr']; rfl
  · rw [hNR k (fun r e => h ⟨r, e⟩)]

/-- A step keeping every notification and every context keeps the codes. -/
theorem of_lookups_eq {st st' : SystemState}
    (hN : ∀ n, st'.getNotification? n = st.getNotification? n)
    (hS : ∀ s, st'.getSchedContext? s = st.getSchedContext? s) :
    NotificationLinksKept st' st := fun k => by
  have eN := hN k
  have eS := hS (SeLe4n.SchedContextId.ofObjId k)
  unfold SystemState.getNotification? at eN
  unfold SystemState.getSchedContext? at eS
  have e2 : (SeLe4n.SchedContextId.ofObjId k).toObjId = k := rfl
  rw [e2] at eS
  cases h1 : st'.objects[k]? with
  | none =>
    cases h2 : st.objects[k]? with
    | none => rfl
    | some o =>
      rw [h1, h2] at eN eS
      cases o <;> simp_all [objNotificationLinkCodes]
  | some o' =>
    cases h2 : st.objects[k]? with
    | none => rw [h1, h2] at eN eS; cases o' <;> simp_all [objNotificationLinkCodes]
    | some o =>
      rw [h1, h2] at eN eS
      cases o' <;> cases o <;> simp_all [objNotificationLinkCodes]

/-- **The codes kept by a step that writes no notification and no context**:
each of either state's notifications and contexts is the other's at its key. -/
theorem of_kindFrames {st st' : SystemState}
    (hNf : ∀ (a : SeLe4n.ObjId) (n : Notification), st.objects[a]? = some (.notification n) →
      st'.objects[a]? = some (.notification n))
    (hNb : ∀ (a : SeLe4n.ObjId) (n : Notification), st'.objects[a]? = some (.notification n) →
      st.objects[a]? = some (.notification n))
    (hSf : ∀ (a : SeLe4n.ObjId) (sc : SchedContext), st.objects[a]? = some (.schedContext sc) →
      st'.objects[a]? = some (.schedContext sc))
    (hSb : ∀ (a : SeLe4n.ObjId) (sc : SchedContext), st'.objects[a]? = some (.schedContext sc) →
      st.objects[a]? = some (.schedContext sc)) :
    NotificationLinksKept st' st := fun k => by
  cases h2 : st'.objects[k]? with
  | some o' =>
    cases o' with
    | notification n => rw [hNb k n h2]
    | schedContext sc => rw [hSb k sc h2]
    | _ =>
      cases h1 : st.objects[k]? with
      | none => rfl
      | some o =>
        cases o with
        | notification n => have h3 := hNf k n h1; rw [h2] at h3; cases h3
        | schedContext sc => have h3 := hSf k sc h1; rw [h2] at h3; cases h3
        | _ => rfl
  | none =>
    cases h1 : st.objects[k]? with
    | none => rfl
    | some o =>
      cases o with
      | notification n => have h3 := hNf k n h1; rw [h2] at h3; cases h3
      | schedContext sc => have h3 := hSf k sc h1; rw [h2] at h3; cases h3
      | _ => rfl

end NotificationLinksKept

/-- A step keeping every slot's link codes keeps the agreement. -/
theorem notificationLinksAgree_of_kept {st st' : SystemState} (hK : NotificationLinksKept st' st)
    (h : notificationLinksAgree st) : notificationLinksAgree st' := fun n s => by
  rw [hK n, hK s]; exact h n s

/-- A store holding no link agrees. -/
theorem notificationLinksAgree_of_clear {st : SystemState}
    (h : ∀ k : SeLe4n.ObjId, objNotificationLinkCodes st.objects[k]? = (0, 0)) :
    notificationLinksAgree st := fun n s => by
  rw [h n, h s]
  exact ⟨fun e => absurd e (by omega), fun e => absurd e (by omega)⟩

/-- The default state holds no object, so no link. -/
theorem default_notificationLinksAgree : notificationLinksAgree (default : SystemState) :=
  notificationLinksAgree_of_clear fun k => by
    have e : (default : SystemState).objects[k]? = none := by
      simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty _ _
    rw [e]; rfl

/-- **A link set between two clear ends keeps the agreement**: slot `a`'s
notification code set to `b`, slot `b`'s context code set to `a`, both clear
before, every other slot's codes kept. -/
theorem notificationLinksAgree_of_link {st st' : SystemState} (h : notificationLinksAgree st)
    {a b : SeLe4n.ObjId} (ha0 : (objNotificationLinkCodes st.objects[a]?).1 = 0)
    (hb0 : (objNotificationLinkCodes st.objects[b]?).2 = 0)
    (hA : objNotificationLinkCodes st'.objects[a]? =
      (b.val + 1, (objNotificationLinkCodes st.objects[a]?).2))
    (hB : objNotificationLinkCodes st'.objects[b]? =
      ((objNotificationLinkCodes st.objects[b]?).1, a.val + 1))
    (hO : ∀ k, k ≠ a → k ≠ b →
      objNotificationLinkCodes st'.objects[k]? = objNotificationLinkCodes st.objects[k]?) :
    notificationLinksAgree st' := by
  have hId : ∀ {x y : SeLe4n.ObjId}, x.val = y.val → x = y := fun {x y} e => by
    cases x; cases y; cases e; rfl
  have hne : a ≠ b := by
    intro e
    rcases objNotificationLinkCodes_fst_or_snd st'.objects[a]? with e' | e'
    · rw [hA] at e'; simp at e'
    · rw [e, hB] at e'; simp at e'
  have hfst : ∀ t, t ≠ a →
      (objNotificationLinkCodes st'.objects[t]?).1 = (objNotificationLinkCodes st.objects[t]?).1 := by
    intro t ht
    by_cases htb : t = b
    · rw [htb, hB]
    · rw [hO t ht htb]
  have hsnd : ∀ s, s ≠ b →
      (objNotificationLinkCodes st'.objects[s]?).2 = (objNotificationLinkCodes st.objects[s]?).2 := by
    intro s hs
    by_cases hsa : s = a
    · rw [hsa, hA]
    · rw [hO s hsa hs]
  intro t s
  by_cases ht : t = a
  · rw [ht, hA]
    by_cases hs : s = b
    · rw [hs, hB]; exact ⟨fun _ => rfl, fun _ => rfl⟩
    · rw [hsnd s hs]
      dsimp only
      constructor
      · intro e; exact absurd (hId (by omega : s.val = b.val)) hs
      · intro e; have := (h a s).mpr e; omega
  · rw [hfst t ht]
    by_cases hs : s = b
    · rw [hs, hB]
      dsimp only
      constructor
      · intro e; have := (h t b).mp e; omega
      · intro e; exact absurd (hId (by omega : t.val = a.val)) ht
    · rw [hsnd s hs]; exact h t s

/-- **A link cleared at both ends keeps the agreement**: slot `a` named `b`,
and both codes of the link are cleared, every other slot's codes kept. -/
theorem notificationLinksAgree_of_unlink {st st' : SystemState} (h : notificationLinksAgree st)
    {a b : SeLe4n.ObjId} (hab : (objNotificationLinkCodes st.objects[a]?).1 = b.val + 1)
    (hA : objNotificationLinkCodes st'.objects[a]? = (0, (objNotificationLinkCodes st.objects[a]?).2))
    (hB : objNotificationLinkCodes st'.objects[b]? = ((objNotificationLinkCodes st.objects[b]?).1, 0))
    (hO : ∀ k, k ≠ a → k ≠ b →
      objNotificationLinkCodes st'.objects[k]? = objNotificationLinkCodes st.objects[k]?) :
    notificationLinksAgree st' := by
  have hba : (objNotificationLinkCodes st.objects[b]?).2 = a.val + 1 := (h a b).mp hab
  have hId : ∀ {x y : SeLe4n.ObjId}, x.val = y.val → x = y := fun {x y} e => by
    cases x; cases y; cases e; rfl
  have hne : a ≠ b := by
    rintro rfl
    rcases objNotificationLinkCodes_fst_or_snd st.objects[a]? with e | e <;> omega
  have hfst : ∀ t, t ≠ a →
      (objNotificationLinkCodes st'.objects[t]?).1 = (objNotificationLinkCodes st.objects[t]?).1 := by
    intro t ht
    by_cases htb : t = b
    · subst htb; rw [hB]
    · rw [hO t ht htb]
  have hsnd : ∀ s, s ≠ b →
      (objNotificationLinkCodes st'.objects[s]?).2 = (objNotificationLinkCodes st.objects[s]?).2 := by
    intro s hs
    by_cases hsa : s = a
    · subst hsa; rw [hA]
    · rw [hO s hsa hs]
  intro t s
  by_cases ht : t = a
  · subst ht
    rw [hA]
    refine ⟨fun e => absurd e (by dsimp only; omega), fun e => ?_⟩
    by_cases hsb : s = b
    · subst hsb; rw [hB] at e; exact absurd e (by dsimp only; omega)
    · rw [hsnd s hsb] at e
      have e' := (h t s).mpr e
      rw [hab] at e'
      exact absurd (hId (by omega)) (Ne.symm hsb)
  · rw [hfst t ht]
    by_cases hsb : s = b
    · subst hsb
      rw [hB]
      refine ⟨fun e => ?_, fun e => absurd e (by dsimp only; omega)⟩
      have e' := (h t s).mp e
      rw [hba] at e'
      exact absurd (hId (by omega)) ht
    · rw [hsnd s hsb]; exact h t s

/-- A record update's object store is the one it names. -/
private theorem objects_withObjects (st : SystemState) (O : RobinHood.RHTable SeLe4n.ObjId KernelObject) :
    ({ st with objects := O } : SystemState).objects = O := rfl

private theorem objects_insert_self (t : RobinHood.RHTable SeLe4n.ObjId KernelObject)
    (k : SeLe4n.ObjId) (v : KernelObject) (h : t.invExt) : (t.insert k v)[k]? = some v :=
  RobinHood.RHTable.getElem?_insert_self t k v h

private theorem objects_insert_ne (t : RobinHood.RHTable SeLe4n.ObjId KernelObject)
    {k k' : SeLe4n.ObjId} (v : KernelObject) (hNe : k ≠ k') (h : t.invExt) :
    (t.insert k v)[k']? = t[k']? :=
  RobinHood.RHTable.getElem?_insert_ne t k k' v (fun e => hNe (eq_of_beq e)) h

/-- **`schedContext_bindNtfn` keeps the agreement**: it links a context bound to
no notification and a notification bound to no context. -/
theorem bindNotificationSchedLink_preserves_notificationLinksAgree (st : SystemState)
    (s : SeLe4n.SchedContextId) (n : SeLe4n.ObjId) (hInv : st.objects.invExt)
    {sc : SchedContext} {ntfn : Notification}
    (hS : st.getSchedContext? s = some sc) (hS0 : sc.notificationCode = 0)
    (hN : st.getNotification? n = some ntfn) (hN0 : ntfn.schedContextCode = 0)
    (h : notificationLinksAgree st) :
    notificationLinksAgree (bindNotificationSchedLink st s n) := by
  obtain ⟨-, e⟩ := bindNotificationSchedLink_eq hS hN hInv
  have hSraw := (SystemState.getSchedContext?_eq_some_iff st s sc).mp hS
  have hNraw := (SystemState.getNotification?_eq_some_iff st n ntfn).mp hN
  have hNe : s.toObjId ≠ n := by intro e; rw [e, hNraw] at hSraw; cases hSraw
  have hI1 := SystemState.updateSchedContext_preserves_objects_invExt st s
    (fun sc => { sc with notificationCode := n.val + 1 }) hInv
  have hObj : (bindNotificationSchedLink st s n).objects =
      (st.updateSchedContext s (fun sc => { sc with notificationCode := n.val + 1 })).objects.insert n
        (.notification { ntfn with schedContextCode := s.val + 1 }) := by rw [e]
  refine notificationLinksAgree_of_link h (a := n) (b := s.toObjId)
    (by rw [hNraw]; exact hN0) (by rw [hSraw]; exact hS0) ?_ ?_ ?_
  · rw [hObj, objects_insert_self _ _ _ hI1, hNraw]; rfl
  · rw [hObj, objects_insert_ne _ _ (Ne.symm hNe) hI1,
      SystemState.updateSchedContext_eq_of_some hS]
    rw [objects_withObjects, objects_insert_self _ _ _ hInv, hSraw]; rfl
  · intro k hkn hks
    rw [hObj, objects_insert_ne _ _ (Ne.symm hkn) hI1,
      SystemState.updateSchedContext_objects_ne _ _ _ _ (Ne.symm hks) hInv]

/-- **The bind on a notification capability keeps the agreement.** -/
theorem schedContextBindNotification_preserves_notificationLinksAgree {st st' : SystemState}
    {vScId : SeLe4n.ValidObjId} {n : SeLe4n.ObjId} (hInv : st.objects.invExt)
    (hStep : schedContextBindNotification vScId n st = .ok ((), st'))
    (h : notificationLinksAgree st) : notificationLinksAgree st' := by
  obtain ⟨hA, rfl⟩ := schedContextBindNotification_ok_admitted hStep
  obtain ⟨sc, ntfn, hS, hS0, hN, hN0⟩ := schedContextBindNotificationAdmitted_facts hA
  exact bindNotificationSchedLink_preserves_notificationLinksAgree st _ n hInv hS hS0 hN hN0 h

/-- **`schedContext_unbindNtfn` keeps the agreement**: under it, a context naming
a notification is named back, so the unbind clears both ends. -/
theorem unbindSchedContextNotification_preserves_notificationLinksAgree (st : SystemState)
    (s : SeLe4n.SchedContextId) (hInv : st.objects.invExt) (h : notificationLinksAgree st) :
    notificationLinksAgree (unbindSchedContextNotification st s) := by
  unfold unbindSchedContextNotification
  cases hS : st.getSchedContext? s with
  | none => exact h
  | some sc =>
    simp only []
    cases hC : sc.notificationCode with
    | zero => exact h
    | succ k =>
      simp only []
      have hSraw := (SystemState.getSchedContext?_eq_some_iff st s sc).mp hS
      have hk : (objNotificationLinkCodes st.objects[(⟨k⟩ : SeLe4n.ObjId)]?).1 =
          s.toObjId.val + 1 :=
        (h ⟨k⟩ s.toObjId).mpr (by rw [hSraw]; simp [objNotificationLinkCodes, hC])
      obtain ⟨ntfn, hNraw, hNc⟩ : ∃ ntfn, st.objects[(⟨k⟩ : SeLe4n.ObjId)]? =
          some (.notification ntfn) ∧ ntfn.schedContextCode = s.val + 1 := by
        cases hO : st.objects[(⟨k⟩ : SeLe4n.ObjId)]? with
        | none => rw [hO] at hk; exact absurd hk (by simp [objNotificationLinkCodes])
        | some o =>
          rw [hO] at hk
          cases o with
          | notification ntfn => exact ⟨ntfn, rfl, hk⟩
          | _ => exact absurd hk (by simp [objNotificationLinkCodes])
      have hNames : notificationNamesSchedContext st ⟨k⟩ s = true := by
        unfold notificationNamesSchedContext
        rw [(SystemState.getNotification?_eq_some_iff st ⟨k⟩ ntfn).mpr hNraw]
        simp [hNc]
      rw [hNames]
      simp only [↓reduceIte]
      have hNe : s.toObjId ≠ ⟨k⟩ := by intro e; rw [e, hNraw] at hSraw; cases hSraw
      have hI1 := SystemState.updateSchedContext_preserves_objects_invExt st s
        (fun c => { c with notificationCode := 0 }) hInv
      have h1 : (st.updateSchedContext s (fun c => { c with notificationCode := 0 })).objects[
          (⟨k⟩ : SeLe4n.ObjId)]? = some (.notification ntfn) := by
        rw [SystemState.updateSchedContext_objects_ne _ _ _ _ hNe hInv]; exact hNraw
      have hObj : ((st.updateSchedContext s (fun c => { c with notificationCode := 0 })).modifyObject
          ⟨k⟩ (mapNotificationSchedContext 0)).objects =
          (st.updateSchedContext s (fun c => { c with notificationCode := 0 })).objects.insert ⟨k⟩
            (.notification { ntfn with schedContextCode := 0 }) := by
        rw [modifyObject_mapNotificationSchedContext_eq h1 0]
      refine notificationLinksAgree_of_unlink h (a := ⟨k⟩) (b := s.toObjId) hk ?_ ?_ ?_
      · rw [hObj, objects_insert_self _ _ _ hI1, hNraw]; rfl
      · rw [hObj, objects_insert_ne _ _ (Ne.symm hNe) hI1,
          SystemState.updateSchedContext_eq_of_some hS]
        rw [objects_withObjects, objects_insert_self _ _ _ hInv, hSraw]; rfl
      · intro j hj1 hj2
        rw [hObj, objects_insert_ne _ _ (Ne.symm hj1) hI1,
          SystemState.updateSchedContext_objects_ne _ _ _ _ (Ne.symm hj2) hInv]

/-- **`schedContext_maybeUnbindNtfn` keeps the agreement**: the unbind read from
the notification's end is the context's end or nothing. -/
theorem unbindNotificationSchedContext_preserves_notificationLinksAgree (st : SystemState)
    (n : SeLe4n.ObjId) (hInv : st.objects.invExt) (h : notificationLinksAgree st) :
    notificationLinksAgree (unbindNotificationSchedContext st n) := by
  rcases unbindNotificationSchedContext_cases st n with e | ⟨c, e⟩ <;> rw [e]
  · exact h
  · exact unbindSchedContextNotification_preserves_notificationLinksAgree st c hInv h

end SeLe4n.Kernel
