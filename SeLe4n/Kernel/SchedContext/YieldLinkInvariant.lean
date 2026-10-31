/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/
import SeLe4n.Kernel.SchedContext.YieldLink

/-! # The yield link agrees in both directions

WS-ZA ZA6.6: **`SystemState.yieldLinksAgree`** — a thread names a context as
the one it yielded to exactly when that context names the thread as its yielder,
as `schedContextBindingBidirectional` holds a binding.  It reads each slot only
through its **yield codes** (`objYieldCodes`: a thread's yield-to code, a
context's yield-from code, `0` for every other object and an empty slot), so a
step that keeps every slot's codes keeps it (`yieldLinksAgree_of_kept`), and a
step that clears both ends of one link keeps it (`yieldLinksAgree_of_unlink`).
It is carried by every kernel transition the way the refill state is
(`RunQueueLinkStage.yield`). -/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- WS-ZA ZA6.6: the yield codes a slot holds: a thread's yield-to code first,
a context's yield-from code second, `0` for every other end. -/
def objYieldCodes : Option KernelObject → Nat × Nat
  | some (.tcb t) => (t.yieldToCode, 0)
  | some (.schedContext sc) => (0, sc.yieldFromCode)
  | _ => (0, 0)

/-- One of a slot's two codes is `0`: a slot holds a thread or a context, never
both. -/
theorem objYieldCodes_fst_or_snd (o : Option KernelObject) :
    (objYieldCodes o).1 = 0 ∨ (objYieldCodes o).2 = 0 := by
  rcases o with _ | o
  · exact Or.inl rfl
  · cases o <;> simp [objYieldCodes]

theorem objYieldCodes_of_getTcb? {st : SystemState} {tid : SeLe4n.ThreadId} {t : TCB}
    (h : st.getTcb? tid = some t) :
    objYieldCodes st.objects[tid.toObjId]? = (t.yieldToCode, 0) := by
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp h]; rfl

theorem objYieldCodes_of_getSchedContext? {st : SystemState} {s : SeLe4n.SchedContextId}
    {sc : SchedContext} (h : st.getSchedContext? s = some sc) :
    objYieldCodes st.objects[s.toObjId]? = (0, sc.yieldFromCode) := by
  rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mp h]; rfl

/-- A slot whose yield-from code is set holds a context. -/
theorem getSchedContext?_of_objYieldCodes_snd {st : SystemState} {k : SeLe4n.ObjId} {n : Nat}
    (h : (objYieldCodes st.objects[k]?).2 = n + 1) :
    ∃ sc, st.getSchedContext? (SeLe4n.SchedContextId.ofObjId k) = some sc ∧
      sc.yieldFromCode = n + 1 := by
  cases hO : st.objects[k]? with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    cases o <;> simp only [objYieldCodes] at h <;> first
      | cases h
      | exact ⟨_, (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hO, h⟩

/-- A slot whose yield-to code is set holds a thread. -/
theorem getTcb?_of_objYieldCodes_fst {st : SystemState} {k : SeLe4n.ObjId} {n : Nat}
    (h : (objYieldCodes st.objects[k]?).1 = n + 1) :
    ∃ t, st.getTcb? (SeLe4n.ThreadId.ofObjId k) = some t ∧ t.yieldToCode = n + 1 := by
  cases hO : st.objects[k]? with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    cases o <;> simp only [objYieldCodes] at h <;> first
      | cases h
      | exact ⟨_, (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO, h⟩

/-- A slot's yield codes, read through the typed lookups at its key. -/
theorem objYieldCodes_eq_lookups (st : SystemState) (k : SeLe4n.ObjId) :
    objYieldCodes st.objects[k]? =
      (((st.getTcb? (SeLe4n.ThreadId.ofObjId k)).map TCB.yieldToCode).getD 0,
        ((st.getSchedContext? (SeLe4n.SchedContextId.ofObjId k)).map
          SchedContext.yieldFromCode).getD 0) := by
  have e1 : (SeLe4n.ThreadId.ofObjId k).toObjId = k := rfl
  have e2 : (SeLe4n.SchedContextId.ofObjId k).toObjId = k := rfl
  unfold SystemState.getTcb? SystemState.getSchedContext?
  rw [e1, e2]
  rcases st.objects[k]? with _ | o
  · rfl
  · cases o <;> rfl

/-- WS-ZA ZA6.6: every slot of the post-state holds the yield codes of the
pre-state's.  A step that writes no link keeps the codes. -/
def YieldLinksKept (st' st : SystemState) : Prop :=
  ∀ k : SeLe4n.ObjId, objYieldCodes st'.objects[k]? = objYieldCodes st.objects[k]?

namespace YieldLinksKept

theorem refl (st : SystemState) : YieldLinksKept st st := fun _ => rfl

theorem trans {a b d : SystemState} (h₁ : YieldLinksKept a b) (h₂ : YieldLinksKept b d) :
    YieldLinksKept a d := fun k => (h₁ k).trans (h₂ k)

theorem symm {st st' : SystemState} (h : YieldLinksKept st' st) : YieldLinksKept st st' :=
  fun k => (h k).symm

theorem of_objects_eq {st st' : SystemState} (h : st'.objects = st.objects) :
    YieldLinksKept st' st := fun k => by rw [h]

/-- Two stores agreeing up to a rewrite that keeps every object's yield codes
keep the codes. -/
theorem of_map {st st' : SystemState} (g : KernelObject → KernelObject)
    (hg : ∀ o, objYieldCodes (some (g o)) = objYieldCodes (some o))
    (h : ∀ k : SeLe4n.ObjId, (st'.objects[k]?).map g = (st.objects[k]?).map g) :
    YieldLinksKept st' st := fun k => by
  have e := h k
  revert e
  cases st'.objects[k]? <;> cases st.objects[k]? <;> intro e
  · rfl
  · cases e
  · cases e
  · rename_i a b
    simp only [Option.map_some, Option.some.injEq] at e
    rw [← hg a, e, hg b]

/-- An insert whose object holds its slot's yield codes keeps the codes. -/
theorem insert {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k o)
    (h : objYieldCodes (some o) = objYieldCodes st.objects[k]?) : YieldLinksKept st' st :=
  fun x => by
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

/-- A store whose object holds its slot's yield codes keeps the codes. -/
theorem storeObject {st st' : SystemState} {k : SeLe4n.ObjId} {o : KernelObject}
    (hInv : st.objects.invExt) (hS : SeLe4n.Model.storeObject k o st = .ok ((), st'))
    (h : objYieldCodes (some o) = objYieldCodes st.objects[k]?) : YieldLinksKept st' st := by
  unfold SeLe4n.Model.storeObject at hS; cases hS
  exact .insert hInv rfl h

/-- A thread update keeping the thread's yield-to code keeps the codes. -/
theorem updateTcb (st : SystemState) (tid : SeLe4n.ThreadId) (g : TCB → TCB)
    (hInv : st.objects.invExt) (hg : ∀ t, (g t).yieldToCode = t.yieldToCode) :
    YieldLinksKept (st.updateTcb tid g) st := fun k => by
  by_cases hk : tid.toObjId = k
  · subst hk
    cases hT : st.getTcb? tid with
    | none => rw [SystemState.updateTcb_eq_self_of_none hT]
    | some t =>
      have h' := SystemState.updateTcb_getTcb?_self st tid g hInv
      rw [hT] at h'
      rw [objYieldCodes_of_getTcb? hT, objYieldCodes_of_getTcb? h', hg]
  · rw [SystemState.updateTcb_objects_ne _ _ _ _ hk hInv]

/-- A context update keeping the context's yield-from code keeps the codes. -/
theorem updateSchedContext (st : SystemState) (s : SeLe4n.SchedContextId)
    (g : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hg : ∀ sc, (g sc).yieldFromCode = sc.yieldFromCode) :
    YieldLinksKept (st.updateSchedContext s g) st := fun k => by
  by_cases hk : s.toObjId = k
  · subst hk
    cases hS : st.getSchedContext? s with
    | none => rw [SystemState.updateSchedContext_eq_self_of_none hS]
    | some sc =>
      have h' := SystemState.updateSchedContext_getSchedContext?_self st s g hInv
      rw [hS] at h'
      rw [objYieldCodes_of_getSchedContext? hS, objYieldCodes_of_getSchedContext? h', hg]
  · rw [SystemState.updateSchedContext_objects_ne _ _ _ _ hk hInv]

/-- **The yield codes read through the typed lookups**: every thread's
yield-to code and every context's yield-from code reads as before, `0` for an
absent one. -/
theorem of_lookups {st st' : SystemState}
    (hT : ∀ t, ((st'.getTcb? t).map TCB.yieldToCode).getD 0 =
      ((st.getTcb? t).map TCB.yieldToCode).getD 0)
    (hS : ∀ s, ((st'.getSchedContext? s).map SchedContext.yieldFromCode).getD 0 =
      ((st.getSchedContext? s).map SchedContext.yieldFromCode).getD 0) :
    YieldLinksKept st' st := fun k => by
  rw [objYieldCodes_eq_lookups, objYieldCodes_eq_lookups, hT, hS]

/-- A step keeping every thread's yield-to code and every context keeps the
codes. -/
theorem of_tcbMap {st st' : SystemState}
    (hT : ∀ t, (st'.getTcb? t).map TCB.yieldToCode = (st.getTcb? t).map TCB.yieldToCode)
    (hS : ∀ s, st'.getSchedContext? s = st.getSchedContext? s) : YieldLinksKept st' st :=
  .of_lookups (fun t => by rw [hT]) (fun s => by rw [hS])

/-- A step keeping every thread and every context keeps the codes. -/
theorem of_getTcb?_eq {st st' : SystemState} (hT : ∀ t, st'.getTcb? t = st.getTcb? t)
    (hS : ∀ s, st'.getSchedContext? s = st.getSchedContext? s) : YieldLinksKept st' st :=
  .of_tcbMap (fun t => by rw [hT]) hS

/-- **The yield codes kept by a step's own frames**: every thread of either
state is one of the other's at its key with the same yield-to code, and every
context of either is the other's at its key.  A step writing threads over
threads with their yield codes kept and no context — an IPC splice, a link
patch — is one. -/
theorem of_frames {st st' : SystemState}
    (hTf : ∀ (a : SeLe4n.ObjId) (t : TCB), st.objects[a]? = some (KernelObject.tcb t) →
      ∃ t', st'.objects[a]? = some (KernelObject.tcb t') ∧ t.yieldToCode = t'.yieldToCode)
    (hTb : ∀ (a : SeLe4n.ObjId) (t' : TCB), st'.objects[a]? = some (KernelObject.tcb t') →
      ∃ t, st.objects[a]? = some (KernelObject.tcb t) ∧ t.yieldToCode = t'.yieldToCode)
    (hSf : ∀ (a : SeLe4n.ObjId) (sc : SchedContext), st.objects[a]? = some (KernelObject.schedContext sc) →
      st'.objects[a]? = some (KernelObject.schedContext sc))
    (hSb : ∀ (a : SeLe4n.ObjId) (sc : SchedContext), st'.objects[a]? = some (KernelObject.schedContext sc) →
      st.objects[a]? = some (KernelObject.schedContext sc)) :
    YieldLinksKept st' st := fun k => by
  cases h2 : st'.objects[k]? with
  | some o' =>
    cases o' with
    | tcb t' =>
      obtain ⟨t, h1, e⟩ := hTb k t' h2
      rw [h1]; simp only [objYieldCodes, e]
    | schedContext sc => rw [hSb k sc h2]
    | _ =>
      cases h1 : st.objects[k]? with
      | none => rfl
      | some o =>
        cases o with
        | tcb t => obtain ⟨_, h3, -⟩ := hTf k t h1; rw [h2] at h3; cases h3
        | schedContext sc => have h3 := hSf k sc h1; rw [h2] at h3; cases h3
        | _ => rfl
  | none =>
    cases h1 : st.objects[k]? with
    | none => rfl
    | some o =>
      cases o with
      | tcb t => obtain ⟨_, h3, -⟩ := hTf k t h1; rw [h2] at h3; cases h3
      | schedContext sc => have h3 := hSf k sc h1; rw [h2] at h3; cases h3
      | _ => rfl

end YieldLinksKept

end SeLe4n.Kernel

namespace SeLe4n.Model.SystemState

open SeLe4n.Kernel

/-- WS-ZA ZA6.6: **the yield link agrees in both directions** — the slot `t`
names `s` as the context it yielded to (seL4-MCS's `tcbYieldTo`) exactly when
the slot `s` names `t` as its yielder (`scYieldFrom`).  So each end names the
other, as `schedContextBindingBidirectional` holds a binding: a context's
yielder is a thread linked back to it, and a thread's yield-to context is a
context linked back to it. -/
def yieldLinksAgree (st : SystemState) : Prop :=
  ∀ t s : SeLe4n.ObjId,
    (objYieldCodes st.objects[t]?).1 = s.val + 1 ↔ (objYieldCodes st.objects[s]?).2 = t.val + 1

/-- A step keeping every slot's yield codes keeps the agreement. -/
theorem yieldLinksAgree_of_kept {st st' : SystemState} (hK : YieldLinksKept st' st)
    (h : st.yieldLinksAgree) : st'.yieldLinksAgree := fun t s => by
  rw [hK t, hK s]; exact h t s

/-- A store holding no link agrees. -/
theorem yieldLinksAgree_of_clear {st : SystemState}
    (h : ∀ k : SeLe4n.ObjId, objYieldCodes st.objects[k]? = (0, 0)) : st.yieldLinksAgree :=
  fun t s => by
    rw [h t, h s]
    exact ⟨fun e => absurd e (by omega), fun e => absurd e (by omega)⟩

/-- The default state holds no object, so no link. -/
theorem default_yieldLinksAgree : (default : SystemState).yieldLinksAgree :=
  yieldLinksAgree_of_clear fun k => by
    have e : (default : SystemState).objects[k]? = none := by
      simp only [RHTable_getElem?_eq_get?]; exact RHTable_get?_empty 16 (by omega)
    rw [e]; rfl

/-- **Clearing both ends of one link keeps the agreement**: when the slot `a`
names `b` as its yield-to context, a step that clears `a`'s yield-to code and
`b`'s yield-from code and keeps every other code agrees as the pre-state did. -/
theorem yieldLinksAgree_of_unlink {st st' : SystemState} (h : st.yieldLinksAgree)
    {a b : SeLe4n.ObjId} (hab : (objYieldCodes st.objects[a]?).1 = b.val + 1)
    (hA : objYieldCodes st'.objects[a]? = (0, (objYieldCodes st.objects[a]?).2))
    (hB : objYieldCodes st'.objects[b]? = ((objYieldCodes st.objects[b]?).1, 0))
    (hO : ∀ k, k ≠ a → k ≠ b → objYieldCodes st'.objects[k]? = objYieldCodes st.objects[k]?) :
    st'.yieldLinksAgree := by
  have hba : (objYieldCodes st.objects[b]?).2 = a.val + 1 := (h a b).mp hab
  have hId : ∀ {x y : SeLe4n.ObjId}, x.val = y.val → x = y := fun {x y} e => by
    cases x; cases y; cases e; rfl
  have hne : a ≠ b := by
    rintro rfl
    rcases objYieldCodes_fst_or_snd st.objects[a]? with e | e <;> omega
  have hfst : ∀ t, t ≠ a →
      (objYieldCodes st'.objects[t]?).1 = (objYieldCodes st.objects[t]?).1 := by
    intro t ht
    by_cases htb : t = b
    · subst htb; rw [hB]
    · rw [hO t ht htb]
  have hsnd : ∀ s, s ≠ b →
      (objYieldCodes st'.objects[s]?).2 = (objYieldCodes st.objects[s]?).2 := by
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

-- ============================================================================
-- The cancel and the completion keep the store and the agreement
-- ============================================================================

theorem cancelYieldTo_preserves_objects_invExt (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : (cancelYieldTo st tid).objects.invExt := by
  unfold cancelYieldTo
  split
  · split
    · exact hInv
    · exact updateTcb_preserves_objects_invExt _ _ _
        (updateSchedContext_preserves_objects_invExt _ _ _ hInv)
  · exact hInv

theorem setConsumed_preserves_objects_invExt (st : SystemState) (s : SeLe4n.SchedContextId)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) : (setConsumed st s t).objects.invExt := by
  unfold setConsumed
  split
  · exact updateTcb_preserves_objects_invExt _ _ _
      (updateSchedContext_preserves_objects_invExt _ _ _ hInv)
  · exact hInv

theorem completeYieldTo_preserves_objects_invExt (st : SystemState) (y : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : (completeYieldTo st y).objects.invExt := by
  unfold completeYieldTo
  split
  · split
    · exact hInv
    · exact cancelYieldTo_preserves_objects_invExt _ _
        (setConsumed_preserves_objects_invExt _ _ _ hInv)
  · exact hInv

theorem cancelYieldFrom_preserves_objects_invExt (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : (cancelYieldFrom st s).objects.invExt := by
  unfold cancelYieldFrom
  split
  · split
    · exact hInv
    · exact updateTcb_preserves_objects_invExt _ _ _
        (updateSchedContext_preserves_objects_invExt _ _ _ hInv)
  · exact hInv

theorem completeYieldFrom_preserves_objects_invExt (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) : (completeYieldFrom st s).objects.invExt := by
  unfold completeYieldFrom
  split
  · split
    · exact hInv
    · exact cancelYieldFrom_preserves_objects_invExt _ _
        (setConsumed_preserves_objects_invExt _ _ _ hInv)
  · exact hInv

/-- After the cancel, the thread has yielded to no context. -/
theorem cancelYieldTo_yieldToCode_self (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) {t' : TCB}
    (h : (cancelYieldTo st tid).getTcb? tid = some t') : t'.yieldToCode = 0 := by
  unfold cancelYieldTo at h
  split at h
  · rename_i t hT
    split at h
    · rename_i h0; rw [hT] at h; cases h; exact h0
    · rw [updateTcb_getTcb?_self _ _ _ (updateSchedContext_preserves_objects_invExt _ _ _ hInv),
        updateSchedContext_getTcb? _ _ _ hInv, hT] at h
      cases h; rfl
  · rename_i hT; rw [hT] at h; cases h

/-- **A cleared yield-to code stays cleared** across a thread write that keeps
or clears it. -/
theorem updateTcb_yieldToCode_zero (st : SystemState) (u : SeLe4n.ThreadId) (f : TCB → TCB)
    (hf : ∀ x, x.yieldToCode = 0 → (f x).yieldToCode = 0) (hInv : st.objects.invExt)
    (tid : SeLe4n.ThreadId) (h0 : ∀ t, st.getTcb? tid = some t → t.yieldToCode = 0) {t' : TCB}
    (h : (st.updateTcb u f).getTcb? tid = some t') : t'.yieldToCode = 0 := by
  by_cases e : u = tid
  · subst e
    rw [updateTcb_getTcb?_self _ _ _ hInv] at h
    cases hT : st.getTcb? u with
    | none => rw [hT] at h; cases h
    | some t => rw [hT] at h; cases h; exact hf t (h0 t hT)
  · rw [updateTcb_getTcb?_ne _ _ _ hInv _
      (fun h' => e (SeLe4n.ThreadId.toObjId_injective _ _ h'))] at h
    exact h0 _ h

theorem setConsumed_yieldToCode_zero (st : SystemState) (s : SeLe4n.SchedContextId)
    (y : SeLe4n.ThreadId) (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId)
    (h0 : ∀ t, st.getTcb? tid = some t → t.yieldToCode = 0) :
    ∀ t, (setConsumed st s y).getTcb? tid = some t → t.yieldToCode = 0 := by
  intro t ht
  unfold setConsumed at ht
  split at ht
  · rename_i sc _
    refine updateTcb_yieldToCode_zero (st.updateSchedContext s SchedContext.updateConsumed) y
      (TCB.withConsumed · sc.consumedReading.toUInt64) (fun x hx => hx)
      (updateSchedContext_preserves_objects_invExt _ _ _ hInv) tid ?_ ht
    intro t2 h2
    rw [updateSchedContext_getTcb? _ _ _ hInv] at h2
    exact h0 _ h2
  · exact h0 _ ht

theorem cancelYieldFrom_yieldToCode_zero (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId)
    (h0 : ∀ t, st.getTcb? tid = some t → t.yieldToCode = 0) :
    ∀ t, (cancelYieldFrom st s).getTcb? tid = some t → t.yieldToCode = 0 := by
  intro t ht
  unfold cancelYieldFrom at ht
  split at ht
  · split at ht
    · exact h0 _ ht
    · rename_i k _
      refine updateTcb_yieldToCode_zero (st.updateSchedContext s SchedContext.yieldCleared) ⟨k⟩
        TCB.yieldCleared (fun _ _ => rfl)
        (updateSchedContext_preserves_objects_invExt _ _ _ hInv) tid ?_ ht
      intro t2 h2
      rw [updateSchedContext_getTcb? _ _ _ hInv] at h2
      exact h0 _ h2
  · exact h0 _ ht

/-- **The completion of a context's recorded yield leaves a cleared yield-to
code cleared**: a thread that has yielded to no context still has not. -/
theorem completeYieldFrom_yieldToCode_zero (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId)
    (h0 : ∀ t, st.getTcb? tid = some t → t.yieldToCode = 0) {t' : TCB}
    (h : (completeYieldFrom st s).getTcb? tid = some t') : t'.yieldToCode = 0 := by
  unfold completeYieldFrom at h
  split at h
  · split at h
    · exact h0 _ h
    · rename_i k _
      exact cancelYieldFrom_yieldToCode_zero _ s (setConsumed_preserves_objects_invExt st s ⟨k⟩ hInv)
        tid (setConsumed_yieldToCode_zero st s ⟨k⟩ hInv tid h0) _ h
  · exact h0 _ h

/-- ...and so does a held context's completion. -/
theorem completeHeldYield_yieldToCode_zero (st : SystemState) (held : Nat)
    (hInv : st.objects.invExt) (tid : SeLe4n.ThreadId)
    (h0 : ∀ t, st.getTcb? tid = some t → t.yieldToCode = 0) {t' : TCB}
    (h : (completeHeldYield st held).getTcb? tid = some t') : t'.yieldToCode = 0 := by
  unfold completeHeldYield at h
  split at h
  · exact h0 _ h
  · exact completeYieldFrom_yieldToCode_zero _ _ hInv tid h0 h

/-- After the context's end of the cancel, the context records no yielder. -/
theorem cancelYieldFrom_yieldFromCode_self (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) {sc' : SchedContext}
    (h : (cancelYieldFrom st s).getSchedContext? s = some sc') : sc'.yieldFromCode = 0 := by
  unfold cancelYieldFrom at h
  split at h
  · rename_i sc hS
    split at h
    · rename_i h0; rw [hS] at h; cases h; exact h0
    · rw [updateTcb_getSchedContext? _ _ _
        (updateSchedContext_preserves_objects_invExt _ _ _ hInv),
        updateSchedContext_getSchedContext?_self _ _ _ hInv, hS] at h
      cases h; rfl
  · rename_i hS; rw [hS] at h; cases h

/-- After the completion of its recorded yield, the context records no yielder. -/
theorem completeYieldFrom_yieldFromCode_self (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) {sc' : SchedContext}
    (h : (completeYieldFrom st s).getSchedContext? s = some sc') : sc'.yieldFromCode = 0 := by
  unfold completeYieldFrom at h
  split at h
  · rename_i sc hS
    split at h
    · rename_i h0; rw [hS] at h; cases h; exact h0
    · exact cancelYieldFrom_yieldFromCode_self _ s (setConsumed_preserves_objects_invExt _ _ _ hInv) h
  · rename_i hS; rw [hS] at h; cases h

theorem completeHeldYield_preserves_objects_invExt (st : SystemState) (held : Nat)
    (hInv : st.objects.invExt) : (completeHeldYield st held).objects.invExt := by
  unfold completeHeldYield
  split
  · exact hInv
  · exact completeYieldFrom_preserves_objects_invExt _ _ hInv

/-- `setConsumed` writes no link. -/
theorem setConsumed_yieldLinksKept (st : SystemState) (s : SeLe4n.SchedContextId)
    (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) : YieldLinksKept (setConsumed st s t) st := by
  unfold setConsumed
  split
  · rename_i sc _
    exact (YieldLinksKept.updateTcb _ t (TCB.withConsumed · sc.consumedReading.toUInt64)
      (updateSchedContext_preserves_objects_invExt _ s
      SchedContext.updateConsumed hInv) (fun _ => rfl)).trans
      (YieldLinksKept.updateSchedContext _ _ _ hInv fun _ => rfl)
  · exact .refl _

/-- **The cancel keeps the agreement**: it clears both ends of the thread's one
link (`yieldLinksAgree_of_unlink`), the context's end found where the thread's
names it. -/
theorem cancelYieldTo_preserves_yieldLinksAgree (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (h : st.yieldLinksAgree) : (cancelYieldTo st tid).yieldLinksAgree := by
  unfold cancelYieldTo
  split
  · rename_i t hT
    split
    · exact h
    · rename_i k hc
      have hab : (objYieldCodes st.objects[tid.toObjId]?).1 =
          (⟨k⟩ : SeLe4n.SchedContextId).toObjId.val + 1 := by
        rw [objYieldCodes_of_getTcb? hT]; exact hc
      obtain ⟨sc, hS, -⟩ := getSchedContext?_of_objYieldCodes_snd ((h _ _).mp hab)
      have hS' : st.getSchedContext? ⟨k⟩ = some sc := hS
      have hInv1 := updateSchedContext_preserves_objects_invExt st ⟨k⟩ SchedContext.yieldCleared hInv
      have hT1 : (st.updateSchedContext ⟨k⟩ SchedContext.yieldCleared).getTcb? tid = some t := by
        rw [updateSchedContext_getTcb? _ _ _ hInv]; exact hT
      have hS1 : (st.updateSchedContext ⟨k⟩ SchedContext.yieldCleared).getSchedContext? ⟨k⟩ =
          some sc.yieldCleared := by
        rw [updateSchedContext_getSchedContext?_self _ _ _ hInv, hS']; rfl
      have hne : tid.toObjId ≠ (⟨k⟩ : SeLe4n.SchedContextId).toObjId := fun e => by
        have e1 := (getTcb?_eq_some_iff _ _ _).mp hT
        have e2 := (getSchedContext?_eq_some_iff _ _ _).mp hS'
        rw [e] at e1; rw [e1] at e2; cases e2
      have hT2 : ((st.updateSchedContext ⟨k⟩ SchedContext.yieldCleared).updateTcb tid
          TCB.yieldCleared).getTcb? tid = some t.yieldCleared := by
        rw [updateTcb_getTcb?_self _ _ _ hInv1, hT1]; rfl
      refine yieldLinksAgree_of_unlink h hab ?_ ?_ ?_
      · rw [objYieldCodes_of_getTcb? hT2, objYieldCodes_of_getTcb? hT]; rfl
      · rw [updateTcb_objects_ne _ _ _ _ hne hInv1, objYieldCodes_of_getSchedContext? hS1,
          objYieldCodes_of_getSchedContext? hS']; rfl
      · intro x hx1 hx2
        rw [updateTcb_objects_ne _ _ _ _ (Ne.symm hx1) hInv1,
          updateSchedContext_objects_ne _ _ _ _ (Ne.symm hx2) hInv]
  · exact h

theorem completeYieldTo_preserves_yieldLinksAgree (st : SystemState) (y : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (h : st.yieldLinksAgree) : (completeYieldTo st y).yieldLinksAgree := by
  unfold completeYieldTo
  split
  · split
    · exact h
    · exact cancelYieldTo_preserves_yieldLinksAgree _ _
        (setConsumed_preserves_objects_invExt _ _ _ hInv)
        (yieldLinksAgree_of_kept (setConsumed_yieldLinksKept _ _ _ hInv) h)
  · exact h

/-- **The context's end of the cancel keeps the agreement**: it clears both
ends of the context's one link (`yieldLinksAgree_of_unlink`), the yielder's end
found where the context's names it. -/
theorem cancelYieldFrom_preserves_yieldLinksAgree (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) (h : st.yieldLinksAgree) :
    (cancelYieldFrom st s).yieldLinksAgree := by
  unfold cancelYieldFrom
  split
  · rename_i sc hS
    split
    · exact h
    · rename_i k hc
      have hba : (objYieldCodes st.objects[s.toObjId]?).2 =
          (⟨k⟩ : SeLe4n.ThreadId).toObjId.val + 1 := by
        rw [objYieldCodes_of_getSchedContext? hS]; exact hc
      have hab := (h _ _).mpr hba
      obtain ⟨t, hT, -⟩ := getTcb?_of_objYieldCodes_fst hab
      have hT' : st.getTcb? ⟨k⟩ = some t := hT
      have hInv1 := updateSchedContext_preserves_objects_invExt st s SchedContext.yieldCleared hInv
      have hne : (⟨k⟩ : SeLe4n.ThreadId).toObjId ≠ s.toObjId := fun e => by
        have e1 := (getTcb?_eq_some_iff _ _ _).mp hT'
        have e2 := (getSchedContext?_eq_some_iff _ _ _).mp hS
        rw [e] at e1; rw [e1] at e2; cases e2
      have hT1 : (st.updateSchedContext s SchedContext.yieldCleared).getTcb? ⟨k⟩ = some t := by
        rw [updateSchedContext_getTcb? _ _ _ hInv]; exact hT'
      have hS1 : (st.updateSchedContext s SchedContext.yieldCleared).getSchedContext? s =
          some sc.yieldCleared := by
        rw [updateSchedContext_getSchedContext?_self _ _ _ hInv, hS]; rfl
      have hT2 : ((st.updateSchedContext s SchedContext.yieldCleared).updateTcb ⟨k⟩
          TCB.yieldCleared).getTcb? ⟨k⟩ = some t.yieldCleared := by
        rw [updateTcb_getTcb?_self _ _ _ hInv1, hT1]; rfl
      refine yieldLinksAgree_of_unlink h hab ?_ ?_ ?_
      · rw [objYieldCodes_of_getTcb? hT2, objYieldCodes_of_getTcb? hT']; rfl
      · rw [updateTcb_objects_ne _ _ _ _ hne hInv1, objYieldCodes_of_getSchedContext? hS1,
          objYieldCodes_of_getSchedContext? hS]; rfl
      · intro x hx1 hx2
        rw [updateTcb_objects_ne _ _ _ _ (Ne.symm hx1) hInv1,
          updateSchedContext_objects_ne _ _ _ _ (Ne.symm hx2) hInv]
  · exact h

theorem completeYieldFrom_preserves_yieldLinksAgree (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) (h : st.yieldLinksAgree) :
    (completeYieldFrom st s).yieldLinksAgree := by
  unfold completeYieldFrom
  split
  · split
    · exact h
    · exact cancelYieldFrom_preserves_yieldLinksAgree _ _
        (setConsumed_preserves_objects_invExt _ _ _ hInv)
        (yieldLinksAgree_of_kept (setConsumed_yieldLinksKept _ _ _ hInv) h)
  · exact h

theorem completeHeldYield_preserves_yieldLinksAgree (st : SystemState) (held : Nat)
    (hInv : st.objects.invExt) (h : st.yieldLinksAgree) :
    (completeHeldYield st held).yieldLinksAgree := by
  unfold completeHeldYield
  split
  · exact h
  · exact completeYieldFrom_preserves_yieldLinksAgree _ _ hInv h

/-- **On agreeing links the completion a context records is seL4-MCS's
`schedContext_completeYieldTo` of its yielder**: the yielder names the context
back, so handing it the context's consumed time and cancelling its link from
either end is one write sequence. -/
theorem completeYieldFrom_eq_completeYieldTo (st : SystemState) (s : SeLe4n.SchedContextId)
    (hInv : st.objects.invExt) (h : st.yieldLinksAgree) {sc : SchedContext} {k : Nat}
    (hS : st.getSchedContext? s = some sc) (hk : sc.yieldFromCode = k + 1) :
    completeYieldFrom st s = completeYieldTo st ⟨k⟩ := by
  have hba : (objYieldCodes st.objects[s.toObjId]?).2 = (⟨k⟩ : SeLe4n.ThreadId).toObjId.val + 1 := by
    rw [objYieldCodes_of_getSchedContext? hS]; exact hk
  obtain ⟨t, hT, ht⟩ := getTcb?_of_objYieldCodes_fst ((h _ _).mpr hba)
  have hT' : st.getTcb? ⟨k⟩ = some t := hT
  have hK := setConsumed_yieldLinksKept st s ⟨k⟩ hInv
  have hb' : (objYieldCodes (setConsumed st s ⟨k⟩).objects[s.toObjId]?).2 = k + 1 := by
    rw [hK, objYieldCodes_of_getSchedContext? hS]; exact hk
  have ha' : (objYieldCodes (setConsumed st s ⟨k⟩).objects[(⟨k⟩ : SeLe4n.ThreadId).toObjId]?).1 =
      s.val + 1 := by
    rw [hK, objYieldCodes_of_getTcb? hT']; exact ht
  obtain ⟨sc', hS', hk'⟩ := getSchedContext?_of_objYieldCodes_snd hb'
  obtain ⟨t', hT'', ht'⟩ := getTcb?_of_objYieldCodes_fst ha'
  unfold completeYieldFrom completeYieldTo
  rw [hS, hT']
  simp only [hk, ht]
  unfold cancelYieldFrom cancelYieldTo
  have e1 : (setConsumed st s ⟨k⟩).getSchedContext? s = some sc' := hS'
  have e2 : (setConsumed st ⟨s.toObjId.val⟩ ⟨k⟩).getTcb? ⟨k⟩ = some t' := hT''
  have ht2 : t'.yieldToCode = s.toObjId.val + 1 := ht'
  rw [e1, e2]
  simp only [hk', ht2]
  rfl

end SeLe4n.Model.SystemState
