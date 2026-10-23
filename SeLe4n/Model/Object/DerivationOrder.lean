-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.Object.DerivationLinks

/-!
# The derivation tree's preorder (WS-ZA ZA5.4 part 15, design D1)

seL4 keeps its capabilities in one doubly linked list, the mapping database, in
which a capability's derived copies follow it.  seLe4n keeps a tree instead,
and this module states the order in which the tree lists its slots: the
preorder of the forest whose top level is the root chain, each slot followed by
its children's subtrees in sibling order (`TreeOrder`).  That preorder is seL4's
list: each tree operation moves it as seL4's list moves.

* An insert puts the new child first under its source, which is right after
  the source in preorder (`TreeOrder.addEdge`, `insertAfter`).
* A delete puts the slot's children where the slot was among its siblings, so
  the preorder loses the slot and nothing else moves (`TreeOrder.spliceNode`).
* A move renames the slot in place (`TreeOrder.moveNode`).
* A new root goes at the end of the root chain (`TreeOrder.appendRoot`).

The preorder is unique (`TreeOrder.unique`), lists each slot once and lists
exactly the slots the tree names (`TreeOrder.mem_iff`).
-/

namespace SeLe4n.Model

namespace CapDerivationTree

/-- **The preorder of a forest.**  `ForestOrder ch S P`: `P` lists the forest
whose top level is `S`, where `ch x` is `x`'s children, each slot followed by
its children's subtrees and then by its later siblings' subtrees. -/
inductive ForestOrder (ch : SlotRef → List SlotRef) : List SlotRef → List SlotRef → Prop
  | nil : ForestOrder ch [] []
  | cons {x : SlotRef} {S Q R : List SlotRef} :
      ForestOrder ch (ch x) Q → ForestOrder ch S R → ForestOrder ch (x :: S) (x :: (Q ++ R))

namespace ForestOrder

variable {ch ch' : SlotRef → List SlotRef}

/-- Two forests side by side list one after the other. -/
theorem append {A B P₁ P₂ : List SlotRef} (h₁ : ForestOrder ch A P₁) (h₂ : ForestOrder ch B P₂) :
    ForestOrder ch (A ++ B) (P₁ ++ P₂) := by
  induction h₁ with
  | nil => simpa using h₂
  | cons hQ _ _ ihR =>
    rw [List.cons_append, List.cons_append, List.append_assoc]
    exact .cons hQ ihR

/-- The preorder of a forest is unique. -/
theorem unique {S P P' : List SlotRef} (h : ForestOrder ch S P) (h' : ForestOrder ch S P') :
    P = P' := by
  induction h generalizing P' with
  | nil => cases h'; rfl
  | cons _ _ ihQ ihR =>
    cases h' with
    | cons hQ' hR' => rw [ihQ hQ', ihR hR']

/-- The top level is listed. -/
theorem mem_of_top {S P : List SlotRef} (h : ForestOrder ch S P) {x : SlotRef} (hx : x ∈ S) :
    x ∈ P := by
  induction h with
  | nil => simp at hx
  | cons _ _ _ ihR =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihR hx))

/-- A listed slot's children are listed. -/
theorem mem_of_child {S P : List SlotRef} (h : ForestOrder ch S P) {x y : SlotRef}
    (hx : x ∈ P) (hy : y ∈ ch x) : y ∈ P := by
  induction h with
  | nil => simp at hx
  | cons hQ _ ihQ ihR =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ (hQ.mem_of_top hy))
    · rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_cons_of_mem _ (List.mem_append_left _ (ihQ hx))
      · exact List.mem_cons_of_mem _ (List.mem_append_right _ (ihR hx))

/-- A listed slot is on the top level or a listed slot's child. -/
theorem mem_cases {S P : List SlotRef} (h : ForestOrder ch S P) {x : SlotRef} (hx : x ∈ P) :
    x ∈ S ∨ ∃ y ∈ P, x ∈ ch y := by
  induction h with
  | nil => simp at hx
  | @cons z S Q R hQ _ ihQ ihR =>
    rcases List.mem_cons.mp hx with rfl | hx
    · exact .inl (List.mem_cons_self ..)
    · rcases List.mem_append.mp hx with hx | hx
      · rcases ihQ hx with hx | ⟨y, hy, hxy⟩
        · exact .inr ⟨z, List.mem_cons_self .., hx⟩
        · exact .inr ⟨y, List.mem_cons_of_mem _ (List.mem_append_left _ hy), hxy⟩
      · rcases ihR hx with hx | ⟨y, hy, hxy⟩
        · exact .inl (List.mem_cons_of_mem _ hx)
        · exact .inr ⟨y, List.mem_cons_of_mem _ (List.mem_append_right _ hy), hxy⟩

/-- The preorder reads only the listed slots' children. -/
theorem congr {S P : List SlotRef} (h : ForestOrder ch S P) (hc : ∀ x ∈ P, ch x = ch' x) :
    ForestOrder ch' S P := by
  induction h with
  | nil => exact .nil
  | @cons x S Q R _ _ ihQ ihR =>
    have hx := hc x (List.mem_cons_self ..)
    refine .cons (hx ▸ ihQ fun y hy => hc y ?_) (ihR fun y hy => hc y ?_)
    · exact List.mem_cons_of_mem _ (List.mem_append_left _ hy)
    · exact List.mem_cons_of_mem _ (List.mem_append_right _ hy)

/-- **Splicing a slot out of a forest**: when every slot but `n` takes `n`'s
children in `n`'s place, and the top level does too, the preorder loses `n` and
nothing else moves. -/
theorem splice (n : SlotRef) (hch : ∀ q, q ≠ n → ch' q = replaceSlot n (ch n) (ch q)) :
    ∀ {S P : List SlotRef}, ForestOrder ch S P → P.Nodup →
      ForestOrder ch' (replaceSlot n (ch n) S) (P.filter (· ≠ n)) := by
  intro S P h
  induction h with
  | nil => intro _; exact .nil
  | @cons x S Q R hQ hR ihQ ihR =>
    intro hnd
    have hnd' := (List.nodup_cons.mp hnd).2
    have hQnd := (List.nodup_append.mp hnd').1
    have hRnd := (List.nodup_append.mp hnd').2.1
    have hS : replaceSlot n (ch n) (x :: S) =
        (if x = n then ch n else [x]) ++ replaceSlot n (ch n) S := by
      simp [replaceSlot]
    rw [hS, List.filter_cons, List.filter_append]
    by_cases hx : x = n
    · subst hx
      have hxQ : x ∉ Q := fun hm => (List.nodup_cons.mp hnd).1 (List.mem_append_left _ hm)
      have hxch : x ∉ ch x := fun hm => hxQ (hQ.mem_of_top hm)
      have e1 := ihQ hQnd
      rw [replaceSlot_of_not_mem hxch] at e1
      simp only [if_true, ne_eq, not_true_eq_false, decide_false, Bool.false_eq_true, if_false]
      exact e1.append (ihR hRnd)
    · simp only [ne_eq, hx, not_false_eq_true, decide_true, if_true]
      refine .cons ?_ (ihR hRnd)
      rw [hch x hx]; exact ihQ hQnd

end ForestOrder

/-- **Insert `c` right after `p`**, at `p`'s first occurrence; a list without
`p` is unchanged. -/
def insertAfter (p c : SlotRef) : List SlotRef → List SlotRef
  | [] => []
  | x :: l => if x = p then x :: c :: l else x :: insertAfter p c l

theorem insertAfter_of_not_mem {p c : SlotRef} : ∀ {l : List SlotRef}, p ∉ l → insertAfter p c l = l
  | [], _ => rfl
  | x :: l, h => by
    have hx : x ≠ p := fun e => h (e ▸ List.mem_cons_self ..)
    rw [insertAfter, if_neg hx, insertAfter_of_not_mem (fun hm => h (List.mem_cons_of_mem _ hm))]

theorem insertAfter_append {p c : SlotRef} :
    ∀ (l₁ l₂ : List SlotRef), p ∉ l₁ ∨ p ∉ l₂ →
      insertAfter p c (l₁ ++ l₂) = insertAfter p c l₁ ++ insertAfter p c l₂
  | [], _, _ => rfl
  | x :: l, l₂, h => by
    rw [List.cons_append, insertAfter.eq_2, insertAfter.eq_2]
    by_cases hx : x = p
    · subst hx
      rw [if_pos rfl, if_pos rfl]
      rcases h with h | h
      · exact absurd (List.mem_cons_self ..) h
      · rw [insertAfter_of_not_mem h]; rfl
    · rw [if_neg hx, if_neg hx, List.cons_append,
        insertAfter_append l l₂ (h.imp (fun h hm => h (List.mem_cons_of_mem _ hm)) id)]

/-- In a list naming `p` once, `c` lands right after `p`. -/
theorem insertAfter_split {p c : SlotRef} {a b : List SlotRef} (ha : p ∉ a) :
    insertAfter p c (a ++ p :: b) = a ++ p :: c :: b := by
  rw [insertAfter_append a (p :: b) (.inl ha), insertAfter_of_not_mem ha]
  simp [insertAfter]

theorem mem_insertAfter {p c x : SlotRef} :
    ∀ {l : List SlotRef}, x ∈ insertAfter p c l ↔ x ∈ l ∨ (x = c ∧ p ∈ l)
  | [] => by simp [insertAfter]
  | y :: l => by
    rw [insertAfter.eq_2]
    by_cases hy : y = p
    · subst hy
      simp only [if_true, List.mem_cons, true_or, and_true]
      constructor
      · rintro (h | h | h)
        · exact .inl (.inl h)
        · exact .inr h
        · exact .inl (.inr h)
      · rintro ((h | h) | h)
        · exact .inl h
        · exact .inr (.inr h)
        · exact .inr (.inl h)
    · rw [if_neg hy]
      simp only [List.mem_cons]
      rw [mem_insertAfter (l := l)]
      constructor
      · rintro (h | h | ⟨h1, h2⟩)
        · exact .inl (.inl h)
        · exact .inl (.inr h)
        · exact .inr ⟨h1, .inr h2⟩
      · rintro ((h | h) | ⟨h1, h | h⟩)
        · exact .inl h
        · exact .inr (.inl h)
        · exact absurd h.symm hy
        · exact .inr (.inr ⟨h1, h⟩)

theorem insertAfter_nodup {p c : SlotRef} (hc : c ∉ l) : l.Nodup → (insertAfter p c l).Nodup := by
  induction l with
  | nil => intro _; exact List.nodup_nil
  | cons y l ih =>
    intro hnd
    have hcl : c ∉ l := fun hm => hc (List.mem_cons_of_mem _ hm)
    have hcy : c ≠ y := fun e => hc (e ▸ List.mem_cons_self ..)
    rw [insertAfter.eq_2]
    split
    · exact List.nodup_cons.mpr ⟨fun hm => (List.mem_cons.mp hm).elim (fun e => hcy e.symm)
        (List.nodup_cons.mp hnd).1, List.nodup_cons.mpr ⟨hcl, (List.nodup_cons.mp hnd).2⟩⟩
    · refine List.nodup_cons.mpr ⟨fun hm => ?_, ih hcl (List.nodup_cons.mp hnd).2⟩
      rcases mem_insertAfter.mp hm with hm | ⟨rfl, -⟩
      · exact (List.nodup_cons.mp hnd).1 hm
      · exact hcy rfl

namespace ForestOrder

variable {ch ch' : SlotRef → List SlotRef}

/-- **Inserting a first child**: when `c`, a slot the forest does not list,
becomes `p`'s first child and nothing else changes, `c` lands right after `p`
in the preorder. -/
theorem insertChild (p c : SlotRef) (hp : ch' p = c :: ch p) (hc : ch' c = [])
    (hq : ∀ q, q ≠ p → q ≠ c → ch' q = ch q) :
    ∀ {S P : List SlotRef}, ForestOrder ch S P → P.Nodup → c ∉ P →
      ForestOrder ch' S (insertAfter p c P) := by
  intro S P h
  induction h with
  | nil => intro _ _; exact .nil
  | @cons x S Q R hQ hR ihQ ihR =>
    intro hnd hcP
    have hxQR := (List.nodup_cons.mp hnd).1
    have hnd' := (List.nodup_cons.mp hnd).2
    have hdis := (List.nodup_append.mp hnd').2.2
    have hcQ : c ∉ Q := fun hm => hcP (List.mem_cons_of_mem _ (List.mem_append_left _ hm))
    have hcR : c ∉ R := fun hm => hcP (List.mem_cons_of_mem _ (List.mem_append_right _ hm))
    have hcx : x ≠ c := fun e => hcP (e ▸ List.mem_cons_self ..)
    rw [insertAfter.eq_2]
    by_cases hx : x = p
    · subst hx
      rw [if_pos rfl]
      have hQ' : ForestOrder ch' (ch x) Q := hQ.congr fun y hy => (hq y
        (fun e => hxQR (e ▸ List.mem_append_left _ hy)) (fun e => hcQ (e ▸ hy))).symm
      have hR' : ForestOrder ch' S R := hR.congr fun y hy => (hq y
        (fun e => hxQR (e ▸ List.mem_append_right _ hy)) (fun e => hcR (e ▸ hy))).symm
      have hC : ForestOrder ch' (ch' x) (c :: ([] ++ Q)) := by
        rw [hp]; exact .cons (by rw [hc]; exact .nil) hQ'
      exact .cons hC hR'
    · rw [if_neg hx]
      have hsplit : p ∉ Q ∨ p ∉ R := by
        by_cases hpQ : p ∈ Q
        · exact .inr fun hpR => hdis _ hpQ _ hpR rfl
        · exact .inl hpQ
      rw [insertAfter_append Q R hsplit]
      refine .cons ?_ (ihR (List.nodup_append.mp hnd').2.1 hcR)
      rw [hq x hx hcx]
      exact ihQ (List.nodup_append.mp hnd').1 hcQ

/-- **Renaming a slot the forest lists to one it does not** renames it in
place in the preorder. -/
theorem rename (old new : SlotRef)
    (hch : ∀ q, q ≠ old → ch' q = (ch (renameSlot new old q)).map (renameSlot old new))
    (hon : old ≠ new) :
    ∀ {S P : List SlotRef}, ForestOrder ch S P → new ∉ P →
      ForestOrder ch' (S.map (renameSlot old new)) (P.map (renameSlot old new)) := by
  intro S P h
  induction h with
  | nil => intro _; exact .nil
  | @cons x S Q R hQ hR ihQ ihR =>
    intro hn
    have hxn : x ≠ new := fun e => hn (e ▸ List.mem_cons_self ..)
    rw [List.map_cons, List.map_cons, List.map_append]
    refine .cons ?_ (ihR fun hm => hn (List.mem_cons_of_mem _ (List.mem_append_right _ hm)))
    rw [hch _ (renameSlot_ne_old hon x), renameSlot_back hxn]
    exact ihQ fun hm => hn (List.mem_cons_of_mem _ (List.mem_append_left _ hm))

end ForestOrder

/-- A slot the tree names has a parent, a child or a place in the root chain. -/
theorem mentions_iff (cdt : CapDerivationTree) (x : SlotRef) :
    cdt.mentions x ↔ cdt.parentOf x ≠ none ∨ cdt.childrenOf x ≠ [] ∨ x ∈ cdt.rootChains.flatten := by
  constructor
  · rintro (⟨e, he, hp | hc⟩ | hr)
    · refine .inr (.inl fun h0 => ?_)
      have : e.child ∈ cdt.childrenOf x := by
        simp only [childrenOf, List.mem_map, List.mem_filter]
        exact ⟨e, ⟨he, by simp [CapDerivationEdge.isParentOf, hp]⟩, rfl⟩
      rw [h0] at this; simp at this
    · exact .inl fun h0 => (parentOf_eq_none_iff cdt x).mp h0 e he hc
    · exact .inr (.inr hr)
  · rintro (hp | hc | hr)
    · cases hP : cdt.parentOf x with
      | none => exact absurd hP hp
      | some y =>
        refine Classical.byContradiction fun hn => ?_
        exact hp (parentOf_of_not_mentions hn)
    · cases hC : cdt.childrenOf x with
      | nil => exact absurd hC hc
      | cons y _ =>
        obtain ⟨e, he, hp, -⟩ := childrenOf_to_edge cdt x y (hC ▸ List.mem_cons_self ..)
        exact .inl ⟨e, he, .inl hp⟩
    · exact .inr hr

/-- **The tree's preorder.**  `P` lists the forest whose top level is the root
chain, each slot followed by its children's subtrees in sibling order; it lists
each slot once and every slot the tree names; and the parentless slots form at
most one chain.  This is seL4's mapping-database list. -/
structure TreeOrder (cdt : CapDerivationTree) (P : List SlotRef) : Prop where
  forest : ForestOrder cdt.childrenOf cdt.rootChains.flatten P
  nodup : P.Nodup
  complete : ∀ x, cdt.mentions x → x ∈ P
  oneChain : cdt.rootChains.length ≤ 1

namespace TreeOrder

variable {cdt : CapDerivationTree} {P : List SlotRef}

/-- A tree has at most one preorder. -/
theorem unique {P' : List SlotRef} (h : TreeOrder cdt P) (h' : TreeOrder cdt P') : P = P' :=
  h.forest.unique h'.forest

/-- **The preorder lists exactly the slots the tree names.** -/
theorem mem_iff (h : TreeOrder cdt P) (x : SlotRef) : x ∈ P ↔ cdt.mentions x := by
  refine ⟨fun hx => ?_, h.complete x⟩
  rcases h.forest.mem_cases hx with hr | ⟨y, -, hy⟩
  · exact .inr hr
  · obtain ⟨e, he, -, hc⟩ := childrenOf_to_edge cdt y x hy
    exact .inl ⟨e, he, .inr hc⟩

/-- The empty tree's preorder is empty. -/
theorem empty_tree (hE : cdt.edges = []) (hR : cdt.rootChains = []) : TreeOrder cdt [] where
  forest := by rw [hR]; exact .nil
  nodup := List.nodup_nil
  complete := fun x hx => by
    rcases hx with ⟨e, he, -⟩ | hr
    · rw [hE] at he; simp at he
    · rw [hR] at hr; simp at hr
  oneChain := by rw [hR]; simp

/-- **A new root goes last.**  Appending a slot the tree does not name to the
root chain lists it after every slot. -/
theorem appendRoot (h : TreeOrder cdt P) {r : SlotRef} (hr : ¬ cdt.mentions r) :
    TreeOrder (cdt.appendRoot r) (P ++ [r]) := by
  have hTail : cdt.rootChains.tail = [] := by
    have := h.oneChain
    rcases hc : cdt.rootChains with _ | ⟨c, _ | ⟨d, cs⟩⟩
    · rfl
    · rfl
    · rw [hc] at this; simp at this
  have hFl : (cdt.appendRoot r).rootChains.flatten = cdt.rootChains.flatten ++ [r] := by
    rw [appendRoot_rootChains_eq, rootChains_flatten_eq, hTail]; simp
  have hrP : r ∉ P := fun hm => hr ((h.mem_iff r).mp hm)
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [hFl]
    have hr' : ForestOrder (cdt.appendRoot r).childrenOf [r] [r] := by
      have := ForestOrder.cons (ch := (cdt.appendRoot r).childrenOf) (x := r)
        (Q := []) (R := []) (S := []) (by
          rw [childrenOf_appendRoot, childrenOf_of_not_mentions hr]; exact .nil) .nil
      simpa using this
    exact (h.forest.congr fun x _ => (childrenOf_appendRoot cdt r x).symm).append hr'
  · exact List.nodup_append.mpr ⟨h.nodup, List.nodup_cons.mpr ⟨by simp, List.nodup_nil⟩,
      fun a ha b hb e => hrP (by simp at hb; exact hb ▸ e ▸ ha)⟩
  · rintro x (⟨e, he, hx⟩ | hx)
    · exact List.mem_append_left _ (h.complete x (.inl ⟨e, he, hx⟩))
    · rw [hFl] at hx
      rcases List.mem_append.mp hx with hx | hx
      · exact List.mem_append_left _ (h.complete x (.inr hx))
      · exact List.mem_append_right _ hx
  · rw [appendRoot_rootChains_eq, hTail]; simp

/-- **An insert puts the new child right after its source.**  Deriving a slot
the tree does not name from one it does lists the new slot right after its
source, as seL4's `cteInsert` links the new capability after its source. -/
theorem addEdge (h : TreeOrder cdt P) {p c : SlotRef} (hp : cdt.mentions p)
    (hc : ¬ cdt.mentions c) (op : DerivationOp) :
    TreeOrder (cdt.addEdge p c op) (insertAfter p c P) := by
  have hpc : p ≠ c := fun e => hc (e ▸ hp)
  have hcP : c ∉ P := fun hm => hc ((h.mem_iff c).mp hm)
  refine ⟨?_, insertAfter_nodup hcP h.nodup, ?_, by rw [addEdge_rootChains]; exact h.oneChain⟩
  · rw [addEdge_rootChains]
    refine h.forest.insertChild p c ?_ ?_ ?_ h.nodup hcP
    · rw [childrenOf_addEdge, if_pos rfl]
    · rw [childrenOf_addEdge, if_neg (Ne.symm hpc), childrenOf_of_not_mentions hc]
    · intro q hq _; rw [childrenOf_addEdge, if_neg hq]
  · rintro x (⟨e, he, hx⟩ | hx)
    · rw [addEdge_edges] at he
      rcases List.mem_cons.mp he with rfl | he
      · rcases hx with hx | hx
        · exact mem_insertAfter.mpr (.inl (hx ▸ h.complete p hp))
        · exact mem_insertAfter.mpr (.inr ⟨hx.symm, h.complete p hp⟩)
      · exact mem_insertAfter.mpr (.inl (h.complete x (.inl ⟨e, he, hx⟩)))
    · rw [addEdge_rootChains] at hx
      exact mem_insertAfter.mpr (.inl (h.complete x (.inr hx)))

private theorem map_replaceSlot_of_not_mem {n : SlotRef} {K : List SlotRef} :
    ∀ {cs : List (List SlotRef)}, n ∉ cs.flatten → cs.map (replaceSlot n K) = cs
  | [], _ => rfl
  | c :: cs, h => by
    rw [List.flatten_cons] at h
    rw [List.map_cons, replaceSlot_of_not_mem fun hm => h (List.mem_append_left _ hm),
      map_replaceSlot_of_not_mem fun hm => h (List.mem_append_right _ hm)]

/-- Under a preorder, splicing a slot replaces it by its children in the root
chain: a slot with a parent is in no chain, and a parentless slot the chain
does not list has no children. -/
theorem spliceNode_rootChains_eq (h : TreeOrder cdt P) (hU : cdt.childrenUnique)
    (hR : cdt.rootsParentless) (n : SlotRef) :
    (cdt.spliceNode n).rootChains = cdt.rootChains.map (replaceSlot n (cdt.childrenOf n)) := by
  by_cases hp : cdt.parentOf n = none
  · rw [spliceNode_rootChains_of_root hp]
    unfold spliceRootChains
    by_cases hn : n ∈ cdt.rootChains.flatten
    · rw [if_pos hn]
    · rw [if_neg hn]
      have hK : cdt.childrenOf n = [] := by
        cases hC : cdt.childrenOf n with
        | nil => rfl
        | cons y _ =>
          have hm : cdt.mentions n := (mentions_iff cdt n).mpr (.inr (.inl (by simp [hC])))
          rcases h.forest.mem_cases (h.complete n hm) with hr | ⟨z, -, hz⟩
          · exact absurd hr hn
          · rw [(mem_childrenOf_iff_parentOf hU z n).mp hz] at hp; exact absurd hp (by simp)
      rw [if_pos hK, hK, map_replaceSlot_of_not_mem hn]
  · rw [spliceNode_rootChains_of_parent hR hp,
      map_replaceSlot_of_not_mem fun hm => hp (hR n hm)]

/-- **A delete puts the slot's children where it was.**  Splicing a slot out of
the tree lists every other slot in the same order: its children's subtrees
take its place among its siblings, as seL4's `cteDelete` unlinks one node of
its list. -/
theorem spliceNode (h : TreeOrder cdt P) (hU : cdt.childrenUnique) (hR : cdt.rootsParentless)
    {n : SlotRef} (hs : cdt.parentOf n ≠ some n) :
    TreeOrder (cdt.spliceNode n) (P.filter (· ≠ n)) := by
  have hRC := spliceNode_rootChains_eq h hU hR n
  have hFl : (cdt.spliceNode n).rootChains.flatten =
      replaceSlot n (cdt.childrenOf n) cdt.rootChains.flatten := by
    rw [hRC, flatten_map_replaceSlot]
  have hNot : ¬ (cdt.spliceNode n).mentions n := by
    rw [mentions_iff]
    rintro (hp | hc | hr)
    · exact hp (by rw [parentOf_spliceNode hU hs, if_pos rfl])
    · exact hc (by rw [childrenOf_spliceNode hU hs, if_pos rfl])
    · rw [hFl] at hr
      rcases mem_replaceSlot.mp hr with ⟨-, hne⟩ | ⟨-, hk⟩
      · exact hne rfl
      · exact not_mem_childrenOf_self hU hs hk
  refine ⟨?_, h.nodup.filter _, ?_, by rw [hRC, List.length_map]; exact h.oneChain⟩
  · rw [hFl]
    refine h.forest.splice n (fun q hq => ?_) h.nodup
    rw [childrenOf_spliceNode hU hs, if_neg hq]
  · intro x hx
    have hxn : x ≠ n := fun e => hNot (e ▸ hx)
    exact List.mem_filter.mpr ⟨h.complete x (spliceNode_mentions cdt n x hx), by simp [hxn]⟩

/-- **A move keeps the slot's place.**  Moving a slot the tree names to one it
does not renames it in place in the preorder, as seL4's `cteMove` relinks the
new slot into the old one's list position. -/
theorem moveNode (h : TreeOrder cdt P) {old new : SlotRef} (hnew : ¬ cdt.mentions new)
    (hon : old ≠ new) :
    TreeOrder (cdt.moveNode old new) (P.map (renameSlot old new)) := by
  have hnP : new ∉ P := fun hm => hnew ((h.mem_iff new).mp hm)
  refine ⟨?_, ?_, ?_, by rw [moveNode_rootChains, List.length_map]; exact h.oneChain⟩
  · rw [moveNode_rootChains_flatten]
    refine h.forest.rename old new (fun q hq => ?_) hon hnP
    rw [childrenOf_moveNode hnew hon, if_neg hq]
  · refine nodup_map_of_inj (fun x hx y hy e => ?_) h.nodup
    exact renameSlot_inj (fun (e : x = new) => hnP (e ▸ hx)) (fun (e : y = new) => hnP (e ▸ hy)) e
  · intro x hx
    rcases moveNode_mentions cdt old new x hx with rfl | ⟨hxo, hm⟩
    · -- the moved slot is named only when the old one was
      have hold : cdt.mentions old := by
        have hb : renameSlot x old x = old := by simp [renameSlot]
        rw [mentions_iff] at hx ⊢
        rcases hx with hp | hc | hr
        · rw [parentOf_moveNode hnew hon, if_neg (Ne.symm hon)] at hp
          rw [hb] at hp
          exact .inl fun e => hp (by rw [e]; rfl)
        · rw [childrenOf_moveNode hnew hon, if_neg (Ne.symm hon)] at hc
          rw [hb] at hc
          exact .inr (.inl fun e => hc (by rw [e]; rfl))
        · rw [moveNode_rootChains_flatten, List.mem_map] at hr
          obtain ⟨y, hy, e⟩ := hr
          by_cases hyo : y = old
          · exact .inr (.inr (hyo ▸ hy))
          · simp only [renameSlot, if_neg hyo] at e
            exact absurd (e ▸ hy) (not_root_of_not_mentions hnew)
      exact List.mem_map.mpr ⟨old, h.complete old hold, by simp [renameSlot]⟩
    · exact List.mem_map.mpr ⟨x, h.complete x hm, by simp [renameSlot, hxo]⟩
end TreeOrder

/-! ### Preorder neighbours (WS-ZA ZA5.4 part 20)

What lies next to a slot in the preorder, read from the tree.  The slot after
`u` is its first child, or, when it has none, its next sibling, or a slot
outside the subtree of the parent it is the last child of (`succ_cases`).  The
slot before `u` is its parent, when `u` is a first child, or its previous
sibling or a slot below it, a sibling `u` does not lie below (`pred_cases`).
Finality reads its four link words through these: seL4's `isFinalCapability`
compares a capability with its two mapping-database neighbours. -/

/-- **`b` lies strictly below `a`** in the forest whose children are `ch`. -/
inductive Desc (ch : SlotRef → List SlotRef) : SlotRef → SlotRef → Prop
  | child {a b : SlotRef} : b ∈ ch a → Desc ch a b
  | trans {a m b : SlotRef} : Desc ch a m → b ∈ ch m → Desc ch a b

/-- A descent from a child is a descent from its parent. -/
theorem Desc.head {ch : SlotRef → List SlotRef} {a b c : SlotRef} (hb : b ∈ ch a)
    (h : Desc ch b c) : Desc ch a c := by
  induction h with
  | child hc => exact .trans (.child hb) hc
  | trans _ hc ih => exact .trans ih hc

/-- A descent in the tree's forest is the tree's descent. -/
theorem desc_childrenOf_iff (cdt : CapDerivationTree) (a b : SlotRef) :
    Desc cdt.childrenOf a b ↔ CdtChildReachable cdt a b := by
  constructor
  · intro h
    induction h with
    | child h => exact .child h
    | trans _ h ih => exact .trans ih h
  · intro h
    induction h with
    | child h => exact .child h
    | trans _ h ih => exact .trans ih h

namespace ForestOrder

variable {ch : SlotRef → List SlotRef}

/-- A forest's preorder starts at its first top slot. -/
theorem head_eq {L Q : List SlotRef} (h : ForestOrder ch L Q) : Q.head? = L.head? := by
  cases h <;> rfl

/-- An empty preorder lists an empty forest. -/
theorem eq_nil_of_nil {L : List SlotRef} (h : ForestOrder ch L []) : L = [] := by
  cases h; rfl

/-- Every slot below a listed slot is listed. -/
theorem desc_mem {L Q : List SlotRef} (h : ForestOrder ch L Q) {y v : SlotRef} (hy : y ∈ Q)
    (hv : Desc ch y v) : v ∈ Q := by
  induction hv with
  | child hb => exact h.mem_of_child hy hb
  | trans _ hb ih => exact h.mem_of_child ih hb

/-- Every slot below `x` is in the preorder of `x`'s children. -/
theorem desc_mem_top {x : SlotRef} {Q : List SlotRef} (h : ForestOrder ch (ch x) Q) {v : SlotRef}
    (hv : Desc ch x v) : v ∈ Q := by
  induction hv with
  | child hb => exact h.mem_of_top hb
  | trans _ hb ih => exact h.mem_of_child ih hb

/-- A listed slot is a top slot or lies below one. -/
theorem mem_top_or_desc {L Q : List SlotRef} (h : ForestOrder ch L Q) {w : SlotRef}
    (hw : w ∈ Q) : w ∈ L ∨ ∃ l ∈ L, Desc ch l w := by
  induction h with
  | nil => cases hw
  | @cons x S Q R hQ _ ihQ ihR =>
    rcases List.mem_cons.mp hw with rfl | hw
    · exact .inl (List.mem_cons_self ..)
    · rcases List.mem_append.mp hw with hw | hw
      · rcases ihQ hw with hw | ⟨l, hl, hd⟩
        · exact .inr ⟨x, List.mem_cons_self .., .child hw⟩
        · exact .inr ⟨x, List.mem_cons_self .., hd.head hl⟩
      · rcases ihR hw with hw | ⟨l, hl, hd⟩
        · exact .inl (List.mem_cons_of_mem _ hw)
        · exact .inr ⟨l, List.mem_cons_of_mem _ hl, hd⟩

private theorem getLast?_cons_append (x : SlotRef) (Q R : List SlotRef) :
    (x :: (Q ++ R)).getLast? = R.getLast?.or (Q.getLast?.or (some x)) := by
  rw [show x :: (Q ++ R) = ([x] ++ Q) ++ R by simp, List.getLast?_append, List.getLast?_append]
  rfl

/-- **The last slot of a preorder has no children.** -/
theorem getLast_childless {L Q : List SlotRef} (h : ForestOrder ch L Q) {u : SlotRef}
    (hu : Q.getLast? = some u) : ch u = [] := by
  induction h with
  | nil => cases hu
  | @cons x S Q R hQ _ ihQ ihR =>
    rw [getLast?_cons_append] at hu
    cases hRl : R.getLast? with
    | some r => rw [hRl, Option.some_or] at hu; cases hu; exact ihR hRl
    | none =>
      rw [hRl, Option.none_or] at hu
      cases hQl : Q.getLast? with
      | some q => rw [hQl, Option.some_or] at hu; cases hu; exact ihQ hQl
      | none =>
        rw [hQl, Option.none_or] at hu
        cases hu
        rw [List.getLast?_eq_none_iff.mp hQl] at hQ
        exact eq_nil_of_nil hQ

/-- **The last slot of a preorder is the last of its siblings**: of the top
level when it is a top slot, and of its parent's children. -/
theorem getLast_succNone {L Q : List SlotRef} (h : ForestOrder ch L Q) (hnd : Q.Nodup)
    {u : SlotRef} (hu : Q.getLast? = some u) :
    (u ∈ L → SlotList.succIn L u = none) ∧
      ∀ y ∈ Q, u ∈ ch y → SlotList.succIn (ch y) u = none := by
  induction h with
  | nil => cases hu
  | @cons x S Q R hQ hR ihQ ihR =>
    have hxQR := (List.nodup_cons.mp hnd).1
    have hnd' := (List.nodup_cons.mp hnd).2
    have hQnd := (List.nodup_append.mp hnd').1
    have hRnd := (List.nodup_append.mp hnd').2.1
    have hdis := (List.nodup_append.mp hnd').2.2
    rw [getLast?_cons_append] at hu
    cases hRl : R.getLast? with
    | some r =>
      rw [hRl, Option.some_or] at hu
      cases hu
      have huR : u ∈ R := List.mem_of_getLast? hRl
      have hux : x ≠ u := fun e => hxQR (List.mem_append_right _ (by rw [e]; exact huR))
      obtain ⟨ih1, ih2⟩ := ihR hRnd hRl
      refine ⟨fun hm => ?_, fun y hy hc => ?_⟩
      · rcases List.mem_cons.mp hm with e | hm
        · exact absurd e.symm hux
        · rw [SlotList.succIn_cons, if_neg hux]; exact ih1 hm
      · rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd rfl (hdis u (hQ.mem_of_top hc) u huR)
        · rcases List.mem_append.mp hy with hy | hy
          · exact absurd rfl (hdis u (hQ.mem_of_child hy hc) u huR)
          · exact ih2 y hy hc
    | none =>
      rw [hRl, Option.none_or] at hu
      have hR0 : R = [] := List.getLast?_eq_none_iff.mp hRl
      subst hR0
      have hS0 : S = [] := eq_nil_of_nil hR
      subst hS0
      cases hQl : Q.getLast? with
      | some q =>
        rw [hQl, Option.some_or] at hu
        cases hu
        have huQ : u ∈ Q := List.mem_of_getLast? hQl
        obtain ⟨ih1, ih2⟩ := ihQ hQnd hQl
        refine ⟨fun hm => ?_, fun y hy hc => ?_⟩
        · rcases List.mem_cons.mp hm with e | hm
          · exact absurd (List.mem_append_left _ (e ▸ huQ)) hxQR
          · cases hm
        · rcases List.mem_cons.mp hy with rfl | hy
          · exact ih1 hc
          · rcases List.mem_append.mp hy with hy | hy
            · exact ih2 y hy hc
            · cases hy
      | none =>
        rw [hQl, Option.none_or] at hu
        cases hu
        have hQ0 : Q = [] := List.getLast?_eq_none_iff.mp hQl
        subst hQ0
        refine ⟨fun _ => by simp [SlotList.succIn], fun y hy hc => ?_⟩
        rcases List.mem_cons.mp hy with rfl | hy
        · exact absurd (hQ.mem_of_top hc) (by simp)
        · simp at hy

private theorem mem_of_succIn {l : List SlotRef} {w x : SlotRef}
    (h : SlotList.succIn l w = some x) : w ∈ l :=
  Classical.byContradiction fun hn => by rw [SlotList.succIn_of_not_mem hn] at h; cases h

/-- **The slot after `u` in a preorder** is its first child; or, when it has
none, its next sibling on the top level or among its parent's children, or a
slot outside the subtree of the parent it is the last child of. -/
theorem succ_cases {S P : List SlotRef} (h : ForestOrder ch S P) (hnd : P.Nodup)
    {A B : List SlotRef} {u v : SlotRef} (hP : P = A ++ u :: v :: B) :
    (ch u).head? = some v ∨
      (ch u = [] ∧ (SlotList.succIn S u = some v ∨ ∃ y ∈ P, u ∈ ch y ∧
        (SlotList.succIn (ch y) u = some v ∨
          (SlotList.succIn (ch y) u = none ∧ ¬ Desc ch y v)))) := by
  induction h generalizing A B with
  | nil => cases A <;> simp at hP
  | @cons x S Q R hQ hR ihQ ihR =>
    have hxQR := (List.nodup_cons.mp hnd).1
    have hnd' := (List.nodup_cons.mp hnd).2
    have hQnd := (List.nodup_append.mp hnd').1
    have hRnd := (List.nodup_append.mp hnd').2.1
    have hdis := (List.nodup_append.mp hnd').2.2
    have hsub : ∀ {y}, y ∈ Q ++ R → y ∈ x :: (Q ++ R) := List.mem_cons_of_mem _
    have hInR : ∀ as, R = as ++ u :: v :: B → ((ch u).head? = some v ∨
        (ch u = [] ∧ (SlotList.succIn (x :: S) u = some v ∨ ∃ y ∈ x :: (Q ++ R), u ∈ ch y ∧
          (SlotList.succIn (ch y) u = some v ∨
            (SlotList.succIn (ch y) u = none ∧ ¬ Desc ch y v))))) := fun as hRe => by
      have huR : u ∈ R := by rw [hRe]; simp
      have hux : x ≠ u := fun e => hxQR (List.mem_append_right _ (by rw [e]; exact huR))
      rcases ihR hRnd hRe with h1 | ⟨h0, h2⟩
      · exact Or.inl h1
      · refine Or.inr ⟨h0, ?_⟩
        rcases h2 with h2 | ⟨y, hy, hc, h3⟩
        · exact .inl (by rw [SlotList.succIn_cons, if_neg hux]; exact h2)
        · exact .inr ⟨y, hsub (List.mem_append_right _ hy), hc, h3⟩
    cases A with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hP
      obtain ⟨rfl, hP⟩ := hP
      cases Q with
      | cons q Q' =>
        left
        rw [← hQ.head_eq]
        simp only [List.cons_append, List.cons.injEq] at hP
        rw [hP.1]; rfl
      | nil =>
        right
        refine ⟨hQ.eq_nil_of_nil, .inl ?_⟩
        simp only [List.nil_append] at hP
        rw [SlotList.succIn_cons, if_pos rfl, ← hR.head_eq, hP]; rfl
    | cons a A' =>
      simp only [List.cons_append, List.cons.injEq] at hP
      obtain ⟨-, hP⟩ := hP
      rcases List.append_eq_append_iff.mp hP with ⟨as, -, hRe⟩ | ⟨bs, hQe, hBe⟩
      · exact hInR as hRe
      · match bs, hBe with
        | [], hBe => exact hInR [] (by simpa using hBe.symm)
        | [b], hBe =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at hBe
          obtain ⟨rfl, hRe⟩ := hBe
          have hQl : Q.getLast? = some u := by rw [hQe]; simp
          have huQ : u ∈ Q := List.mem_of_getLast? hQl
          have hvR : v ∈ R := by rw [← hRe]; simp
          have h0 := hQ.getLast_childless hQl
          obtain ⟨hl1, hl2⟩ := hQ.getLast_succNone hQnd hQl
          refine .inr ⟨h0, .inr ?_⟩
          rcases hQ.mem_cases huQ with hc | ⟨y, hy, hc⟩
          · exact ⟨x, List.mem_cons_self .., hc, .inr ⟨hl1 hc, fun hd =>
              hdis v (hQ.desc_mem_top hd) v hvR rfl⟩⟩
          · exact ⟨y, hsub (List.mem_append_left _ hy), hc, .inr ⟨hl2 y hy hc, fun hd =>
              hdis v (hQ.desc_mem hy hd) v hvR rfl⟩⟩
        | b :: c :: bs', hBe =>
          simp only [List.cons_append, List.cons.injEq] at hBe
          obtain ⟨rfl, rfl, -⟩ := hBe
          rcases ihQ hQnd hQe with h1 | ⟨h0, h2⟩
          · exact .inl h1
          · refine .inr ⟨h0, .inr ?_⟩
            rcases h2 with h2 | ⟨y, hy, hc, h3⟩
            · exact ⟨x, List.mem_cons_self .., mem_of_succIn h2, .inl h2⟩
            · exact ⟨y, hsub (List.mem_append_left _ hy), hc, h3⟩

private theorem predIn_cons_of_some {c w q : SlotRef} {l : List SlotRef} (hc : c ≠ w)
    (h : SlotList.predIn l w = some q) : SlotList.predIn (c :: l) w = some q := by
  rw [SlotList.predIn_cons, if_neg hc]
  split
  · next hh =>
    cases l with
    | nil => cases hh
    | cons a l =>
      simp only [List.head?_cons, Option.some.injEq] at hh
      subst hh
      rw [SlotList.predIn_cons, if_pos rfl] at h; cases h
  · exact h

private theorem predIn_cons_head {c w : SlotRef} {l : List SlotRef} (hc : c ≠ w)
    (h : l.head? = some w) : SlotList.predIn (c :: l) w = some c := by
  rw [SlotList.predIn_cons, if_neg hc, if_pos h]

/-- **The slot before `u` in a preorder** is its parent, when `u` is that
parent's first child; or its previous sibling `q` (on the top level or among its
parent's children), or a slot below `q`, where `u` does not lie below `q`. -/
theorem pred_cases {S P : List SlotRef} (h : ForestOrder ch S P) (hnd : P.Nodup)
    {A B : List SlotRef} {u v : SlotRef} (hP : P = A ++ v :: u :: B) :
    (u ∈ ch v ∧ (ch v).head? = some u) ∨
      ∃ M, (M = S ∨ ∃ y ∈ P, M = ch y) ∧ ∃ q, SlotList.predIn M u = some q ∧
        (v = q ∨ Desc ch q v) ∧ ¬ Desc ch q u := by
  induction h generalizing A B with
  | nil => cases A <;> simp at hP
  | @cons x S Q R hQ hR ihQ ihR =>
    have hxQR := (List.nodup_cons.mp hnd).1
    have hnd' := (List.nodup_cons.mp hnd).2
    have hQnd := (List.nodup_append.mp hnd').1
    have hRnd := (List.nodup_append.mp hnd').2.1
    have hdis := (List.nodup_append.mp hnd').2.2
    have hsub : ∀ {y}, y ∈ Q ++ R → y ∈ x :: (Q ++ R) := List.mem_cons_of_mem _
    have hInR : ∀ as, R = as ++ v :: u :: B → ((u ∈ ch v ∧ (ch v).head? = some u) ∨
        ∃ M, (M = x :: S ∨ ∃ y ∈ x :: (Q ++ R), M = ch y) ∧ ∃ q, SlotList.predIn M u = some q ∧
          (v = q ∨ Desc ch q v) ∧ ¬ Desc ch q u) := fun as hRe => by
      have huR : u ∈ R := by rw [hRe]; simp
      have hux : x ≠ u := fun e => hxQR (List.mem_append_right _ (by rw [e]; exact huR))
      rcases ihR hRnd hRe with h1 | ⟨M, hM, q, hq, h2⟩
      · exact Or.inl h1
      · rcases hM with rfl | ⟨y, hy, rfl⟩
        · exact Or.inr ⟨x :: M, .inl rfl, q, predIn_cons_of_some hux hq, h2⟩
        · exact Or.inr ⟨ch y, .inr ⟨y, hsub (List.mem_append_right _ hy), rfl⟩, q, hq, h2⟩
    cases A with
    | nil =>
      simp only [List.nil_append, List.cons.injEq] at hP
      obtain ⟨rfl, hP⟩ := hP
      cases Q with
      | cons q Q' =>
        simp only [List.cons_append, List.cons.injEq] at hP
        obtain ⟨rfl, -⟩ := hP
        have hh : (ch x).head? = some q := by rw [← hQ.head_eq]; rfl
        exact .inl ⟨List.mem_of_mem_head? hh, hh⟩
      | nil =>
        simp only [List.nil_append] at hP
        have huR : u ∈ R := by rw [hP]; simp
        have hux : x ≠ u := fun e => hxQR (List.mem_append_right _ (by rw [e]; exact huR))
        refine .inr ⟨x :: S, .inl rfl, x, predIn_cons_head hux (by rw [← hR.head_eq, hP]; rfl),
          .inl rfl, fun hd => ?_⟩
        have := hQ.desc_mem_top hd
        cases this
    | cons a A' =>
      simp only [List.cons_append, List.cons.injEq] at hP
      obtain ⟨-, hP⟩ := hP
      rcases List.append_eq_append_iff.mp hP with ⟨as, -, hRe⟩ | ⟨bs, hQe, hBe⟩
      · exact hInR as hRe
      · match bs, hBe with
        | [], hBe => exact hInR [] (by simpa using hBe.symm)
        | [b], hBe =>
          simp only [List.cons_append, List.nil_append, List.cons.injEq] at hBe
          obtain ⟨rfl, hRe⟩ := hBe
          have hvQ : v ∈ Q := by rw [hQe]; simp
          have huR : u ∈ R := by rw [← hRe]; simp
          have hux : x ≠ u := fun e => hxQR (List.mem_append_right _ (by rw [e]; exact huR))
          refine .inr ⟨x :: S, .inl rfl, x,
            predIn_cons_head hux (by rw [← hR.head_eq, ← hRe]; rfl), .inr ?_, fun hd =>
              hdis u (hQ.desc_mem_top hd) u huR rfl⟩
          rcases hQ.mem_top_or_desc hvQ with hc | ⟨l, hl, hd⟩
          · exact .child hc
          · exact hd.head hl
        | b :: c :: bs', hBe =>
          simp only [List.cons_append, List.cons.injEq] at hBe
          obtain ⟨rfl, rfl, -⟩ := hBe
          rcases ihQ hQnd hQe with h1 | ⟨M, hM, q, hq, h2⟩
          · exact .inl h1
          · rcases hM with rfl | ⟨y, hy, rfl⟩
            · exact .inr ⟨ch x, .inr ⟨x, List.mem_cons_self .., rfl⟩, q, hq, h2⟩
            · exact .inr ⟨ch y, .inr ⟨y, hsub (List.mem_append_left _ hy), rfl⟩, q, hq, h2⟩

end ForestOrder


/-- A descent starts at a slot with a child. -/
theorem Desc.first {ch : SlotRef → List SlotRef} {a b : SlotRef} (h : Desc ch a b) :
    ∃ c, c ∈ ch a := by
  induction h with
  | child hb => exact ⟨_, hb⟩
  | trans _ _ ih => exact ih

/-- **A slot of a duplicate-free list has one place in it.** -/
theorem split_unique {b : SlotRef} :
    ∀ {X Y X' Y' : List SlotRef}, (X ++ b :: Y).Nodup → X ++ b :: Y = X' ++ b :: Y' →
      X = X' ∧ Y = Y'
  | [], Y, [], Y', _, e => by simpa using e
  | [], Y, c :: X', Y', hnd, e => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, rfl⟩ := e
    exact absurd (by simp) (List.nodup_cons.mp hnd).1
  | c :: X, Y, [], Y', hnd, e => by
    simp only [List.nil_append, List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, -⟩ := e
    exact absurd (by simp) (List.nodup_cons.mp hnd).1
  | c :: X, Y, c' :: X', Y', hnd, e => by
    simp only [List.cons_append, List.cons.injEq] at e
    obtain ⟨rfl, e⟩ := e
    obtain ⟨h1, h2⟩ := split_unique (List.nodup_cons.mp hnd).2 e
    exact ⟨by rw [h1], h2⟩

namespace ForestOrder

variable {ch : SlotRef → List SlotRef}

/-- **A slot's descendants follow it in the preorder.** -/
theorem desc_split {S P : List SlotRef} (h : ForestOrder ch S P) {a b : SlotRef}
    (ha : a ∈ P) (hb : Desc ch a b) : ∃ X Y, P = X ++ a :: Y ∧ b ∈ Y := by
  induction h with
  | nil => cases ha
  | @cons x S Q R hQ _ ihQ ihR =>
    rcases List.mem_cons.mp ha with rfl | ha
    · exact ⟨[], Q ++ R, rfl, List.mem_append_left _ (hQ.desc_mem_top hb)⟩
    · rcases List.mem_append.mp ha with ha | ha
      · obtain ⟨X, Y, rfl, hY⟩ := ihQ ha
        exact ⟨x :: X, Y ++ R, by simp, List.mem_append_left _ hY⟩
      · obtain ⟨X, Y, rfl, hY⟩ := ihR ha
        exact ⟨x :: (Q ++ X), Y, by simp, hY⟩

end ForestOrder

/-- **An ancestor precedes its descendant in the preorder**: nothing after `b`
lies above it. -/
theorem TreeOrder.not_after_of_reach {cdt : CapDerivationTree} {P : List SlotRef}
    (h : TreeOrder cdt P) {a b : SlotRef} (hr : CdtChildReachable cdt a b) {X Y : List SlotRef}
    (hP : P = X ++ b :: Y) : a ∉ Y := by
  intro haY
  have hd := (desc_childrenOf_iff cdt a b).mpr hr
  obtain ⟨c, hc⟩ := hd.first
  have ha : a ∈ P := by
    obtain ⟨e, he, hp, -⟩ := childrenOf_to_edge cdt a c hc
    exact h.complete a (.inl ⟨e, he, .inl hp⟩)
  obtain ⟨X', Y', hP', hbY'⟩ := h.forest.desc_split ha hd
  obtain ⟨Y1, Y2, rfl⟩ := List.append_of_mem haY
  have hnd := h.nodup
  have e : P = (X ++ b :: Y1) ++ a :: Y2 := by rw [hP]; simp
  obtain ⟨-, rfl⟩ := split_unique (e ▸ hnd) (e.symm.trans hP')
  rw [hP] at hnd
  exact (List.nodup_cons.mp (List.nodup_append.mp hnd).2.1).1 (by simp [hbY'])

end CapDerivationTree

namespace SlotList

/-- **`q` holds on one contiguous run of `l`**: `l` is a part where `q` fails,
then a run where it holds, then a part where it fails.  seL4's `mdb_chunked`
read on a list: over the preorder, with `q` "names object `o`", it says the
slots naming `o` are one contiguous run of the mapping database. -/
def Chunked (q : SlotRef → Prop) (l : List SlotRef) : Prop :=
  ∃ A B C, l = A ++ B ++ C ∧ (∀ x ∈ A, ¬ q x) ∧ (∀ x ∈ B, q x) ∧ (∀ x ∈ C, ¬ q x)

namespace Chunked

variable {q q' : SlotRef → Prop} {l : List SlotRef}

/-- A list where `q` holds nowhere has one (empty) run. -/
theorem of_none (h : ∀ x ∈ l, ¬ q x) : Chunked q l :=
  ⟨l, [], [], by simp, h, by simp, by simp⟩

/-- A predicate agreeing on the list's slots has the same runs. -/
theorem congr (h : Chunked q l) (hq : ∀ x ∈ l, q' x ↔ q x) : Chunked q' l := by
  obtain ⟨A, B, C, rfl, hA, hB, hC⟩ := h
  exact ⟨A, B, C, rfl, fun x hx e => hA x hx ((hq x (by simp [hx])).mp e),
    fun x hx => (hq x (by simp [hx])).mpr (hB x hx),
    fun x hx e => hC x hx ((hq x (by simp [hx])).mp e)⟩

/-- **Dropping slots keeps a run contiguous** (a delete's splice). -/
theorem filter (h : Chunked q l) (f : SlotRef → Bool) : Chunked q (l.filter f) := by
  obtain ⟨A, B, C, rfl, hA, hB, hC⟩ := h
  exact ⟨A.filter f, B.filter f, C.filter f, by simp [List.filter_append],
    fun x hx => hA x (List.mem_filter.mp hx).1, fun x hx => hB x (List.mem_filter.mp hx).1,
    fun x hx => hC x (List.mem_filter.mp hx).1⟩

/-- **Renaming slots in place keeps a run contiguous** (a move). -/
theorem map (h : Chunked q l) (g : SlotRef → SlotRef) (hq : ∀ x ∈ l, q' (g x) ↔ q x) :
    Chunked q' (l.map g) := by
  obtain ⟨A, B, C, rfl, hA, hB, hC⟩ := h
  refine ⟨A.map g, B.map g, C.map g, by simp [List.map_append], ?_, ?_, ?_⟩
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact fun e => hA x hx ((hq x (by simp [hx])).mp e)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact (hq x (by simp [hx])).mpr (hB x hx)
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := List.mem_map.mp hy
    exact fun e => hC x hx ((hq x (by simp [hx])).mp e)

/-- **A slot appended last keeps the run contiguous** when it is outside the run
or the run is empty (a new root). -/
theorem append_last (h : Chunked q l) {r : SlotRef} (hr : ¬ q r ∨ ∀ x ∈ l, ¬ q x) :
    Chunked q (l ++ [r]) := by
  by_cases hq : q r
  · have hl := hr.resolve_left (· hq)
    exact ⟨l, [r], [], by simp, hl, fun x hx => by rw [List.mem_singleton.mp hx]; exact hq,
      by simp⟩
  · obtain ⟨A, B, C, rfl, hA, hB, hC⟩ := h
    refine ⟨A, B, C ++ [r], by simp, hA, hB, fun x hx => ?_⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hC x hx
    · rw [List.mem_singleton.mp hx]; exact hq

theorem not_mem_of_nodup_split {X Y : List SlotRef} {p : SlotRef} (h : (X ++ p :: Y).Nodup) :
    p ∉ X :=
  fun hm => (List.nodup_append.mp h).2.2 p hm p (List.mem_cons_self ..) rfl

/-- **A slot inserted right after `p` keeps every run contiguous** (an insert)
when it is in `p`'s run exactly when `p` is (a copy), or when it starts a run of
its own (a fresh object) right after the last slot of `p`'s run. -/
theorem insertAfter (h : Chunked q l) (hnd : l.Nodup) {p d : SlotRef} (hp : p ∈ l)
    (hd : q d → q p ∨ ∀ x ∈ l, ¬ q x)
    (hlast : q p → ¬ q d → ∀ X Y, l = X ++ p :: Y → ∀ x ∈ Y, ¬ q x) :
    Chunked q (CapDerivationTree.insertAfter p d l) := by
  have ins : ∀ X Y, l = X ++ p :: Y → CapDerivationTree.insertAfter p d l = X ++ p :: d :: Y :=
    fun X Y e => by
      rw [e]; exact CapDerivationTree.insertAfter_split (not_mem_of_nodup_split (e ▸ hnd))
  have hl := h
  obtain ⟨A, B, C, rfl, hA, hB, hC⟩ := h
  have hpB : q p → p ∈ B := fun hqp => by
    rcases List.mem_append.mp hp with hp | hp
    · rcases List.mem_append.mp hp with hp | hp
      · exact absurd hqp (hA p hp)
      · exact hp
    · exact absurd hqp (hC p hp)
  by_cases hqd : q d <;> by_cases hqp : q p
  · obtain ⟨B1, B2, rfl⟩ := List.append_of_mem (hpB hqp)
    rw [ins (A ++ B1) (B2 ++ C) (by simp)]
    refine ⟨A, B1 ++ p :: d :: B2, C, by simp, hA, fun x hx => ?_, hC⟩
    simp only [List.mem_append, List.mem_cons] at hx
    rcases hx with hx | rfl | rfl | hx
    · exact hB x (by simp [hx])
    · exact hqp
    · exact hqd
    · exact hB x (by simp [hx])
  · have hall := (hd hqd).resolve_left hqp
    obtain ⟨X, Y, e⟩ := List.append_of_mem hp
    rw [ins X Y e]
    refine ⟨X ++ [p], [d], Y, by simp, fun x hx => ?_, fun x hx => by
      rw [List.mem_singleton.mp hx]; exact hqd, fun x hx => hall x (by rw [e]; simp [hx])⟩
    rcases List.mem_append.mp hx with hx | hx
    · exact hall x (by rw [e]; simp [hx])
    · rw [List.mem_singleton.mp hx]; exact hqp
  · obtain ⟨B1, B2, rfl⟩ := List.append_of_mem (hpB hqp)
    have hY := hlast hqp hqd (A ++ B1) (B2 ++ C) (by simp)
    cases B2 with
    | cons b B2' => exact absurd (hB b (by simp)) (hY b (by simp))
    | nil =>
      rw [ins (A ++ B1) C (by simp)]
      refine ⟨A, B1 ++ [p], d :: C, by simp, hA, fun x hx => hB x (by simpa using hx), ?_⟩
      intro x hx
      rcases List.mem_cons.mp hx with rfl | hx
      · exact hqd
      · exact hC x hx
  · rcases List.mem_append.mp hp with hp' | hp'
    · rcases List.mem_append.mp hp' with hp' | hp'
      · obtain ⟨A1, A2, rfl⟩ := List.append_of_mem hp'
        rw [ins A1 (A2 ++ B ++ C) (by simp)]
        refine ⟨A1 ++ p :: d :: A2, B, C, by simp, fun x hx => ?_, hB, hC⟩
        simp only [List.mem_append, List.mem_cons] at hx
        rcases hx with hx | rfl | rfl | hx
        · exact hA x (by simp [hx])
        · exact hqp
        · exact hqd
        · exact hA x (by simp [hx])
      · exact absurd (hB p hp') hqp
    · obtain ⟨C1, C2, rfl⟩ := List.append_of_mem hp'
      rw [ins (A ++ B ++ C1) C2 (by simp)]
      refine ⟨A, B, C1 ++ p :: d :: C2, by simp, hA, hB, fun x hx => ?_⟩
      simp only [List.mem_append, List.mem_cons] at hx
      rcases hx with hx | rfl | rfl | hx
      · exact hC x (by simp [hx])
      · exact hqp
      · exact hqd
      · exact hC x (by simp [hx])

/-- **A slot in a run of two or more has a run neighbour**: the slot right
before it or the slot right after it is in the run. -/
theorem neighbour (h : Chunked q l) {r t : SlotRef} (hr : r ∈ l) (hqr : q r) (ht : t ∈ l)
    (hqt : q t) (htr : t ≠ r) :
    (∃ X x Y, l = X ++ x :: r :: Y ∧ q x) ∨ (∃ X x Y, l = X ++ r :: x :: Y ∧ q x) := by
  obtain ⟨A, B, C, rfl, hA, hB, hC⟩ := h
  have inB : ∀ {y}, y ∈ A ++ B ++ C → q y → y ∈ B := fun hy hq => by
    rcases List.mem_append.mp hy with hy | hy
    · rcases List.mem_append.mp hy with hy | hy
      · exact absurd hq (hA _ hy)
      · exact hy
    · exact absurd hq (hC _ hy)
  obtain ⟨B1, B2, rfl⟩ := List.append_of_mem (inB hr hqr)
  cases B2 with
  | cons x B2' => exact .inr ⟨A ++ B1, x, B2' ++ C, by simp, hB x (by simp)⟩
  | nil =>
    have htB1 : t ∈ B1 := by
      have := inB ht hqt
      simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at this
      exact this.resolve_right htr
    rcases List.eq_nil_or_concat B1 with e | ⟨B1', x, e⟩
    · rw [e] at htB1; cases htB1
    · rw [List.concat_eq_append] at e
      subst e
      exact .inl ⟨A ++ B1', x, C, by simp, hB x (by simp)⟩

end Chunked

end SlotList

end SeLe4n.Model
