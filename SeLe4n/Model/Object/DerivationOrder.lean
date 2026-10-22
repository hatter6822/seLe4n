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
end CapDerivationTree
end SeLe4n.Model
