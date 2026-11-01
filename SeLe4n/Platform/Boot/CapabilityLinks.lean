-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Platform.Boot

/-!
# WS-ZA ZA5.4 — the boot links its capabilities into the derivation tree

seL4's `create_initial_thread` derives the initial thread's CSpace and VSpace
capabilities from the root CNode's, so every boot capability lies in one
derivation tree in MDB order.  This module is that stage.  It walks the
configuration's capability slots in boot order (`bootCapabilitySlots`: every
configured CNode's occupied slots, then every configured thread's two space
slots) and links each slot that holds a capability (`bootLinkSlot`): the first
slot naming an object (`Capability.namedObject`, seL4's `sameObjectAs`) joins
the end of the root chain, and a later slot naming the same object becomes that
root's first child, a copy of it.  The slots naming one object are therefore one
contiguous preorder run, a root followed by its copies (`sameObjectContiguous`).
Until `v0.36.131` slots were grouped by their whole target, so a CNode's own
capability and a CNode-slot capability into it were two runs of one object.

`BootLinks.Sound` is what each step keeps: link writes and a tree alone moved,
the links agree with the tree, the tree names exactly the linked slots and each
holds a capability, the tree is acyclic and has a preorder
(`CapDerivationTree.TreeOrder`) over which the slots naming each object are one
run.  `linkBootCapabilities_bootLinkedShape` reads
the stage's whole effect off it: a boot-shaped state is taken to a state of
linked boot shape (`bootLinkedShape`), whose proof-layer bundle
`proofLayerInvariantBundle_of_bootLinkedShape` gives.
-/

namespace SeLe4n.Platform.Boot

open SeLe4n.Model
open SeLe4n.Model.SystemState (linkReach)
open SeLe4n.Kernel

/-- Link writes keep every VSpace root, so every root's mapping table. -/
theorem linkReach_perObjectMappingsInvariant {st₀ st : SystemState} (h : linkReach st₀ st)
    (hInv : st₀.objects.invExt) (hM : perObjectMappingsInvariant st₀) :
    perObjectMappingsInvariant st := fun oid vs hv =>
  hM oid vs (((h.agree hInv) oid).obj_back hv (fun _ e => by cases e))



/-- The boot's capability linking in progress: the state so far, the last slot
of the root chain, the slots linked, and the root of each object linked with
the object it names. -/
structure BootLinks where
  st : SystemState
  last : Option SlotRef
  done : List SlotRef
  roots : List (SlotRef × Option SeLe4n.ObjId)

/-- **Link one boot slot**: a slot holding a capability to an object no
earlier root names goes to the end of the root chain; one naming an object an
earlier root names (`Capability.namedObject`, seL4's `sameObjectAs`) becomes
that root's first child, a copy of it, as seL4's `create_initial_thread` derives
a thread's slots from the root CNode's.  Grouping by object rather than by
target is what keeps the slots naming one object one contiguous preorder run
(WS-ZA ZA5.4 part 20): a CNode-slot capability names its CNode as the CNode's
own capability does.  A slot that holds nothing, or that is already linked, is
left alone. -/
def bootLinkSlot (a : BootLinks) (r : SlotRef) : BootLinks :=
  match a.st.slotCapAt r with
  | none => a
  | some cap =>
      if r ∈ a.done then a
      else
        match a.roots.find? (fun q => decide (q.2 = cap.namedObject)) with
        | some q => { a with st := a.st.cdtAddChild q.1 r .copy, done := r :: a.done }
        | none =>
            { st := a.st.cdtAppendRoot a.last r, last := some r, done := r :: a.done,
              roots := a.roots ++ [(r, cap.namedObject)] }

/-- What the linking keeps, against the state it started from: link writes and
a tree alone moved, the links agree with the tree, the tree names exactly the
linked slots, each of which holds a capability, the tree is acyclic, `last` is
the root chain's last slot, every root is linked, every child holds a capability
naming its parent's object, every root holds a capability naming the object it
is recorded under, every linked slot names a recorded root's object, and the
tree has a preorder in which the slots naming one object are one contiguous
run. -/
def BootLinks.Sound (st₀ : SystemState) (a : BootLinks) : Prop :=
  linkReach { st₀ with cdt := a.st.cdt } a.st ∧
  LinksAgree a.st.slotLinkAt a.st.cdt ∧
  (∀ x, a.st.cdt.mentions x ↔ x ∈ a.done) ∧
  (∀ x ∈ a.done, st₀.slotCapAt x ≠ none) ∧
  a.st.cdt.edgeWellFounded ∧
  a.last = a.st.cdt.firstChain.getLast? ∧
  (∀ q ∈ a.roots, q.1 ∈ a.done) ∧
  (∀ p c, c ∈ a.st.cdt.childrenOf p → ∃ cp cc, st₀.slotCapAt p = some cp ∧
    st₀.slotCapAt c = some cc ∧ cc.namedObject = cp.namedObject) ∧
  (∀ q ∈ a.roots, ∃ cq, st₀.slotCapAt q.1 = some cq ∧ cq.namedObject = q.2) ∧
  (∀ x ∈ a.done, ∃ q ∈ a.roots, ∃ cx, st₀.slotCapAt x = some cx ∧ cx.namedObject = q.2) ∧
  ∃ P, CapDerivationTree.TreeOrder a.st.cdt P ∧
    ∀ o, SlotList.Chunked (SystemState.namesAt st₀.slotCapAt · o) P

theorem BootLinks.Sound.start {st₀ : SystemState} (hE : st₀.cdt = CapDerivationTree.empty)
    (hL : LinksAgree st₀.slotLinkAt st₀.cdt) : BootLinks.Sound st₀ ⟨st₀, none, [], []⟩ := by
  refine ⟨linkReach.refl _, hL, fun x => ?_, fun _ h => (by cases h), ?_, ?_,
    fun _ h => (by cases h), fun p c h => ?_, fun _ h => (by cases h), fun _ h => (by cases h),
    [], ?_, fun _ => SlotList.Chunked.of_none fun _ h => by cases h⟩
  · simp only [List.not_mem_nil, iff_false]; rw [hE]; exact CapDerivationTree.empty_not_mentions x
  · rw [hE]; exact CapDerivationTree.empty_edgeWellFounded
  · show none = _
    rw [hE]; unfold CapDerivationTree.firstChain; rw [CapDerivationTree.empty_rootChains]; rfl
  · rw [hE] at h
    exact absurd (CapDerivationTree.mentions_of_mem_childrenOf h).2
      (CapDerivationTree.empty_not_mentions c)
  · rw [hE]; exact CapDerivationTree.TreeOrder.empty_tree (by simp) (by simp)




theorem BootLinks.Sound.step {st₀ : SystemState} (hInv₀ : st₀.objects.invExt) {a : BootLinks}
    (h : BootLinks.Sound st₀ a) (r : SlotRef) : BootLinks.Sound st₀ (bootLinkSlot a r) := by
  obtain ⟨hR, hL, hM, hD, hW, hLast, hRoots, hEd, hRT, hDR, P, hP, hC⟩ := h
  have hInv : a.st.objects.invExt := hR.invExt hInv₀
  have hCap : ∀ x, a.st.slotCapAt x = st₀.slotCapAt x := fun x =>
    (hR.agree hInv₀).slotCapAt x
  have hIn : ∀ x, a.st.cdt.mentions x → a.st.slotInObject x := fun x hx =>
    SystemState.slotInObject_of_slotCapAt (by rw [hCap]; exact hD x ((hM x).mp hx))
  unfold bootLinkSlot
  cases hc : a.st.slotCapAt r with
  | none => exact ⟨hR, hL, hM, hD, hW, hLast, hRoots, hEd, hRT, hDR, P, hP, hC⟩
  | some cap =>
    simp only
    by_cases hr : r ∈ a.done
    · rw [if_pos hr]; exact ⟨hR, hL, hM, hD, hW, hLast, hRoots, hEd, hRT, hDR, P, hP, hC⟩
    rw [if_neg hr]
    have hrN : ¬ a.st.cdt.mentions r := fun e => hr ((hM r).mp e)
    have hrO : a.st.slotInObject r := SystemState.slotInObject_of_slotCapAt (by rw [hc]; simp)
    have hrD : st₀.slotCapAt r ≠ none := by rw [← hCap, hc]; simp
    have hcap : st₀.slotCapAt r = some cap := by rw [← hCap, hc]
    cases hq : a.roots.find? (fun q => decide (q.2 = cap.namedObject)) with
    | some q =>
      have hqT : q.2 = cap.namedObject := of_decide_eq_true
        (List.find?_some (p := fun q : SlotRef × Option SeLe4n.ObjId =>
          decide (q.2 = cap.namedObject)) hq)
      obtain ⟨cq, hcq, hT⟩ := hRT q (List.mem_of_find?_eq_some hq)
      have hNameEq : ∀ o, SystemState.namesAt st₀.slotCapAt r o ↔
          SystemState.namesAt st₀.slotCapAt q.1 o := fun o => by
        unfold SystemState.namesAt
        rw [hcap, hcq]
        simp only [Option.some.injEq, exists_eq_left']
        rw [hT, hqT]
      have hqD : q.1 ∈ a.done := hRoots q (List.mem_of_find?_eq_some hq)
      have hqM : a.st.cdt.mentions q.1 := (hM q.1).mpr hqD
      have hqr : q.1 ≠ r := fun e => hr (e ▸ hqD)
      have hR' := SystemState.cdtAddChild_reach a.st q.1 r .copy
      have hCdt : (a.st.cdtAddChild q.1 r .copy).cdt = a.st.cdt.addEdge q.1 r .copy := hR'.cdt
      refine ⟨?_, SystemState.cdtAddChild_agree hInv hL hIn .copy (hIn _ hqM) hrO hrN hqr,
        fun x => ?_, ?_, ?_, ?_, fun q' hq' => List.mem_cons_of_mem _ (hRoots q' hq'),
        fun p c hc' => ?_, hRT, fun x hx => ?_, CapDerivationTree.insertAfter q.1 r P, ?_,
        fun o => (hC o).insertAfter hP.nodup (hP.complete q.1 hqM)
          (fun h => .inl ((hNameEq o).mp h)) fun h hn => absurd ((hNameEq o).mpr h) hn⟩
      · rw [hCdt]; exact (hR.with_cdt (a.st.cdt.addEdge q.1 r .copy)).trans hR'
      · simp only; rw [hCdt, CapDerivationTree.mentions_addEdge, hM, List.mem_cons]
        constructor
        · rintro (h | rfl | rfl)
          · exact .inr h
          · exact .inr hqD
          · exact .inl rfl
        · rintro (rfl | h)
          · exact .inr (.inr rfl)
          · exact .inl h
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hrD
        · exact hD x hx
      · simp only; rw [hCdt]
        exact CapDerivationTree.addEdge_preserves_edgeWellFounded_fresh _ _ _ _ hqr hW
          fun e he => ⟨fun h => hrN (CapDerivationTree.mentions_of_edge he (.inl h)),
            fun h => hrN (CapDerivationTree.mentions_of_edge he (.inr h))⟩
      · simp only; rw [hCdt, CapDerivationTree.firstChain_addEdge]; exact hLast
      · simp only at hc'; rw [hCdt, CapDerivationTree.childrenOf_addEdge] at hc'
        split at hc'
        · rename_i hp; subst hp
          rcases List.mem_cons.mp hc' with rfl | hc'
          · exact ⟨cq, cap, hcq, hcap, by rw [hT, hqT]⟩
          · exact hEd _ _ hc'
        · exact hEd _ _ hc'
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨q, List.mem_of_find?_eq_some hq, cap, hcap, hqT.symm⟩
        · exact hDR x hx
      · simp only; rw [hCdt]; exact hP.addEdge hqM hrN .copy
    | none =>
      have hR' := SystemState.cdtAppendRoot_reach a.st a.last r
      have hCdt : (a.st.cdtAppendRoot a.last r).cdt = a.st.cdt.appendRoot r := hR'.cdt
      refine ⟨?_, SystemState.cdtAppendRoot_agree hInv hL hIn hrO hrN hLast,
        fun x => ?_, ?_, ?_, ?_, fun q' hq' => ?_, fun p c hc' => ?_, fun q' hq' => ?_,
        fun x hx => ?_, P ++ [r], ?_, fun o => (hC o).append_last ?_⟩
      · rw [hCdt]; exact (hR.with_cdt (a.st.cdt.appendRoot r)).trans hR'
      · simp only; rw [hCdt, CapDerivationTree.mentions_appendRoot, hM, List.mem_cons]
        exact Or.comm
      · intro x hx
        rcases List.mem_cons.mp hx with rfl | hx
        · exact hrD
        · exact hD x hx
      · simp only; rw [hCdt]; exact CapDerivationTree.appendRoot_edgeWellFounded hW r
      · simp only; rw [hCdt, CapDerivationTree.firstChain_appendRoot, List.getLast?_concat]
      · rcases List.mem_append.mp hq' with hq' | hq'
        · exact List.mem_cons_of_mem _ (hRoots q' hq')
        · rw [List.mem_singleton] at hq'; subst hq'; exact List.mem_cons_self ..
      · simp only at hc'
        rw [hCdt, CapDerivationTree.childrenOf_appendRoot] at hc'
        exact hEd _ _ hc'
      · rcases List.mem_append.mp hq' with hq' | hq'
        · exact hRT q' hq'
        · rw [List.mem_singleton] at hq'; subst hq'
          exact ⟨cap, hcap, rfl⟩
      · rcases List.mem_cons.mp hx with rfl | hx
        · exact ⟨(x, cap.namedObject), List.mem_append_right _ (List.mem_singleton_self _), cap,
            hcap, rfl⟩
        · obtain ⟨q', hq', cx, hcx, hxq⟩ := hDR x hx
          exact ⟨q', List.mem_append_left _ hq', cx, hcx, hxq⟩
      · simp only; rw [hCdt]; exact hP.appendRoot hrN
      · by_cases hro : SystemState.namesAt st₀.slotCapAt r o
        · refine .inr fun x hx hxo => ?_
          obtain ⟨q', hq', cx, hcx, hxq⟩ := hDR x ((hM x).mp ((hP.mem_iff x).mp hx))
          obtain ⟨c1, h1, h1o⟩ := hxo
          obtain ⟨c2, h2, h2o⟩ := hro
          rw [hcx] at h1; cases h1
          rw [hcap] at h2; cases h2
          exact absurd (decide_eq_true (hxq.symm.trans (h1o.trans h2o.symm)))
            (List.find?_eq_none.mp hq q' hq')
        · exact .inl hro

/-- The linking of a list of slots keeps `Sound`. -/
theorem BootLinks.Sound.foldl {st₀ : SystemState} (hInv₀ : st₀.objects.invExt) :
    ∀ (rs : List SlotRef) {a : BootLinks}, BootLinks.Sound st₀ a →
      BootLinks.Sound st₀ (rs.foldl bootLinkSlot a)
  | [], _, h => h
  | r :: rs, _, h => BootLinks.Sound.foldl hInv₀ rs (h.step hInv₀ r)




/-- Linking a slot writes a tree and link words alone. -/
theorem bootLinkSlot_reach {st₀ : SystemState} {a : BootLinks}
    (h : linkReach { st₀ with cdt := a.st.cdt } a.st) (r : SlotRef) :
    linkReach { st₀ with cdt := (bootLinkSlot a r).st.cdt } (bootLinkSlot a r).st := by
  unfold bootLinkSlot
  split
  · exact h
  · split
    · exact h
    · split
      · rename_i q _
        have hR' := SystemState.cdtAddChild_reach a.st q.1 r .copy
        rw [hR'.cdt]; exact (h.with_cdt _).trans hR'
      · have hR' := SystemState.cdtAppendRoot_reach a.st a.last r
        rw [hR'.cdt]; exact (h.with_cdt _).trans hR'

theorem bootLinkSlots_reach {st₀ : SystemState} :
    ∀ (rs : List SlotRef) {a : BootLinks}, linkReach { st₀ with cdt := a.st.cdt } a.st →
      linkReach { st₀ with cdt := (rs.foldl bootLinkSlot a).st.cdt } (rs.foldl bootLinkSlot a).st
  | [], _, h => h
  | r :: rs, _, h => bootLinkSlots_reach rs (bootLinkSlot_reach h r)

/-- **The boot's capability slots, in boot order**: every configured CNode's
occupied slots, then every configured thread's two space slots, its CSpace and
VSpace roots.  A CNode slot comes first, so a thread's space capability that
names what a CNode slot names is derived from it. -/
def bootCapabilitySlots (objs : List ObjectEntry) : List SlotRef :=
  objs.flatMap (fun e => match e.obj with
    | .cnode cn => cn.occupiedSlots.map fun p => ⟨e.id, p.1⟩
    | _ => []) ++
  objs.flatMap (fun e => match e.obj with
    | .tcb _ => [⟨e.id, SeLe4n.Slot.ofNat 0⟩, ⟨e.id, SeLe4n.Slot.ofNat 1⟩]
    | _ => [])

/-- **Every slot holding a capability is listed** in `rs`: the linking of `rs`
then leaves no capability outside the tree. -/
def bootSlotsListed (rs : List SlotRef) (st : SystemState) : Prop :=
  ∀ r, st.slotCapAt r ≠ none → r ∈ rs

/-- A configured object's slot that holds a capability is a boot capability
slot. -/
theorem mem_bootCapabilitySlots {objs : List ObjectEntry} {e : ObjectEntry} (he : e ∈ objs)
    {s : SeLe4n.Slot} (hs : e.obj.slotCap s ≠ none) : ⟨e.id, s⟩ ∈ bootCapabilitySlots objs := by
  unfold bootCapabilitySlots
  rw [List.mem_append, List.mem_flatMap, List.mem_flatMap]
  cases ho : e.obj with
  | cnode cn =>
    rw [ho] at hs
    obtain ⟨c, hc⟩ := Option.ne_none_iff_exists'.mp hs
    exact .inl ⟨e, he, by
      rw [ho]; exact List.mem_map.mpr ⟨(s, c), CNode.mem_occupiedSlots_of_lookup hc, rfl⟩⟩
  | tcb t =>
    rw [ho] at hs
    have hl : s.toNat < 2 := by
      simp only [KernelObject.slotCap, TCB.spaceSlotCap] at hs
      split at hs
      · assumption
      · exact absurd rfl hs
    refine .inr ⟨e, he, ?_⟩
    rw [ho]
    rcases (by omega : s.toNat = 0 ∨ s.toNat = 1) with h | h
    · rw [← SeLe4n.Slot.ofNat_toNat s, h]; exact List.mem_cons_self ..
    · rw [← SeLe4n.Slot.ofNat_toNat s, h]; exact List.mem_cons_of_mem _ (List.mem_cons_self ..)
  | _ => rw [ho] at hs; exact absurd rfl hs

/-- Linking a slot keeps every linked slot linked, and links the slot when it
holds a capability. -/
theorem bootLinkSlot_done (a : BootLinks) (r : SlotRef) :
    (∀ x ∈ a.done, x ∈ (bootLinkSlot a r).done) ∧
    (a.st.slotCapAt r ≠ none → r ∈ (bootLinkSlot a r).done) := by
  unfold bootLinkSlot
  cases hc : a.st.slotCapAt r with
  | none => exact ⟨fun _ h => h, fun h => absurd rfl h⟩
  | some cap =>
    simp only
    by_cases hr : r ∈ a.done
    · rw [if_pos hr]; exact ⟨fun _ h => h, fun _ => hr⟩
    · rw [if_neg hr]
      split
      · exact ⟨fun _ h => List.mem_cons_of_mem _ h, fun _ => List.mem_cons_self ..⟩
      · exact ⟨fun _ h => List.mem_cons_of_mem _ h, fun _ => List.mem_cons_self ..⟩

/-- **The linking of `rs` links every slot of `rs` that holds a capability**,
and every slot linked before. -/
theorem BootLinks.Sound.foldl_done {st₀ : SystemState} (hInv₀ : st₀.objects.invExt) :
    ∀ (rs : List SlotRef) {a : BootLinks}, BootLinks.Sound st₀ a →
      (∀ x ∈ a.done, x ∈ (rs.foldl bootLinkSlot a).done) ∧
      (∀ r ∈ rs, st₀.slotCapAt r ≠ none → r ∈ (rs.foldl bootLinkSlot a).done)
  | [], _, _ => ⟨fun _ h => h, fun _ h => absurd h (List.not_mem_nil)⟩
  | r :: rs, a, h => by
    have ih := BootLinks.Sound.foldl_done hInv₀ rs (h.step hInv₀ r)
    have hStep := bootLinkSlot_done a r
    refine ⟨fun x hx => ih.1 x (hStep.1 x hx), fun x hx hc => ?_⟩
    rcases List.mem_cons.mp hx with rfl | hx
    · exact ih.1 x (hStep.2 (by rw [(h.1.agree hInv₀).slotCapAt x]; exact hc))
    · exact ih.2 x hx hc

/-- **Link the boot's capabilities into the derivation tree** (`bootLinkSlot`
over `rs`, from an empty linking). -/
def linkBootSlots (st : SystemState) (rs : List SlotRef) : SystemState :=
  (rs.foldl bootLinkSlot ⟨st, none, [], []⟩).st

theorem linkBootSlots_reach (st : SystemState) (rs : List SlotRef) :
    linkReach { st with cdt := (linkBootSlots st rs).cdt } (linkBootSlots st rs) :=
  bootLinkSlots_reach (st₀ := st) rs (a := ⟨st, none, [], []⟩) (linkReach.refl _)

/-- **WS-ZA ZA5.4**: the boot stage that links the configuration's
capabilities (`bootCapabilitySlots`) into the derivation tree, its four
structural witnesses carried through the link writes. -/
def linkBootCapabilities (config : PlatformConfig) (ist : IntermediateState) :
    IntermediateState where
  state := linkBootSlots ist.state (bootCapabilitySlots config.initialObjects)
  hAllTables := (linkBootSlots_reach _ _).allTablesInvExtK ist.hAllTables
  hPerObjectSlots := perObjectSlotsInvariant_holds _
  hPerObjectMappings := linkReach_perObjectMappingsInvariant (linkBootSlots_reach _ _) ist.hAllTables.objects.1
    ist.hPerObjectMappings
  hLifecycleConsistent := (linkBootSlots_reach _ _).objectTypeMetadataConsistent
    ist.hAllTables.objects.1 ist.hLifecycleConsistent

theorem linkBootCapabilities_state (config : PlatformConfig) (ist : IntermediateState) :
    (linkBootCapabilities config ist).state =
      linkBootSlots ist.state (bootCapabilitySlots config.initialObjects) := rfl



/-! ### What the linking frames -/

/-- A thread projection that reads past the space-slot links reads the same
    after link writes. -/
theorem getTcb?_map_of_agree {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st) {α : Type _} (f : TCB → α)
    (hf : ∀ c : TCB, f c.withoutLinks = f c) (t : SeLe4n.ThreadId) :
    (st'.getTcb? t).map f = (st.getTcb? t).map f := by
  have e := congrArg (Option.map f) (hA.getTcb? t)
  simpa only [Option.map_map, Function.comp_def, hf] using e

theorem runLinkOn_of_agree {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (t : SeLe4n.ThreadId) :
    st'.runLinkOn c t = st.runLinkOn c t := by
  have e := getTcb?_map_of_agree hA (fun x => x.runLinkOn c) (fun _ => rfl) t
  unfold SystemState.runLinkOn
  cases h' : st'.getTcb? t <;> cases h : st.getTcb? t <;> simp_all

/-- The linked state is the state it linked, but for its objects and its tree. -/
theorem linkBootCapabilities_fields (config : PlatformConfig) (ist : IntermediateState) :
    (linkBootCapabilities config ist).state =
      { ist.state with objects := (linkBootCapabilities config ist).state.objects,
                       cdt := (linkBootCapabilities config ist).state.cdt } :=
  (linkBootSlots_reach _ _).fields

/-- The linked state's objects agree with the linked state's off their links. -/
theorem linkBootCapabilities_agree (config : PlatformConfig) (ist : IntermediateState) :
    SystemState.objectsAgreeOffDerivationLinks (linkBootCapabilities config ist).state ist.state :=
  (linkBootSlots_reach _ _).agree ist.hAllTables.objects.1

/-- The linking keeps every object's table back-links and writes no reference
table: it writes derivation links and the tree. -/
theorem linkBootCapabilities_tableReferenceFrame (config : PlatformConfig)
    (ist : IntermediateState) :
    SystemState.TableReferenceFrame ist.state (linkBootCapabilities config ist).state :=
  .of_map (g := KernelObject.withoutLinks) KernelObject.tableBackLinks_withoutLinks
    (by rw [linkBootCapabilities_fields]; rfl)
    (fun k => ((linkBootCapabilities_agree config ist) k).map_withoutLinks)

theorem linkBootCapabilities_scheduler (config : PlatformConfig) (ist : IntermediateState) :
    (linkBootCapabilities config ist).state.scheduler = ist.state.scheduler := by
  rw [linkBootCapabilities_fields]

theorem linkBootCapabilities_machine (config : PlatformConfig) (ist : IntermediateState) :
    (linkBootCapabilities config ist).state.machine = ist.state.machine := by
  rw [linkBootCapabilities_fields]


/-! ### The linked boot's shape -/

/-- **WS-ZA ZA5.4**: **linking a boot-shaped state leaves a state of linked
    boot shape.**  The tree starts empty over objects holding no link, so the
    linking is `Sound` throughout (`BootLinks.Sound.foldl`), and its end is the
    tree's half of the shape; every other conjunct reads past the links, which
    are all the linking writes besides the tree. -/
theorem linkBootCapabilities_bootLinkedShape (config : PlatformConfig) (ist : IntermediateState)
    (h : bootStartShape ist)
    (hListed : bootSlotsListed (bootCapabilitySlots config.initialObjects) ist.state)
    (hLive : ∀ r o, SystemState.namesAt ist.state.slotCapAt r o → ist.state.objectPresent o)
    (hUnique : ∀ u r r', SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r u →
      SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r' u → r = r')
    (hUncarved : ∀ u U, ist.state.getUntyped? u = some U → U.children = [])
    (hNamedU : ∀ r u, SystemState.namesAt ist.state.slotCapAt r u → ist.state.getUntyped? u ≠ none →
      SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r u) :
    bootLinkedShape (linkBootCapabilities config ist) := by
  obtain ⟨hShape, ⟨hCdt, hF⟩, ⟨hA1, hA2⟩, hUnt, ⟨rq, re, rp, hSch⟩, hRun, ⟨hNodup, hQ⟩,
    hBindings, hTab⟩ := h
  have hInv₀ := ist.hAllTables.objects.1
  have hE : ist.state.cdt = CapDerivationTree.empty := hCdt
  have hL₀ := cdtLinksAgree_of_bootEmpty hCdt fun oid obj hO => (hShape oid obj hO).2
  have hStart := BootLinks.Sound.start hE hL₀
  have hDone := (BootLinks.Sound.foldl_done hInv₀ (bootCapabilitySlots config.initialObjects)
    hStart).2
  obtain ⟨-, hL, hM, hD, hW, -, -, hEd, -, -, P, hP, hC⟩ :=
    BootLinks.Sound.foldl hInv₀ (bootCapabilitySlots config.initialObjects) hStart
  have hA := linkBootCapabilities_agree config ist
  have hUt : (linkBootCapabilities config ist).state.getUntyped? = ist.state.getUntyped? :=
    hA.getUntyped?
  -- an untyped capability of the linked state is one of the state it linked
  have hBack : ∀ {r u}, SystemState.untypedCapAt (linkBootCapabilities config ist).state.slotCapAt
      (linkBootCapabilities config ist).state.getUntyped? r u →
      SystemState.untypedCapAt ist.state.slotCapAt ist.state.getUntyped? r u :=
    fun {r _} ⟨c, hc, ht, hu⟩ => ⟨c, (hA.slotCapAt r).symm.trans hc, ht, hUt ▸ hu⟩
  have hU : ∀ u p r, SystemState.untypedCapAt (linkBootCapabilities config ist).state.slotCapAt
      (linkBootCapabilities config ist).state.getUntyped? p u →
      SystemState.untypedCapAt (linkBootCapabilities config ist).state.slotCapAt
      (linkBootCapabilities config ist).state.getUntyped? r u → p = r :=
    fun u p r hp hr => hUnique u p r (hBack hp) (hBack hr)
  have hFl := linkBootCapabilities_fields config ist
  have hSch' := linkBootCapabilities_scheduler config ist
  have hVs : ∀ oid vs, (linkBootCapabilities config ist).state.objects[oid]? =
      some (KernelObject.vspaceRoot vs) ↔ ist.state.objects[oid]? = some (KernelObject.vspaceRoot vs) :=
    fun _ _ => hA.obj_iff (fun _ e => by cases e)
  refine ⟨fun oid obj hO => ?_, ?_, ⟨fun asid oid hT => ?_, fun oid root hR => ?_⟩,
    untypedRegionsDisjoint_of_untyped_subset hUnt
      (fun _ _ hO => (hA.obj_iff (fun _ e => by cases e)).mp hO),
    ⟨rq, re, rp, hSch'.trans hSch⟩,
    SystemState.runQueueRefined_of_frame (runLinkOn_of_agree hA) (by rw [hSch'])
      (by rw [hSch']) hRun,
    ⟨by rw [hSch']; exact hNodup, fun tid hMem => ?_⟩,
    ⟨fun ref hRef => ?_, hW, hL, fun r hr => ?_, ⟨P, hP⟩, fun r o hN => ?_,
    fun p c o hc hcN _ hpN => ?_, fun u p r hp hr => .inl (hU u p r hp hr),
    fun u p r hp hr hR => ?_, fun p c u U _ hc ht hu _ r hR hr => ?_,
    fun u x hx => (SystemState.CarvedFrom.not_of_childless (fun U h => hUncarved u U
      (hUt ▸ h)) hx).elim,
    fun u U h => by rw [hUncarved u U (hUt ▸ h)]; simp,
    fun u _ U _ h => by rw [hUncarved u U (hUt ▸ h)]; simp,
    fun r u hr hu => ?_, fun Q hQ o => ?_⟩,
    .of_codes (.of_objectsAgreeOffDerivationLinks hA) hBindings,
    (linkBootCapabilities_tableReferenceFrame config ist).preserves hTab⟩
  · have e := (hA oid).map_withoutLinks
    rw [hO] at e
    cases h0 : ist.state.objects[oid]? with
    | none => rw [h0] at e; cases e
    | some o =>
      rw [h0] at e
      exact bootObjectShapeOffLinks_of_withoutLinks (Option.some.inj e) (hShape oid o h0).1
  · rw [hFl]; exact hF
  · rw [hFl] at hT
    obtain ⟨root, hRoot, hAs⟩ := hA1 asid oid hT
    exact ⟨root, (hVs oid root).mpr hRoot, hAs⟩
  · rw [hFl]; exact hA2 oid root ((hVs oid root).mp hR)
  · rw [hSch'] at hMem ⊢
    obtain ⟨t, hT, hPos, hB, hPrio⟩ := hQ tid hMem
    obtain ⟨t', hT', hw⟩ := (hA tid.toObjId).tcb_fwd hT
    exact ⟨t', hT', (TCB.proj_eq_of_withoutLinks_eq TCB.timeSlice hw).symm ▸ hPos,
      (TCB.proj_eq_of_withoutLinks_eq TCB.pipBoost hw).trans hB,
      hPrio.trans (congrArg some (TCB.proj_eq_of_withoutLinks_eq TCB.priority hw).symm)⟩
  · have hc := hD ref ((hM ref).mp hRef)
    rw [← hA.slotCapAt ref] at hc
    unfold SystemState.slotCapAt SystemState.getObject? at hc
    cases hO : (linkBootCapabilities config ist).state.objects[ref.cnode]? with
    | none => rw [hO] at hc; exact absurd rfl hc
    | some o => rw [hO] at hc; exact ⟨o, rfl, hc⟩
  · rw [hA.slotCapAt r] at hr
    exact (hM r).mpr (hDone r (hListed r hr) hr)
  · rw [SystemState.namesAt_of_eq (hA.slotCapAt r)] at hN
    exact hA.present o (hLive r o hN)
  · -- every child is a copy of its parent's capability, so names what it names
    obtain ⟨cp, cc, hp, hcc, hT⟩ := hEd p c hc
    obtain ⟨c', hc', hco⟩ := hcN
    rw [hA.slotCapAt c, hcc] at hc'
    cases hc'
    exact absurd ⟨cp, by rw [hA.slotCapAt p]; exact hp,
      hT.symm.trans hco⟩ hpN
  · -- one slot names the untyped, and the tree is acyclic
    cases hU u p r hp hr
    exact absurd (CapDerivationTree.CdtChildReachable_implies_cdtReachable _ hR) (hW p)
  · cases hU u p r ⟨c, hc, ht, by rw [hu]; exact Option.some_ne_none _⟩ hr
    exact absurd (CapDerivationTree.CdtChildReachable_implies_cdtReachable _ hR) (hW p)
  · -- a capability naming an untyped is an untyped capability, as the started state's are
    obtain ⟨c, hc, ht, hu'⟩ := hNamedU r u ((SystemState.namesAt_of_eq (hA.slotCapAt r)).mp hr)
      (hUt ▸ hu)
    exact ⟨c, (hA.slotCapAt r).trans hc, ht, hUt ▸ hu'⟩
  · -- the linking's own preorder, over the slots it read
    rw [hQ.unique hP]
    exact (hC o).congr fun x _ => SystemState.namesAt_of_eq (hA.slotCapAt x)


/-! ### What the linking keeps of the threads -/

theorem queuedOn_of_agree {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st)
    (c : SeLe4n.Kernel.Concurrency.CoreId) (t : SeLe4n.ThreadId) :
    st'.queuedOn c t = st.queuedOn c t := by
  rw [SystemState.queuedOn_eq_runLinkOn, SystemState.queuedOn_eq_runLinkOn, runLinkOn_of_agree hA]

theorem runnableOnSomeCore_of_agree {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st) (t : SeLe4n.ThreadId) :
    runnableOnSomeCore st' t = runnableOnSomeCore st t := by
  unfold runnableOnSomeCore; simp only [queuedOn_of_agree hA]

/-- A thread projection's `∃`-reading, carried across link writes. -/
theorem exists_getTcb?_of_agree {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st) (Q : TCB → Prop)
    (hQ : ∀ c : TCB, Q c.withoutLinks ↔ Q c) (t : SeLe4n.ThreadId) :
    (∃ x, st'.getTcb? t = some x ∧ Q x) ↔ (∃ x, st.getTcb? t = some x ∧ Q x) := by
  have e := hA.getTcb? t
  constructor
  · rintro ⟨x, hx, hq⟩
    rw [hx] at e
    cases hy : st.getTcb? t with
    | none => rw [hy] at e; cases e
    | some y =>
      rw [hy] at e
      have hw := Option.some.inj e
      exact ⟨y, rfl, (hQ y).mp (hw ▸ (hQ x).mpr hq)⟩
  · rintro ⟨y, hy, hq⟩
    rw [hy] at e
    cases hx : st'.getTcb? t with
    | none => rw [hx] at e; cases e
    | some x =>
      rw [hx] at e
      have hw := Option.some.inj e
      exact ⟨x, rfl, (hQ x).mp (hw ▸ (hQ y).mpr hq)⟩

theorem threadStarted_of_agree {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st) {t : SeLe4n.ThreadId}
    (h : threadStarted st t) : threadStarted st' t :=
  ⟨(runnableOnSomeCore_of_agree hA t).trans h.1,
   (exists_getTcb?_of_agree hA (fun x => x.threadState = .Ready) (fun _ => Iff.rfl) t).mpr h.2⟩

theorem threadStateConsistent_of_agree {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st)
    (hSch : st'.scheduler = st.scheduler) (h : threadStateConsistent st) :
    threadStateConsistent st' := by
  intro oid tcb' hO
  obtain ⟨tcb, hT, hw⟩ := (hA oid).tcb_back hO
  have hE : inferThreadState st' ⟨oid.toNat⟩ tcb' = inferThreadState st ⟨oid.toNat⟩ tcb := by
    unfold inferThreadState threadQueuedOnSomeCore threadRunningOnSomeCore
    rw [runnableOnSomeCore_of_agree hA, TCB.proj_eq_of_withoutLinks_eq TCB.ipcState hw]
    simp only [runningOnSomeCore, hSch]
  rw [hE, TCB.proj_eq_of_withoutLinks_eq TCB.threadState hw]
  exact h oid tcb hT

theorem stateMono_of_agree {st st' : SystemState}
    (hA : SystemState.objectsAgreeOffDerivationLinks st' st) : SystemState.StateMono st st' :=
  fun t => ⟨(exists_getTcb?_of_agree hA _ (fun _ => Iff.rfl) t).mpr,
    fun h x hx => by
      obtain ⟨y, hy, hw⟩ : ∃ y, st.getTcb? t = some y ∧ x.withoutLinks = y.withoutLinks := by
        have e := hA.getTcb? t
        rw [hx] at e
        cases hy : st.getTcb? t with
        | none => rw [hy] at e; cases e
        | some y => rw [hy] at e; exact ⟨y, rfl, Option.some.inj e⟩
      exact (TCB.proj_eq_of_withoutLinks_eq (fun c => c.Coherent) hw).mpr (h y hy),
    (exists_getTcb?_of_agree hA _ (fun _ => Iff.rfl) t).mpr,
    fun _ y x hy hx => by
      have e := hA.getTcb? t
      rw [hx, hy] at e
      exact TCB.proj_eq_of_withoutLinks_eq TCB.cpuAffinity (Option.some.inj e),
    fun h x hx => by
      have e := hA.getTcb? t
      rw [hx] at e
      cases hy : st.getTcb? t with
      | none => rw [hy] at e; cases e
      | some y =>
        rw [hy] at e
        rw [TCB.proj_eq_of_withoutLinks_eq TCB.ipcState (Option.some.inj e)]
        exact h y hy⟩

/-- The linking keeps every thread, so the labeling's witnesses. -/
theorem linkBootCapabilities_declaredWitnessesInstalled (config : PlatformConfig)
    (ist : IntermediateState) (ctx : SeLe4n.Kernel.LabelingContext) :
    declaredWitnessesInstalled (linkBootCapabilities config ist).state ctx =
      declaredWitnessesInstalled ist.state ctx := by
  unfold declaredWitnessesInstalled
  have hA := linkBootCapabilities_agree config ist
  cases ctx.separatedThreads with
  | none => rfl
  | some p => obtain ⟨lo, hi⟩ := p; simp only [hA.getTcb?_isSome]

end SeLe4n.Platform.Boot
