-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Invariant.Preservation.Revoke

/-!
# The zombie loop's passes end

WS-ZA ZA5.4 part 35.  A final delete of a capability whose object still holds
capabilities runs the zombie loop's passes on its slot (`zombiePasses`, seL4's
`finaliseSlot` loop) at most `zombieFuel` times, one more than the store holds.
This module proves that bound enough on every state the capability invariants
hold in: the passes end with the slot naming nothing that holds a capability
(`zombiePasses_end`), so the slot's own delete then retires a leaf.

The measure is **the objects the passes can still reach that hold a capability**
(`zombieLive`): the object the loop's slot names, and every object a slot of a
reached object names, the loop's own slot passed over (`ZombieReach`), each
object counted once, over the store's keys at the start (`objectKeys`).  It
assumes nothing about the shape of the graph below the slot: a CNode may hold a
capability to itself or to one above it, the cycle seL4's Zombie capability
breaks.

* Every step of a pass only empties slots (`SlotsShrink`): a finalising delete
  empties its own slot and keeps every other (`zombieDeleteSlot_slots`), and a
  finalisation writes no slot.  So nothing the passes cannot reach becomes
  reachable and no object comes to hold a capability, and the measure never
  rises (`zombieLive_le`).
* Each pass lowers it (`zombieDescend_live`).  A pass ends when the object it
  stands on holds no capability, which it held before; or with the slot naming a
  refused thread, or an object past the way down's bound, deleted — that slot's
  capability was final, so after it no slot names the object and it is out of
  reach (`not_zombieReach_of_final_deleted`).  The object a pass stands on stays
  reachable while the pass empties it, since a shortest way to it uses none of
  its own slots (`zombieReach_of_own_deleted`), and the pass empties at most its
  occupied slots there, within the budget it is given (`zombieOccupied`).
* The measure is at most the number of keys, the store's size
  (`objectKeys_length`), so `zombieFuel` passes suffice.
* A pass never reaches the way down's bound (`zombieDescend_depth_never_binds`):
  it goes down only through a final capability, so the slot naming each object
  it reaches is the one it came through and no object is visited twice
  (`zombiePath_fresh`), and the bound is one more than the store holds.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  Slots only emptied
-- ============================================================================

/-- **Every slot keeps its capability or is emptied**: what each step of the
zombie loop does to the slots. -/
def SlotsShrink (st st' : SystemState) : Prop :=
  ∀ r, st'.slotCapAt r = st.slotCapAt r ∨ st'.slotCapAt r = none

namespace SlotsShrink

theorem refl (st : SystemState) : SlotsShrink st st := fun _ => .inl rfl

theorem of_eq {st st' : SystemState} (h : ∀ r, st'.slotCapAt r = st.slotCapAt r) :
    SlotsShrink st st' := fun r => .inl (h r)

theorem trans {a b c : SystemState} (h₁ : SlotsShrink a b) (h₂ : SlotsShrink b c) :
    SlotsShrink a c := fun r =>
  match h₂ r with
  | .inl e => (h₁ r).imp e.trans e.trans
  | .inr e => .inr e

theorem names {a b : SystemState} (h : SlotsShrink a b) {r : SlotRef} {o : SeLe4n.ObjId}
    (hn : SystemState.namesAt b.slotCapAt r o) : SystemState.namesAt a.slotCapAt r o := by
  obtain ⟨c, hc, ho⟩ := hn
  rcases h r with e | e
  · exact ⟨c, e ▸ hc, ho⟩
  · rw [e] at hc; cases hc

theorem occupied {a b : SystemState} (h : SlotsShrink a b) {r : SlotRef}
    (hr : b.slotCapAt r ≠ none) : a.slotCapAt r ≠ none := by
  rcases h r with e | e
  · exact e ▸ hr
  · exact absurd e hr

/-- Finality only grows as slots are emptied. -/
theorem capFinal {a b : SystemState} (h : SlotsShrink a b) {r : SlotRef}
    (hf : a.capFinalSpec r) : b.capFinalSpec r :=
  fun o hn r' hne hn' => hf o (h.names hn) r' hne (h.names hn')

end SlotsShrink

-- ============================================================================
-- §2  The loop's two steps
-- ============================================================================

/-- **The finalisation writes no slot and keeps the capability invariants.** -/
theorem finaliseFinalObject_slots (target : Nat) {st : SystemState}
    (hB : capabilityInvariantBundle st) :
    capabilityInvariantBundle (finaliseFinalObject target st) ∧
      ∀ r, (finaliseFinalObject target st).slotCapAt r = st.slotCapAt r :=
  ⟨finaliseFinalObject_preserves_capabilityInvariantBundle target st hB,
    (finaliseFinalObject_frame target st hB.2.2.2.2.1).slotCapAt⟩

/-- **A slot with no object holding slots behind it holds nothing.** -/
theorem slotCapAt_none_of_not_admitted {st : SystemState} {addr : CSpaceAddr}
    (h : cspaceDeleteFinalisingAdmitted addr st = false) :
    st.slotCapAt ⟨addr.cnode, addr.slot⟩ = none := by
  unfold cspaceDeleteFinalisingAdmitted at h
  unfold SystemState.slotCapAt
  cases hO : st.getObject? addr.cnode with
  | none => rfl
  | some o =>
    rw [hO] at h
    cases o <;> first | rfl | (simp [KernelObject.holdsSlots] at h)

/-- **One slot's delete in the loop empties that slot and keeps every other**,
and keeps the capability invariants: the delete itself, the teardown (which
writes no slot), the finalisation (which writes no slot) and the retire (which
erases an object holding no capability, `retireFinalObject_slotCapAt`). -/
theorem zombieDeleteSlot_slots (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) {st : SystemState} (hB : capabilityInvariantBundle st) :
    capabilityInvariantBundle (zombieDeleteSlot ec cnode slot st) ∧
      (zombieDeleteSlot ec cnode slot st).slotCapAt ⟨cnode, slot⟩ = none ∧
      ∀ r, r ≠ ⟨cnode, slot⟩ →
        (zombieDeleteSlot ec cnode slot st).slotCapAt r = st.slotCapAt r := by
  unfold zombieDeleteSlot
  split
  · next hA =>
    have hD := cspaceDeleteSlotFinalising_of_slotHolder (ec := ec) hA
    refine ⟨cspaceDeleteSlotFinalising_preserves_capabilityInvariantBundle ec _ st _ hB hD, ?_⟩
    obtain ⟨st1, st2, h1, h2, e⟩ := cspaceDeleteSlotFinalising_ok ec _ st _ hD
    have hB1 := cspaceDeleteSlot_preserves_capabilityInvariantBundle st st1 _ hB h1
    obtain ⟨hC1n, hC1, -⟩ := cspaceDeleteSlot_slots hB.2.2.2.2.1 h1
    obtain ⟨hI2, -, hC2, -, -⟩ := finaliseDestroyedCapabilities_slots ec _ _ st1 st2
      hB1.2.2.2.2.1 h2
    have hLast : ∀ r, (cspaceDeleteFinalisingPerformAt ec cnode slot st).slotCapAt r =
        st2.slotCapAt r := by
      intro r
      rw [e]
      unfold retireFinalisedObject
      rw [retireFinalObject_slotCapAt ec _ _ _
          (finaliseFinalObject_frame _ st2 hI2).invExt r,
        (finaliseFinalObject_frame _ st2 hI2).slotCapAt r]
    refine ⟨by rw [hLast, hC2]; exact hC1n, fun r hr => ?_⟩
    rw [hLast, hC2, hC1 r hr]
  · next hA =>
    refine ⟨hB, slotCapAt_none_of_not_admitted (addr := ⟨cnode, slot⟩) ?_, fun _ _ => rfl⟩
    simpa using hA

/-- One slot's delete only empties slots. -/
theorem zombieDeleteSlot_shrink (ec : Concurrency.CoreId) (cnode : SeLe4n.ObjId)
    (slot : SeLe4n.Slot) {st : SystemState} (hB : capabilityInvariantBundle st) :
    SlotsShrink st (zombieDeleteSlot ec cnode slot st) := by
  obtain ⟨-, h0, h1⟩ := zombieDeleteSlot_slots ec cnode slot hB
  intro r
  by_cases hr : r = ⟨cnode, slot⟩
  · subst hr; exact .inr h0
  · exact .inl (h1 r hr)

-- ============================================================================
-- §3  What the loop's codes say about the slots
-- ============================================================================

/-- A CNode's slot holds a capability exactly when its cell is occupied. -/
theorem cnode_slotCap_ne_none_iff (cn : CNode) (i : Nat) :
    (KernelObject.cnode cn).slotCap (SeLe4n.Slot.ofNat i) ≠ none ↔
      SlotOccupancy.occupied cn.cells i = true := by
  simp only [KernelObject.slotCap, CNode.lookup, CNode.slots, cn.slots_agree, slotArrayGet,
    SlotOccupancy.occupied, SeLe4n.Slot.ofNat, SeLe4n.Slot.toNat]
  by_cases h : i < cn.cells.size
  · simp [h, Array.getD_eq_getD_getElem?, Option.isSome_iff_ne_none]
  · simp [h, Array.getD_eq_getD_getElem?]

/-- **What a CNode's next-slot code says**: `0` when every occupied slot is the
passed-over one, or `k + 1` for an occupied slot `k` that is not. -/
theorem zombieNextSlot_cnode (cn : CNode) (skip : Nat) :
    (zombieNextSlot (.cnode cn) skip = 0 ∧
        ∀ i, SlotOccupancy.occupied cn.cells i = true → i + 1 = skip) ∨
      ∃ k, zombieNextSlot (.cnode cn) skip = k + 1 ∧
        SlotOccupancy.occupied cn.cells k = true ∧ k + 1 ≠ skip := by
  obtain ⟨L, hL⟩ := cn.occ_agree
  have hH := hL.head_eq
  have hC := hL.chain
  dsimp only [zombieNextSlot]
  cases L with
  | nil =>
    left
    simp only [List.head?_nil, SlotOccupancy.code_none] at hH
    refine ⟨?_, fun i hi => absurd ((hL.mem i).2 hi) (by simp)⟩
    rw [hH]
    by_cases hs : skip = 0 <;> simp [hs]
    omega
  | cons a rest =>
    simp only [List.head?_cons, SlotOccupancy.code_some] at hH
    obtain ⟨-, hN, -⟩ := hC
    by_cases hs : skip ≠ 0 ∧ a + 1 = skip
    · have e : (skip != 0 && cn.occHead == skip) = true := by
        simp [hH, hs.1, hs.2]
      rw [if_pos e, hH, Nat.add_sub_cancel, hN]
      cases rest with
      | nil =>
        left
        refine ⟨rfl, fun i hi => ?_⟩
        have := (hL.mem i).2 hi
        simp only [List.mem_singleton] at this
        rw [this]; exact hs.2
      | cons b rest' =>
        right
        refine ⟨b, rfl, (hL.mem b).1 (by simp), fun hb => ?_⟩
        have hab : a ≠ b := by
          have := hL.nodup
          simp only [List.nodup_cons, List.mem_cons, not_or] at this
          exact this.1.1
        omega
    · have e : (skip != 0 && cn.occHead == skip) = false := by
        simp only [hH]
        by_cases h0 : skip = 0
        · simp [h0]
        · have : a + 1 ≠ skip := fun h => hs ⟨h0, h⟩
          simp [h0, this]
      rw [if_neg (by simp [e]), hH]
      right
      refine ⟨a, rfl, (hL.mem a).1 (by simp), fun h => hs ⟨by omega, h⟩⟩

/-- **What an object's next-slot code says**: `0` when every slot holding a
capability is the passed-over one (`skip`, a code), or `k + 1` for a slot `k`
holding one that is not. -/
theorem zombieNextSlot_spec (o : KernelObject) (skip : Nat) :
    (zombieNextSlot o skip = 0 ∧ ∀ i, o.slotCap (SeLe4n.Slot.ofNat i) ≠ none → i + 1 = skip) ∨
      ∃ k, zombieNextSlot o skip = k + 1 ∧ o.slotCap (SeLe4n.Slot.ofNat k) ≠ none ∧
        k + 1 ≠ skip := by
  cases o with
  | cnode cn =>
    rcases zombieNextSlot_cnode cn skip with ⟨h0, hA⟩ | ⟨k, hk, hO, hne⟩
    · exact .inl ⟨h0, fun i hi => hA i ((cnode_slotCap_ne_none_iff cn i).1 hi)⟩
    · exact .inr ⟨k, hk, (cnode_slotCap_ne_none_iff cn k).2 hO, hne⟩
  | tcb t =>
    have hS : ∀ i, (KernelObject.tcb t).slotCap (SeLe4n.Slot.ofNat i) =
        if h : i < 2 then t.spaceCells[i] else none := fun _ => rfl
    have hS0 : (KernelObject.tcb t).slotCap (SeLe4n.Slot.ofNat 0) = t.spaceCells[0] := rfl
    have hS1 : (KernelObject.tcb t).slotCap (SeLe4n.Slot.ofNat 1) = t.spaceCells[1] := rfl
    dsimp only [zombieNextSlot]
    by_cases hA : (t.spaceCells[0].isSome && skip != 1) = true
    · rw [if_pos hA]
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hA
      refine .inr ⟨0, rfl, ?_, fun h => hA.2 (by omega)⟩
      rw [hS0]; exact Option.isSome_iff_ne_none.1 hA.1
    · rw [if_neg hA]
      by_cases hB : (t.spaceCells[1].isSome && skip != 2) = true
      · rw [if_pos hB]
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq] at hB
        refine .inr ⟨1, rfl, ?_, fun h => hB.2 (by omega)⟩
        rw [hS1]; exact Option.isSome_iff_ne_none.1 hB.1
      · rw [if_neg hB]
        simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, not_and, Decidable.not_not] at hA hB
        refine .inl ⟨rfl, fun i hi => ?_⟩
        rw [hS] at hi
        by_cases hi2 : i < 2
        · rw [dif_pos hi2] at hi
          have hs := Option.isSome_iff_ne_none.2 hi
          have : i = 0 ∨ i = 1 := by omega
          rcases this with rfl | rfl
          · exact (hA hs).symm
          · exact (hB hs).symm
        · rw [dif_neg hi2] at hi; exact absurd rfl hi
  | _ => exact .inl ⟨rfl, fun _ h => absurd rfl h⟩

-- ============================================================================
-- §4  What the passes can still reach
-- ============================================================================

/-- **The objects the zombie loop on slot `rootSlot` of `root` can still
reach**: the object that slot's capability names, and every object a slot of a
reached object names, the loop's own slot passed over.  Every capability
counts, final or not, since a capability that is not final now may be later. -/
inductive ZombieReach (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot) (st : SystemState) :
    SeLe4n.ObjId → Prop
  | named {y : SeLe4n.ObjId} : SystemState.namesAt st.slotCapAt ⟨root, rootSlot⟩ y →
      ZombieReach root rootSlot st y
  | through {x y : SeLe4n.ObjId} (s : SeLe4n.Slot) : ZombieReach root rootSlot st x →
      (⟨x, s⟩ : SlotRef) ≠ ⟨root, rootSlot⟩ → SystemState.namesAt st.slotCapAt ⟨x, s⟩ y →
      ZombieReach root rootSlot st y

/-- **The object at `x` holds a capability the loop may delete**: in a slot
other than the loop's own. -/
def zombieHolds (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot) (st : SystemState)
    (x : SeLe4n.ObjId) : Prop :=
  ∃ s : SeLe4n.Slot, (⟨x, s⟩ : SlotRef) ≠ ⟨root, rootSlot⟩ ∧ st.slotCapAt ⟨x, s⟩ ≠ none

/-- Nothing becomes reachable as slots are emptied. -/
theorem ZombieReach.of_shrink {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {st st' : SystemState} (h : SlotsShrink st st') {y : SeLe4n.ObjId}
    (hy : ZombieReach root rootSlot st' y) : ZombieReach root rootSlot st y := by
  induction hy with
  | named hn => exact .named (h.names hn)
  | through s _ hne hn ih => exact .through s ih hne (h.names hn)

/-- No object comes to hold a capability as slots are emptied. -/
theorem zombieHolds.of_shrink {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {st st' : SystemState} (h : SlotsShrink st st') {x : SeLe4n.ObjId}
    (hx : zombieHolds root rootSlot st' x) : zombieHolds root rootSlot st x :=
  let ⟨s, hne, hs⟩ := hx; ⟨s, hne, h.occupied hs⟩

/-- **An object stays reachable when one of its own slots is emptied**: a
shortest way to it uses none of its own slots. -/
theorem zombieReach_of_own_deleted {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {st st' : SystemState} {x : SeLe4n.ObjId} {s0 : SeLe4n.Slot}
    (hne : (⟨x, s0⟩ : SlotRef) ≠ ⟨root, rootSlot⟩)
    (hS : ∀ r, r ≠ ⟨x, s0⟩ → st'.slotCapAt r = st.slotCapAt r)
    (hx : ZombieReach root rootSlot st x) : ZombieReach root rootSlot st' x := by
  have key : ∀ y, ZombieReach root rootSlot st y →
      ZombieReach root rootSlot st' y ∨ ZombieReach root rootSlot st' x := by
    intro y hy
    induction hy with
    | named hn =>
      exact .inl (.named ((SystemState.namesAt_of_eq (hS _ (Ne.symm hne))).2 hn))
    | @through u v s hu hne' hn ih =>
      rcases ih with hu' | hx'
      · by_cases e : (⟨u, s⟩ : SlotRef) = ⟨x, s0⟩
        · cases e; exact .inr hu'
        · exact .inl (.through s hu' hne' ((SystemState.namesAt_of_eq (hS _ e)).2 hn))
      · exact .inr hx'
  exact (key x hx).elim id id

/-- **An object whose final capability was emptied is out of reach**: no other
slot named it, and slots are only emptied. -/
theorem not_zombieReach_of_final_deleted {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {st st' : SystemState} {r : SlotRef} {y : SeLe4n.ObjId} (hf : st.capFinalSpec r)
    (hn : SystemState.namesAt st.slotCapAt r y) (hS : SlotsShrink st st')
    (h0 : st'.slotCapAt r = none) : ¬ ZombieReach root rootSlot st' y := by
  have gone : ∀ q, SystemState.namesAt st'.slotCapAt q y → False := by
    intro q hq
    by_cases e : q = r
    · subst e; obtain ⟨c, hc, -⟩ := hq; rw [h0] at hc; cases hc
    · exact hf y hn q e (hS.names hq)
  intro h
  cases h with
  | named hq => exact gone _ hq
  | through s _ _ hq => exact gone _ hq

-- ============================================================================
-- §5  The loop's codes, read as reach and holding
-- ============================================================================

/-- The passed-over code names exactly the loop's own slot. -/
theorem zombieSkip_eq_iff (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot) (x : SeLe4n.ObjId)
    (s : SeLe4n.Slot) :
    s.toNat + 1 = zombieSkip root rootSlot x ↔ (⟨x, s⟩ : SlotRef) = ⟨root, rootSlot⟩ := by
  unfold zombieSkip
  by_cases hx : x = root
  · subst hx
    simp only [beq_self_eq_true, ↓reduceIte, Nat.add_right_cancel_iff, SlotRef.mk.injEq,
      true_and]
    constructor
    · intro h; cases s; cases rootSlot; simp_all [SeLe4n.Slot.toNat]
    · intro h; rw [h]
  · have : (x == root) = false := by simpa using hx
    simp only [this, Bool.false_eq_true, ↓reduceIte, Nat.add_one_ne_zero, false_iff]
    intro h; cases h; exact hx rfl

/-- **Holding a capability, read off the next-slot code**: an object holds one
the loop may delete exactly when it stands in the store with a nonzero code. -/
theorem zombieHolds_iff (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot) (st : SystemState)
    (x : SeLe4n.ObjId) :
    zombieHolds root rootSlot st x ↔
      ∃ o, st.getObject? x = some o ∧ zombieNextSlot o (zombieSkip root rootSlot x) ≠ 0 := by
  constructor
  · rintro ⟨s, hne, hs⟩
    unfold SystemState.slotCapAt at hs
    cases hO : st.getObject? x with
    | none => rw [hO] at hs; exact absurd rfl hs
    | some o =>
      rw [hO] at hs
      refine ⟨o, rfl, fun h0 => ?_⟩
      rcases zombieNextSlot_spec o (zombieSkip root rootSlot x) with ⟨-, hA⟩ | ⟨k, hk, -⟩
      · exact hne ((zombieSkip_eq_iff root rootSlot x s).1 (hA s.toNat hs))
      · rw [hk] at h0; cases h0
  · rintro ⟨o, hO, hN⟩
    rcases zombieNextSlot_spec o (zombieSkip root rootSlot x) with ⟨h0, -⟩ | ⟨k, -, hs, hne⟩
    · exact absurd h0 hN
    · refine ⟨SeLe4n.Slot.ofNat k, fun e => hne ((zombieSkip_eq_iff root rootSlot x _).2 e), ?_⟩
      unfold SystemState.slotCapAt; rw [hO]; exact hs

/-- `ObjId.ofNat` of an object's word is the object. -/
@[simp] theorem objId_ofNat_val (x : SeLe4n.ObjId) : SeLe4n.ObjId.ofNat x.val = x := rfl

/-- **A nonzero class, read**: the slot's capability is final and names an
object standing in the store with a nonzero next-slot code; from `2` up, the
class is that code plus one. -/
theorem zombieSlotClass_ne_zero {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {st : SystemState} {cnode : SeLe4n.ObjId} {slot : SeLe4n.Slot}
    (hB : capabilityInvariantBundle st) (h : zombieSlotClass st root rootSlot cnode slot ≠ 0) :
    ∃ x o, slotRetireTarget st cnode slot = x.val + 1 ∧
      SystemState.namesAt st.slotCapAt ⟨cnode, slot⟩ x ∧ st.capFinalSpec ⟨cnode, slot⟩ ∧
      st.getObject? x = some o ∧ zombieNextSlot o (zombieSkip root rootSlot x) ≠ 0 ∧
      (2 ≤ zombieSlotClass st root rootSlot cnode slot →
        zombieSlotClass st root rootSlot cnode slot =
          zombieNextSlot o (zombieSkip root rootSlot x) + 1) := by
  have hT : slotRetireTarget st cnode slot ≠ 0 := by
    intro h0; apply h; unfold zombieSlotClass; simp only [h0, ↓reduceIte]
  obtain ⟨c, hc, hn, hf⟩ := slotRetireTarget_spec hB hT
  refine ⟨SeLe4n.ObjId.ofNat (slotRetireTarget st cnode slot - 1), ?_⟩
  have ht : slotRetireTarget st cnode slot =
      (SeLe4n.ObjId.ofNat (slotRetireTarget st cnode slot - 1)).val + 1 := by
    simp only [SeLe4n.ObjId.ofNat]; omega
  unfold zombieSlotClass at h ⊢
  simp only [hT, ↓reduceIte] at h ⊢
  cases hO : st.getObject? (SeLe4n.ObjId.ofNat (slotRetireTarget st cnode slot - 1)) with
  | none => rw [hO] at h; exact absurd rfl h
  | some o =>
    rw [hO] at h
    dsimp only at h ⊢
    by_cases hk : zombieNextSlot o (zombieSkip root rootSlot
        (SeLe4n.ObjId.ofNat (slotRetireTarget st cnode slot - 1))) = 0
    · rw [if_pos hk] at h; exact absurd rfl h
    · refine ⟨o, ht, ⟨c, hc, hn⟩, hf, rfl, hk, fun h2 => ?_⟩
      rw [if_neg hk] at h2 ⊢
      cases o with
      | tcb t =>
        dsimp only at h2 ⊢
        split
        · rfl
        · next hF => rw [if_neg hF] at h2; omega
      | _ => rfl

/-- **A final capability names its retire target**: when the object it names is
of a retirable kind. -/
theorem slotRetireTarget_of_final {st : SystemState} {cnode : SeLe4n.ObjId}
    {slot : SeLe4n.Slot} {x : SeLe4n.ObjId} (hB : capabilityInvariantBundle st)
    (hn : SystemState.namesAt st.slotCapAt ⟨cnode, slot⟩ x)
    (hf : st.capFinalSpec ⟨cnode, slot⟩) (hK : retirableKind st x = true) :
    slotRetireTarget st cnode slot = x.val + 1 := by
  obtain ⟨c, hc, ho⟩ := hn
  have hF : st.capIsFinal cnode slot = true := (capIsFinal_iff_capFinalSpec hB ⟨cnode, slot⟩).2 hf
  unfold slotRetireTarget
  rw [hc]
  dsimp only
  unfold Capability.namedObject at ho
  cases ht : c.target with
  | object y => rw [ht] at ho; cases ho; simp [hK, hF]
  | replyCap r => rw [ht] at ho; cases ho; simp [hK, hF]
  | cnodeSlot cn _ => rw [ht] at ho; cases ho; simp [hK, hF]
  | auditTrail => rw [ht] at ho; cases ho

/-- An object holding a capability is of a retirable kind. -/
theorem retirableKind_of_zombieHolds {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {st : SystemState} {x : SeLe4n.ObjId} (h : zombieHolds root rootSlot st x) :
    retirableKind st x = true := by
  obtain ⟨o, hO, hN⟩ := (zombieHolds_iff root rootSlot st x).1 h
  have hH := holdsSlots_of_zombieNextSlot hN
  unfold retirableKind SystemState.getObjectType?
  unfold SystemState.getObject? at hO
  rw [hO]
  cases o <;> simp_all [KernelObject.holdsSlots, KernelObject.objectType]

/-- **A final capability naming an object that holds a capability has a nonzero
class.** -/
theorem zombieSlotClass_ne_zero_of {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {st : SystemState} {cnode : SeLe4n.ObjId} {slot : SeLe4n.Slot} {x : SeLe4n.ObjId}
    (hB : capabilityInvariantBundle st) (hn : SystemState.namesAt st.slotCapAt ⟨cnode, slot⟩ x)
    (hf : st.capFinalSpec ⟨cnode, slot⟩) (hH : zombieHolds root rootSlot st x) :
    zombieSlotClass st root rootSlot cnode slot ≠ 0 := by
  have hT := slotRetireTarget_of_final hB hn hf (retirableKind_of_zombieHolds hH)
  obtain ⟨o, hO, hN⟩ := (zombieHolds_iff root rootSlot st x).1 hH
  unfold zombieSlotClass
  simp only [hT, Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, objId_ofNat_val, hO]
  rw [if_neg hN]
  cases o with
  | tcb t => dsimp only; split <;> omega
  | _ => dsimp only; omega

-- ============================================================================
-- §6  The measure
-- ============================================================================

/-- A count that loses a counted element and gains none is smaller. -/
theorem countP_lt_of_lost {α : Type} {p q : α → Bool} :
    ∀ {l : List α}, (∀ x ∈ l, q x = true → p x = true) → ∀ {y : α}, y ∈ l →
      p y = true → q y = false → l.countP q < l.countP p
  | [], _, _, hy, _, _ => absurd hy List.not_mem_nil
  | a :: l, hM, y, hy, hp, hq => by
    rw [List.countP_cons, List.countP_cons]
    have hM' : ∀ x ∈ l, q x = true → p x = true := fun x hx => hM x (List.mem_cons_of_mem a hx)
    have hHead : (if q a = true then 1 else 0) ≤ (if p a = true then 1 else 0) := by
      by_cases hqa : q a = true
      · rw [if_pos hqa, if_pos (hM a List.mem_cons_self hqa)]; exact Nat.le_refl 1
      · rw [if_neg hqa]; exact Nat.zero_le _
    rcases List.mem_cons.1 hy with rfl | hy'
    · have := List.countP_mono_left hM'
      rw [hq, hp]; simp only [Bool.false_eq_true, ↓reduceIte]; omega
    · have := countP_lt_of_lost hM' hy' hp hq
      omega

open Classical in
/-- **The objects the passes can still reach that hold a capability**, counted
over the keys `K`, each once: the zombie loop's measure. -/
noncomputable def zombieLive (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot)
    (K : List SeLe4n.ObjId) (st : SystemState) : Nat :=
  K.countP fun y => decide (ZombieReach root rootSlot st y ∧ zombieHolds root rootSlot st y)

/-- The measure never rises as slots are emptied. -/
theorem zombieLive_le {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot} {K : List SeLe4n.ObjId}
    {st st' : SystemState} (h : SlotsShrink st st') :
    zombieLive root rootSlot K st' ≤ zombieLive root rootSlot K st := by
  unfold zombieLive
  refine List.countP_mono_left fun y _ hy => ?_
  simp only [decide_eq_true_eq] at hy ⊢
  exact ⟨hy.1.of_shrink h, hy.2.of_shrink h⟩

/-- **The measure falls** when a key it counted is out of reach or holds no
capability after the slots are emptied. -/
theorem zombieLive_lt {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot} {K : List SeLe4n.ObjId}
    {st st' : SystemState} (h : SlotsShrink st st') {y : SeLe4n.ObjId} (hy : y ∈ K)
    (hR : ZombieReach root rootSlot st y) (hH : zombieHolds root rootSlot st y)
    (hn : ¬ (ZombieReach root rootSlot st' y ∧ zombieHolds root rootSlot st' y)) :
    zombieLive root rootSlot K st' < zombieLive root rootSlot K st := by
  unfold zombieLive
  refine countP_lt_of_lost (fun x _ hx => ?_) hy (by simpa using ⟨hR, hH⟩) (by simpa using hn)
  simp only [decide_eq_true_eq] at hx ⊢
  exact ⟨hx.1.of_shrink h, hx.2.of_shrink h⟩

/-- The measure is at most the number of keys. -/
theorem zombieLive_le_length (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot)
    (K : List SeLe4n.ObjId) (st : SystemState) : zombieLive root rootSlot K st ≤ K.length :=
  List.countP_le_length

-- ============================================================================
-- §7  The slots a pass may empty where it stands
-- ============================================================================

/-- **The slots of the object at `x` below `M` that hold a capability the loop
may delete**: what a pass standing there still has to empty. -/
def zombieOccupied (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot) (st : SystemState)
    (x : SeLe4n.ObjId) (M : Nat) : Nat :=
  (List.range M).countP fun i =>
    decide ((⟨x, SeLe4n.Slot.ofNat i⟩ : SlotRef) ≠ ⟨root, rootSlot⟩) &&
      (st.slotCapAt ⟨x, SeLe4n.Slot.ofNat i⟩).isSome

theorem zombieOccupied_le (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot) (st : SystemState)
    (x : SeLe4n.ObjId) (M : Nat) : zombieOccupied root rootSlot st x M ≤ M := by
  unfold zombieOccupied
  exact Nat.le_trans List.countP_le_length (Nat.le_of_eq List.length_range)

theorem zombieOccupied_le_of_shrink {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {st st' : SystemState} (h : SlotsShrink st st') (x : SeLe4n.ObjId) (M : Nat) :
    zombieOccupied root rootSlot st' x M ≤ zombieOccupied root rootSlot st x M := by
  unfold zombieOccupied
  refine List.countP_mono_left fun i _ hi => ?_
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_ne_none] at hi ⊢
  exact ⟨hi.1, h.occupied hi.2⟩

/-- **Emptying a counted slot lowers the count.** -/
theorem zombieOccupied_lt {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {st st' : SystemState} (h : SlotsShrink st st') {x : SeLe4n.ObjId} {M k : Nat}
    (hk : k < M) (hne : (⟨x, SeLe4n.Slot.ofNat k⟩ : SlotRef) ≠ ⟨root, rootSlot⟩)
    (hs : st.slotCapAt ⟨x, SeLe4n.Slot.ofNat k⟩ ≠ none)
    (h0 : st'.slotCapAt ⟨x, SeLe4n.Slot.ofNat k⟩ = none) :
    zombieOccupied root rootSlot st' x M < zombieOccupied root rootSlot st x M := by
  unfold zombieOccupied
  refine countP_lt_of_lost (fun i _ hi => ?_) (List.mem_range.2 hk) ?_ ?_
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_ne_none] at hi ⊢
    exact ⟨hi.1, h.occupied hi.2⟩
  · simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_ne_none]
    exact ⟨hne, hs⟩
  · simp [h0]

/-- **An object holding a capability below `M` has one to empty.** -/
theorem zombieOccupied_pos {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot} {st : SystemState}
    {x : SeLe4n.ObjId} {M : Nat} (hH : zombieHolds root rootSlot st x)
    (hM : ∀ i : SeLe4n.Slot, st.slotCapAt ⟨x, i⟩ ≠ none → i.toNat < M) :
    0 < zombieOccupied root rootSlot st x M := by
  obtain ⟨s, hne, hs⟩ := hH
  unfold zombieOccupied
  refine List.countP_pos_iff.2 ⟨s.toNat, List.mem_range.2 (hM s hs), ?_⟩
  simp only [Bool.and_eq_true, decide_eq_true_eq, Option.isSome_iff_ne_none]
  exact ⟨hne, hs⟩

/-- **Every slot holding a capability lies below the object's slot count**
(`zombieObjectSlots`): a CNode's cells, a thread's two space slots. -/
theorem zombieObjectSlots_bound (st : SystemState) (x : SeLe4n.ObjId) :
    ∀ i : SeLe4n.Slot, st.slotCapAt ⟨x, i⟩ ≠ none → i.toNat < zombieObjectSlots st x := by
  intro i hi
  unfold SystemState.slotCapAt at hi
  unfold zombieObjectSlots
  cases hO : st.getObject? x with
  | none => rw [hO] at hi; exact absurd rfl hi
  | some o =>
    rw [hO] at hi
    cases o with
    | cnode cn =>
      dsimp only
      have := (cnode_slotCap_ne_none_iff cn i.toNat).1 hi
      exact SlotOccupancy.occupied_lt this
    | tcb t =>
      dsimp only
      simp only [KernelObject.slotCap, TCB.spaceSlotCap] at hi
      by_cases h2 : i.toNat < 2
      · exact h2
      · rw [dif_neg h2] at hi; exact absurd rfl hi
    | _ => exact absurd rfl hi

-- ============================================================================
-- §8  The store's keys
-- ============================================================================

/-- **The store's keys**, one per occupied entry of its table. -/
def objectKeys (st : SystemState) : List SeLe4n.ObjId :=
  st.objects.slots.toList.filterMap fun o => o.map (·.key)

/-- There are as many keys as the store holds objects. -/
theorem objectKeys_length {st : SystemState} (hInv : st.objects.invExt) :
    (objectKeys st).length = st.objects.size := by
  unfold objectKeys
  rw [List.length_filterMap_eq_countP, hInv.1.sizeCount]
  unfold SeLe4n.Kernel.RobinHood.countOccupied
  congr 1
  funext o
  cases o <;> rfl

/-- Every object in the store is under a key. -/
theorem mem_objectKeys {st : SystemState} {x : SeLe4n.ObjId} {o : KernelObject}
    (h : st.getObject? x = some o) : x ∈ objectKeys st := by
  obtain ⟨p, hp, e, he, hk, -⟩ := SeLe4n.Kernel.RobinHood.RHTable.get_some_slot_entry
    st.objects x o h
  unfold objectKeys
  refine List.mem_filterMap.2 ⟨some e, ?_, ?_⟩
  · rw [← he]; exact Array.getElem_mem_toList _
  · simp only [Option.map_some, Option.some.injEq]; exact beq_iff_eq.1 hk

/-- An object holding a capability is under a key. -/
theorem mem_objectKeys_of_holds {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {st : SystemState} {x : SeLe4n.ObjId} (h : zombieHolds root rootSlot st x) :
    x ∈ objectKeys st :=
  let ⟨_, hO, _⟩ := (zombieHolds_iff root rootSlot st x).1 h
  mem_objectKeys hO

-- ============================================================================
-- §9  Each pass lowers the measure
-- ============================================================================

/-- A slot names at most one object. -/
theorem namesAt_unique {cap : SlotRef → Option Capability} {r : SlotRef} {a b : SeLe4n.ObjId}
    (ha : SystemState.namesAt cap r a) (hb : SystemState.namesAt cap r b) : a = b := by
  obtain ⟨c, hc, hca⟩ := ha
  obtain ⟨c', hc', hcb⟩ := hb
  rw [hc] at hc'; cases hc'
  rw [hca] at hcb; cases hcb; rfl

/-- **Where a pass stands**: at slot `slot` of `cnode`, whose class is `cls`;
when that is not `0`, the object the slot names is reachable, and at most
`budget` of its slots below some bound `M` past all it holds are occupied. -/
def ZombieStand (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot) (st : SystemState)
    (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (cls budget : Nat) : Prop :=
  cls = zombieSlotClass st root rootSlot cnode slot ∧
    (cls ≠ 0 → ∃ x : SeLe4n.ObjId, slotRetireTarget st cnode slot = x.val + 1 ∧
      ZombieReach root rootSlot st x ∧
      ∃ M, (∀ i : SeLe4n.Slot, st.slotCapAt ⟨x, i⟩ ≠ none → i.toNat < M) ∧
        zombieOccupied root rootSlot st x M ≤ budget)

/-- **A pass's standing, read**: the object the slot names, its final
capability, the object's next-slot code, its reach, its occupied slots, and that
it holds a capability. -/
theorem ZombieStand.target {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot} {st : SystemState}
    {cnode : SeLe4n.ObjId} {slot : SeLe4n.Slot} {cls budget : Nat}
    (hB : capabilityInvariantBundle st) (hc : cls ≠ 0)
    (hS : ZombieStand root rootSlot st cnode slot cls budget) :
    ∃ x : SeLe4n.ObjId, slotRetireTarget st cnode slot = x.val + 1 ∧
      SystemState.namesAt st.slotCapAt ⟨cnode, slot⟩ x ∧ st.capFinalSpec ⟨cnode, slot⟩ ∧
      ZombieReach root rootSlot st x ∧ zombieHolds root rootSlot st x ∧
      ∃ M, (∀ i : SeLe4n.Slot, st.slotCapAt ⟨x, i⟩ ≠ none → i.toNat < M) ∧
        zombieOccupied root rootSlot st x M ≤ budget := by
  obtain ⟨hcls, hR⟩ := hS
  obtain ⟨x, hT, hRx, hM⟩ := hR hc
  obtain ⟨x', o, hT', hn, hf, hO, hN, -⟩ := zombieSlotClass_ne_zero hB (hcls ▸ hc)
  have e : x' = x := SeLe4n.ObjId.ext (by omega)
  subst e
  exact ⟨x', hT, hn, hf, hRx, (zombieHolds_iff root rootSlot st x').2 ⟨o, hO, hN⟩, hM⟩

/-- **Deleting the slot of a final capability whose object is counted lowers
the measure.** -/
theorem zombieLive_lt_of_final_deleted {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {K : List SeLe4n.ObjId} {s t r : SystemState} {ref : SlotRef} {x : SeLe4n.ObjId}
    (hSt : SlotsShrink s t) (hTr : SlotsShrink t r) (hf : s.capFinalSpec ref)
    (hn : SystemState.namesAt s.slotCapAt ref x) (h0 : r.slotCapAt ref = none)
    (hR : ZombieReach root rootSlot s x) (hH : zombieHolds root rootSlot s x) (hK : x ∈ K) :
    zombieLive root rootSlot K r < zombieLive root rootSlot K s :=
  zombieLive_lt (hSt.trans hTr) hK hR hH
    (fun h => not_zombieReach_of_final_deleted hf hn (hSt.trans hTr) h0 h.1)

/-- **What a pass leaves**: the capability invariants, slots only emptied, and,
when it started on a nonzero class, the measure lowered. -/
def ZombieDone (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot) (K : List SeLe4n.ObjId)
    (st r : SystemState) (cls : Nat) : Prop :=
  capabilityInvariantBundle r ∧ SlotsShrink st r ∧
    (cls ≠ 0 → zombieLive root rootSlot K r < zombieLive root rootSlot K st)

/-- **Each pass lowers the measure** (`zombieDescend`): from a standing with a
nonzero class, whatever the depth and budget, the pass ends with the measure
lower, slots only emptied and the capability invariants kept. -/
theorem zombieDescend_live (ec : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) (K : List SeLe4n.ObjId) :
    ∀ (depth budget : Nat) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (cls : Nat)
      (st : SystemState), capabilityInvariantBundle st →
      (∀ y, zombieHolds root rootSlot st y → y ∈ K) →
      ZombieStand root rootSlot st cnode slot cls budget →
      ZombieDone root rootSlot K st
        (zombieDescend ec root rootSlot depth budget cnode slot cls st) cls
  | 0, _, cnode, slot, cls, st, hB, hK, hS => by
    rw [zombieDescend]
    obtain ⟨hB', h0, -⟩ := zombieDeleteSlot_slots ec cnode slot hB
    have hSh := zombieDeleteSlot_shrink ec cnode slot hB
    refine ⟨hB', hSh, fun hc => ?_⟩
    obtain ⟨x, -, hn, hf, hR, hH, -⟩ := hS.target hB hc
    exact zombieLive_lt_of_final_deleted (.refl _) hSh hf hn h0 hR hH (hK x hH)
  | _ + 1, 0, cnode, slot, cls, st, hB, _, hS => by
    rw [zombieDescend]
    refine ⟨hB, .refl st, fun hc => ?_⟩
    obtain ⟨x, -, -, -, -, hH, M, hM, hO⟩ := hS.target hB hc
    have := zombieOccupied_pos hH hM
    omega
  | depth + 1, budget + 1, cnode, slot, cls, st, hB, hK, hS => by
    rw [zombieDescend]
    dsimp only
    by_cases hc : cls = 0
    · rw [if_pos hc]; exact ⟨hB, .refl st, fun h => absurd hc h⟩
    rw [if_neg hc]
    obtain ⟨x, -, hn, hf, hR, hH, M, hM, hOcc⟩ := hS.target hB hc
    have hst1 : capabilityInvariantBundle
          (if cls = 1 then finaliseFinalObject (slotRetireTarget st cnode slot) st else st) ∧
        ∀ r, (if cls = 1 then finaliseFinalObject (slotRetireTarget st cnode slot) st
          else st).slotCapAt r = st.slotCapAt r := by
      split
      · exact finaliseFinalObject_slots _ hB
      · exact ⟨hB, fun _ => rfl⟩
    have hc1 : (if cls = 1 then zombieSlotClass
          (if cls = 1 then finaliseFinalObject (slotRetireTarget st cnode slot) st else st)
          root rootSlot cnode slot else cls) =
        zombieSlotClass
          (if cls = 1 then finaliseFinalObject (slotRetireTarget st cnode slot) st else st)
          root rootSlot cnode slot := by
      split
      · rfl
      · next h1 => exact hS.1
    rw [hc1]
    generalize (if cls = 1 then finaliseFinalObject (slotRetireTarget st cnode slot) st
      else st) = st1 at hst1 ⊢
    obtain ⟨hB1, hE1⟩ := hst1
    have hSh1 : SlotsShrink st st1 := SlotsShrink.of_eq hE1
    have hSh1' : SlotsShrink st1 st := SlotsShrink.of_eq fun r => (hE1 r).symm
    have hR1 : ZombieReach root rootSlot st1 x := hR.of_shrink hSh1'
    have hn1 : SystemState.namesAt st1.slotCapAt ⟨cnode, slot⟩ x :=
      (SystemState.namesAt_of_eq (hE1 _)).2 hn
    split
    · obtain ⟨hB', h0, -⟩ := zombieDeleteSlot_slots ec cnode slot hB1
      have hSh := zombieDeleteSlot_shrink ec cnode slot hB1
      exact ⟨hB', hSh1.trans hSh,
        fun _ => zombieLive_lt_of_final_deleted hSh1 hSh hf hn h0 hR hH (hK x hH)⟩
    · next hlt =>
      have hne1 : zombieSlotClass st1 root rootSlot cnode slot ≠ 0 := by omega
      obtain ⟨x1, o1, hT1, hnx1, -, hO1, hN1, hcl1⟩ := zombieSlotClass_ne_zero hB1 hne1
      have e : x1 = x := namesAt_unique hnx1 hn1
      subst e
      rw [hT1, Nat.add_sub_cancel, objId_ofNat_val]
      rcases zombieNextSlot_spec o1 (zombieSkip root rootSlot x1) with ⟨h0, -⟩ | ⟨k, hk, hs, hkne⟩
      · exact absurd h0 hN1
      have hk2 : zombieSlotClass st1 root rootSlot cnode slot - 2 = k := by
        rw [hcl1 (by omega), hk]; omega
      rw [hk2]
      have hs1 : st1.slotCapAt ⟨x1, SeLe4n.Slot.ofNat k⟩ ≠ none := by
        unfold SystemState.slotCapAt; rw [hO1]; exact hs
      have hneR : (⟨x1, SeLe4n.Slot.ofNat k⟩ : SlotRef) ≠ ⟨root, rootSlot⟩ :=
        fun e => hkne ((zombieSkip_eq_iff root rootSlot x1 _).2 e)
      have hK1 : ∀ y, zombieHolds root rootSlot st1 y → y ∈ K :=
        fun y h => hK y (h.of_shrink hSh1)
      split
      · next hj =>
        have hneC : (⟨cnode, slot⟩ : SlotRef) ≠ ⟨x1, SeLe4n.Slot.ofNat k⟩ := by
          intro e
          apply hne1
          have h1 : cnode = x1 := congrArg SlotRef.cnode e
          have h2 : slot = SeLe4n.Slot.ofNat k := congrArg SlotRef.slot e
          rw [h1, h2]; exact hj
        obtain ⟨hB2, hEmpty2, hE2⟩ := zombieDeleteSlot_slots ec x1 (SeLe4n.Slot.ofNat k) hB1
        have hSh2 := zombieDeleteSlot_shrink ec x1 (SeLe4n.Slot.ofNat k) hB1
        generalize zombieDeleteSlot ec x1 (SeLe4n.Slot.ofNat k) st1 = st2 at hB2 hEmpty2 hE2 hSh2 ⊢
        have hSh12 := hSh1.trans hSh2
        have hnx2 : SystemState.namesAt st2.slotCapAt ⟨cnode, slot⟩ x1 :=
          (SystemState.namesAt_of_eq (hE2 _ hneC)).2 hn1
        have hkM : k < M := hM _ (hSh1.occupied hs1)
        have hOcc2 : zombieOccupied root rootSlot st2 x1 M ≤ budget := by
          have := zombieOccupied_lt hSh2 hkM hneR hs1 hEmpty2
          have := zombieOccupied_le_of_shrink (root := root) (rootSlot := rootSlot) hSh1 x1 M
          omega
        have hS2 : ZombieStand root rootSlot st2 cnode slot
            (zombieSlotClass st2 root rootSlot cnode slot) budget := by
          refine ⟨rfl, fun hc2 => ?_⟩
          obtain ⟨x2, -, hT2, hn2, -⟩ := zombieSlotClass_ne_zero hB2 hc2
          have e : x2 = x1 := namesAt_unique hn2 hnx2
          subst e
          exact ⟨x2, hT2, zombieReach_of_own_deleted hneR hE2 hR1, M,
            fun i hi => hM i (hSh12.occupied hi), hOcc2⟩
        obtain ⟨hBr, hShr, hlt2⟩ := zombieDescend_live ec root rootSlot K (depth + 1) budget
          cnode slot _ st2 hB2 (fun y h => hK y (h.of_shrink hSh12)) hS2
        refine ⟨hBr, hSh12.trans hShr, fun _ => ?_⟩
        by_cases hc2 : zombieSlotClass st2 root rootSlot cnode slot = 0
        · have hL := zombieLive_lt (K := K) hSh12 (hK x1 hH) hR hH
            (fun h => zombieSlotClass_ne_zero_of hB2 hnx2 (hSh12.capFinal hf) h.2 hc2)
          have := zombieLive_le (root := root) (rootSlot := rootSlot) (K := K) hShr
          omega
        · have := hlt2 hc2
          have := zombieLive_le (root := root) (rootSlot := rootSlot) (K := K) hSh12
          omega
      · next hj =>
        obtain ⟨y, o2, hT2, hn2, -⟩ := zombieSlotClass_ne_zero hB1 hj
        rw [hT2, Nat.add_sub_cancel, objId_ofNat_val]
        obtain ⟨hBr, hShr, hlt2⟩ := zombieDescend_live ec root rootSlot K depth
          (zombieObjectSlots st1 y) x1 (SeLe4n.Slot.ofNat k) _ st1 hB1 hK1
          ⟨rfl, fun _ => ⟨y, hT2, .through _ hR1 hneR hn2, _, zombieObjectSlots_bound st1 y,
            zombieOccupied_le _ _ _ _ _⟩⟩
        refine ⟨hBr, hSh1.trans hShr, fun _ => ?_⟩
        have := hlt2 hj
        have := zombieLive_le (root := root) (rootSlot := rootSlot) (K := K) hSh1
        omega
  termination_by depth budget => (depth, budget)

-- ============================================================================
-- §10  The passes end within the fuel
-- ============================================================================

/-- **Passes beyond the measure end the loop**: with more passes than the
measure counts, they end with the loop's slot of class `0`, naming nothing that
holds a capability, slots only emptied and the capability invariants kept. -/
theorem zombiePasses_live (ec : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) (K : List SeLe4n.ObjId) :
    ∀ (n : Nat) (st : SystemState), capabilityInvariantBundle st →
      (∀ y, zombieHolds root rootSlot st y → y ∈ K) → zombieLive root rootSlot K st < n →
      capabilityInvariantBundle (zombiePasses ec root rootSlot n st) ∧
        SlotsShrink st (zombiePasses ec root rootSlot n st) ∧
        zombieSlotClass (zombiePasses ec root rootSlot n st) root rootSlot root rootSlot = 0
  | 0, _, _, _, h => absurd h (Nat.not_lt_zero _)
  | n + 1, st, hB, hK, hL => by
    rw [zombiePasses]
    by_cases hc : zombieSlotClass st root rootSlot root rootSlot = 0
    · rw [if_pos hc]; exact ⟨hB, .refl st, hc⟩
    rw [if_neg hc]
    have hS : ZombieStand root rootSlot st root rootSlot
        (zombieSlotClass st root rootSlot root rootSlot)
        (zombieObjectSlots st (SeLe4n.ObjId.ofNat (slotRetireTarget st root rootSlot - 1))) := by
      refine ⟨rfl, fun _ => ?_⟩
      obtain ⟨x, o, hT, hn, -⟩ := zombieSlotClass_ne_zero hB hc
      rw [hT, Nat.add_sub_cancel, objId_ofNat_val]
      exact ⟨x, rfl, .named hn, _, zombieObjectSlots_bound st x, zombieOccupied_le _ _ _ _ _⟩
    obtain ⟨hB1, hSh1, hlt⟩ := zombieDescend_live ec root rootSlot K (zombieDepth st) _ root
      rootSlot _ st hB hK hS
    obtain ⟨hB2, hSh2, h0⟩ := zombiePasses_live ec root rootSlot K n _ hB1
      (fun y h => hK y (h.of_shrink hSh1)) (by have := hlt hc; omega)
    exact ⟨hB2, hSh1.trans hSh2, h0⟩

/-- **The zombie fuel always suffices** (`zombieFuel`, one more than the store
holds): on every state the capability invariants hold in, the passes the zombie
delete gives the slot end with it naming nothing that holds a capability, so
the slot's own delete then retires a leaf. -/
theorem zombiePasses_end (ec : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) {st : SystemState} (hB : capabilityInvariantBundle st) :
    capabilityInvariantBundle (zombiePasses ec root rootSlot (zombieFuel st) st) ∧
      SlotsShrink st (zombiePasses ec root rootSlot (zombieFuel st) st) ∧
      zombieSlotClass (zombiePasses ec root rootSlot (zombieFuel st) st)
        root rootSlot root rootSlot = 0 := by
  refine zombiePasses_live ec root rootSlot (objectKeys st) _ st hB
    (fun _ h => mem_objectKeys_of_holds h) ?_
  have h1 := zombieLive_le_length root rootSlot (objectKeys st) st
  rw [objectKeys_length hB.2.2.2.2.1] at h1
  unfold zombieFuel
  omega

-- ============================================================================
-- §11  The way down's bound never binds
-- ============================================================================

/-- A list without repeats inside another is no longer than it. -/
theorem nodup_length_le {α : Type} [DecidableEq α] :
    ∀ {l k : List α}, l.Nodup → (∀ a ∈ l, a ∈ k) → l.length ≤ k.length
  | [], _, _, _ => Nat.zero_le _
  | a :: l, k, hn, hs => by
    obtain ⟨ha, hl⟩ := List.nodup_cons.1 hn
    have hk : a ∈ k := hs a List.mem_cons_self
    have := nodup_length_le (k := k.erase a) hl fun b hb =>
      (List.mem_erase_of_ne (fun (e : b = a) => ha (e ▸ hb))).2 (hs b (List.mem_cons_of_mem a hb))
    rw [List.length_erase_of_mem hk] at this
    have := List.length_pos_of_mem hk
    simp only [List.length_cons]; omega

/-- **The way a pass has come down**: the objects it went down to, the one it
stands on (`x`) first, each once and each under a key; the slot it stands on
names `x` while its class is not `0`; and each of them is named by the loop's
own slot or by a slot of an object it went down to before `x`.  The last clause
is what keeps an object from being visited twice: the slot that names it is
final, so it is the one the pass came down through. -/
def ZombiePath (root : SeLe4n.ObjId) (rootSlot : SeLe4n.Slot) (K : List SeLe4n.ObjId)
    (st : SystemState) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (cls : Nat)
    (x : SeLe4n.ObjId) (rest : List SeLe4n.ObjId) : Prop :=
  (x :: rest).Nodup ∧ (∀ o ∈ x :: rest, o ∈ K) ∧
    (cls ≠ 0 → SystemState.namesAt st.slotCapAt ⟨cnode, slot⟩ x) ∧
    ∀ o ∈ x :: rest, ∃ w : SlotRef, SystemState.namesAt st.slotCapAt w o ∧
      (w = ⟨root, rootSlot⟩ ∨ w.cnode ∈ rest)

/-- **Emptying a slot of the object a pass stands on keeps the way it came
down**: no slot it came down through is one of that object's. -/
theorem zombiePath_witness_keep {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot}
    {s t : SystemState} {x : SeLe4n.ObjId} {rest : List SeLe4n.ObjId} {d : SlotRef}
    (hd : d ≠ ⟨root, rootSlot⟩) (hdx : d.cnode = x) (hx : x ∉ rest)
    (hS : ∀ r, r ≠ d → t.slotCapAt r = s.slotCapAt r)
    (hW : ∀ o ∈ x :: rest, ∃ w : SlotRef, SystemState.namesAt s.slotCapAt w o ∧
      (w = ⟨root, rootSlot⟩ ∨ w.cnode ∈ rest)) :
    ∀ o ∈ x :: rest, ∃ w : SlotRef, SystemState.namesAt t.slotCapAt w o ∧
      (w = ⟨root, rootSlot⟩ ∨ w.cnode ∈ rest) := by
  intro o ho
  obtain ⟨w, hw, hwc⟩ := hW o ho
  have hne : w ≠ d := by
    intro e
    subst e
    rcases hwc with h | h
    · exact hd h
    · exact hx (hdx ▸ h)
  exact ⟨w, (SystemState.namesAt_of_eq (hS w hne)).2 hw, hwc⟩

/-- **An object a final slot of the object a pass stands on names is not one it
came down through.** -/
theorem zombiePath_fresh {root : SeLe4n.ObjId} {rootSlot : SeLe4n.Slot} {s : SystemState}
    {x y : SeLe4n.ObjId} {rest : List SeLe4n.ObjId} {k : SeLe4n.Slot}
    (hn : SystemState.namesAt s.slotCapAt ⟨x, k⟩ y) (hf : s.capFinalSpec ⟨x, k⟩)
    (hneR : (⟨x, k⟩ : SlotRef) ≠ ⟨root, rootSlot⟩) (hx : x ∉ rest)
    (hW : ∀ o ∈ x :: rest, ∃ w : SlotRef, SystemState.namesAt s.slotCapAt w o ∧
      (w = ⟨root, rootSlot⟩ ∨ w.cnode ∈ rest)) : y ∉ x :: rest := by
  intro hy
  obtain ⟨w, hw, hwc⟩ := hW y hy
  by_cases e : w = ⟨x, k⟩
  · subst e
    rcases hwc with h | h
    · exact hneR h
    · exact hx h
  · exact hf y hn w e hw

/-- **A pass ends the same with any deeper bound**: from a way down that has
visited no object twice, the pass never reaches the bound, since each object it
goes down to is named by a final slot and so is not one it came through, and
the store holds fewer objects than the bound leaves room for. -/
theorem zombieDescend_depth_free (ec : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) (K : List SeLe4n.ObjId) :
    ∀ (depth budget : Nat) (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot) (cls : Nat)
      (st : SystemState) (x : SeLe4n.ObjId) (rest : List SeLe4n.ObjId) (m : Nat),
      capabilityInvariantBundle st → (∀ y, zombieHolds root rootSlot st y → y ∈ K) →
      depth + rest.length = K.length + 1 → cls = zombieSlotClass st root rootSlot cnode slot →
      ZombiePath root rootSlot K st cnode slot cls x rest →
      zombieDescend ec root rootSlot depth budget cnode slot cls st =
        zombieDescend ec root rootSlot (depth + m) budget cnode slot cls st
  | 0, _, _, _, _, _, x, rest, _, _, _, hLen, _, hP => by
    have := nodup_length_le hP.1 hP.2.1
    simp only [List.length_cons] at this
    omega
  | depth + 1, 0, cnode, slot, cls, st, _, _, m, _, _, _, _, _ => by
    rw [show depth + 1 + m = (depth + m) + 1 by omega, zombieDescend, zombieDescend]
  | depth + 1, budget + 1, cnode, slot, cls, st, x, rest, m, hB, hK, hLen, hcls, hP => by
    rw [show depth + 1 + m = (depth + m) + 1 by omega, zombieDescend, zombieDescend]
    dsimp only
    by_cases hc : cls = 0
    · rw [if_pos hc, if_pos hc]
    rw [if_neg hc, if_neg hc]
    obtain ⟨hNd, hKs, hCur, hW⟩ := hP
    have hnx := hCur hc
    have hx : x ∉ rest := (List.nodup_cons.1 hNd).1
    have hst1 : capabilityInvariantBundle
          (if cls = 1 then finaliseFinalObject (slotRetireTarget st cnode slot) st else st) ∧
        ∀ r, (if cls = 1 then finaliseFinalObject (slotRetireTarget st cnode slot) st
          else st).slotCapAt r = st.slotCapAt r := by
      split
      · exact finaliseFinalObject_slots _ hB
      · exact ⟨hB, fun _ => rfl⟩
    have hc1 : (if cls = 1 then zombieSlotClass
          (if cls = 1 then finaliseFinalObject (slotRetireTarget st cnode slot) st else st)
          root rootSlot cnode slot else cls) =
        zombieSlotClass
          (if cls = 1 then finaliseFinalObject (slotRetireTarget st cnode slot) st else st)
          root rootSlot cnode slot := by
      split
      · rfl
      · exact hcls
    rw [hc1]
    generalize (if cls = 1 then finaliseFinalObject (slotRetireTarget st cnode slot) st
      else st) = st1 at hst1 ⊢
    obtain ⟨hB1, hE1⟩ := hst1
    have hSh1 : SlotsShrink st st1 := SlotsShrink.of_eq hE1
    have hn1 : SystemState.namesAt st1.slotCapAt ⟨cnode, slot⟩ x :=
      (SystemState.namesAt_of_eq (hE1 _)).2 hnx
    have hW1 : ∀ o ∈ x :: rest, ∃ w : SlotRef, SystemState.namesAt st1.slotCapAt w o ∧
        (w = ⟨root, rootSlot⟩ ∨ w.cnode ∈ rest) := fun o ho =>
      let ⟨w, hw, hwc⟩ := hW o ho; ⟨w, (SystemState.namesAt_of_eq (hE1 _)).2 hw, hwc⟩
    by_cases hlt : zombieSlotClass st1 root rootSlot cnode slot < 2
    · rw [if_pos hlt, if_pos hlt]
    rw [if_neg hlt, if_neg hlt]
    have hne1 : zombieSlotClass st1 root rootSlot cnode slot ≠ 0 := by omega
    obtain ⟨x1, o1, hT1, hnx1, -, hO1, hN1, hcl1⟩ := zombieSlotClass_ne_zero hB1 hne1
    have e : x1 = x := namesAt_unique hnx1 hn1
    subst e
    rw [hT1, Nat.add_sub_cancel, objId_ofNat_val]
    rcases zombieNextSlot_spec o1 (zombieSkip root rootSlot x1) with ⟨h0, -⟩ | ⟨k, hk, -, hkne⟩
    · exact absurd h0 hN1
    have hk2 : zombieSlotClass st1 root rootSlot cnode slot - 2 = k := by
      rw [hcl1 (by omega), hk]; omega
    rw [hk2]
    have hneR : (⟨x1, SeLe4n.Slot.ofNat k⟩ : SlotRef) ≠ ⟨root, rootSlot⟩ :=
      fun e => hkne ((zombieSkip_eq_iff root rootSlot x1 _).2 e)
    have hK1 : ∀ y, zombieHolds root rootSlot st1 y → y ∈ K :=
      fun y h => hK y (h.of_shrink hSh1)
    by_cases hj : zombieSlotClass st1 root rootSlot x1 (SeLe4n.Slot.ofNat k) = 0
    · rw [if_pos hj, if_pos hj]
      have hneC : (⟨cnode, slot⟩ : SlotRef) ≠ ⟨x1, SeLe4n.Slot.ofNat k⟩ := by
        intro e
        apply hne1
        have h1 : cnode = x1 := congrArg SlotRef.cnode e
        have h2 : slot = SeLe4n.Slot.ofNat k := congrArg SlotRef.slot e
        rw [h1, h2]; exact hj
      obtain ⟨hB2, -, hE2⟩ := zombieDeleteSlot_slots ec x1 (SeLe4n.Slot.ofNat k) hB1
      have hSh2 := zombieDeleteSlot_shrink ec x1 (SeLe4n.Slot.ofNat k) hB1
      generalize zombieDeleteSlot ec x1 (SeLe4n.Slot.ofNat k) st1 = st2 at hB2 hE2 hSh2 ⊢
      have hP2 : ZombiePath root rootSlot K st2 cnode slot
          (zombieSlotClass st2 root rootSlot cnode slot) x1 rest :=
        ⟨hNd, hKs, fun _ => (SystemState.namesAt_of_eq (hE2 _ hneC)).2 hn1,
          zombiePath_witness_keep hneR rfl hx hE2 hW1⟩
      have := zombieDescend_depth_free ec root rootSlot K (depth + 1) budget cnode slot _ st2
        x1 rest m hB2 (fun y h => hK1 y (h.of_shrink hSh2)) hLen rfl hP2
      rwa [show depth + 1 + m = depth + m + 1 by omega] at this
    · rw [if_neg hj, if_neg hj]
      obtain ⟨y, o2, hT2, hn2, hf2, hO2, hN2, -⟩ := zombieSlotClass_ne_zero hB1 hj
      rw [hT2, Nat.add_sub_cancel, objId_ofNat_val]
      have hH2 : zombieHolds root rootSlot st1 y :=
        (zombieHolds_iff root rootSlot st1 y).2 ⟨o2, hO2, hN2⟩
      have hy := zombiePath_fresh hn2 hf2 hneR hx hW1
      refine zombieDescend_depth_free ec root rootSlot K depth _ x1 (SeLe4n.Slot.ofNat k) _ st1
        y (x1 :: rest) m hB1 hK1 (by simp only [List.length_cons]; omega) rfl
        ⟨List.nodup_cons.2 ⟨hy, hNd⟩, ?_, fun _ => hn2, ?_⟩
      · intro o ho
        rcases List.mem_cons.1 ho with rfl | ho
        · exact hK1 _ hH2
        · exact hKs o ho
      · intro o ho
        rcases List.mem_cons.1 ho with rfl | ho
        · exact ⟨_, hn2, .inr List.mem_cons_self⟩
        · obtain ⟨w, hw, hwc⟩ := hW1 o ho
          exact ⟨w, hw, hwc.imp id (List.mem_cons_of_mem _)⟩
  termination_by depth budget => (depth, budget)

/-- **The way down's bound never binds** (`zombieDepth`): a pass from the
loop's own slot ends the same with any deeper bound, so it never reaches the
bound, and the delete the bound's branch makes of a slot whose object still
holds capabilities never runs on a state the capability invariants hold in. -/
theorem zombieDescend_depth_never_binds (ec : Concurrency.CoreId) (root : SeLe4n.ObjId)
    (rootSlot : SeLe4n.Slot) {st : SystemState} (hB : capabilityInvariantBundle st)
    (budget m : Nat) :
    zombieDescend ec root rootSlot (zombieDepth st) budget root rootSlot
        (zombieSlotClass st root rootSlot root rootSlot) st =
      zombieDescend ec root rootSlot (zombieDepth st + m) budget root rootSlot
        (zombieSlotClass st root rootSlot root rootSlot) st := by
  by_cases hc : zombieSlotClass st root rootSlot root rootSlot = 0
  · rw [hc]
    unfold zombieDepth
    rw [show st.objects.size + 1 + m = (st.objects.size + m) + 1 by omega]
    cases budget with
    | zero => rw [zombieDescend, zombieDescend]
    | succ b => rw [zombieDescend, zombieDescend]; simp
  obtain ⟨x, o, -, hn, -, hO, hN, -⟩ := zombieSlotClass_ne_zero hB hc
  have hH : zombieHolds root rootSlot st x := (zombieHolds_iff root rootSlot st x).2 ⟨o, hO, hN⟩
  refine zombieDescend_depth_free ec root rootSlot (objectKeys st) _ budget root rootSlot _ st
    x [] m hB (fun _ h => mem_objectKeys_of_holds h) ?_ rfl
    ⟨List.nodup_cons.2 ⟨List.not_mem_nil, List.nodup_nil⟩, ?_, fun _ => hn, ?_⟩
  · rw [objectKeys_length hB.2.2.2.2.1]; rfl
  · intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · exact mem_objectKeys_of_holds hH
    · exact absurd ho List.not_mem_nil
  · intro o ho
    rcases List.mem_cons.1 ho with rfl | ho
    · exact ⟨_, hn, .inl rfl⟩
    · exact absurd ho List.not_mem_nil

end SeLe4n.Kernel
