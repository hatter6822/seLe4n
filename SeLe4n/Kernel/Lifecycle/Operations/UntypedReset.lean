-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations

/-!
# The untyped reset — seL4's `resetUntypedCap`

An untyped's free index is its capability's (`Capability.freeIndex`, seL4's
`capFreeIndex`), and a carve advances it.  The reset hands the untyped's memory
back by rewinding that index to 0, as seL4's `resetUntypedCap` does once
`decodeUntypedInvocation`'s `ensureNoChildren` has found the invoked slot with no
derivation child.  It is O(1): it reads the invoked slot's first-child link word,
its capability and the untyped that capability names, and writes one word.

## Why a slot with no child may rewind

Every capability to an object carved from the untyped lies strictly below every
capability to the untyped (`TreeShapeOver.carvedBelow`), so once the invoked slot
has no child no slot names anything carved from it.  Every other capability to
the untyped lies on one descent with it (`chainLinear`), so above it, and one
with a capability to the untyped below it is full (`notFullLeaf`): the rewound
capability is the only one that can carve (the sole-carver conjunct of
`untypedResetSlot_preserves_untypedMemoryInvariant`).

## What is decided rather than assumed

An object outlives its last capability only where its final delete could not
retire it (`retireFinalObject`: a passive object still named outside a slot, or an
object table without headroom for the erase).  Such an object is still recorded on
its untyped's child list, so the reset also reads that list and refuses while it
records any child (`.revocationRequired`): a carve at index 0 must not be handed
memory a live object holds.  With the list empty nothing is carved from the
untyped (`untypedResetSlot_ok_uncarved`), and the untyped invariants hold with
the index at 0 (`untypedResetSlot_preserves_untypedMemoryInvariant`).

## What it does not do

It erases nothing, unmaps nothing and zeroes nothing.  Every object carved from
the untyped left the store with its last capability, its mappings removed and its
ASID released by its finalisation (`retireRecordedObject`); and a carve zeroes
every RAM page before any capability to it exists (`carveZeroFrame`), so memory is
scrubbed when it is handed out, which is when seL4's reset-time clear is first
observable.

## What it refuses

* an invoked slot with a derivation child (`.revocationRequired`) — revoke the
  capability (`.cspaceRevoke`), which deletes every capability derived from it;
* a capability that names no untyped (`.untypedTypeMismatch`), or an empty slot
  or one naming no object (`.invalidCapability`);
* an untyped whose child list records a carved object (`.revocationRequired`).

Every refusal precedes the one write (`untypedResetAdmittedAt`,
`untypedResetSlot_of_admitted`), so the live arm runs through
`RefusalCarrying.ofChecked` and keeps no copy of the state it was handed.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The reset's checks**, read before anything is written: the invoked slot has
no derivation child (`hasCdtChildren`, seL4's `ensureNoChildren`), it holds a
capability to an untyped, and that untyped records no carved child.  The slot is
passed as its two words, so no slot reference is built. -/
@[inline] def untypedResetAdmittedAt (st : SystemState) (srcCnode : SeLe4n.ObjId)
    (srcSlot : SeLe4n.Slot) : Bool :=
  !hasCdtChildren st { cnode := srcCnode, slot := srcSlot } &&
  match SystemState.lookupSlotCap st { cnode := srcCnode, slot := srcSlot } with
  | some cap =>
    match cap.target with
    | .object untypedId =>
      match st.getUntyped? untypedId with
      | some ut => ut.children.isEmpty
      | none => false
    | _ => false
  | none => false

/-- **The reset's write**: the invoked capability's free index rewound to 0, in
place (`setCapFreeIndex`). -/
@[inline] def untypedResetPerformAt (srcCnode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot)
    (st : SystemState) : SystemState :=
  setCapFreeIndex st { cnode := srcCnode, slot := srcSlot } 0

/-- **The untyped reset, invoked through the slot `srcCnode`/`srcSlot`** — seL4's
`resetUntypedCap` behind `ensureNoChildren`.  The refusals the module docstring
lists, in that order, then the rewind. -/
def untypedResetSlot (srcCnode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) : Kernel Unit :=
  fun st =>
    if hasCdtChildren st { cnode := srcCnode, slot := srcSlot } then .error .revocationRequired
    else
      match SystemState.lookupSlotCap st { cnode := srcCnode, slot := srcSlot } with
      | none => .error .invalidCapability
      | some cap =>
        match cap.target with
        | .object untypedId =>
          match st.getUntyped? untypedId with
          | none => .error .untypedTypeMismatch
          | some ut =>
            if ut.children.isEmpty then
              .ok ((), setCapFreeIndex st { cnode := srcCnode, slot := srcSlot } 0)
            else .error .revocationRequired
        | _ => .error .invalidCapability

/-- **An admitted reset is its write.** -/
theorem untypedResetSlot_of_admitted {st : SystemState} {srcCnode : SeLe4n.ObjId}
    {srcSlot : SeLe4n.Slot} (h : untypedResetAdmittedAt st srcCnode srcSlot = true) :
    untypedResetSlot srcCnode srcSlot st = .ok ((), untypedResetPerformAt srcCnode srcSlot st) := by
  unfold untypedResetAdmittedAt at h
  unfold untypedResetSlot untypedResetPerformAt
  revert h
  cases hasCdtChildren st { cnode := srcCnode, slot := srcSlot } with
  | true => simp
  | false =>
    simp only [Bool.not_false, Bool.true_and, Bool.false_eq_true, ↓reduceIte]
    cases SystemState.lookupSlotCap st { cnode := srcCnode, slot := srcSlot } with
    | none => simp
    | some cap =>
      simp only
      cases cap.target with
      | object u =>
        simp only
        cases st.getUntyped? u with
        | none => simp
        | some ut => simp only; intro hE; rw [if_pos hE]
      | _ => simp

/-- **What a successful reset consists of**: the invoked slot has no derivation
child and holds a capability to an untyped that records no child, and the
post-state is the pre-state with that capability's free index rewound to 0. -/
theorem untypedResetSlot_ok {st st' : SystemState} {srcCnode : SeLe4n.ObjId}
    {srcSlot : SeLe4n.Slot} (h : untypedResetSlot srcCnode srcSlot st = .ok ((), st')) :
    ∃ (cap : Capability) (untypedId : SeLe4n.ObjId) (ut : UntypedObject),
      hasCdtChildren st { cnode := srcCnode, slot := srcSlot } = false ∧
      SystemState.lookupSlotCap st { cnode := srcCnode, slot := srcSlot } = some cap ∧
      cap.target = .object untypedId ∧ st.getUntyped? untypedId = some ut ∧
      ut.children = [] ∧ st' = setCapFreeIndex st { cnode := srcCnode, slot := srcSlot } 0 := by
  unfold untypedResetSlot at h
  cases hC : hasCdtChildren st { cnode := srcCnode, slot := srcSlot } with
  | true => rw [hC] at h; cases h
  | false =>
    rw [hC] at h
    simp only [Bool.false_eq_true, ↓reduceIte] at h
    cases hL : SystemState.lookupSlotCap st { cnode := srcCnode, slot := srcSlot } with
    | none => rw [hL] at h; cases h
    | some cap =>
      rw [hL] at h
      simp only at h
      cases hT : cap.target with
      | object u =>
        rw [hT] at h
        simp only at h
        cases hU : st.getUntyped? u with
        | none => rw [hU] at h; cases h
        | some ut =>
          rw [hU] at h
          simp only at h
          by_cases hE : ut.children.isEmpty = true
          · rw [if_pos hE] at h
            simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
            exact ⟨cap, u, ut, rfl, rfl, hT, hU, List.isEmpty_iff.mp hE, h.symm⟩
          · rw [if_neg hE] at h; cases h
      | _ => rw [hT] at h; cases h

/-- **The rewound capability**: on a well-formed object table, the invoked slot
holds its capability with free index 0 after a successful reset. -/
theorem untypedResetSlot_ok_freeIndex {st st' : SystemState} {srcCnode : SeLe4n.ObjId}
    {srcSlot : SeLe4n.Slot} (hObjInv : st.objects.invExt)
    (h : untypedResetSlot srcCnode srcSlot st = .ok ((), st')) :
    ∃ cap, SystemState.lookupSlotCap st { cnode := srcCnode, slot := srcSlot } = some cap ∧
      SystemState.lookupSlotCap st' { cnode := srcCnode, slot := srcSlot } =
        some (cap.withFreeIndex 0) := by
  obtain ⟨cap, -, -, -, hL, -, -, -, rfl⟩ := untypedResetSlot_ok h
  obtain ⟨cn, hO, hLk⟩ := SystemState.lookupSlotCap_cnode hL
  refine ⟨cap, hL, ?_⟩
  unfold SystemState.lookupSlotCap SystemState.lookupCNode
  rw [setCapFreeIndex_objects_self hObjInv hO, CNode.setFreeIndex_of_lookup hLk]
  exact CNode.lookup_insert_eq cn srcSlot (cap.withFreeIndex 0) (CNode.slotsUnique_holds cn)
    (CNode.slotAddressable_of_lookup cn srcSlot cap hLk)

/-- **Nothing carved remains**: after a successful reset the untyped the invoked
capability names records no child, so no object is carved from it
(`SystemState.CarvedFrom` reads the child lists). -/
theorem untypedResetSlot_ok_uncarved {st st' : SystemState} {srcCnode : SeLe4n.ObjId}
    {srcSlot : SeLe4n.Slot} (hObjInv : st.objects.invExt)
    (h : untypedResetSlot srcCnode srcSlot st = .ok ((), st')) :
    ∃ (cap : Capability) (untypedId : SeLe4n.ObjId) (ut : UntypedObject),
      SystemState.lookupSlotCap st { cnode := srcCnode, slot := srcSlot } = some cap ∧
      cap.target = .object untypedId ∧ st'.getUntyped? untypedId = some ut ∧
      ut.children = [] := by
  obtain ⟨cap, u, ut, -, hL, hT, hU, hE, rfl⟩ := untypedResetSlot_ok h
  obtain ⟨cn, hO, -⟩ := SystemState.lookupSlotCap_cnode hL
  refine ⟨cap, u, ut, hL, hT, ?_, hE⟩
  have hNe : u ≠ srcCnode := by
    intro e; subst e
    have := (SystemState.getUntyped?_eq_some_iff st u ut).mp hU
    rw [hO] at this; cases this
  rw [← hU]
  unfold SystemState.getUntyped?
  rw [setCapFreeIndex_objects_ne hObjInv hNe]

/-- **The reset's frame**: it writes the invoked slot's CNode alone, and keeps the
scheduler, the machine and every other field of the state. -/
theorem untypedResetSlot_ok_frame {st st' : SystemState} {srcCnode : SeLe4n.ObjId}
    {srcSlot : SeLe4n.Slot} (h : untypedResetSlot srcCnode srcSlot st = .ok ((), st')) :
    st' = setCapFreeIndex st { cnode := srcCnode, slot := srcSlot } 0 := by
  obtain ⟨-, -, -, -, -, -, -, -, h'⟩ := untypedResetSlot_ok h
  exact h'

end SeLe4n.Kernel
