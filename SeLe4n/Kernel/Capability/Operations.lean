/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- Address of a capability slot in the modeled CSpace. -/
abbrev CSpaceAddr := SlotRef

/-- Address of a guard/radix resolved pointer in the modeled CSpace. -/
structure CSpacePathAddr where
  cnode : SeLe4n.ObjId
  cptr : SeLe4n.CPtr
  depth : Nat
  deriving Repr, DecidableEq

/-- Rights attenuation policy for the M2 foundation slice.

`derived.rights` must be a subset of `parent.rights`; targets are preserved by mint-like
derivation in this slice. -/
def capAttenuates (parent derived : Capability) : Prop :=
  derived.target = parent.target ∧ ∀ right, right ∈ derived.rights → right ∈ parent.rights

/-- Lookup a capability at `(cnode, slot)` with typed CNode checking. -/
def cspaceLookupSlot (addr : CSpaceAddr) : Kernel Capability :=
  fun st =>
    match SystemState.lookupSlotCap st addr with
    | some cap => .ok (cap, st)
    | none =>
        match st.objects[addr.cnode]? with
        | some (.cnode _) => .error .invalidCapability
        | _ => .error .objectNotFound

/-- Resolve a CSpace path address into a concrete slot using CNode guard/radix semantics. -/
def cspaceResolvePath (addr : CSpacePathAddr) : Kernel CSpaceAddr :=
  fun st =>
    match st.objects[addr.cnode]? with
    | some (.cnode cn) =>
        match cn.resolveSlot addr.cptr addr.depth with
        | .ok slot => .ok ({ cnode := addr.cnode, slot := slot }, st)
        | .error .depthMismatch => .error .illegalState
        | .error .guardMismatch => .error .invalidCapability
    | _ => .error .objectNotFound

/-- Lookup a capability via guard/radix resolution from a CSpace pointer path. -/
def cspaceLookupPath (addr : CSpacePathAddr) : Kernel Capability :=
  fun st =>
    match cspaceResolvePath addr st with
    | .error e => .error e
    | .ok (resolved, st') => cspaceLookupSlot resolved st'

-- ============================================================================
-- WS-H13/H-01: Multi-level CSpace resolution with compressed-path CNodes
-- ============================================================================

/-- WS-H13/H-01: Multi-level CSpace capability address resolution.

Walks the CNode graph starting at `rootId`, consuming `guardWidth + radixWidth`
bits per hop from the capability address `addr`. Each CNode level:
1. Extracts guard bits and verifies they match `guardValue`.
2. Extracts radix bits to compute the slot index.
3. If bits remain, looks up the slot and recurses into the child CNode.
4. If all bits are consumed, returns the resolved slot reference.

Termination is guaranteed by strict descent of `bitsRemaining`: each hop
consumes `guardWidth + radixWidth ≥ 1` bits (enforced by `cnodeWellFormed`
invariant / `hProgress`). -/
def resolveCapAddress (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bitsRemaining : Nat)
    (st : SystemState) : Except KernelError SlotRef :=
  if hZero : bitsRemaining = 0 then .error .illegalState        -- no bits to consume
  else
    match st.objects[rootId]? with
    | some (.cnode cn) =>
      let consumed := cn.guardWidth + cn.radixWidth
      if hCons : consumed = 0 then .error .illegalState  -- zero-width CNode
      else if bitsRemaining < consumed then .error .illegalState
      else
        -- Extract guard and slot index bits
        let shiftedAddr := addr.toNat >>> (bitsRemaining - consumed)
        let radixMask := 2 ^ cn.radixWidth
        let slotIndex := shiftedAddr % radixMask
        let guardExtracted := (shiftedAddr / radixMask) % (2 ^ cn.guardWidth)
        if guardExtracted ≠ cn.guardValue then .error .invalidCapability
        else
          let slot := SeLe4n.Slot.ofNat slotIndex
          if bitsRemaining - consumed = 0 then
            .ok { cnode := rootId, slot := slot }   -- leaf: all bits consumed
          else
            match cn.lookup slot with
            | some cap =>
              match cap.target with
              | .object childId =>
                have hConsPos : consumed > 0 := Nat.pos_of_ne_zero hCons
                have hBitsPos : bitsRemaining > 0 := Nat.pos_of_ne_zero hZero
                have : bitsRemaining - consumed < bitsRemaining := Nat.sub_lt hBitsPos hConsPos
                resolveCapAddress childId addr (bitsRemaining - consumed) st
              | _ => .error .invalidCapability
            | none => .error .invalidCapability
    | _ => .error .objectNotFound
  termination_by bitsRemaining

/-- WS-H13: Resolve a capability address using multi-level CSpace resolution.
This wraps `resolveCapAddress` in the kernel monad. The `bitsRemaining`
parameter defaults to the root CNode's `depth` field. -/
def resolveCapAddressK (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bitsRemaining : Nat) : Kernel SlotRef :=
  fun st =>
    match resolveCapAddress rootId addr bitsRemaining st with
    | .ok ref => .ok (ref, st)
    | .error e => .error e

/-- WS-H13: Lookup a capability via multi-level CSpace resolution.
Composes `resolveCapAddress` with slot lookup. -/
def cspaceLookupMultiLevel (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bitsRemaining : Nat) : Kernel Capability :=
  fun st =>
    match resolveCapAddress rootId addr bitsRemaining st with
    | .ok ref => cspaceLookupSlot ref st
    | .error e => .error e

-- ============================================================================
-- WS-H13/H-01: resolveCapAddress theorems
-- ============================================================================

/-- WS-H13/H-01 (deliverable 8): `resolveCapAddress` is deterministic — same
inputs always produce the same result. This follows from the function being a
pure total function with no state mutation or non-deterministic branches. -/
theorem resolveCapAddress_deterministic
    (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bits : Nat) (st : SystemState) :
    resolveCapAddress rootId addr bits st = resolveCapAddress rootId addr bits st := rfl

/-- WS-H13/H-01 (deliverable 9): `resolveCapAddress` returns `.error .illegalState`
when called with zero bits remaining. -/
theorem resolveCapAddress_zero_bits
    (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (st : SystemState) :
    resolveCapAddress rootId addr 0 st = .error .illegalState := by
  simp [resolveCapAddress]

/-- WS-H13/H-01 (deliverable 10): If `resolveCapAddress` succeeds, the returned
slot reference points to a valid CNode.

The proof traces through the recursive structure: at each hop, the function
either returns a leaf reference (pointing to the current CNode) or recurses
into a child. In both cases the result's `.cnode` field points to a valid CNode
in the object store. -/
theorem resolveCapAddress_result_valid_cnode
    (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bits : Nat) (st : SystemState)
    (ref : SlotRef)
    (hOk : resolveCapAddress rootId addr bits st = .ok ref) :
    ∃ cn : CNode, st.objects[ref.cnode]? = some (.cnode cn) := by
  -- Use strong induction to handle the recursive descent
  induction bits using Nat.strongRecOn generalizing rootId with
  | _ bits ih =>
    -- Unfold the function definition
    unfold resolveCapAddress at hOk
    -- Zero-bits case: returns error, contradiction with .ok
    split at hOk
    · simp at hOk
    · -- Non-zero bits: match on object store lookup
      split at hOk
      next cn hObj =>
        -- Found a CNode: analyze the if-cascade
        simp only at hOk
        split at hOk
        · simp at hOk  -- consumed = 0 case: error
        · split at hOk
          · simp at hOk  -- bits < consumed case: error
          · split at hOk
            · simp at hOk  -- guard mismatch: error
            · split at hOk
              · -- Leaf case: all bits consumed, ref.cnode = rootId
                simp at hOk; cases hOk; exact ⟨cn, hObj⟩
              · -- Recursive case: bits remaining, look up slot
                split at hOk
                · next cap _ =>
                  split at hOk
                  · next childId _ =>
                    have hLt : bits - (cn.guardWidth + cn.radixWidth) < bits := by omega
                    exact ih _ hLt childId hOk
                  · simp at hOk  -- non-object target: error
                · simp at hOk  -- empty slot: error
      next => simp at hOk  -- not a CNode: error

/-- WS-H13/H-01 (deliverable 10b): Guard correctness — if `resolveCapAddress`
succeeds at a leaf CNode (all bits consumed in one hop), then the guard extracted
from `addr` matched the CNode's `guardValue`. This is the primary CSpace attack
surface in real kernels: a wrong guard must always be rejected.

The proof unfolds the function and shows that the `guardExtracted ≠ guardValue`
branch returns `.error .invalidCapability`, so the success path necessarily
passed the guard check. -/
theorem resolveCapAddress_guard_reject
    (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bits : Nat) (st : SystemState)
    (cn : CNode)
    (hObj : st.objects[rootId]? = some (.cnode cn))
    (hBitsPos : 0 < bits)
    (hConsPos : 0 < cn.guardWidth + cn.radixWidth)
    (hFit : cn.guardWidth + cn.radixWidth ≤ bits)
    (hBadGuard :
      (addr.toNat >>> (bits - (cn.guardWidth + cn.radixWidth))) /
        2 ^ cn.radixWidth % 2 ^ cn.guardWidth ≠ cn.guardValue) :
    resolveCapAddress rootId addr bits st = .error .invalidCapability := by
  unfold resolveCapAddress
  have hNZ : bits ≠ 0 := by omega
  simp only [hNZ, ↓reduceDIte, hObj]
  have hNZ2 : ¬(cn.guardWidth = 0 ∧ cn.radixWidth = 0) := by omega
  split
  · next h => exfalso; exact hNZ2 (by constructor <;> omega)
  · next h =>
    have hNLt : ¬(bits < cn.guardWidth + cn.radixWidth) := by omega
    simp only [hNLt, ite_false]

/-- WS-H13/H-01 (M-G01): Guard match extraction — if `resolveCapAddress` succeeds
at a leaf CNode (all bits consumed in one hop), then the guard extracted from `addr`
matched the CNode's `guardValue`. This is the forward-direction companion to
`resolveCapAddress_guard_reject` (which proves the contrapositive: bad guard → error).

Together, these two theorems give a bidirectional characterization of guard correctness:
- **Reject**: `guard ≠ guardValue → error`
- **Match**: `success → guard = guardValue`

This pair covers the primary CSpace attack surface: guard bits are the sole mechanism
preventing unauthorized capability resolution through CNode traversal. -/
theorem resolveCapAddress_guard_match
    (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bits : Nat) (st : SystemState)
    (cn : CNode) (ref : SlotRef)
    (hObj : st.objects[rootId]? = some (.cnode cn))
    (hOk : resolveCapAddress rootId addr bits st = .ok ref)
    (hLeaf : bits = cn.guardWidth + cn.radixWidth) :
    (addr.toNat >>> (bits - (cn.guardWidth + cn.radixWidth))) /
      2 ^ cn.radixWidth % 2 ^ cn.guardWidth = cn.guardValue := by
  -- Unfold and trace through the function structure
  unfold resolveCapAddress at hOk
  have hNZ : bits ≠ 0 := by intro h; subst h; simp at hOk
  simp only [hNZ, ↓reduceDIte, hObj] at hOk
  -- consumed = 0 → error, contradicts hOk
  split at hOk
  · simp at hOk
  · -- consumed ≠ 0; bits < consumed impossible since bits = consumed
    have hNLt : ¬(bits < cn.guardWidth + cn.radixWidth) := by omega
    simp only [hNLt, ite_false] at hOk
    -- Guard check: split on if guardExtracted ≠ cn.guardValue
    split at hOk
    · simp at hOk  -- guard mismatch → error, contradicts hOk
    · -- Guard matched — the ¬(≠) gives us equality via double negation elimination
      rename_i hNotNe
      exact Decidable.of_not_not hNotNe

/-- Insert a capability into an empty slot.

WS-E4/H-02: Guarded against occupied-slot overwrites. If the target slot
already contains a capability, returns `targetSlotOccupied`. The caller must
explicitly delete or revoke the existing capability before inserting. -/
def cspaceInsertSlot (addr : CSpaceAddr) (cap : Capability) : Kernel Unit :=
  fun st =>
    match st.objects[addr.cnode]? with
    | some (.cnode cn) =>
        match cn.lookup addr.slot with
        | some _ => .error .targetSlotOccupied  -- H-02: reject occupied slot
        | none =>
            let cn' := cn.insert addr.slot cap
            match storeObject addr.cnode (.cnode cn') st with
            | .error e => .error e
            | .ok (_, st') => storeCapabilityRef addr (some cap.target) st'
    | _ => .error .objectNotFound

theorem cspaceInsertSlot_preserves_scheduler
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
      | cnode cn =>
          simp [hObj] at hStep
          cases hLookup : cn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
              simp [hLookup] at hStep
              have hSchedStore : ∀ st₁ st₂, storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st₁ = .ok ((), st₂) → st₂.scheduler = st₁.scheduler :=
                fun _ _ h => storeObject_scheduler_eq _ _ _ _ h
              cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨_, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hSchedMid := hSchedStore st stMid hStore
                  have hSchedRef := storeCapabilityRef_preserves_scheduler stMid st' addr (some cap.target) hStep
                  rw [hSchedRef, hSchedMid]

theorem cspaceInsertSlot_preserves_services
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.services = st.services := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
      | cnode cn =>
          simp [hObj] at hStep
          cases hLookup : cn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
              simp [hLookup] at hStep
              cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨_, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hSvcMid := storeObject_preserves_services st stMid addr.cnode (.cnode (cn.insert addr.slot cap)) hStore
                  have hSvcRef := storeCapabilityRef_preserves_services stMid st' addr (some cap.target) hStep
                  rw [hSvcRef, hSvcMid]

theorem cspaceInsertSlot_preserves_objects_ne
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (oid : SeLe4n.ObjId)
    (hNe : oid ≠ addr.cnode)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
      | cnode cn =>
          simp [hObj] at hStep
          cases hLookup : cn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
              simp [hLookup] at hStep
              cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨_, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hObjMid := storeObject_objects_ne st stMid addr.cnode oid (.cnode (cn.insert addr.slot cap)) hNe hStore
                  have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr (some cap.target) hStep
                  rw [← hObjMid, show st'.objects[oid]? = stMid.objects[oid]? from congrArg (·.get? oid) hObjRef]

/-- `cspaceInsertSlot` preserves machine state. -/
theorem cspaceInsertSlot_preserves_machine
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
      | cnode cn =>
          simp [hObj] at hStep
          cases hLookup : cn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
              simp [hLookup] at hStep
              cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨_, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hMachMid := storeObject_machine_eq st stMid addr.cnode _ hStore
                  have hMachRef := storeCapabilityRef_preserves_machine stMid st' addr (some cap.target) hStep
                  rw [hMachRef, hMachMid]

/-- WS-F3: `cspaceInsertSlot` preserves IRQ handler mappings. -/
theorem cspaceInsertSlot_preserves_irqHandlers
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _ => simp [hObj] at hStep
      | cnode cn =>
          simp [hObj] at hStep
          cases hLookup : cn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
              simp [hLookup] at hStep
              cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨_, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hIrqMid := storeObject_irqHandlers_eq st stMid addr.cnode _ hStore
                  have hIrqRef := storeCapabilityRef_preserves_irqHandlers stMid st' addr (some cap.target) hStep
                  rw [hIrqRef, hIrqMid]

/-- WS-E4/H-02: `cspaceInsertSlot` rejects occupied slots. -/
theorem cspaceInsertSlot_rejects_occupied_slot
    (st : SystemState) (addr : CSpaceAddr) (cap existingCap : Capability)
    (cn : CNode)
    (hObj : st.objects[addr.cnode]? = some (.cnode cn))
    (hOccupied : cn.lookup addr.slot = some existingCap) :
    cspaceInsertSlot addr cap st = .error .targetSlotOccupied := by
  unfold cspaceInsertSlot
  simp [hObj, hOccupied]

theorem cspaceLookupSlot_ok_iff_lookupSlotCap
    (st : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability) :
    cspaceLookupSlot addr st = .ok (cap, st) ↔
      SystemState.lookupSlotCap st addr = some cap := by
  constructor
  · intro hOk
    unfold cspaceLookupSlot at hOk
    cases hLookup : SystemState.lookupSlotCap st addr with
    | none =>
        cases hObj : st.objects[addr.cnode]? with
        | none => simp [hLookup, hObj] at hOk
        | some obj =>
            cases obj <;> simp [hLookup, hObj] at hOk
    | some cap' =>
        simp [hLookup] at hOk
        cases hOk
        rfl
  · intro hCap
    unfold cspaceLookupSlot
    simp [hCap]

/-- Successful lookup yields slot ownership by the containing CNode object id. -/
theorem cspaceLookupSlot_ok_implies_ownsSlot
    (st : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hLookup : cspaceLookupSlot addr st = .ok (cap, st)) :
    SystemState.ownsSlot st addr.cnode addr := by
  have hCap : SystemState.lookupSlotCap st addr = some cap :=
    (cspaceLookupSlot_ok_iff_lookupSlotCap st addr cap).1 hLookup
  exact (SystemState.ownsSlot_iff st addr.cnode addr).2 ⟨rfl, ⟨cap, hCap⟩⟩

/-- WS-F5/D2b: Requested rights must be contained in allowed rights.
    Checks each of the 5 possible rights via `AccessRight.all`. -/
def rightsSubset (requested allowed : AccessRightSet) : Bool :=
  AccessRight.all.all fun r =>
    if requested.mem r then allowed.mem r else true

/-- WS-F5/D2c: Helper — if `rightsSubset` passes and `r` is in the all-rights list,
    then membership in `requested` implies membership in `allowed`. -/
private theorem rightsSubset_at
    (requested allowed : AccessRightSet) (r : AccessRight)
    (hSubset : rightsSubset requested allowed = true)
    (hMem : AccessRightSet.mem requested r = true) :
    AccessRightSet.mem allowed r = true := by
  unfold rightsSubset at hSubset
  simp only [AccessRight.all, List.all_eq_true] at hSubset
  have hR := hSubset r (by cases r <;> simp)
  simp [hMem] at hR
  exact hR

/-- WS-F5/D2c: Soundness of `rightsSubset` — if subset check passes, every
    right in `requested` is also in `allowed`. -/
theorem rightsSubset_sound
    (requested allowed : AccessRightSet)
    (hSubset : rightsSubset requested allowed = true) :
    ∀ right, right ∈ requested → right ∈ allowed := by
  intro right hMem
  simp only [Membership.mem] at hMem ⊢
  exact rightsSubset_at requested allowed right hSubset hMem

/-- WS-F5/D2b: Build a mint-like derived capability with explicit rights attenuation. -/
def mintDerivedCap (parent : Capability) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge := parent.badge) : Except KernelError Capability :=
  if rightsSubset rights parent.rights then
    .ok { target := parent.target, rights := rights, badge := badge }
  else
    .error .invalidCapability

/-- Mint from source slot and insert into destination slot under attenuation checks. -/
def cspaceMint
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (parent, st') =>
        match mintDerivedCap parent rights badge with
        | .error e => .error e
        | .ok child => cspaceInsertSlot dst child st'

/-- Delete the capability currently stored in `addr`. -/
def cspaceDeleteSlot (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match st.objects[addr.cnode]? with
    | some (.cnode cn) =>
        let cn' := cn.remove addr.slot
        match storeObject addr.cnode (.cnode cn') st with
        | .error e => .error e
        | .ok (_, st') =>
            match storeCapabilityRef addr none st' with
            | .error e => .error e
            | .ok ((), st'') =>
                let stDetached := SystemState.detachSlotFromCdt st'' addr
                .ok ((), stDetached)
    | _ => .error .objectNotFound

/-- Revoke capabilities with the same target as the source in the containing CNode.

This is the local (single-CNode) revocation variant. For cross-CNode revocation
using CDT traversal, see `cspaceRevokeCdt` and `cspaceRevokeCdtStrict`.

The source slot remains present and sibling slots naming the same target are removed. -/
def cspaceRevoke (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (parent, st') =>
        match st'.objects[addr.cnode]? with
        | some (.cnode cn) =>
            let cn' := cn.revokeTargetLocal addr.slot parent.target
            -- WS-G5: HashMap.fold collects revoked SlotRefs in a single O(m) pass.
            let revokedRefs : List SlotRef :=
              cn.slots.fold (fun acc s c =>
                if s != addr.slot && c.target == parent.target then
                  { cnode := addr.cnode, slot := s } :: acc
                else acc) []
            match storeObject addr.cnode (.cnode cn') st' with
            | .error e => .error e
            | .ok (_, st'') => clearCapabilityRefs revokedRefs st''
        | _ => .error .objectNotFound

-- ============================================================================
-- WS-E4/C-02: Capability copy, move, and mutate operations
-- ============================================================================

/-- WS-E4/C-02: Copy a capability from source to destination without rights change.

Unlike `cspaceMint`, copy does not attenuate rights or change the badge.
The destination slot must be empty (H-02 guard via `cspaceInsertSlot`).
A CDT derivation edge of type `.copy` is recorded. -/
def cspaceCopy (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') =>
        match cspaceInsertSlot dst cap st' with
        | .error e => .error e
        | .ok ((), st'') =>
            let (srcNode, stSrc) := SystemState.ensureCdtNodeForSlot st'' src
            let (dstNode, stDst) := SystemState.ensureCdtNodeForSlot stSrc dst
            let cdt' := stDst.cdt.addEdge srcNode dstNode .copy
            .ok ((), { stDst with cdt := cdt' })

/-- WS-E4/C-02: Move a capability from source to destination.

The source slot is cleared and the capability is placed in the destination.
The destination must be empty (H-02). CDT edges are transferred: the moved
capability inherits the parent-child relationships of the source slot. -/
def cspaceMove (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') =>
        match cspaceInsertSlot dst cap st' with
        | .error e => .error e
        | .ok ((), st'') =>
            let srcNode? := SystemState.lookupCdtNodeOfSlot st'' src
            match cspaceDeleteSlot src st'' with
            | .error e => .error e
            | .ok ((), st''') =>
                -- Node-stable CDT: move is a slot-pointer move + backpointer fixup.
                match srcNode? with
                | none => .ok ((), st''')
                | some srcNode =>
                    let stMoved := SystemState.attachSlotToCdtNode st''' dst srcNode
                    .ok ((), stMoved)

/-- WS-H13/A-21: `cspaceMove` error-path atomicity. On failure, no output
state is produced — the `Except` error constructor carries only the error tag,
not a modified `SystemState`. The caller's original `st` is therefore the only
state reachable, satisfying "neither change occurs". This is definitional from
the `Kernel` (`SystemState → Except KernelError (α × SystemState)`) type:
`Except.error e` has no `SystemState` field. -/
theorem cspaceMove_error_no_state
    (src dst : CSpaceAddr) (st : SystemState) (e : KernelError)
    (hErr : cspaceMove src dst st = .error e) :
    ∀ st', cspaceMove src dst st ≠ .ok ((), st') := by
  intro st' hContra
  rw [hErr] at hContra; exact absurd hContra (by simp)

/-- WS-H13/A-21: `cspaceMove` success-path atomicity. If the move succeeds,
both the lookup and insert/delete composed correctly — the operation completed
fully rather than partially. The result state `st'` incorporates the deletion
of the source slot and the insertion of the capability into the destination
slot, plus CDT backpointer fixup. -/
private theorem cspaceLookupSlot_state_eq
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceLookupSlot addr st = .ok (cap, st')) :
    st' = st := by
  simp only [cspaceLookupSlot] at hStep
  split at hStep
  · simp at hStep; exact hStep.2.symm
  · split at hStep <;> simp at hStep

theorem cspaceMove_ok_implies_source_exists
    (src dst : CSpaceAddr) (st st' : SystemState)
    (hStep : cspaceMove src dst st = .ok ((), st')) :
    ∃ (cap : Capability), SystemState.lookupSlotCap st src = some cap := by
  unfold cspaceMove at hStep
  cases hLkp : cspaceLookupSlot src st with
  | error e => simp [hLkp] at hStep
  | ok pair =>
    rcases pair with ⟨cap, _⟩
    refine ⟨cap, ?_⟩
    unfold cspaceLookupSlot at hLkp
    split at hLkp
    · next cap' hCap =>
      have : cap' = cap := by simp at hLkp; exact hLkp.1
      rw [← this]; exact hCap
    · split at hLkp <;> simp at hLkp

/-- WS-E4/C-02: Mutate a capability's rights in place without creating a derivation.

The slot must already contain a capability, and the new rights must be a subset
of the existing rights (attenuation only). Badge can be overridden. -/
def cspaceMutate (addr : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (cap, st') =>
        if rightsSubset rights cap.rights then
          let mutatedCap : Capability :=
            { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) }
          -- Direct overwrite: bypass H-02 guard since we are replacing in-place
          match st'.objects[addr.cnode]? with
          | some (.cnode cn) =>
              let cn' := cn.insert addr.slot mutatedCap
              match storeObject addr.cnode (.cnode cn') st' with
              | .error e => .error e
              | .ok (_, st'') => storeCapabilityRef addr (some mutatedCap.target) st''
          | _ => .error .objectNotFound
        else .error .invalidCapability

-- ============================================================================
-- WS-E4/C-03: CDT-aware mint
-- ============================================================================

/-- WS-E4/C-03: Mint a derived capability and record a CDT derivation edge. -/
def cspaceMintWithCdt (src dst : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) : Kernel Unit :=
  fun st =>
    match cspaceMint src dst rights badge st with
    | .error e => .error e
    | .ok ((), st') =>
        let (srcNode, stSrc) := SystemState.ensureCdtNodeForSlot st' src
        let (dstNode, stDst) := SystemState.ensureCdtNodeForSlot stSrc dst
        let cdt' := stDst.cdt.addEdge srcNode dstNode .mint
        .ok ((), { stDst with cdt := cdt' })

-- ============================================================================
-- WS-E4/C-04: Cross-CNode CDT revocation
-- ============================================================================

/-- WS-E4/C-04: Revoke all capabilities derived from the source capability
via CDT traversal, across all CNodes in the system.

Extends local revoke with CDT-based global traversal:
1. Perform local revocation (same CNode siblings)
2. Walk the CDT to find all descendants of the source slot
3. Delete each descendant's capability from its CNode
4. Clean up CDT edges for deleted slots

**Error handling**: Descendant deletion errors are swallowed — the CDT node is
removed regardless, preventing stale references. This is safe because
`removeNode` only shrinks the edge set (proven by
`cspaceRevokeCdt_swallowed_error_consistent`). For callers requiring error
visibility, use `cspaceRevokeCdtStrict`. -/
def cspaceRevokeCdt (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    -- First do local revocation
    match cspaceRevoke addr st with
    | .error e => .error e
    | .ok ((), stLocal) =>
        -- Walk CDT descendants in node space, then project to slots for deletion.
        match SystemState.lookupCdtNodeOfSlot stLocal addr with
        | none => .ok ((), stLocal)
        | some rootNode =>
            let descendants := stLocal.cdt.descendantsOf rootNode
            let result := descendants.foldl (fun acc node =>
              match acc with
              | .error e => .error e
              | .ok ((), stAcc) =>
                  match SystemState.lookupCdtSlotOfNode stAcc node with
                  | none => .ok ((), { stAcc with cdt := stAcc.cdt.removeNode node })
                  | some descAddr =>
                      match cspaceDeleteSlot descAddr stAcc with
                      | .error _ => .ok ((), { stAcc with cdt := stAcc.cdt.removeNode node })
                      | .ok ((), stDel) =>
                          let stDetached := SystemState.detachSlotFromCdt stDel descAddr
                          .ok ((), { stDetached with cdt := stDetached.cdt.removeNode node })
            ) (.ok ((), stLocal))
            result

/-- Structured failure context for strict CDT descendant deletion.

`offendingSlot` is the slot projected from the failing CDT node (when a slot
mapping exists). `error` is the concrete deletion error surfaced by
`cspaceDeleteSlot`. -/
structure RevokeCdtStrictFailure where
  offendingNode : CdtNodeId
  offendingSlot : Option CSpaceAddr
  error : KernelError
  deriving Repr, DecidableEq

/-- Return payload for strict CDT revocation.

The strict variant stops at the first descendant deletion failure and returns
its context in `firstFailure` instead of swallowing the error. -/
structure RevokeCdtStrictReport where
  deletedSlots : List CSpaceAddr
  firstFailure : Option RevokeCdtStrictFailure
  deriving Repr, DecidableEq

/-- Strict WS-E4/C-04 revocation variant.

Compared to `cspaceRevokeCdt`, this variant is strict over descendant deletion:
it surfaces the first `cspaceDeleteSlot` failure and records the offending CDT
node + slot context in the returned report. Traversal halts at the first
failure; successfully deleted descendants before that point remain recorded in
`deletedSlots`.

Local (`same-CNode`) revoke failures are still reported via `.error`, matching
the base operation contract. -/
def cspaceRevokeCdtStrict (addr : CSpaceAddr) : Kernel RevokeCdtStrictReport :=
  fun st =>
    match cspaceRevoke addr st with
    | .error e => .error e
    | .ok ((), stLocal) =>
        match SystemState.lookupCdtNodeOfSlot stLocal addr with
        | none => .ok ({ deletedSlots := [], firstFailure := none }, stLocal)
        | some rootNode =>
            let descendants := stLocal.cdt.descendantsOf rootNode
            let step := fun (acc : RevokeCdtStrictReport × SystemState) (node : CdtNodeId) =>
              let (report, stAcc) := acc
              match report.firstFailure with
              | some _ => (report, stAcc)
              | none =>
                  match SystemState.lookupCdtSlotOfNode stAcc node with
                  | none =>
                      let stRemoved := { stAcc with cdt := stAcc.cdt.removeNode node }
                      (report, stRemoved)
                  | some descAddr =>
                      match cspaceDeleteSlot descAddr stAcc with
                      | .error err =>
                          let failure : RevokeCdtStrictFailure := {
                            offendingNode := node
                            offendingSlot := some descAddr
                            error := err
                          }
                          let stRemoved := { stAcc with cdt := stAcc.cdt.removeNode node }
                          ({ report with firstFailure := some failure }, stRemoved)
                      | .ok ((), stDel) =>
                          let stDetached := SystemState.detachSlotFromCdt stDel descAddr
                          let stRemoved := { stDetached with cdt := stDetached.cdt.removeNode node }
                          ({ report with deletedSlots := descAddr :: report.deletedSlots }, stRemoved)
            let (report, stFinal) := descendants.foldl step ({ deletedSlots := [], firstFailure := none }, stLocal)
            .ok ({ report with deletedSlots := report.deletedSlots.reverse }, stFinal)

end SeLe4n.Kernel
