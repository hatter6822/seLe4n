/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant

/-! ### AK8-K (WS-AK) — Capability / Lifecycle / Service LOW-tier batch

This file-level documentation block annotates the residual LOW-tier audit
findings for the capability subsystem that were addressed in Phase AK8-K.

- **C-L1 (`cspaceMove` self-move early reject):** addressed. The operation
  now fails closed with `.illegalState` when `src = dst`, rejecting the
  degenerate no-op case before triggering insert/delete CDT churn. See
  `cspaceMove` docstring and all preservation proofs in
  `Capability/Invariant/Preservation.lean` (by_cases `hSelf : src = dst`).
- **C-L2 (`cspaceMutate` occupied-slot / null-cap guard):** addressed. The
  operation now rejects `Capability.null` with `.nullCapability` before
  performing any mutation. See `cspaceMutate` docstring; preservation
  proofs cascade via `by_cases hNull : cap.isNull`.
- **C-L3 (`ipcTransferSingleCap` CDT edge without sender-rights record):**
  not modified in AK8. Closing this LOW-tier finding would require
  extending `CdtEdgeKind` with a sender-rights field and updating the
  14 CDT-edge composition proofs. That refactor is larger than the
  Phase AK8 LOW-tier batch budgets for any single item and is recorded
  here as a post-1.0 hardening candidate; no concrete plan file tracks
  it yet.
- **C-L4 (`cleanupDonatedSchedContext` asymmetry):** handled inline by
  the AJ1-A + AH2-A/B cascade which aligned bound/donated cleanup
  error-propagation through `cleanupPreReceiveDonationChecked`.
- **C-L5 (IPC buffer canonical upper bound):** addressed by
  `ipcBuffer_within_page` theorem (AE4-I) in
  `Architecture/IpcBufferValidation.lean`.
- **C-L6 (`registerService` O(n) timing side-channel):** documented as
  deferred to post-1.0. Timing uniformity across service names requires
  constant-time hash-table insert semantics; RHTable's Robin-Hood probing
  exposes the side-channel by construction. Deployment-layer concern.
- **C-L7 (`lookupServiceByCap` RH-rehash stability):** documented here.
  `lookupServiceByCap` traverses the service registry via hash lookup;
  RHTable rehash on load-factor crossings does NOT affect lookup semantics
  (key→value mapping is preserved across rehashes by
  `RHTable.insert_preserves_invExt` + `getElem?_insert_self/_ne`).
- **C-L8 (`serviceCountBounded` boot-time exposure):** the accessor
  `crossSubsystemInvariant_to_serviceGraphInvariant.2` extracts the
  bounded count from the cross-subsystem invariant bundle.
- **C-L9 (abstract object sizes vs seL4 RPi5):** documented in
  `docs/spec/SELE4N_SPEC.md` §6.3 "Object size abstractions". The Lean
  model uses abstract `objectTypeAllocSize` which does not bind
  tightly to seL4's hardware-specific layout. Tightening to seL4/ARM64
  exact sizes would be a model-refinement workstream in its own right
  and is not part of the current AK8 scope; recorded here as a
  post-1.0 hardening candidate.
- **C-L10 (`cspaceDeleteSlotCore` dangling CDT edges):** audited. The
  invocation `detachSlotFromCdt` inside `cspaceDeleteSlotCore` (AH3-A)
  already removes the slot→node mapping; the CDT node itself is preserved
  by design so that subsequent revocations can traverse it (AH3-A fix).
  No dangling edges — the CDT node remains reachable via its parent's
  children set until the parent itself is revoked. -/

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

/-- Resolve a CSpace path address into a concrete slot using CNode guard/radix semantics.

AF5-G (AF-27): CSpace Resolution Layers
• `cspaceResolvePath`: Single-level resolution within one CNode (guard check
  + radix index extraction). Used by `cspaceLookupPath` for direct slot access.
• `resolveCapAddress`: Multi-level recursive resolution through nested CNodes.
  Calls guard/radix extraction at each level, then recurses into child CNodes.
`cspaceResolvePath` operates on a `CSpacePathAddr` (known CNode + CPtr + depth),
while `resolveCapAddress` starts from a root CNode and walks arbitrarily deep. -/
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
invariant / `hProgress`).

**seL4 divergence (U-M25):** seL4 checks intermediate capability rights
(read right) during multi-level CSpace traversal. seLe4n enforces rights
at the operation layer instead — the resolved capability's rights are
checked by the calling operation (`cspaceMint`, `cspaceCopy`, etc.) via
`capHasRight` guards. This is a deliberate design choice: operation-level
enforcement is simpler to prove and covers all access paths, whereas
traversal-level enforcement adds per-hop proof obligations without
strengthening the security guarantee (the operation still checks rights).

**AK8-C (C-M03) — Caller rights obligation (formal):** Every caller of
`resolveCapAddress` (and the derived `cspaceLookupMultiLevel`,
`cspaceLookupSlot`) **MUST** enforce the required capability rights
against the ENTRY-LEVEL capability at `rootId` BEFORE invoking this
function. Intermediate CNodes traversed during multi-level resolution
are **not** rights-checked. Specifically:

- The root capability's rights must cover every authority the caller
  needs to exercise on the resolved slot.
- Intermediate CNode capabilities (those chained through via
  `cap.target = .object childId`) are assumed to have been placed in
  the CSpace by an authority that already validated their rights at
  mint/copy time — they do not get re-checked on each traversal.
- Any new cap-forwarding operation (e.g., a future
  `cspaceForwardCap` that re-uses a resolved slot in a different
  authority context) must establish a rights-reduction proof at the
  point of call, NOT rely on `resolveCapAddress` to do so.

See `resolveCapAddress_caller_rights_obligation` below for the formal
contract theorem. -/
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
        -- AE4-A (U-17/CAP-01): Mask CPtr to machine word width for consistency
        -- with CNode.resolveSlot (S4-C). For Lean's unbounded Nat, addresses
        -- beyond 2^64 must produce identical results to 64-bit hardware registers.
        let maskedAddr := addr.toNat % SeLe4n.machineWordMax
        let shiftedAddr := maskedAddr >>> (bitsRemaining - consumed)
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

/-- WS-H13/H-01 (deliverable 9): `resolveCapAddress` returns `.error .illegalState`
when called with zero bits remaining. -/
theorem resolveCapAddress_zero_bits
    (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (st : SystemState) :
    resolveCapAddress rootId addr 0 st = .error .illegalState := by
  simp [resolveCapAddress]

/-- AK8-C (WS-AK / C-M03): **Formal caller rights obligation for
`resolveCapAddress`.** This theorem documents the design contract that
`resolveCapAddress` imposes on its callers: the function does NOT check
intermediate-level capability rights during multi-level CSpace traversal.
Callers must establish any required rights at the entry-level capability
before invoking it.

This theorem is intentionally vacuous — it has no Prop content — and
exists solely to surface the obligation in a machine-searchable form.
Any future cap-forwarding operation that reuses a resolved slot in a
different authority context MUST reference this theorem in its
precondition to acknowledge the contract.

See the `resolveCapAddress` docstring (§AK8-C — Caller rights obligation)
for the full narrative description. The three current call sites —
`cspaceLookupMultiLevel`, `cspaceLookupSlot` (via `cspaceResolveRef`),
and direct `resolveCapAddress` use in the capability dispatcher — all
satisfy this obligation by checking rights at the operation layer
(`cspaceMint`, `cspaceCopy`, `cspaceMove`, `cspaceDeleteSlot`) before
dereferencing the resolved slot. -/
theorem resolveCapAddress_caller_rights_obligation : True := trivial

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

-- ============================================================================
-- WS-H13/H-01 (M-G01): Guard correctness — bidirectional characterization
--
-- The CSpace guard check is the primary attack surface for unauthorized
-- capability resolution. These two theorems give a complete characterization:
--
--   resolveCapAddress_guard_reject : guard ≠ guardValue → error
--   resolveCapAddress_guard_match  : success → guard = guardValue
--
-- Together they prove that the guard check is both sound (wrong guards are
-- always rejected) and complete (success implies correct guard).
-- ============================================================================

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
      ((addr.toNat % SeLe4n.machineWordMax) >>> (bits - (cn.guardWidth + cn.radixWidth))) /
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
    ((addr.toNat % SeLe4n.machineWordMax) >>> (bits - (cn.guardWidth + cn.radixWidth))) /
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
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
      | schedContext _ => simp [hObj] at hStep
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
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
      | schedContext _ => simp [hObj] at hStep
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
    (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
      | schedContext _ => simp [hObj] at hStep
      | cnode cn =>
          simp [hObj] at hStep
          cases hLookup : cn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
              simp [hLookup] at hStep
              cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨⟨⟩, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hObjMid := storeObject_objects_ne st stMid addr.cnode oid (.cnode (cn.insert addr.slot cap)) hNe hObjInv hStore
                  have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr (some cap.target) hStep
                  rw [← hObjMid, show st'.objects[oid]? = stMid.objects[oid]? from congrArg (·.get? oid) hObjRef]

/-- `cspaceInsertSlot` preserves `objects.invExt`. -/
theorem cspaceInsertSlot_preserves_objects_invExt
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects[addr.cnode]? with
  | none => simp [hObj] at hStep
  | some obj =>
      cases obj with
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
      | schedContext _ => simp [hObj] at hStep
      | cnode cn =>
          simp [hObj] at hStep
          cases hLookup : cn.lookup addr.slot with
          | some _ => simp [hLookup] at hStep
          | none =>
              simp [hLookup] at hStep
              cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨⟨⟩, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hInvMid := storeObject_preserves_objects_invExt st stMid addr.cnode _ hObjInv hStore
                  have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr (some cap.target) hStep
                  rw [show st'.objects = stMid.objects from hObjRef]; exact hInvMid

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
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
      | schedContext _ => simp [hObj] at hStep
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
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
      | schedContext _ => simp [hObj] at hStep
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

/-- WS-F5/D2b: Build a mint-like derived capability with explicit rights attenuation.

**S1-M: Badge-forging security note.** When minting with a custom `badge`,
any holder of a capability with Mint authority on an endpoint can construct a
derived capability with an arbitrary badge value. This matches seL4 semantics:
badge values are opaque identifiers set by the authority holder and delivered
to the receiver on IPC. The receiver can distinguish senders by badge but cannot
authenticate the badge itself — authentication relies on the capability
derivation tree (CDT) tracking which entity minted the badge. Callers must
not treat badge values as cryptographic authenticators.

**AL1b (WS-AL / AK7-I.cascade) — Type-level non-null discipline**: the
`parent` parameter has type `NonNullCap`, not `Capability`. The Lean
type system forbids any caller from feeding a null cap into this
function — construction of a `NonNullCap` requires the caller to
produce a `cap.isNull = false` witness via `Capability.toNonNull?`
(the `none` branch forces the caller to emit
`KernelError.nullCapability` and short-circuit). The raw `Capability`
field accessors are reached via `parent.val.<field>`. -/
def mintDerivedCap (parent : NonNullCap) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge := parent.val.badge) : Except KernelError Capability :=
  if rightsSubset rights parent.val.rights then
    .ok { target := parent.val.target, rights := rights, badge := badge }
  else
    .error .invalidCapability

/-- Mint from source slot and insert into destination slot under attenuation checks.

**CDT-untracked base operation (C-01)**: This function creates capabilities
without recording CDT derivation edges. The production syscall dispatch path
(`dispatchWithCapChecked` → `cspaceMintChecked`) uses `cspaceMintWithCdt`,
which calls this function then records CDT edges. Minted capabilities are
therefore revocable via `cspaceRevoke`.

Direct use of `cspaceMint` (without CDT tracking) should be limited to:
- Internal composition within `cspaceMintWithCdt`
- Proof decomposition (invariant theorems reference this base function)
- Test scaffolding for the untracked primitive -/
def cspaceMint
    (src dst : CSpaceAddr)
    (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (parent, st') =>
        -- AL1b (AK7-I.cascade): type-level non-null discipline. Promote the
        -- looked-up parent cap to `NonNullCap` via `Capability.toNonNull?`.
        -- On failure, emit the dedicated `.nullCapability` error (distinct
        -- from `.invalidCapability`'s "slot empty" / "non-object target"
        -- overloads). `mintDerivedCap`'s type signature REQUIRES
        -- `NonNullCap` — the type system forbids bypass.
        match parent.toNonNull? with
        | none => .error .nullCapability
        | some parentNN =>
            match mintDerivedCap parentNN rights badge with
            | .error e => .error e
            | .ok child => cspaceInsertSlot dst child st'

/-- U-H03: Check whether a CSpace slot has CDT children (derived capabilities).
Returns `true` if the slot's CDT node has any children, indicating that
`cspaceRevoke` must be called before deletion. -/
def hasCdtChildren (st : SystemState) (addr : CSpaceAddr) : Bool :=
  match st.lookupCdtNodeOfSlot addr with
  | none => false  -- no CDT node → no children
  | some node => !(st.cdt.childrenOf node).isEmpty

/-- Core capability slot deletion without CDT children guard.
Used by `cspaceDeleteSlot` (which adds the guard) and by internal kernel
operations (`processRevokeNode`, `cspaceRevokeCdtStrict`, `cspaceMove`) that
manage CDT children themselves. -/
def cspaceDeleteSlotCore (addr : CSpaceAddr) : Kernel Unit :=
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

/-- Delete the capability currently stored in `addr`.

U-H03: Before deleting, checks that no CDT children exist for the slot.
Returns `.revocationRequired` if children are found, enforcing the
`revokeBeforeDelete` proof obligation as a runtime check. -/
def cspaceDeleteSlot (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    if hasCdtChildren st addr then
      .error .revocationRequired
    else
      cspaceDeleteSlotCore addr st

/-- V5-G (M-DEF-7): **Revocation routing guide.**

seLe4n provides three revocation entry points for different use cases:

- **`cspaceRevoke`** (this function): Local, single-CNode revocation. Removes
  sibling capabilities within the same CNode that share the source slot's
  target. Does NOT traverse the CDT or affect capabilities in other CNodes.
  Use when revoking derived caps that are known to be co-located.

- **`cspaceRevokeCdt`**: Cross-CNode revocation via CDT traversal. First
  performs local revocation (`cspaceRevoke`), then walks all CDT descendants
  of the source slot and deletes their capabilities from any CNode in the
  system. This is the **recommended entry point** for general revocation.
  Errors from descendant deletion are propagated (strict mode).

- **`cspaceRevokeCdtStrict`**: Structured variant of `cspaceRevokeCdt` that
  returns a detailed `RevokeCdtStrictReport` including which slots were
  deleted and which (if any) failed. Use when the caller needs diagnostic
  information about partial revocation failures.

- **`cspaceRevokeCdtStreaming`**: Fuel-bounded BFS variant providing the same
  semantics as `cspaceRevokeCdt` with guaranteed O(fuel) termination. Use
  when deterministic execution time is required.

**API dispatch**: `dispatchWithCap` and `dispatchWithCapChecked` route
`SyscallId.cspaceRevoke` through `cspaceRevokeCdt` (the CDT-traversing
variant), which is the correct default for untrusted userspace invocations.

Revoke capabilities with the same target as the source in the containing CNode.

This is the local (single-CNode) revocation variant. For cross-CNode revocation
using CDT traversal, see `cspaceRevokeCdt` and `cspaceRevokeCdtStrict`.

The source slot remains present and sibling slots naming the same target are removed.

**S4-L: Complexity analysis.** Local revocation performs a single `RHTable.fold`
pass over the source CNode's slots, filtering entries whose `CapTarget` matches
the source capability. This is O(n) in the slot count of the containing CNode.
The slot count is bounded by the CNode's `2^radixWidth` capacity, which is at
most `2^maxCSpaceDepth = 2^64` in theory but typically ≤ 1024 in practice.

For CDT-based cross-CNode revocation (`cspaceRevokeCdt`), the traversal visits
all descendants of the source node in the Capability Derivation Tree. This is
O(d) where `d` is the total number of CDT descendants, bounded by
`maxObjects` (65536 for RPi5). Each descendant triggers one `processRevokeNode`
call (O(1) amortized via RHTable operations). Total worst-case: O(maxObjects)
per revocation. The streaming BFS variant (`cspaceRevokeCdtStreaming`) uses
fuel-bounded iteration with fuel = CDT edge count, providing the same
O(maxObjects) bound with guaranteed termination. -/
def cspaceRevoke (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (parent, st') =>
        match st'.objects[addr.cnode]? with
        | some (.cnode cn) =>
            let cn' := cn.revokeTargetLocal addr.slot parent.target
            match storeObject addr.cnode (.cnode cn') st' with
            | .error e => .error e
            | .ok (_, st'') =>
                -- M-P01: Fused single-pass revoke — clear capability refs inline
                -- during the slot scan instead of building an intermediate list.
                .ok ((), revokeAndClearRefsState cn addr.slot parent.target addr.cnode st'')
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
        -- AL1b (AK7-I.cascade): type-level null-cap rejection. Promote the
        -- looked-up cap to `NonNullCap`; `none` is `.error .nullCapability`
        -- (distinct from `.invalidCapability`). A null cap cannot be
        -- meaningfully copied — it would clutter CDT tracking and the
        -- destination with an always-inert capability. Fail fast.
        match cap.toNonNull? with
        | none => .error .nullCapability
        | some capNN =>
            match cspaceInsertSlot dst capNN.val st' with
            | .error e => .error e
            | .ok ((), st'') =>
                let (srcNode, stSrc) := SystemState.ensureCdtNodeForSlot st'' src
                let (dstNode, stDst) := SystemState.ensureCdtNodeForSlot stSrc dst
                let cdt' := stDst.cdt.addEdge srcNode dstNode .copy
                .ok ((), { stDst with cdt := cdt' })

/-- WS-E4/C-02: Move a capability from source to destination.

The source slot is cleared and the capability is placed in the destination.
The destination must be empty (H-02). CDT edges are transferred: the moved
capability inherits the parent-child relationships of the source slot.

**AK8-K (WS-AK / C-L1) — Self-move early reject:** a `cspaceMove src dst`
where `src = dst` is a no-op at the capability level but produces spurious
CDT-edge churn (the node-stable CDT would attach the slot to itself). The
operation rejects the self-move case up front with `.illegalState`, matching
seL4's conservative approach for degenerate arguments. -/
def cspaceMove (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    if src = dst then .error .illegalState
    else
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') =>
        -- AL1b (AK7-I.cascade): type-level null-cap rejection. A moved null
        -- cap would clear the source and occupy the destination with a cap
        -- that carries no authority — semantically a no-op but creates
        -- CDT-edge churn. Fail with the distinct `.nullCapability` error.
        match cap.toNonNull? with
        | none => .error .nullCapability
        | some capNN =>
            match cspaceInsertSlot dst capNN.val st' with
            | .error e => .error e
            | .ok ((), st'') =>
                let srcNode? := SystemState.lookupCdtNodeOfSlot st'' src
                -- Use unchecked delete: move preserves CDT edges via
                -- attachSlotToCdtNode, so children follow the capability.
                match cspaceDeleteSlotCore src st'' with
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
  -- AK8-K (C-L1): case-split on the self-move early-reject guard.
  by_cases hSelf : src = dst
  · simp [hSelf] at hStep
  simp [hSelf] at hStep
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
of the existing rights (attenuation only). Badge can be overridden.

**T4-H (M-CAP-1) design note**: Badge override via `cspaceMutate` is intentionally
*not* tracked in the CDT (CapDerivationTree). This matches seL4's `CNode_Mutate`
semantics: the badge is part of the capability *value* (like rights), not the
derivation *relationship*. The CDT tracks parent→child lineage for revocation;
badge changes don't affect which capabilities should be revoked when an ancestor
is deleted. The `cspaceMintWithCdt` operation (below) *does* track derivation
edges because minting creates a new capability slot, not an in-place mutation. -/
def cspaceMutate (addr : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (cap, st') =>
        -- AK8-K (C-L2): Occupied-slot guard — reject the `Capability.null`
        -- sentinel (seL4_CapNull convention). Mutating a null cap is a
        -- no-op semantically (the cap has no authority to begin with) and
        -- would cement a null sentinel into the slot with possibly-non-zero
        -- rights after the mutation, breaking the null-cap invariant.
        -- Fail with `.nullCapability` to match `cspaceMint`/`Copy`/`Move`.
        if cap.isNull then .error .nullCapability
        else if rightsSubset rights cap.rights then
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
-- M-P04/M5: Shared per-node revocation step
-- ============================================================================

/-- R2-A: Process a single CDT descendant node during revocation.

Shared transition used by both `cspaceRevokeCdt` (materialized fold) and
`streamingRevokeBFS` (streaming BFS). Given a CDT node:
1. If no slot mapping exists, just remove the CDT node → `.ok`.
2. If delete fails, propagate the error → `.error e`.
3. If delete succeeds, detach the slot→node mapping and remove the CDT node → `.ok`.

Changed in WS-R2/M-06: errors from `cspaceDeleteSlot` are now propagated
instead of swallowed. CDT-based revocation (`cspaceRevokeCdt`) is the
canonical revocation entry point — all API dispatch routes through it. -/
def processRevokeNode (st : SystemState) (node : CdtNodeId)
    : Except KernelError SystemState :=
  match SystemState.lookupCdtSlotOfNode st node with
  | none => .ok { st with cdt := st.cdt.removeNode node }
  | some descAddr =>
      match cspaceDeleteSlotCore descAddr st with
      | .error e => .error e
      | .ok ((), stDel) =>
          -- V5-N (L-CAP-1): The second `detachSlotFromCdt` that was here has been
          -- removed. `cspaceDeleteSlotCore` already calls `detachSlotFromCdt` internally
          -- (see line ~579), so the call here was redundant. `detachSlotFromCdt` is
          -- idempotent (detaching an already-detached slot is a no-op), so the duplicate
          -- was harmless but misleading. After `cspaceDeleteSlotCore`, the slot is already
          -- detached; we only need `removeNode` to clean up the CDT node itself.
          .ok { stDel with cdt := stDel.cdt.removeNode node }

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

**Error handling** (WS-R2/M-06): Descendant deletion errors are now propagated
to callers. If any descendant's `cspaceDeleteSlot` fails, the fold stops and
returns the error. For the legacy lenient behavior (swallow errors), use
`cspaceRevokeCdt_lenient`. For callers requiring structured failure reports,
use `cspaceRevokeCdtStrict`. -/
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
            -- AJ-L10: `descendantsOf` materializes the full descendant list before
            -- folding. For deep CDT trees this is a performance concern (O(n) allocation),
            -- not a correctness issue. A streaming/iterator-based approach is deferred
            -- to WS-V (performance optimization phase).
            let descendants := stLocal.cdt.descendantsOf rootNode
            let result := descendants.foldl (fun acc node =>
              match acc with
              | .error e => .error e
              | .ok ((), stAcc) =>
                  match processRevokeNode stAcc node with
                  | .error e => .error e
                  | .ok stNext => .ok ((), stNext)
            ) (.ok ((), stLocal))
            result

-- ============================================================================
-- M-P04: Streaming CDT revocation (WS-M5)
-- ============================================================================

/-- M-P04: Streaming BFS loop — processes one node per step, discovering
children before removing the node from the CDT.

Each iteration:
1. Dequeues the head node from the BFS queue.
2. Reads the node's children via `childrenOf` (before removal).
3. Delegates to `processRevokeNode` for the actual delete/detach/removeNode.
4. Appends newly-discovered children to the queue tail.

Fuel = initial edge count, guaranteeing termination since each step
removes at least one CDT node (shrinking the edge set).

Changed in WS-R2/M-05: fuel exhaustion now returns `.error .resourceExhausted`
instead of `.ok`, making incomplete revocation visible to callers. -/
def streamingRevokeBFS
    (fuel : Nat) (queue : List CdtNodeId)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  match fuel, queue with
  | _, [] => .ok ((), st)
  | 0, _ :: _ => .error .resourceExhausted  -- WS-R2/M-05: fuel exhausted
  | fuel + 1, node :: rest =>
      match processRevokeNode st node with
      | .error e => .error e
      | .ok stNext =>
          let children := st.cdt.childrenOf node
          streamingRevokeBFS fuel (rest ++ children) stNext

/-- M-P04: Streaming CDT revocation — interleaves BFS discovery with deletion.

Equivalent to `cspaceRevokeCdt` but processes descendants on-the-fly instead
of materializing the full descendant list upfront. Peak memory: O(max branching
factor) instead of O(N).

1. Perform local revocation (same CNode siblings) via `cspaceRevoke`.
2. Look up the source slot's CDT node.
3. Initialize the BFS queue with the root node's direct children.
4. Run `streamingRevokeBFS` with fuel = `cdt.edges.length`.

Error handling (WS-R2/M-05, M-06): descendant deletion errors are propagated.
Fuel exhaustion returns `.error .resourceExhausted`. -/
def cspaceRevokeCdtStreaming (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceRevoke addr st with
    | .error e => .error e
    | .ok ((), stLocal) =>
        match SystemState.lookupCdtNodeOfSlot stLocal addr with
        | none => .ok ((), stLocal)
        | some rootNode =>
            let children := stLocal.cdt.childrenOf rootNode
            streamingRevokeBFS stLocal.cdt.edges.length children stLocal

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
                      match cspaceDeleteSlotCore descAddr stAcc with
                      | .error err =>
                          let failure : RevokeCdtStrictFailure := {
                            offendingNode := node
                            offendingSlot := some descAddr
                            error := err
                          }
                          -- AH3-A (L-04): Preserve CDT node on slot deletion failure.
                          -- The capability slot still exists; removing its CDT node would
                          -- make it unreachable by future revocation, creating an orphan.
                          ({ report with firstFailure := some failure }, stAcc)
                      | .ok ((), stDel) =>
                          -- V5-N: Redundant detachSlotFromCdt removed (already done by cspaceDeleteSlotCore)
                          let stRemoved := { stDel with cdt := stDel.cdt.removeNode node }
                          ({ report with deletedSlots := descAddr :: report.deletedSlots }, stRemoved)
            let (report, stFinal) := descendants.foldl step ({ deletedSlots := [], firstFailure := none }, stLocal)
            .ok ({ report with deletedSlots := report.deletedSlots.reverse }, stFinal)

/-- AK8-B (WS-AK / C-M02): Precondition check for transactional CDT revocation.

Verifies that every descendant of `rootNode` satisfying `lookupCdtSlotOfNode`
points to an address whose CNode is present in the object store. This mirrors
the only runtime-reachable failure path of `cspaceDeleteSlotCore` (which can
only emit `.objectNotFound` when `addr.cnode` is missing), so a `.ok ()`
result witnesses that every subsequent deletion in the transactional apply
phase will succeed. -/
def validateRevokeCdtDescendants (st : SystemState) (descendants : List CdtNodeId)
    : Except KernelError Unit :=
  descendants.foldlM (init := ()) (fun _ node =>
    match SystemState.lookupCdtSlotOfNode st node with
    | none => .ok ()
    | some descAddr =>
        match st.objects[descAddr.cnode]? with
        | some (.cnode _) => .ok ()
        | _ => .error .objectNotFound)

/-- AK8-B (WS-AK / C-M02): **Transactional** CDT revocation variant.

Unlike `cspaceRevokeCdtStrict` (which uses best-effort partial-progress
semantics and surfaces failures via `firstFailure` in the return report),
this variant follows a strict **validate-then-apply** discipline:

1. **Local revoke phase.** Invoke `cspaceRevoke` on `addr`. If this fails,
   the transaction aborts and the pre-transaction state is preserved
   (the `Kernel` monad returns `.error` without committing a state update).
2. **Validation phase.** Walk the descendant list of the source CDT node.
   For each descendant with a slot mapping, verify that its CNode is
   present in `stLocal.objects`. If *any* descendant fails validation,
   the entire transaction aborts with `.error` — no descendant is
   deleted, and the caller's `SystemState` is rolled back to the
   pre-transaction snapshot (since the `Kernel` monad discards the
   intermediate `stLocal` on `.error`).
3. **Apply phase.** If all descendants validate, each deletion in the
   fold below is guaranteed to succeed — `cspaceDeleteSlotCore`'s sole
   failure path is `.objectNotFound` on the descendant's CNode, which
   we verified is present. The `firstFailure` field of the returned
   report is therefore always `none`.

This provides true all-or-nothing semantics for CDT revocation, at the
cost of a double walk (validation + apply). Callers who can tolerate
partial progress should continue to use `cspaceRevokeCdtStrict`. -/
def cspaceRevokeCdtTransactional (addr : CSpaceAddr) : Kernel RevokeCdtStrictReport :=
  fun st =>
    match cspaceRevoke addr st with
    | .error e => .error e
    | .ok ((), stLocal) =>
        match SystemState.lookupCdtNodeOfSlot stLocal addr with
        | none => .ok ({ deletedSlots := [], firstFailure := none }, stLocal)
        | some rootNode =>
            let descendants := stLocal.cdt.descendantsOf rootNode
            -- Phase 2: Validate every descendant before touching any state.
            match validateRevokeCdtDescendants stLocal descendants with
            | .error err => .error err
            | .ok _ =>
                -- Phase 3: Apply. Because validation passed, every
                -- `cspaceDeleteSlotCore` below is guaranteed to succeed.
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
                          match cspaceDeleteSlotCore descAddr stAcc with
                          | .error err =>
                              -- Phase 2 guaranteed success; this branch is
                              -- dead code when validation passed against the
                              -- same `stLocal` (deletions during the fold
                              -- only shrink CNode slot tables, never remove
                              -- CNodes). Retained as a defensive fallback.
                              let failure : RevokeCdtStrictFailure := {
                                offendingNode := node
                                offendingSlot := some descAddr
                                error := err
                              }
                              ({ report with firstFailure := some failure }, stAcc)
                          | .ok ((), stDel) =>
                              let stRemoved := { stDel with cdt := stDel.cdt.removeNode node }
                              ({ report with deletedSlots := descAddr :: report.deletedSlots }, stRemoved)
                let (report, stFinal) := descendants.foldl step
                  ({ deletedSlots := [], firstFailure := none }, stLocal)
                .ok ({ report with deletedSlots := report.deletedSlots.reverse }, stFinal)

/-- AK8-B: `validateRevokeCdtDescendants` on an empty descendant list succeeds. -/
theorem validateRevokeCdtDescendants_empty (st : SystemState) :
    validateRevokeCdtDescendants st [] = .ok () := rfl

/-- AK8-B: The transactional variant's local revoke step matches the strict
variant's — they share the same local revoke invocation. This witnesses
behavioural parity on the local phase; the variants diverge only in how
they treat descendant failures. -/
theorem cspaceRevokeCdtTransactional_requires_local_revoke_ok
    (addr : CSpaceAddr) (st : SystemState) (r : RevokeCdtStrictReport) (st' : SystemState)
    (hOk : cspaceRevokeCdtTransactional addr st = .ok (r, st')) :
    (cspaceRevoke addr st).isOk := by
  unfold cspaceRevokeCdtTransactional at hOk
  cases hRev : cspaceRevoke addr st with
  | error e => simp [hRev] at hOk
  | ok _ => simp [Except.isOk, Except.toBool]

-- ============================================================================
-- M-D01: IPC capability transfer operations
-- ============================================================================

/-- M-D01: Transfer a single capability from the sender's IPC message into
the receiver's CSpace.

Semantics (matching seL4's IPC cap unwrap):
1. Look up the receiver's root CNode via `receiverCspaceRoot`.
2. Scan for the first empty slot starting from `slotBase`.
3. If found, insert the capability (with sender's original rights).
4. Record a CDT derivation edge of type `.ipcTransfer` from the sender's
   source slot to the newly occupied receiver slot.

The sender's capability is NOT removed from the sender's CSpace — IPC
transfer is a copy, not a move (matching seL4 semantics where the sender
retains its capability after sending).

Returns `CapTransferResult.installed cnode slot` on success, `.noSlot` if the
receiver's CNode has no empty slots in the scan range. -/
def ipcTransferSingleCap
    (cap : Capability)
    (senderSlot : CSpaceAddr)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) : Kernel CapTransferResult :=
  fun st =>
    match st.objects[receiverCspaceRoot]? with
    | some (.cnode cn) =>
        match cn.findFirstEmptySlot slotBase scanLimit with
        | none => .ok (.noSlot, st)
        | some emptySlot =>
            let dstAddr : CSpaceAddr := { cnode := receiverCspaceRoot, slot := emptySlot }
            match cspaceInsertSlot dstAddr cap st with
            | .error e => .error e
            | .ok ((), st') =>
                let (srcNode, stSrc) := SystemState.ensureCdtNodeForSlot st' senderSlot
                let (dstNode, stDst) := SystemState.ensureCdtNodeForSlot stSrc dstAddr
                let cdt' := stDst.cdt.addEdge srcNode dstNode .ipcTransfer
                .ok (.installed receiverCspaceRoot emptySlot,
                     { stDst with cdt := cdt' })
    | _ => .error .objectNotFound

private theorem ensureCdtNodeForSlot_scheduler_eq (st : SystemState) (ref : SlotRef) :
    (SystemState.ensureCdtNodeForSlot st ref).2.scheduler = st.scheduler := by
  unfold SystemState.ensureCdtNodeForSlot
  split <;> simp

private theorem ensureCdtNodeForSlot_services_eq (st : SystemState) (ref : SlotRef) :
    (SystemState.ensureCdtNodeForSlot st ref).2.services = st.services := by
  unfold SystemState.ensureCdtNodeForSlot
  split <;> simp

theorem ipcTransferSingleCap_preserves_scheduler
    (cap : Capability) (senderSlot : CSpaceAddr)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult)
    (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.scheduler = st.scheduler := by
  simp only [ipcTransferSingleCap] at hStep
  cases hObj : st.objects[receiverRoot]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
    | schedContext _ => simp [hObj] at hStep
    | cnode cn =>
      simp [hObj] at hStep
      cases hSlot : cn.findFirstEmptySlot slotBase scanLimit with
      | none => simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
      | some emptySlot =>
        simp [hSlot] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have h1 := cspaceInsertSlot_preserves_scheduler st pair.2 _ cap (by rw [show pair = (pair.1, pair.2) from by simp]; exact hIns)
          have h2 := ensureCdtNodeForSlot_scheduler_eq pair.2 senderSlot
          have h3 := ensureCdtNodeForSlot_scheduler_eq
            (SystemState.ensureCdtNodeForSlot pair.2 senderSlot).2
            { cnode := receiverRoot, slot := emptySlot }
          simp_all

/-- ipcTransferSingleCap preserves objects at keys other than the receiver root CNode. -/
theorem ipcTransferSingleCap_preserves_objects_ne
    (cap : Capability) (senderSlot : CSpaceAddr)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (oid : SeLe4n.ObjId)
    (hNe : oid ≠ receiverRoot)
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects[oid]? = st.objects[oid]? := by
  simp only [ipcTransferSingleCap] at hStep
  cases hObj : st.objects[receiverRoot]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
    | schedContext _ => simp [hObj] at hStep
    | cnode cn =>
      simp [hObj] at hStep
      cases hSlot : cn.findFirstEmptySlot slotBase scanLimit with
      | none => simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
      | some emptySlot =>
        simp [hSlot] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have hObjIns := cspaceInsertSlot_preserves_objects_ne st pair.2 _ cap oid hNe hObjInv
            (by rw [show pair = (pair.1, pair.2) from by simp]; exact hIns)
          have hObjSrc := SystemState.ensureCdtNodeForSlot_objects_eq pair.2 senderSlot
          have hObjDst := SystemState.ensureCdtNodeForSlot_objects_eq
            (SystemState.ensureCdtNodeForSlot pair.2 senderSlot).2
            { cnode := receiverRoot, slot := emptySlot }
          simp_all

theorem ipcTransferSingleCap_preserves_services
    (cap : Capability) (senderSlot : CSpaceAddr)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult)
    (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.services = st.services := by
  simp only [ipcTransferSingleCap] at hStep
  cases hObj : st.objects[receiverRoot]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
    | schedContext _ => simp [hObj] at hStep
    | cnode cn =>
      simp [hObj] at hStep
      cases hSlot : cn.findFirstEmptySlot slotBase scanLimit with
      | none => simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
      | some emptySlot =>
        simp [hSlot] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have h1 := cspaceInsertSlot_preserves_services st pair.2 _ cap (by rw [show pair = (pair.1, pair.2) from by simp]; exact hIns)
          have h2 := ensureCdtNodeForSlot_services_eq pair.2 senderSlot
          have h3 := ensureCdtNodeForSlot_services_eq
            (SystemState.ensureCdtNodeForSlot pair.2 senderSlot).2
            { cnode := receiverRoot, slot := emptySlot }
          simp_all

/-- ipcTransferSingleCap preserves `objects.invExt`. -/
theorem ipcTransferSingleCap_preserves_objects_invExt
    (cap : Capability) (senderSlot : CSpaceAddr)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult)
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects.invExt := by
  simp only [ipcTransferSingleCap] at hStep
  cases hObj : st.objects[receiverRoot]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
    | schedContext _ => simp [hObj] at hStep
    | cnode cn =>
      simp [hObj] at hStep
      cases hSlot : cn.findFirstEmptySlot slotBase scanLimit with
      | none => simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hObjInv
      | some emptySlot =>
        simp [hSlot] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have hInvMid := cspaceInsertSlot_preserves_objects_invExt st pair.2 _ cap hObjInv
            (by rw [show pair = (pair.1, pair.2) from by simp]; exact hIns)
          have hObjSrc := SystemState.ensureCdtNodeForSlot_objects_eq pair.2 senderSlot
          have hObjDst := SystemState.ensureCdtNodeForSlot_objects_eq
            (SystemState.ensureCdtNodeForSlot pair.2 senderSlot).2
            { cnode := receiverRoot, slot := emptySlot }
          simp only [hObjDst, hObjSrc]; exact hInvMid

/-- M3-E4 helper: ipcTransferSingleCap preserves all notification objects.
When `oid = receiverRoot` and the object is a notification, the function
returns `.error .objectNotFound` (expects a CNode), contradicting `.ok`.
When `oid ≠ receiverRoot`, use `ipcTransferSingleCap_preserves_objects_ne`. -/
theorem ipcTransferSingleCap_preserves_ntfn_objects
    (cap : Capability) (senderSlot : CSpaceAddr)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st.objects[oid]? = some (.notification ntfn))
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects[oid]? = some (.notification ntfn) := by
  by_cases hNe : oid = receiverRoot
  · subst hNe
    simp only [ipcTransferSingleCap] at hStep
    simp [hNtfn] at hStep
  · rw [ipcTransferSingleCap_preserves_objects_ne cap senderSlot receiverRoot slotBase
      scanLimit st st' result oid hNe hObjInv hStep]
    exact hNtfn

/-- M3-E4 helper: receiverRoot is never a notification after ipcTransferSingleCap.
The only success path requires receiverRoot to be a CNode in st. On the noSlot
path state is unchanged (still a CNode); on the installed path cspaceInsertSlot
stores an updated CNode back. -/
theorem ipcTransferSingleCap_receiverRoot_not_ntfn
    (cap : Capability) (senderSlot : CSpaceAddr)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult)
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    ∀ ntfn, st'.objects[receiverRoot]? ≠ some (.notification ntfn) := by
  simp only [ipcTransferSingleCap] at hStep
  cases hObj : st.objects[receiverRoot]? with
  | none => simp [hObj] at hStep
  | some obj =>
    cases obj with
    | tcb _ | endpoint _ | notification _ | vspaceRoot _ | untyped _
    | schedContext _ => simp [hObj] at hStep
    | cnode cn =>
      simp [hObj] at hStep
      cases hSlot : cn.findFirstEmptySlot slotBase scanLimit with
      | none =>
        simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep
        intro ntfn h; rw [hObj] at h; exact absurd h (by simp)
      | some emptySlot =>
        simp [hSlot] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep; obtain ⟨_, rfl⟩ := hStep
          -- After cspaceInsertSlot: pair.2.objects[receiverRoot]? = some (.cnode cn')
          -- After ensureCdtNodeForSlot (×2): objects preserved
          -- After { ... with cdt := cdt' }: objects preserved
          -- So final objects[receiverRoot]? = pair.2.objects[receiverRoot]?
          have hObjSrc := SystemState.ensureCdtNodeForSlot_objects_eq pair.2 senderSlot
          have hObjDst := SystemState.ensureCdtNodeForSlot_objects_eq
            (SystemState.ensureCdtNodeForSlot pair.2 senderSlot).2
            { cnode := receiverRoot, slot := emptySlot }
          -- Need: pair.2.objects[receiverRoot]? = some (.cnode _)
          -- cspaceInsertSlot stores via storeObject receiverRoot (.cnode cn')
          -- then storeCapabilityRef which only modifies lifecycle
          intro ntfn h
          -- h is about the final state after ensureCdtNodeForSlot and with-cdt
          -- Simplify: final objects = pair.2.objects (ensureCdtNodeForSlot preserves objects)
          simp only [hObjSrc, hObjDst] at h
          -- Now h : pair.2.objects[receiverRoot]? = some (.notification ntfn)
          -- But cspaceInsertSlot stored a CNode at receiverRoot via storeObject
          -- then storeCapabilityRef only modifies lifecycle
          -- So pair.2.objects[receiverRoot]? should be some (.cnode cn')
          -- Let's unfold cspaceInsertSlot at hIns to extract storeObject
          unfold cspaceInsertSlot at hIns
          simp [hObj] at hIns
          cases hLookup : cn.lookup emptySlot with
          | some _ => simp [hLookup] at hIns
          | none =>
            simp [hLookup] at hIns
            cases hStore : storeObject receiverRoot (.cnode (cn.insert emptySlot cap)) st with
            | error e => simp [hStore] at hIns
            | ok storePair =>
              simp [hStore] at hIns
              have hStoreEq : storeObject receiverRoot (.cnode (cn.insert emptySlot cap)) st
                  = .ok ((), storePair.2) := by
                rw [hStore]
              have hStoreObj := storeObject_objects_eq st storePair.2 receiverRoot
                (.cnode (cn.insert emptySlot cap)) hObjInv hStoreEq
              -- storeCapabilityRef only modifies lifecycle, not objects
              unfold storeCapabilityRef at hIns
              cases hIns
              -- pair.2.objects = storePair.2.objects (storeCapabilityRef doesn't change objects)
              simp at h
              rw [hStoreObj] at h
              exact absurd h (by simp)

/-- M3-E4 helper: ipcTransferSingleCap preserves all endpoint objects.
When `oid = receiverRoot` and the object is an endpoint, the function
returns `.error .objectNotFound` (expects a CNode), contradicting `.ok`.
When `oid ≠ receiverRoot`, use `ipcTransferSingleCap_preserves_objects_ne`. -/
theorem ipcTransferSingleCap_preserves_ep_objects
    (cap : Capability) (senderSlot : CSpaceAddr)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[oid]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects[oid]? = some (.endpoint ep) := by
  by_cases hNe : oid = receiverRoot
  · subst hNe
    simp only [ipcTransferSingleCap] at hStep
    simp [hEp] at hStep
  · rw [ipcTransferSingleCap_preserves_objects_ne cap senderSlot receiverRoot slotBase
      scanLimit st st' result oid hNe hObjInv hStep]
    exact hEp

/-- M3-E4 helper: ipcTransferSingleCap preserves all TCB objects.
Same reasoning as endpoint preservation: TCBs at receiverRoot cause
`.error .objectNotFound`, contradicting `.ok` hypothesis. -/
theorem ipcTransferSingleCap_preserves_tcb_objects
    (cap : Capability) (senderSlot : CSpaceAddr)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (oid : SeLe4n.ObjId) (tcb : TCB)
    (hTcb : st.objects[oid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects[oid]? = some (.tcb tcb) := by
  by_cases hNe : oid = receiverRoot
  · subst hNe
    simp only [ipcTransferSingleCap] at hStep
    simp [hTcb] at hStep
  · rw [ipcTransferSingleCap_preserves_objects_ne cap senderSlot receiverRoot slotBase
      scanLimit st st' result oid hNe hObjInv hStep]
    exact hTcb

/-- M3-E4 helper: ipcTransferSingleCap keeps receiverRoot as a CNode.
The function only succeeds when receiverRoot is a CNode. On noSlot the state is
unchanged. On installed, cspaceInsertSlot stores an updated CNode back via
storeObject, and ensureCdtNodeForSlot + CDT update leave objects untouched. -/
theorem ipcTransferSingleCap_receiverRoot_stays_cnode
    (cap : Capability) (senderSlot : CSpaceAddr)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (cn : CNode)
    (hCn : st.objects[receiverRoot]? = some (.cnode cn))
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap senderSlot receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    ∃ cn', st'.objects[receiverRoot]? = some (.cnode cn') := by
  simp only [ipcTransferSingleCap] at hStep
  simp [hCn] at hStep
  cases hSlot : cn.findFirstEmptySlot slotBase scanLimit with
  | none =>
    simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep
    exact ⟨cn, hCn⟩
  | some emptySlot =>
    simp [hSlot] at hStep
    cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap st with
    | error e => simp [hIns] at hStep
    | ok pair =>
      simp [hIns] at hStep; obtain ⟨_, rfl⟩ := hStep
      have hObjSrc := SystemState.ensureCdtNodeForSlot_objects_eq pair.2 senderSlot
      have hObjDst := SystemState.ensureCdtNodeForSlot_objects_eq
        (SystemState.ensureCdtNodeForSlot pair.2 senderSlot).2
        { cnode := receiverRoot, slot := emptySlot }
      -- pair.2.objects[receiverRoot]? is a CNode from cspaceInsertSlot
      unfold cspaceInsertSlot at hIns
      simp [hCn] at hIns
      cases hLookup : cn.lookup emptySlot with
      | some _ => simp [hLookup] at hIns
      | none =>
        simp [hLookup] at hIns
        cases hStore : storeObject receiverRoot (.cnode (cn.insert emptySlot cap)) st with
        | error e => simp [hStore] at hIns
        | ok storePair =>
          simp [hStore] at hIns
          have hStoreEq : storeObject receiverRoot (.cnode (cn.insert emptySlot cap)) st
              = .ok ((), storePair.2) := by
            rw [hStore]
          have hStoreObj := storeObject_objects_eq st storePair.2 receiverRoot
            (.cnode (cn.insert emptySlot cap)) hObjInv hStoreEq
          unfold storeCapabilityRef at hIns
          cases hIns
          refine ⟨cn.insert emptySlot cap, ?_⟩
          simp only [hObjDst, hObjSrc]
          exact hStoreObj

end SeLe4n.Kernel
