-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Invariant
import SeLe4n.Model.SlotLinks

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
  here as a post-1.0 hardening candidate, registered in the *Registered
  debt index* (table C.1) in `docs/REGISTERED_DEBT.md`, row 32.
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
- **C-L10 (`cspaceDeleteSlotCore` dangling CDT edges):** resolved.  The core
  delete leaves the tree to its caller, and every caller takes the slot out
  of it: the delete splices it out (`spliceDeletedCdtNode`, since `v0.36.101`),
  revocation removes it (`processRevokeNode`), and a move hands its edges to
  the destination (`CapDerivationTree.moveNode`). -/

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

/-- Lookup a capability at `(cnode, slot)` with typed CNode checking.

AN10 residual closure (R1): the absent-arm is migrated to the `getCNode?`
typed helper. Semantically equivalent — `getCNode?` returns `none` for
both wrong-variant and absent, collapsing into the original
`.objectNotFound` arm; `getCNode? = some _` matches the original
`.cnode _` arm exactly. -/
def cspaceLookupSlot (addr : CSpaceAddr) : Kernel Capability :=
  fun st =>
    match SystemState.lookupSlotCap st addr with
    | some cap => .ok (cap, st)
    | none =>
        match st.getCNode? addr.cnode with
        | some _ => .error .invalidCapability
        | none   => .error .objectNotFound

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
    -- AN10-residual (R2): typed-helper migration. `getCNode?` returns
    -- `none` for both wrong-variant and absent, collapsing into the
    -- original catch-all `_` arm that yielded `.objectNotFound`.
    match st.getCNode? addr.cnode with
    | some cn =>
        match cn.resolveSlot addr.cptr addr.depth with
        | .ok slot => .ok ({ cnode := addr.cnode, slot := slot }, st)
        | .error .depthMismatch => .error .illegalState
        | .error .guardMismatch => .error .invalidCapability
    | none => .error .objectNotFound

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
    -- AN10-residual (R3): typed-helper migration. Termination metric
    -- is `bitsRemaining` (Nat-strict descent), unaffected by the lookup
    -- shape.
    match st.getCNode? rootId with
    | some cn =>
      let consumed := cn.guardWidth + cn.radixWidth
      if hCons : consumed = 0 then .error .illegalState  -- zero-width CNode
      else if bitsRemaining < consumed then .error .illegalState
      else
        -- The slot index and guard are bit fields of the address word, as in
        -- CNode.resolveSlot (S4-C); compiled, they shift and mask the word
        -- (`CPtr.slotBits_eq_impl`, WS-ZA ZA4.8).
        let slotIndex := addr.slotBits (bitsRemaining - consumed) cn.radixWidth
        let guardExtracted := addr.guardBits (bitsRemaining - consumed) cn.radixWidth cn.guardWidth
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
    | none => .error .objectNotFound
  termination_by bitsRemaining

/-- WS-H13: Lookup a capability via multi-level CSpace resolution.
Composes `resolveCapAddress` with slot lookup.

**AN4-D (H-05) — SMP precondition (Theme 4.4 single-core inventory).**
This function calls `resolveCapAddress` to walk to a concrete `SlotRef`,
then `cspaceLookupSlot` to dereference it. Between those two calls the
implementation assumes the resolved CNode still backs a `.cnode` variant
in the object store (`resolvedCnodeStillValid` below). On a single core
this precondition holds unconditionally because the kernel is non-preemptible
during the dispatch critical section — no other thread can retype the
resolved CNode between the resolve and the dereference. On SMP (deferred to
AN9-J), the same predicate becomes a critical-section obligation the
caller must enforce with an interrupt-disable bracket on the dispatch
path (AN9-D). `cspaceLookupSlot` additionally fails closed with
`.invalidCapability` / `.objectNotFound` if the CNode has actually been
retyped, so the behaviour degrades gracefully rather than unsoundly. -/
def cspaceLookupMultiLevel (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bitsRemaining : Nat) : Kernel Capability :=
  fun st =>
    match resolveCapAddress rootId addr bitsRemaining st with
    | .ok ref => cspaceLookupSlot ref st
    | .error e => .error e

/-- AN4-D (H-05): SMP precondition captured as a Prop on a resolved
`SlotRef`. On a single core this is discharged unconditionally by
`resolvedCnodeStillValid_singleCore` (proven below, after the underlying
`resolveCapAddress_result_valid_cnode` structural lemma is available);
on SMP it becomes a critical-section obligation. -/
def resolvedCnodeStillValid (st : SystemState) (resolvedRef : SlotRef) : Prop :=
  ∃ cn, st.objects[resolvedRef.cnode]? = some (.cnode cn)

-- ============================================================================
-- WS-H13/H-01: resolveCapAddress theorems
-- ============================================================================

/-- **WS-RR RR7.3**: `resolveCapAddress` reads the object store and nothing
else, so two states with the same store resolve identically.

The CSpace walk consults `st.getCNode?` at every hop and no other component of
`SystemState`.  Stated as a congruence rather than left implicit because the
live syscall entry resolves against a state its own decode has *pre-processed*
(`tlbFillIpcBufferOnCore`, which touches only the per-core TLB view), and the
guarantee a reader wants is about the state the caller trapped in.  Without
this the entry-point theorem could only speak of the filled state.

Proved by the walk's own functional induction, so the recursion's descent is
the induction's and no separate termination argument is needed. -/
theorem resolveCapAddress_congr_objects
    (st₁ st₂ : SystemState) (hObjects : st₁.objects = st₂.objects)
    (addr : SeLe4n.CPtr) :
    ∀ (bitsRemaining : Nat) (rootId : SeLe4n.ObjId),
      resolveCapAddress rootId addr bitsRemaining st₁
        = resolveCapAddress rootId addr bitsRemaining st₂ := by
  intro bitsRemaining
  induction bitsRemaining using Nat.strongRecOn with
  | _ bits ih =>
    intro rootId
    have hCNode : st₁.getCNode? rootId = st₂.getCNode? rootId := by
      simp only [SystemState.getCNode?, hObjects]
    rw [resolveCapAddress, resolveCapAddress, hCNode]
    -- Both sides are now the same expression apart from the state the
    -- recursive call carries, so every branch closes by `rfl` and the one
    -- descending branch by the induction hypothesis.
    repeat' (first | split | (simp only []; split))
    all_goals first
      | rfl
      | (exact ih _ (by omega) _)

/-- **WS-RR RR7.3**: `lookupSlotCap` reads the object store and nothing else. -/
theorem lookupSlotCap_congr_objects
    (st₁ st₂ : SystemState) (ref : SlotRef)
    (hObjects : st₁.objects = st₂.objects) :
    SystemState.lookupSlotCap st₁ ref = SystemState.lookupSlotCap st₂ ref := by
  simp only [SystemState.lookupSlotCap, SystemState.lookupCNode, hObjects]

/-- `resolveCapAddress` in continuation form: the refusal goes to `onErr` and
the resolved slot's CNode and index to `onOk`, so a caller that matches the
result at once builds neither the `Except` nor the `SlotRef`
(`resolveCapAddressK_eq`).  WS-ZA ZA2.5. -/
@[specialize] def resolveCapAddressK {α : Type} (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState)
    (onErr : KernelError → α) (onOk : SeLe4n.ObjId → SeLe4n.Slot → α) : α :=
  if hZero : bitsRemaining = 0 then onErr .illegalState
  else
    match st.getCNode? rootId with
    | some cn =>
      let consumed := cn.guardWidth + cn.radixWidth
      if hCons : consumed = 0 then onErr .illegalState
      else if bitsRemaining < consumed then onErr .illegalState
      else
        let slotIndex := addr.slotBits (bitsRemaining - consumed) cn.radixWidth
        let guardExtracted := addr.guardBits (bitsRemaining - consumed) cn.radixWidth cn.guardWidth
        if guardExtracted ≠ cn.guardValue then onErr .invalidCapability
        else
          let slot := SeLe4n.Slot.ofNat slotIndex
          if bitsRemaining - consumed = 0 then onOk rootId slot
          else
            match cn.lookup slot with
            | some cap =>
              match cap.target with
              | .object childId =>
                have hConsPos : consumed > 0 := Nat.pos_of_ne_zero hCons
                have hBitsPos : bitsRemaining > 0 := Nat.pos_of_ne_zero hZero
                have : bitsRemaining - consumed < bitsRemaining := Nat.sub_lt hBitsPos hConsPos
                resolveCapAddressK childId addr (bitsRemaining - consumed) st onErr onOk
              | _ => onErr .invalidCapability
            | none => onErr .invalidCapability
    | none => onErr .objectNotFound
  termination_by bitsRemaining

theorem resolveCapAddressK_eq {α : Type} (addr : SeLe4n.CPtr) (st : SystemState)
    (onErr : KernelError → α) (onOk : SeLe4n.ObjId → SeLe4n.Slot → α) :
    ∀ (bitsRemaining : Nat) (rootId : SeLe4n.ObjId),
      resolveCapAddressK rootId addr bitsRemaining st onErr onOk =
        match resolveCapAddress rootId addr bitsRemaining st with
        | .error e => onErr e
        | .ok ref => onOk ref.cnode ref.slot := by
  intro bitsRemaining
  induction bitsRemaining using Nat.strongRecOn with
  | _ bits ih =>
    intro rootId
    rw [resolveCapAddressK, resolveCapAddress]
    by_cases hZero : bits = 0
    · simp only [hZero, ↓reduceDIte]
    · simp only [hZero, ↓reduceDIte]
      cases st.getCNode? rootId with
      | none => rfl
      | some cn =>
        by_cases hCons : cn.guardWidth + cn.radixWidth = 0
        · simp only [hCons, ↓reduceDIte]
        · simp only [hCons, ↓reduceDIte]
          by_cases hLt : bits < cn.guardWidth + cn.radixWidth
          · simp only [hLt, ↓reduceIte]
          · simp only [hLt, ↓reduceIte]
            split
            · rfl
            · split
              · rfl
              · cases cn.lookup _ with
                | none => rfl
                | some cap =>
                  simp only []
                  cases cap.target with
                  | object childId => exact ih _ (by omega) _
                  | _ => rfl

/-- `resolveCapAddressK` with its first level unrolled: a CSpace whose root
resolves the whole address (one level, the common case) reaches `onOk` in the
caller's own body, so a caller that inlines it keeps its continuations' results
unboxed; only a deeper CSpace calls the recursive `resolveCapAddress`, whose
`Except` is matched here, so no continuation is ever captured as a closure
(`resolveCapAddressKUnrolled_eq`).  WS-ZA. -/
@[inline] def resolveCapAddressKUnrolled {α : Type} (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState)
    (onErr : KernelError → α) (onOk : SeLe4n.ObjId → SeLe4n.Slot → α) : α :=
  if bitsRemaining = 0 then onErr .illegalState
  else
    match st.getCNode? rootId with
    | some cn =>
      let consumed := cn.guardWidth + cn.radixWidth
      if consumed = 0 then onErr .illegalState
      else if bitsRemaining < consumed then onErr .illegalState
      else
        let slotIndex := addr.slotBits (bitsRemaining - consumed) cn.radixWidth
        let guardExtracted := addr.guardBits (bitsRemaining - consumed) cn.radixWidth cn.guardWidth
        if guardExtracted ≠ cn.guardValue then onErr .invalidCapability
        else
          let slot := SeLe4n.Slot.ofNat slotIndex
          if bitsRemaining - consumed = 0 then onOk rootId slot
          else
            match cn.lookup slot with
            | some cap =>
              match cap.target with
              | .object childId =>
                match resolveCapAddress childId addr (bitsRemaining - consumed) st with
                | .error e => onErr e
                | .ok ref => onOk ref.cnode ref.slot
              | _ => onErr .invalidCapability
            | none => onErr .invalidCapability
    | none => onErr .objectNotFound

theorem resolveCapAddressKUnrolled_eq {α : Type} (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr)
    (bitsRemaining : Nat) (st : SystemState)
    (onErr : KernelError → α) (onOk : SeLe4n.ObjId → SeLe4n.Slot → α) :
    resolveCapAddressKUnrolled rootId addr bitsRemaining st onErr onOk =
      resolveCapAddressK rootId addr bitsRemaining st onErr onOk := by
  rw [resolveCapAddressK]
  unfold resolveCapAddressKUnrolled
  simp only [← resolveCapAddressK_eq]
  by_cases hZero : bitsRemaining = 0
  · simp only [hZero, ↓reduceIte, ↓reduceDIte]
  · simp only [hZero, ↓reduceIte, ↓reduceDIte]
    cases st.getCNode? rootId with
    | none => rfl
    | some cn =>
      by_cases hCons : cn.guardWidth + cn.radixWidth = 0
      · simp only [hCons, ↓reduceIte, ↓reduceDIte]
      · simp only [hCons, ↓reduceIte, ↓reduceDIte]

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
dereferencing the resolved slot.

**AN4-F.1 (CAP-M01)**: typed `DocumentedObligation` (a marker constant,
not a vacuous Prop). Search the codebase for `: DocumentedObligation` to
enumerate every such caller contract. -/
def resolveCapAddress_caller_rights_obligation : DocumentedObligation := .recorded

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
                -- AN10-residual (R3): bridge typed-helper hypothesis to raw form.
                simp at hOk; cases hOk
                exact ⟨cn, (SystemState.getCNode?_eq_some_iff st rootId cn).mp hObj⟩
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

/-- AN4-D (H-05): On the single-core kernel, `resolveCapAddress` succeeding
with a `SlotRef` immediately establishes `resolvedCnodeStillValid` for the
same state — the object store cannot have changed between the resolve and
the dereference because the dispatch path is non-preemptible. This is the
first formalised entry in the AN12-B SMP inventory (Theme 4.4): the
hypothesis is discharged right at the resolve site, so
`cspaceLookupMultiLevel` never observes a violation on single core.
Under SMP (deferred to AN9-D/AN9-J), the same predicate is re-established
by the interrupt-disable bracket around each dispatch invocation. -/
theorem resolvedCnodeStillValid_singleCore
    (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bits : Nat) (st : SystemState)
    (ref : SlotRef)
    (hOk : resolveCapAddress rootId addr bits st = .ok ref) :
    resolvedCnodeStillValid st ref :=
  resolveCapAddress_result_valid_cnode rootId addr bits st ref hOk

/-- AN4-D (H-05): Defense-in-depth structural reject witness. If an SMP
race retyped the resolved CNode between `resolveCapAddress` returning and
`cspaceLookupMultiLevel` completing, the composite operation would fail
closed via `cspaceLookupSlot`'s kind check rather than return an unsound
capability. This theorem anchors that fail-closed guarantee at the type
level: any successful composite lookup witnesses the
`resolvedCnodeStillValid` precondition at the observed state. -/
theorem cspaceLookupMultiLevel_fails_closed_on_missing_cnode
    (rootId : SeLe4n.ObjId) (addr : SeLe4n.CPtr) (bits : Nat) (st : SystemState)
    (ref : SlotRef)
    (cap : Capability) (st' : SystemState)
    (hOk : resolveCapAddress rootId addr bits st = .ok ref)
    (_hStep : cspaceLookupMultiLevel rootId addr bits st = .ok (cap, st')) :
    resolvedCnodeStillValid st ref :=
  -- In the current single-core model the discharge is identical to the
  -- resolve-site witness (the object store does not change between the
  -- two lookup calls). The theorem is factored separately so AN9-D can
  -- generalise it under SMP, where the hStep hypothesis rules out the
  -- racy interleaving that would otherwise invalidate the predicate.
  resolvedCnodeStillValid_singleCore rootId addr bits st ref hOk

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
      addr.guardBits (bits - (cn.guardWidth + cn.radixWidth)) cn.radixWidth cn.guardWidth ≠
        cn.guardValue) :
    resolveCapAddress rootId addr bits st = .error .invalidCapability := by
  -- AN10-residual (R3): bridge raw-form hypothesis to typed-helper form.
  have hCN : st.getCNode? rootId = some cn :=
    (SystemState.getCNode?_eq_some_iff st rootId cn).mpr hObj
  unfold resolveCapAddress
  have hNZ : bits ≠ 0 := by omega
  simp only [hNZ, ↓reduceDIte, hCN]
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
    addr.guardBits (bits - (cn.guardWidth + cn.radixWidth)) cn.radixWidth cn.guardWidth =
      cn.guardValue := by
  -- AN10-residual (R3): bridge the raw-form hypothesis to the typed-helper
  -- form so the simp set still collapses the inner match.
  have hCN : st.getCNode? rootId = some cn :=
    (SystemState.getCNode?_eq_some_iff st rootId cn).mpr hObj
  -- Unfold and trace through the function structure
  unfold resolveCapAddress at hOk
  have hNZ : bits ≠ 0 := by intro h; subst h; simp at hOk
  simp only [hNZ, ↓reduceDIte, hCN] at hOk
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
    match st.getCNode? addr.cnode with
    | some cn =>
        -- **WS-RR RR8.16** (`v0.35.201`): the destination index must be one this
        -- CNode can *address*.  `resolveSlot` extracts a slot by masking with
        -- `2 ^ radixWidth`, so an index at or above `slotCount` can be stored
        -- and can never be reached by any CPtr — and `CNode.insert` at a fresh
        -- key grows the slot table, so without this check a holder of a copy- or
        -- mint-bearing capability grows a *fixed-size* kernel object without
        -- bound and falsifies `cspaceSlotCountBounded`.
        --
        -- The check is here, and only here, because this is the one primitive
        -- all four installs pass through — `cspaceCopy`, `cspaceMint`,
        -- `cspaceMove` (each taking `dstSlot` verbatim from a message register)
        -- and `ipcTransferSingleCap`.  *The creator is exactly one function*,
        -- which is the reasoning `ipcTransferSingleCap` already records for the
        -- revocation window; checking at each caller is what let this through.
        if !cn.slotAddressable addr.slot then .error .invalidArgument
        else
          match cn.lookup addr.slot with
          | some _ => .error .targetSlotOccupied  -- H-02: reject occupied slot
          | none =>
              let cn' := cn.insert addr.slot cap
              storeObject addr.cnode (.cnode cn') st
    | none => .error .objectNotFound

/-- **WS-RR RR8.16** (`v0.35.201`): **what a successful insert consists of.**

One description of the operation, so every frame over it is a citation rather
than a re-run of its `match` tree — and so the range guard is threaded once
rather than at each of the six frames below, and at the eight further sites
across the capability, information-flow and IPC invariant surfaces that split on
the lookup themselves.  The pattern is
`returnDonatedSchedContext_ok_storeChain`'s, at a much smaller operation. -/
theorem cspaceInsertSlot_ok_decompose
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    ∃ cn, st.getCNode? addr.cnode = some cn
      ∧ cn.slotAddressable addr.slot = true
      ∧ cn.lookup addr.slot = none
      ∧ storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st = .ok ((), st') := by
  unfold cspaceInsertSlot at hStep
  cases hCn : st.getCNode? addr.cnode with
  | none => rw [hCn] at hStep; cases hStep
  | some cn =>
      rw [hCn] at hStep
      simp only at hStep
      by_cases hAddr : cn.slotAddressable addr.slot = true
      · rw [hAddr] at hStep
        simp only [Bool.not_true, Bool.false_eq_true, if_false] at hStep
        cases hLk : cn.lookup addr.slot with
        | some _ => rw [hLk] at hStep; cases hStep
        | none =>
            rw [hLk] at hStep
            exact ⟨cn, rfl, hAddr, hLk, hStep⟩
      · simp only [Bool.not_eq_true] at hAddr
        rw [hAddr] at hStep
        simp only [Bool.not_false, if_true] at hStep
        cases hStep

/-- **WS-RR RR8.16** (`v0.35.201`): the guard is the refusal, stated so a caller
can see what it costs — an out-of-range destination is `.invalidArgument`, never
an install. -/
theorem cspaceInsertSlot_rejects_unaddressable_slot
    (st : SystemState) (addr : CSpaceAddr) (cap : Capability) (cn : CNode)
    (hObj : st.objects[addr.cnode]? = some (.cnode cn))
    (hAddr : cn.slotAddressable addr.slot = false) :
    cspaceInsertSlot addr cap st = .error .invalidArgument := by
  unfold cspaceInsertSlot SystemState.getCNode?
  simp [hObj, hAddr]

theorem cspaceInsertSlot_preserves_scheduler
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  obtain ⟨cn, _, _, _, hStore⟩ :=
    cspaceInsertSlot_ok_decompose st st' addr cap hStep
  exact storeObject_scheduler_eq _ _ _ _ hStore

theorem cspaceInsertSlot_preserves_services
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.services = st.services := by
  obtain ⟨cn, _, _, _, hStore⟩ :=
    cspaceInsertSlot_ok_decompose st st' addr cap hStep
  exact storeObject_preserves_services _ _ _ _ hStore

theorem cspaceInsertSlot_preserves_objects_ne
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (oid : SeLe4n.ObjId)
    (hNe : oid ≠ addr.cnode)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? := by
  obtain ⟨cn, _, _, _, hStore⟩ :=
    cspaceInsertSlot_ok_decompose st st' addr cap hStep
  exact storeObject_objects_ne _ _ _ _ _ hNe hObjInv hStore

/-- **WS-RR RR8.16** (`v0.35.201`): ...and the CNode it names holds the
capability afterwards — the "at the key" half of the frame whose "every other
key" half sits above.  The IPC dispatch surface had its own `private` copy of
this, which is a second reading of what a successful insert leaves behind. -/
theorem cspaceInsertSlot_objects_eq
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    ∃ cn : CNode, st.objects[addr.cnode]? = some (.cnode cn)
      ∧ st'.objects[addr.cnode]? = some (.cnode (cn.insert addr.slot cap)) := by
  obtain ⟨cn, hCnOpt, _, _, hStore⟩ :=
    cspaceInsertSlot_ok_decompose st st' addr cap hStep
  exact ⟨cn, (SystemState.getCNode?_eq_some_iff st addr.cnode cn).mp hCnOpt,
    storeObject_objects_eq _ _ _ _ hObjInv hStore⟩

/-- `cspaceInsertSlot` preserves `objects.invExt`. -/
theorem cspaceInsertSlot_preserves_objects_invExt
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hObjInv : st.objects.invExt)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.objects.invExt := by
  obtain ⟨cn, _, _, _, hStore⟩ :=
    cspaceInsertSlot_ok_decompose st st' addr cap hStep
  exact storeObject_preserves_objects_invExt _ _ _ _ hObjInv hStore

/-- `cspaceInsertSlot` preserves machine state. -/
theorem cspaceInsertSlot_preserves_machine
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.machine = st.machine := by
  obtain ⟨cn, _, _, _, hStore⟩ :=
    cspaceInsertSlot_ok_decompose st st' addr cap hStep
  exact storeObject_machine_eq _ _ _ _ hStore

/-- WS-E4/C-03: `cspaceInsertSlot` preserves the CDT — it only calls
`storeObject`, which touches objects, the lifecycle table and the object index
and nothing else.

Relocated here at `v0.35.201` from `Capability/Invariant/Preservation/Insert.lean`:
a *frame over a primitive* belongs beside the primitive, so the CDT pair reads like the scheduler, services,
machine and IRQ frames above rather than like an invariant argument. -/
theorem cspaceInsertSlot_cdt_eq
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.cdt = st.cdt := by
  obtain ⟨cn, _, _, _, hStore⟩ :=
    cspaceInsertSlot_ok_decompose st st' addr cap hStep
  exact storeObject_cdt_eq _ _ _ _ hStore

/-- WS-F3: `cspaceInsertSlot` preserves IRQ handler mappings. -/
theorem cspaceInsertSlot_preserves_irqHandlers
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  obtain ⟨cn, _, _, _, hStore⟩ :=
    cspaceInsertSlot_ok_decompose st st' addr cap hStep
  exact storeObject_irqHandlers_eq _ _ _ _ hStore

/-- WS-E4/H-02: `cspaceInsertSlot` rejects occupied slots. -/
theorem cspaceInsertSlot_rejects_occupied_slot
    (st : SystemState) (addr : CSpaceAddr) (cap existingCap : Capability)
    (cn : CNode)
    (hObj : st.objects[addr.cnode]? = some (.cnode cn))
    (hAddr : cn.slotAddressable addr.slot = true)
    (hOccupied : cn.lookup addr.slot = some existingCap) :
    cspaceInsertSlot addr cap st = .error .targetSlotOccupied := by
  unfold cspaceInsertSlot SystemState.getCNode?
  simp [hObj, hAddr, hOccupied]

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
        -- AN10-residual (R1): destructure on the typed helper to match
        -- the migrated outer match shape.
        cases hCN : st.getCNode? addr.cnode with
        | none => simp [hLookup, hCN] at hOk
        | some _ => simp [hLookup, hCN] at hOk
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

**WS-AL AL1b (cascades AK7-I) — Type-level non-null discipline**: the
`parent` parameter has type `NonNullCap`, not `Capability`. The Lean
type system forbids any caller from feeding a null cap into this
function — construction of a `NonNullCap` requires the caller to
produce a `cap.isNull = false` witness via `Capability.toNonNull?`
(the `none` branch forces the caller to emit
`KernelError.nullCapability` and short-circuit). The raw `Capability`
field accessors are reached via `parent.val.<field>`.

**AN4-E (H-06) — Fail-closed on null-valued outputs.** The function copies
the parent's target verbatim and attenuates rights. A subtle corner case
exists: if the parent's target is a reserved/sentinel `ObjId` **and** the
caller requested empty rights (a valid subset), the minted child would
match `Capability.isNull`'s pattern (reserved object + empty rights bits).
Left unchecked, a subsequent `Capability.toNonNull?` call on the minted
cap would surface a `.nullCapability` error, but the mint path would
already have "succeeded" and propagated an unusable null cap to the caller.
The explicit `isNull` guard below rejects that corner case eagerly with
`.nullCapability`. This makes `mintDerivedCap_preserves_non_null`
unconditional and removes the need for every downstream caller to re-check
the mint result against the null sentinel. -/
def mintDerivedCap (parent : NonNullCap) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge := parent.val.badge) : Except KernelError Capability :=
  if rightsSubset rights parent.val.rights then
    if ({ target := parent.val.target, rights := rights, badge := badge } : Capability).isNull then
      .error .nullCapability
    else
      .ok { target := parent.val.target, rights := rights, badge := badge }
  else
    .error .invalidCapability

/-- WS-SM SM9.A.9: `mintDerivedCap` **preserves the target** — minting attenuates
rights and rewrites the badge, never the thing a capability names. -/
theorem mintDerivedCap_preserves_target
    (parent : NonNullCap) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (child : Capability)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    child.target = parent.val.target := by
  unfold mintDerivedCap at hMint
  split at hMint
  · split at hMint
    · simp at hMint
    · cases hMint; rfl
  · simp at hMint

/-- WS-SM SM9.A.9 (**audit authority is unforgeable by minting**): a mint
produces a capability targeting the audit trail **only** if its parent already
did.

The property that makes `CapTarget.auditTrail` a real gate rather than a
label: `cspaceMint` is the kernel's capability-derivation path, and it cannot
manufacture audit authority from a capability that lacks it.  So an audit
capability exists in a deployment exactly where the boot/CSpace layer put one —
which is why an unconfigured deployment has no audit reader at all. -/
theorem mintDerivedCap_no_audit_forgery
    (parent : NonNullCap) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (child : Capability)
    (hMint : mintDerivedCap parent rights badge = .ok child)
    (hChild : child.target = .auditTrail) :
    parent.val.target = .auditTrail := by
  rw [← mintDerivedCap_preserves_target parent rights badge child hMint]
  exact hChild

/-- AN4-E (H-06): `mintDerivedCap` always produces a non-null capability.
Unconditional consequence of the explicit null-guard added to the function
body — the `.ok` branch is only reached when the constructed child's
`isNull` is false. -/
theorem mintDerivedCap_preserves_non_null
    (parent : NonNullCap) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (child : Capability)
    (hMint : mintDerivedCap parent rights badge = .ok child) :
    child.isNull = false := by
  unfold mintDerivedCap at hMint
  split at hMint
  · -- rightsSubset passed
    split at hMint
    · -- isNull candidate = true: contradiction with `.ok`
      simp at hMint
    · -- isNull candidate = false: .ok constructed, extract equality
      rename_i hNotNull
      injection hMint with hEq
      subst hEq
      -- The constructed candidate equals the extracted child, so their
      -- isNull results match.
      exact Bool.not_eq_true _ |>.mp hNotNull
  · -- rightsSubset failed: .error
    simp at hMint

/-- AN4-E (H-06): Tightened post-condition convenience wrapper — returns a
`NonNullCap` directly. Internally invokes `mintDerivedCap` and lifts the
`.ok` result through `Capability.toNonNull?` using
`mintDerivedCap_preserves_non_null`. Callers that do not need to destructure
the raw `Capability` should prefer this variant. -/
def mintDerivedCapNonNull (parent : NonNullCap) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge := parent.val.badge) : Except KernelError NonNullCap :=
  match hMint : mintDerivedCap parent rights badge with
  | .error e => .error e
  | .ok child =>
      have hNN : child.isNull = false :=
        mintDerivedCap_preserves_non_null parent rights badge child hMint
      .ok ⟨child, hNN⟩

/-- AN4-E (H-06): Forward direction bridge — if `mintDerivedCapNonNull`
returns a concrete `NonNullCap`, `mintDerivedCap` returns the same
capability's raw `Capability` value. Used by the `cspaceMint` migration. -/
theorem mintDerivedCapNonNull_ok_implies_mintDerivedCap_ok
    (parent : NonNullCap) (rights : AccessRightSet) (badge : Option SeLe4n.Badge)
    (childNN : NonNullCap)
    (hMintNN : mintDerivedCapNonNull parent rights badge = .ok childNN) :
    mintDerivedCap parent rights badge = .ok childNN.val := by
  unfold mintDerivedCapNonNull at hMintNN
  split at hMintNN
  · simp at hMintNN
  · rename_i _child hMint
    simp at hMintNN
    subst hMintNN
    exact hMint

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
Returns `true` if the slot has any children in the tree, read off its first-child
link (`SystemState.linkHasChild`, equal to the tree's read under the links'
agreement: `hasCdtChildren_eq_tree`).  No operation refuses on it: a delete
splices the slot's node out and its children are re-derived from its parent
(`spliceDeletedCdtNode`). -/
def hasCdtChildren (st : SystemState) (addr : CSpaceAddr) : Bool :=
  st.linkHasChild addr

theorem hasCdtChildren_eq_tree {st : SystemState}
    (h : LinksAgree st.slotLinkAt st.cdt) (addr : CSpaceAddr) :
    hasCdtChildren st addr = !(st.cdt.childrenOf addr).isEmpty :=
  SystemState.linkHasChild_eq h addr

/-- Core capability slot deletion: empties the slot, leaving the derivation tree
to the caller.
Used by `cspaceDeleteSlot` (which then splices the slot out of the tree) and by
internal kernel operations (`processRevokeNode`, `cspaceRevokeCdtStrict`,
`cspaceMove`) that write the tree themselves. -/
def cspaceDeleteSlotCore (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match st.getCNode? addr.cnode with
    | some cn =>
        let cn' := cn.remove addr.slot
        match storeObject addr.cnode (.cnode cn') st with
        | .error e => .error e
        | .ok (_, st') => .ok ((), st')
    | none => .error .objectNotFound

/-- **A destroyed slot leaves the derivation tree** (`CapDerivationTree.spliceNode`):
its edges go and its children are derived from its parent instead, as seL4's
`cteDelete` unlinks a capability from the mapping database.  The one tree step
every destroyer of a slot takes: the delete, retyping a CNode for each of its
slots, and the local revoke for each sibling it empties.  A slot outside the
tree leaves it unchanged.  The slots' derivation links are rewritten with the
tree (`SystemState.cdtSplice`), as seL4 rewrites the mapping-database words. -/
def spliceDeletedCdtNode (st : SystemState) (ref : SlotRef) : SystemState :=
  st.cdtSplice ref

/-- Delete the capability currently stored in `addr`.

The slot's derivation node leaves the tree with it, and any capabilities derived
from it are re-derived from its parent (`spliceDeletedCdtNode`), as seL4's
`cteDelete` unlinks a capability from the mapping database.  So a delete never
depends on whether the slot has derived capabilities: refusing while it had
some let a thread that holds a derived copy decide whether a delete by another
thread succeeds, which is a channel between them.  Revoking an ancestor still
reaches every capability derived through the deleted one.  Unmapping the slot
alone, as an earlier version did, left the node's edges behind, so each
copy-and-delete round grew the tree without bound. -/
def cspaceDeleteSlot (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceDeleteSlotCore addr st with
    | .error e => .error e
    | .ok ((), st') => .ok ((), spliceDeletedCdtNode st' addr)

/-- **WS-BP BP7.1 (`v0.36.7`)**: the core delete writes one CNode and the CDT —
never the scheduler or the machine. -/
theorem cspaceDeleteSlotCore_scheduler_machine (addr : CSpaceAddr) (st st' : SystemState)
    (h : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    st'.scheduler = st.scheduler ∧ st'.machine = st.machine := by
  unfold cspaceDeleteSlotCore at h
  cases hCn : st.getCNode? addr.cnode with
  | none => rw [hCn] at h; cases h
  | some cn =>
    rw [hCn] at h
    simp only at h
    cases hS : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
    | error e => rw [hS] at h; cases h
    | ok pr =>
      obtain ⟨u, st1⟩ := pr; cases u
      rw [hS] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact ⟨storeObject_scheduler_eq _ _ _ _ hS, storeObject_machine_eq _ _ _ _ hS⟩

/-- The core delete leaves the tree as it was; the wrapper splices the slot out. -/
theorem cspaceDeleteSlotCore_cdt_eq (st st' : SystemState) (addr : CSpaceAddr)
    (h : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    st'.cdt = st.cdt := by
  unfold cspaceDeleteSlotCore at h
  cases hCn : st.getCNode? addr.cnode with
  | none => rw [hCn] at h; cases h
  | some cn =>
    rw [hCn] at h
    simp only at h
    cases hS : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
    | error e => rw [hS] at h; cases h
    | ok pr =>
      obtain ⟨u, st1⟩ := pr; cases u
      rw [hS] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact storeObject_cdt_eq _ _ _ _ hS

/-- The core delete keeps the object table well formed. -/
theorem cspaceDeleteSlotCore_invExt (st st' : SystemState) (addr : CSpaceAddr)
    (hObjInv : st.objects.invExt) (h : cspaceDeleteSlotCore addr st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold cspaceDeleteSlotCore at h
  cases hCn : st.getCNode? addr.cnode with
  | none => rw [hCn] at h; cases h
  | some cn =>
    rw [hCn] at h
    simp only at h
    cases hS : storeObject addr.cnode (.cnode (cn.remove addr.slot)) st with
    | error e => rw [hS] at h; cases h
    | ok pr =>
      obtain ⟨u, st1⟩ := pr; cases u
      rw [hS] at h
      simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
      subst h
      exact storeObject_preserves_objects_invExt _ _ _ _ hObjInv hS

/-- The splice writes the tree, then link words alone. -/
theorem spliceDeletedCdtNode_reach (st : SystemState) (ref : SlotRef) :
    SystemState.linkReach { st with cdt := st.cdt.spliceNode ref } (spliceDeletedCdtNode st ref) :=
  SystemState.cdtSplice_reach st ref

theorem spliceDeletedCdtNode_fields (st : SystemState) (ref : SlotRef) :
    spliceDeletedCdtNode st ref =
      { st with cdt := st.cdt.spliceNode ref, objects := (spliceDeletedCdtNode st ref).objects } :=
  (spliceDeletedCdtNode_reach st ref).fields

@[simp] theorem spliceDeletedCdtNode_cdt (st : SystemState) (ref : SlotRef) :
    (spliceDeletedCdtNode st ref).cdt = st.cdt.spliceNode ref := by
  rw [spliceDeletedCdtNode_fields]

@[simp] theorem spliceDeletedCdtNode_scheduler (st : SystemState) (ref : SlotRef) :
    (spliceDeletedCdtNode st ref).scheduler = st.scheduler := by
  rw [spliceDeletedCdtNode_fields]

@[simp] theorem spliceDeletedCdtNode_machine (st : SystemState) (ref : SlotRef) :
    (spliceDeletedCdtNode st ref).machine = st.machine := by
  rw [spliceDeletedCdtNode_fields]

@[simp] theorem spliceDeletedCdtNode_lifecycle (st : SystemState) (ref : SlotRef) :
    (spliceDeletedCdtNode st ref).lifecycle = st.lifecycle := by
  rw [spliceDeletedCdtNode_fields]

@[simp] theorem spliceDeletedCdtNode_tlbShootdown (st : SystemState) (ref : SlotRef) :
    (spliceDeletedCdtNode st ref).tlbShootdown = st.tlbShootdown := by
  rw [spliceDeletedCdtNode_fields]

/-- The splice changes objects only in their derivation links, and keeps the
object table well formed. -/
theorem spliceDeletedCdtNode_agree {st : SystemState} (hInv : st.objects.invExt) (ref : SlotRef) :
    SystemState.objectsAgreeOffDerivationLinks (spliceDeletedCdtNode st ref) st ∧
      (spliceDeletedCdtNode st ref).objects.invExt :=
  ⟨(spliceDeletedCdtNode_reach st ref).agree hInv, (spliceDeletedCdtNode_reach st ref).invExt hInv⟩

/-- A slot lookup reads no derivation link: it answers alike in two states whose
objects agree off those links. -/
theorem cspaceLookupSlot_of_agree {st st' : SystemState}
    (h : SystemState.objectsAgreeOffDerivationLinks st' st) (addr : CSpaceAddr) :
    cspaceLookupSlot addr st' = (cspaceLookupSlot addr st).map (fun p => (p.1, st')) := by
  unfold cspaceLookupSlot
  rw [h.lookupSlotCap addr]
  cases SystemState.lookupSlotCap st addr with
  | some cap => rfl
  | none =>
    have hG := h.getCNode?_isSome addr.cnode
    cases e : st.getCNode? addr.cnode <;> cases e' : st'.getCNode? addr.cnode <;>
      simp_all [Except.map]

/-- **The delete's success shape**: the core delete succeeded and the deleted
slot was spliced out of the tree. -/
theorem cspaceDeleteSlot_ok_decompose (addr : CSpaceAddr) (st st' : SystemState)
    (h : cspaceDeleteSlot addr st = .ok ((), st')) :
    ∃ stC, cspaceDeleteSlotCore addr st = .ok ((), stC) ∧
      st' = spliceDeletedCdtNode stC addr := by
  unfold cspaceDeleteSlot at h
  cases hC : cspaceDeleteSlotCore addr st with
  | error e => rw [hC] at h; cases h
  | ok pr =>
    obtain ⟨u, stC⟩ := pr; cases u
    rw [hC] at h
    simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
    exact ⟨stC, rfl, h.symm⟩

/-- **A delete's outcome never depends on the derivation tree**: it fails
exactly when the core delete does, whatever capabilities were derived from the
slot. -/
theorem cspaceDeleteSlot_isOk_iff_core (addr : CSpaceAddr) (st : SystemState) :
    (cspaceDeleteSlot addr st).isOk = (cspaceDeleteSlotCore addr st).isOk := by
  unfold cspaceDeleteSlot
  cases cspaceDeleteSlotCore addr st with
  | error e => rfl
  | ok pr => obtain ⟨u, _⟩ := pr; cases u; rfl

/-- ...and so does the guarded delete. -/
theorem cspaceDeleteSlot_scheduler_machine (addr : CSpaceAddr) (st st' : SystemState)
    (h : cspaceDeleteSlot addr st = .ok ((), st')) :
    st'.scheduler = st.scheduler ∧ st'.machine = st.machine := by
  obtain ⟨stC, hC, rfl⟩ := cspaceDeleteSlot_ok_decompose addr st st' h
  rw [spliceDeletedCdtNode_scheduler, spliceDeletedCdtNode_machine]
  exact cspaceDeleteSlotCore_scheduler_machine addr st stC hC

/-- **The siblings the local revoke empties leave the derivation tree**: each
slot `revokeTargetLocal` drops (every slot but the source naming its target)
is spliced out (`spliceDeletedCdtNode`), so no capability the revoke destroyed
stays in the tree. -/
def detachRevokedSlots (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode)
    (sourceSlot : SeLe4n.Slot) (target : CapTarget) : SystemState :=
  cn.foldCells st (fun acc slot cap =>
    if CNode.revokeTargetLocalKeeps sourceSlot target slot cap then acc
    else spliceDeletedCdtNode acc { cnode := cnodeId, slot := slot })

/-- Detaching the revoked siblings writes the tree and link words alone. -/
theorem detachRevokedSlots_shape (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode)
    (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    ∃ cdt, SystemState.linkReach { st with cdt := cdt }
      (detachRevokedSlots st cnodeId cn sourceSlot target) := by
  unfold detachRevokedSlots
  refine SeLe4n.Model.CNode.foldCells_preserves cn st _
    (fun acc => ∃ cdt, SystemState.linkReach { st with cdt := cdt } acc)
    ⟨_, .refl _⟩ (fun acc slot cap _ ⟨c, hAcc⟩ => ?_)
  split
  · exact ⟨c, hAcc⟩
  · exact ⟨_, (hAcc.with_cdt _).trans (spliceDeletedCdtNode_reach acc _)⟩

theorem detachRevokedSlots_agree {st : SystemState} (hInv : st.objects.invExt)
    (cnodeId : SeLe4n.ObjId) (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    SystemState.objectsAgreeOffDerivationLinks (detachRevokedSlots st cnodeId cn sourceSlot target) st ∧
      (detachRevokedSlots st cnodeId cn sourceSlot target).objects.invExt := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target
  exact ⟨h.agree hInv, h.invExt hInv⟩

/-- V5-G (M-DEF-7): **Revocation routing guide.**

seLe4n provides three revocation entry points for different use cases:

- **`cspaceRevoke`** (this function): the local same-TARGET sweep.  Removes
  every capability in the source's CNode that names the source slot's target,
  whether or not it was derived from the source.  It walks no derivations, but
  each capability it removes leaves the CDT as a delete's does
  (`detachRevokedSlots`, splicing the slot's node out).  **It is not seL4's revoke**: `seL4_CNode_Revoke`
  destroys exactly the source's derivations, and a target match reaches an
  independently rooted capability to the same object and the source's own
  parent as well.  It predates the CDT, and since `v0.36.1` no syscall reaches
  it — `revokeCdtScaffold` no longer opens with it.  What still calls it is the
  internal proof helper `lifecycleRevokeDeleteRetype` and the non-interference
  operation catalogue, where it is an operation in its own right.

- **`cspaceRevokeCdt`**: revocation of exactly the source slot's CDT
  descendants, in every CNode including the source's own, and of nothing else.
  Validates the source slot, walks its descendants and deletes their
  capabilities, then consumes the derivations still in flight.  This is the
  **recommended entry point** and the one `seL4_CNode_Revoke` dispatches.
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
the source capability, then splices the node of each slot it removed out of the
CDT (`detachRevokedSlots`, a second pass over the same slots).  Each splice scans
the tree's edge list for the node's parent edge and child edges, so the cost is
O(n + r·E), where `n` is the slot count of the containing CNode, `r` the number of
slots removed and `E` the CDT's edge count.  The slot count is bounded by the
CNode's `2^radixWidth` capacity, which is at most `2^maxCSpaceDepth = 2^64` in
theory but typically ≤ 1024 in practice.  WS-ZA ZA5.3, which links the tree
through the slots as seL4's mapping database does, makes each splice
proportional to the removed node's children.

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
        match st'.getCNode? addr.cnode with
        | some cn =>
            let cn' := cn.revokeTargetLocal addr.slot parent.target
            match storeObject addr.cnode (.cnode cn') st' with
            | .error e => .error e
            | .ok ((), st'') =>
                .ok ((), detachRevokedSlots st'' addr.cnode cn addr.slot parent.target)
        | none => .error .objectNotFound

@[simp] theorem detachRevokedSlots_scheduler (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    (detachRevokedSlots st cnodeId cn sourceSlot target).scheduler = st.scheduler := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target; rw [h.fields]

@[simp] theorem detachRevokedSlots_machine (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    (detachRevokedSlots st cnodeId cn sourceSlot target).machine = st.machine := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target; rw [h.fields]

@[simp] theorem detachRevokedSlots_lifecycle (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    (detachRevokedSlots st cnodeId cn sourceSlot target).lifecycle = st.lifecycle := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target; rw [h.fields]

@[simp] theorem detachRevokedSlots_tlbShootdown (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    (detachRevokedSlots st cnodeId cn sourceSlot target).tlbShootdown = st.tlbShootdown := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target; rw [h.fields]

@[simp] theorem detachRevokedSlots_objectIndex (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    (detachRevokedSlots st cnodeId cn sourceSlot target).objectIndex = st.objectIndex := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target; rw [h.fields]

@[simp] theorem detachRevokedSlots_objectIndexSet (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    (detachRevokedSlots st cnodeId cn sourceSlot target).objectIndexSet = st.objectIndexSet := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target; rw [h.fields]

@[simp] theorem detachRevokedSlots_services (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    (detachRevokedSlots st cnodeId cn sourceSlot target).services = st.services := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target; rw [h.fields]

@[simp] theorem detachRevokedSlots_irqHandlers (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    (detachRevokedSlots st cnodeId cn sourceSlot target).irqHandlers = st.irqHandlers := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target; rw [h.fields]

@[simp] theorem detachRevokedSlots_asidTable (st : SystemState) (cnodeId : SeLe4n.ObjId)
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget) :
    (detachRevokedSlots st cnodeId cn sourceSlot target).asidTable = st.asidTable := by
  obtain ⟨_, h⟩ := detachRevokedSlots_shape st cnodeId cn sourceSlot target; rw [h.fields]

/-- **The local revoke's success shape**: the source resolved, its CNode was
rewritten without the revoked siblings, and those siblings left the tree. -/
theorem cspaceRevoke_ok_decompose (addr : CSpaceAddr) (st st' : SystemState)
    (h : cspaceRevoke addr st = .ok ((), st')) :
    ∃ parent cn stS, cspaceLookupSlot addr st = .ok (parent, st) ∧
      st.getCNode? addr.cnode = some cn ∧
      storeObject addr.cnode (.cnode (cn.revokeTargetLocal addr.slot parent.target)) st =
        .ok ((), stS) ∧
      st' = detachRevokedSlots stS addr.cnode cn addr.slot parent.target := by
  unfold cspaceRevoke at h
  cases hL : cspaceLookupSlot addr st with
  | error e => rw [hL] at h; cases h
  | ok pr =>
    obtain ⟨parent, stL⟩ := pr
    have hEq : stL = st := by
      unfold cspaceLookupSlot at hL
      split at hL
      · cases hL; rfl
      · split at hL <;> cases hL
    subst hEq
    rw [hL] at h
    simp only at h
    cases hCn : stL.getCNode? addr.cnode with
    | none => rw [hCn] at h; cases h
    | some cn =>
      rw [hCn] at h
      simp only at h
      cases hS : storeObject addr.cnode (.cnode (cn.revokeTargetLocal addr.slot parent.target)) stL with
      | error e => rw [hS] at h; cases h
      | ok pr =>
        obtain ⟨u, stS⟩ := pr; cases u
        rw [hS] at h
        simp only [Except.ok.injEq, Prod.mk.injEq, true_and] at h
        exact ⟨parent, cn, stS, rfl, rfl, hS, h.symm⟩

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
            -- WS-BP BP7.1 (`v0.36.7`): a copy is a *derivation* — a new
            -- authority over the target, not the authority that made a frame
            -- mapping — so it carries no mapping record (seL4's `deriveCap`).
            match cspaceInsertSlot dst capNN.val.withoutMapping st' with
            | .error e => .error e
            | .ok ((), st'') =>
                .ok ((), st''.cdtAddChild src dst .copy)

/-- WS-E4/C-02: Move a capability from source to destination.

The source slot is cleared and the capability is placed in the destination.
The destination must be empty (H-02). CDT edges are transferred: the moved
capability inherits the parent-child relationships of the source slot.

**AK8-K (WS-AK / C-L1) — Self-move early reject:** a `cspaceMove src dst`
where `src = dst` is a no-op at the capability level but would move the slot's
tree edges onto itself (`CapDerivationTree.moveNode`). The
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
                -- The core delete leaves the tree alone; the source's edges
                -- then move to the destination, so its parent and children
                -- follow the capability (seL4's `cteMove`).
                match cspaceDeleteSlotCore src st'' with
                | .error e => .error e
                | .ok ((), st''') => .ok ((), st'''.cdtMove src dst)

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
slot, plus the move of the source's tree edges to the destination. -/
theorem cspaceLookupSlot_state_eq
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
edges because minting creates a new capability slot, not an in-place mutation.

**WS-RC R4.D — null-cap rejection is structurally witnessed**: the runtime
guard at the line-1093 `if cap.isNull then .error .nullCapability` arm is
proven by two companion theorems in
`Capability/Invariant/Preservation/CopyMoveMutate.lean`:
`cspaceMutate_rejects_null_cap` (every successful mutation witnesses a
non-null pre-state capability) and `cspaceMutate_null_cap_rejected` (every
null-cap input totalises to `.nullCapability`). A future refactor that drops
the guard fails the Lean elaboration of these theorems, so the runtime check
cannot be silently weakened. -/
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
          -- Direct overwrite: bypass H-02 guard since we are replacing in-place.
          -- AN4-I (LOW) cross-reference: the preservation guarantee for this
          -- path is `cspaceMutate_preserves_capabilityInvariantBundle` in
          -- `Capability/Invariant/Preservation/CopyMoveMutate.lean`, which
          -- witnesses that the in-place overwrite leaves the tree sound.
          match st'.getCNode? addr.cnode with
          | some cn =>
              let cn' := cn.insert addr.slot mutatedCap
              storeObject addr.cnode (.cnode cn') st'
          | none => .error .objectNotFound
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
        .ok ((), st'.cdtAddChild src dst .mint)

/-- WS-SM SM6.D (PR #822 review, Phase H): **mint a reply capability** from an
`.object` capability that targets a `.reply` object.  `lifecycleRetypeDirect` retypes
an ObjId in place, so after retyping Untyped → Reply the holder's authority is still an
`.object target` cap; the receive-with-reply ABI (`resolveRecvReplyId`/`extractReplyId`)
needs a `.replyCap rid`.  This is the production path that derives it: given an
`.object target` cap at `src` where `target` holds a Reply object (`getReply?
(ReplyId.ofObjId target)` resolves), install `.replyCap (ReplyId.ofObjId target)` at
`dst`.  Authority flows from holding the `.object` cap to the Reply (the object *is* the
reply object); single-use semantics are unchanged (consume clears `reply.caller`).

Fails closed: `.nullCapability` on an empty `src`; `.invalidCapability` on a non-`.object`
cap or an `.object` whose target is not a Reply object.  The round-trip
`(ReplyId.ofObjId target).toObjId = target` (Prelude) makes the minted cap resolve back
to the same Reply, so the result satisfies `replyCapPointsToValidReply` by construction.
Mirrors `cspaceMint`'s lookup → derive → insert shape. -/
def mintReplyCap (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (parent, st') =>
        match parent.target with
        | .object target =>
            let rid := SeLe4n.ReplyId.ofObjId target
            match st'.getReply? rid with
            | some _ =>
                -- WS-SM SM6.D (#1 residual, PR #827 review): the minted reply cap
                -- conveys **single-use reply authority**, which the live lookup paths
                -- model as the `.write` right: `syscallRequiredRight .reply = .write`,
                -- and both `resolveRecvReplyId` / `resolveReplyRecvReply` build the
                -- reply-cap gate with `requiredRight := .write`.  A rights-less cap
                -- would fail `.illegalAuthority` before `extractReplyId` ever inspects
                -- `cap.target`, leaving a freshly minted reply cap unusable for
                -- `reply` / `receive_with_reply` / `replyRecv`.  We mint exactly
                -- `.write` (least authority sufficient for every reply gate; no
                -- reply-cap consumer requires `.read`), matching the `.write`-bearing
                -- reply caps the model/conformance suites construct.
                let child : Capability :=
                  { target := .replyCap rid
                    rights := AccessRightSet.ofList [.write]
                    badge := none }
                cspaceInsertSlot dst child st'
            | none => .error .invalidCapability
        | _ => .error .invalidCapability

/-- WS-SM SM6.D (PR #822 review, Phase H): CDT-tracked `mintReplyCap` — derives the reply
cap (above) then records the mint edge `src → dst` in the CDT, so the minted reply cap is
revocable through the standard `cspaceRevokeCdt` path (exactly like `cspaceMintWithCdt`).
Production dispatch routes through this CDT-tracked form. -/
def mintReplyCapWithCdt (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match mintReplyCap src dst st with
    | .error e => .error e
    | .ok ((), st') =>
        .ok ((), st'.cdtAddChild src dst .mint)

/-- WS-ZA ZA5.3: **the destination checks every install makes**: an
addressable, empty slot of a CNode (`cspaceInsertSlot`'s refusals). -/
def cspaceDstAdmitted (dst : CSpaceAddr) (st : SystemState) : Bool :=
  match st.getCNode? dst.cnode with
  | some cn => cn.slotAddressable dst.slot && (cn.lookup dst.slot).isNone
  | none => false

/-- WS-ZA ZA5.3: an admitted destination's insert is the capability written into
its slot in place. -/
theorem cspaceInsertSlot_of_admitted {dst : CSpaceAddr} {st : SystemState}
    (h : cspaceDstAdmitted dst st = true) (cap : Capability) :
    cspaceInsertSlot dst cap st = .ok ((), st.storeCNodeWith dst.cnode (·.insert dst.slot cap)) := by
  unfold cspaceDstAdmitted at h
  cases hD : st.getCNode? dst.cnode with
  | none => simp [hD] at h
  | some cn =>
    simp only [hD, Bool.and_eq_true, Option.isNone_iff_eq_none] at h
    obtain ⟨hA, hE⟩ := h
    simp only [cspaceInsertSlot, hD, hA, hE, Bool.not_true, Bool.false_eq_true, ↓reduceIte]
    exact SystemState.storeObject_cnode_eq_storeCNodeWith
      ((SystemState.getCNode?_eq_some_iff st dst.cnode cn).mp hD) (·.insert dst.slot cap)

/-- WS-ZA ZA5.3: **an install's writes**, in place: `child` written into the
destination's slot (`storeCNodeWith`) and the derivation edge into the tree's
tables (`modifyCdt`). -/
@[inline] def cspaceInstallPerform (src dst : CSpaceAddr) (child : Capability)
    (op : DerivationOp) (st : SystemState) : SystemState :=
  (st.storeCNodeWith dst.cnode (·.insert dst.slot child)).cdtAddChild src dst op

/-- WS-ZA ZA5.3: the capability a mint of `parent` with `rights` and `badge`
writes (`mintDerivedCap`'s). -/
@[inline] def mintedCap (parent : Capability) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) : Capability :=
  { target := parent.target, rights := rights, badge := badge }

/-- WS-ZA ZA5.3: **`cspaceMintWithCdt`'s checks**, read before any write: the
source holds a capability that is not null, the rights attenuate it, the minted
capability is not null, and the destination is admitted
(`cspaceMintWithCdt_of_admitted`). -/
def cspaceMintAdmitted (src dst : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) (st : SystemState) : Bool :=
  (match SystemState.lookupSlotCap st src with
   | some parent => parent.isNotNull && rightsSubset rights parent.rights &&
       (mintedCap parent rights badge).isNotNull
   | none => false) &&
  cspaceDstAdmitted dst st

/-- WS-ZA ZA5.3: **`cspaceMintWithCdt`'s writes**, in place. -/
def cspaceMintPerform (src dst : CSpaceAddr) (rights : AccessRightSet)
    (badge : Option SeLe4n.Badge) (st : SystemState) : SystemState :=
  match SystemState.lookupSlotCap st src with
  | some parent => cspaceInstallPerform src dst (mintedCap parent rights badge) .mint st
  | none => st

/-- WS-ZA ZA5.3: an admitted mint is its writes. -/
theorem cspaceMintWithCdt_of_admitted {src dst : CSpaceAddr} {rights : AccessRightSet}
    {badge : Option SeLe4n.Badge} {st : SystemState}
    (h : cspaceMintAdmitted src dst rights badge st = true) :
    cspaceMintWithCdt src dst rights badge st =
      .ok ((), cspaceMintPerform src dst rights badge st) := by
  unfold cspaceMintAdmitted at h
  unfold cspaceMintWithCdt cspaceMint cspaceMintPerform cspaceLookupSlot
  cases hL : SystemState.lookupSlotCap st src with
  | none => simp [hL] at h
  | some parent =>
    simp only [hL, Capability.isNotNull, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨⟨⟨hN, hR⟩, hC⟩, hD⟩ := h
    have hNN : parent.toNonNull? = some ⟨parent, hN⟩ := by
      unfold Capability.toNonNull?; rw [dif_pos hN]
    have hM : mintDerivedCap ⟨parent, hN⟩ rights badge = .ok (mintedCap parent rights badge) := by
      unfold mintDerivedCap mintedCap at *
      simp only [hR, ↓reduceIte, hC, Bool.false_eq_true]
    simp only [hNN, hM, cspaceInsertSlot_of_admitted hD]
    rfl

/-- WS-ZA ZA5.3: the reply capability a reply-capability mint writes. -/
@[inline] def mintedReplyCap (rid : SeLe4n.ReplyId) : Capability :=
  { target := .replyCap rid, rights := AccessRightSet.ofList [.write], badge := none }

/-- WS-ZA ZA5.3: **`mintReplyCapWithCdt`'s checks**: the source names an object
that is a reply object, and the destination is admitted
(`mintReplyCapWithCdt_of_admitted`). -/
def mintReplyCapAdmitted (src dst : CSpaceAddr) (st : SystemState) : Bool :=
  (match SystemState.lookupSlotCap st src with
   | some parent =>
       match parent.target with
       | .object target => (st.getReply? (SeLe4n.ReplyId.ofObjId target)).isSome
       | _ => false
   | none => false) &&
  cspaceDstAdmitted dst st

/-- WS-ZA ZA5.3: **`mintReplyCapWithCdt`'s writes**, in place. -/
def mintReplyCapPerform (src dst : CSpaceAddr) (st : SystemState) : SystemState :=
  match SystemState.lookupSlotCap st src with
  | some parent =>
      match parent.target with
      | .object target =>
          cspaceInstallPerform src dst (mintedReplyCap (SeLe4n.ReplyId.ofObjId target)) .mint st
      | _ => st
  | none => st

/-- WS-ZA ZA5.3: an admitted reply-capability mint is its writes. -/
theorem mintReplyCapWithCdt_of_admitted {src dst : CSpaceAddr} {st : SystemState}
    (h : mintReplyCapAdmitted src dst st = true) :
    mintReplyCapWithCdt src dst st = .ok ((), mintReplyCapPerform src dst st) := by
  unfold mintReplyCapAdmitted at h
  unfold mintReplyCapWithCdt mintReplyCap mintReplyCapPerform cspaceLookupSlot
  cases hL : SystemState.lookupSlotCap st src with
  | none => simp [hL] at h
  | some parent =>
    simp only [hL, Bool.and_eq_true] at h
    obtain ⟨hT, hD⟩ := h
    cases hP : parent.target with
    | object target =>
      rw [hP] at hT
      simp only [Option.isSome_iff_exists] at hT
      obtain ⟨r, hr⟩ := hT
      simp only [hP, hr, cspaceInsertSlot_of_admitted hD]
      rfl
    | _ => rw [hP] at hT; simp at hT

/-- WS-ZA ZA5.3: **`cspaceCopy`'s checks**, read before any write: the source
slot holds a capability that is not null, and the destination is admitted.
Exactly the copy's refusals (`cspaceCopy_of_admitted`), so a dispatcher that
reads them first hands the state to `cspaceCopyPerform` alone. -/
def cspaceCopyAdmitted (src dst : CSpaceAddr) (st : SystemState) : Bool :=
  (match SystemState.lookupSlotCap st src with
   | some cap => cap.isNotNull
   | none => false) &&
  cspaceDstAdmitted dst st

/-- WS-ZA ZA5.3: **`cspaceCopy`'s writes**, in place: the derived capability and
the copy's edge (`cspaceInstallPerform`). -/
def cspaceCopyPerform (src dst : CSpaceAddr) (st : SystemState) : SystemState :=
  match SystemState.lookupSlotCap st src with
  | some cap => cspaceInstallPerform src dst cap.withoutMapping .copy st
  | none => st

/-- WS-ZA ZA5.3: an admitted copy is its writes. -/
theorem cspaceCopy_of_admitted {src dst : CSpaceAddr} {st : SystemState}
    (h : cspaceCopyAdmitted src dst st = true) :
    cspaceCopy src dst st = .ok ((), cspaceCopyPerform src dst st) := by
  unfold cspaceCopyAdmitted at h
  unfold cspaceCopy cspaceCopyPerform cspaceLookupSlot
  cases hL : SystemState.lookupSlotCap st src with
  | none => simp [hL] at h
  | some cap =>
    simp only [hL, Capability.isNotNull, Bool.and_eq_true, Bool.not_eq_true'] at h
    obtain ⟨hN, hD⟩ := h
    have hNN : cap.toNonNull? = some ⟨cap, hN⟩ := by
      unfold Capability.toNonNull?; rw [dif_pos hN]
    simp only [hNN, cspaceInsertSlot_of_admitted hD]
    rfl

/-- WS-ZA ZA5.3: **`cspaceMove`'s checks**, read before any write: two distinct
slots, the source holding a capability that is not null, an admitted
destination, and a destination CNode the object table rewrites where it stands
(`RHTable.findsInPlace`), so the source's CNode is read back unchanged, or as
just written, by the source's write (`cspaceMove_of_admitted`). -/
def cspaceMoveAdmitted (src dst : CSpaceAddr) (st : SystemState) : Bool :=
  !decide (src = dst) &&
  (match SystemState.lookupSlotCap st src with
   | some cap => cap.isNotNull
   | none => false) &&
  cspaceDstAdmitted dst st &&
  st.objects.findsInPlace dst.cnode

/-- WS-ZA ZA5.3: **`cspaceMove`'s writes**, in place: the capability into the
destination's slot, the source's slot emptied, and the source's edges moved to
the destination (`CapDerivationTree.moveNode`). -/
def cspaceMovePerform (src dst : CSpaceAddr) (st : SystemState) : SystemState :=
  match SystemState.lookupSlotCap st src with
  | some cap =>
      ((st.storeCNodeWith dst.cnode (·.insert dst.slot cap)).storeCNodeWith src.cnode
        (·.remove src.slot)).cdtMove src dst
  | none => st

/-- WS-ZA ZA5.3: an admitted move is its writes. -/
theorem cspaceMove_of_admitted {src dst : CSpaceAddr} {st : SystemState}
    (h : cspaceMoveAdmitted src dst st = true) :
    cspaceMove src dst st = .ok ((), cspaceMovePerform src dst st) := by
  unfold cspaceMoveAdmitted at h
  unfold cspaceMove cspaceMovePerform cspaceLookupSlot
  cases hL : SystemState.lookupSlotCap st src with
  | none => simp [hL] at h
  | some cap =>
    simp only [hL, Capability.isNotNull, Bool.and_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not] at h
    obtain ⟨⟨⟨hNe, hN⟩, hD⟩, hF⟩ := h
    have hNN : cap.toNonNull? = some ⟨cap, hN⟩ := by
      unfold Capability.toNonNull?; rw [dif_pos hN]
    have hS : ∃ cnS, st.objects[src.cnode]? = some (.cnode cnS) := by
      unfold SystemState.lookupSlotCap at hL
      cases hC : SystemState.lookupCNode st src.cnode with
      | none => rw [hC] at hL; cases hL
      | some cnS =>
        refine ⟨cnS, ?_⟩
        unfold SystemState.lookupCNode at hC
        split at hC
        · next c hx => cases hC; exact hx
        · cases hC
    obtain ⟨cnS, hSrc⟩ := hS
    have hD' := hD
    unfold cspaceDstAdmitted at hD'
    cases hDC : st.getCNode? dst.cnode with
    | none => simp [hDC] at hD'
    | some cnD =>
    have hDst := (SystemState.getCNode?_eq_some_iff st dst.cnode cnD).mp hDC
    simp only [hNe, ↓reduceIte, hNN, cspaceInsertSlot_of_admitted hD]
    have h1 : (st.storeCNodeWith dst.cnode (·.insert dst.slot cap)).objects =
        st.objects.insert dst.cnode (.cnode (cnD.insert dst.slot cap)) :=
      SystemState.storeCNodeWith_objects hDst _
    have hS1 : ∃ cn2, (st.storeCNodeWith dst.cnode (·.insert dst.slot cap)).objects[src.cnode]?
        = some (.cnode cn2) := by
      by_cases hEq : dst.cnode = src.cnode
      · refine ⟨cnD.insert dst.slot cap, ?_⟩
        show SeLe4n.Kernel.RobinHood.RHTable.get? _ src.cnode = _
        rw [h1, ← hEq]
        exact SeLe4n.Kernel.RobinHood.RHTable.get?_insert_self_of_findsInPlace _ hF
      · refine ⟨cnS, ?_⟩
        show SeLe4n.Kernel.RobinHood.RHTable.get? _ src.cnode = _
        rw [h1, SeLe4n.Kernel.RobinHood.RHTable.get?_insert_ne_of_findsInPlace _ _ hF hEq]
        exact hSrc
    obtain ⟨cn2, hS2⟩ := hS1
    have hG2 := (SystemState.getCNode?_eq_some_iff _ src.cnode cn2).mpr hS2
    unfold cspaceDeleteSlotCore
    rw [hG2]
    dsimp only
    rw [SystemState.storeObject_cnode_eq_storeCNodeWith hS2 (·.remove src.slot)]

-- ============================================================================
-- M-P04/M5: Shared per-node revocation step
-- ============================================================================

/-- R2-A: Process a single CDT descendant node during revocation.

Shared transition used by both `cspaceRevokeCdt` (materialized fold) and
`streamingRevokeBFS` (streaming BFS). Given a descendant slot:
1. If the delete fails, propagate the error → `.error e`.
2. If it succeeds, remove the slot from the tree → `.ok`.

Changed in WS-R2/M-06: errors from `cspaceDeleteSlot` are now propagated
instead of swallowed. CDT-based revocation (`cspaceRevokeCdt`) is the
canonical revocation entry point — all API dispatch routes through it. -/
def processRevokeNode (st : SystemState) (node : SlotRef)
    : Except KernelError SystemState :=
  match cspaceDeleteSlotCore node st with
  | .error e => .error e
  | .ok ((), stDel) => .ok (stDel.cdtRemove node)

-- ============================================================================
-- WS-E4/C-04: Cross-CNode CDT revocation
-- ============================================================================

/-- Structured failure context for strict CDT descendant deletion.

`offendingSlot` is the descendant slot whose deletion failed. `error` is the
concrete deletion error surfaced by `cspaceDeleteSlotCore`. -/
structure RevokeCdtStrictFailure where
  offendingSlot : CSpaceAddr
  error : KernelError
  deriving Repr, DecidableEq

/-- Return payload for strict CDT revocation.

The strict variant stops at the first descendant deletion failure and returns
its context in `firstFailure` instead of swallowing the error. -/
structure RevokeCdtStrictReport where
  deletedSlots : List CSpaceAddr
  firstFailure : Option RevokeCdtStrictFailure
  deriving Repr, DecidableEq

/-- **What a revocation traversal produced.**

`report` is the policy-specific payload the caller sees; `state` is the store
after the deletions. -/
structure RevokeTraversalOutcome (ρ : Type) where
  report : ρ
  state : SystemState

/-- **CDT revocation, once.**

Every public revocation entry point is this function at a different traversal.
The shape they share is not a coincidence to be re-typed four times:

1. validate the source slot — a read, so a revocation naming an empty or
   unresolvable slot is refused exactly as the local sweep refused it, and the
   step destroys nothing (see *what the prologue must not do* below),
2. look up the source slot's CDT node — no node means nothing was derived,
3. walk the subtree (the part that differs: materialized fold, streaming BFS,
   strict report, validate-then-apply).

A variant *is* its traversal: the prologue is not the variant's to write.
No derivation is ever in flight between syscalls (WS-ZA ZA4.7: a blocked
sender keeps capability addresses, not capabilities, and the receive resolves
and installs them in one step), so the traversal's state is the result.

**What the prologue must not do** (PR #900 review, `v0.36.1`).  Step 1 was the
local `cspaceRevoke` until `v0.36.1`, and that sweep matches on the **target**:
it deleted every capability in the source's CNode naming the same object — an
independently rooted capability outside the source's subtree, and the source's
own **parent** when the two share a CNode — and it stored the swept CNode without
touching the CDT maps, so each swept slot's node went on mapping to an empty
slot.  None of that is revocation: seL4-MCS's `cteRevoke` deletes exactly the
slots `isMDBParentOf` the source (read at `13.0.0`), and step 3 already reaches
every derivation in every CNode, the source's own included, because each live
install path records its edge (`cspaceMintWithCdt`, `cspaceCopy`, `cspaceMove`,
`mintReplyCapWithCdt`, `ipcTransferSingleCap`).  So the prologue is the source
slot's *validation* and nothing more: `cspaceLookupSlot` refuses on exactly the
states the sweep refused on (its CNode arm is unreachable once the lookup
succeeds) and writes nothing (`cspaceLookupSlot_preserves_state`). -/
def revokeCdtScaffold {ρ : Type}
    (traverse : SystemState → SlotRef → List SlotRef →
      Except KernelError (RevokeTraversalOutcome ρ))
    (addr : CSpaceAddr) : Kernel ρ :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok _ =>
        match traverse st addr (st.linkDescendantsOf addr) with
        | .error e => .error e
        | .ok out => .ok (out.report, out.state)

/-- **What a successful scaffold run is made of.**

The source slot resolves, and then the traversal over its descendants succeeds;
the prologue is a read (`v0.36.1`: it was the local same-target sweep, which
destroyed capabilities that were not derivations).  A slot outside the tree has
no descendants, so its traversal walks nothing.

Every preservation argument over a revocation entry point is a case analysis of
exactly this shape.  Until `v0.35.190` the capability bundle's was the only one
and it was spelled inline; the IPC bundle needs the identical analysis, so it is
stated once here, **predicate-free and beside the definition**, rather than
re-derived once per predicate.  The report is deliberately not mentioned: no
invariant reads it, and a decomposition that named it would have to be
instantiated at the variant's report type to be used.
-/
theorem revokeCdtScaffold_ok_decompose {ρ : Type}
    (traverse : SystemState → SlotRef → List SlotRef →
      Except KernelError (RevokeTraversalOutcome ρ))
    (st st' : SystemState) (addr : CSpaceAddr) (r : ρ)
    (hStep : revokeCdtScaffold traverse addr st = .ok (r, st')) :
    (∃ cap, cspaceLookupSlot addr st = .ok (cap, st)) ∧
      ∃ (out : RevokeTraversalOutcome ρ),
        traverse st addr (st.linkDescendantsOf addr) = .ok out ∧ st' = out.state := by
  unfold revokeCdtScaffold at hStep
  split at hStep
  · simp at hStep
  · rename_i res hLookup
    obtain ⟨cap, stL⟩ := res
    have hStL : stL = st := cspaceLookupSlot_state_eq st stL addr cap hLookup
    subst hStL
    refine ⟨⟨cap, hLookup⟩, ?_⟩
    split at hStep
    · simp at hStep
    · rename_i out hTrav
      simp only [Except.ok.injEq, Prod.mk.injEq] at hStep
      exact ⟨out, hTrav, hStep.2.symm⟩

-- ============================================================================
-- WS-BP BP7.1 (`v0.36.7`): frame capabilities own their mappings
-- ============================================================================

/-! A frame capability records where it has mapped its frame
(`Capability.mapping`), so destroying the capability can remove that mapping —
seL4's `finaliseCap` → `unmapPage`.  The capability layer answers two questions
and leaves the unmapping itself to the architecture layer
(`Architecture/PageTeardown.lean`), which it does not import: *which page does a
capability's record name* (here), and *which capabilities did a destruction
destroy* (`cspaceRevokeCdt`'s report, below).
The composites that unmap are `cspaceDeleteSlotFinalising` and
`cspaceRevokeCdtFinalising` (`Capability/FrameFinalise.lean`). -/

/-- **The page a capability's mapping record names**: the recorded address space
and virtual address, and the physical page of the frame the capability targets.
`none` for a capability that records no mapping or targets no frame. -/
def capabilityMappedPage (st : SystemState) (cap : Capability) : Option MappedPage :=
  match cap.mapping, cap.target with
  | some m, .object frameId =>
    (st.getFrame? frameId).map fun f =>
      { asid := m.asid, vaddr := m.vaddr, paddr := f.base, epoch := some m.epoch }
  | _, _ => none

/-- **The pages a slot's capability records** — at most one — read off the state
the deletion runs on. -/
def slotMappedPages (st : SystemState) (addr : CSpaceAddr) : List MappedPage :=
  ((SystemState.lookupSlotCap st addr).bind (capabilityMappedPage st)).toList

/-- Fold body for the materialized traversal: process one CDT descendant node,
propagating a failure rather than swallowing it, and **report the page the
destroyed capability records**.

Before a descendant's slot is deleted, the page its capability records is
appended to the report — read at the state the deletion runs on, from the very
slot `processRevokeNode` deletes, so the report names exactly the destroyed
capabilities' mappings and nothing a separate walk could get wrong
(`revokeCdtFoldBody_records`).  The report is what `cspaceRevokeCdtFinalising`
unmaps (WS-BP BP7.1, `v0.36.7`); it is the fold's only addition to the
state-only fold it replaced, which it therefore is on the state component.

Materializing the descendant list and folding this over it is what
`revokeCdtMaterializedTraversal` below is.

AJ-L10: the descendant read (`SystemState.linkDescendantsOf`, the tree's
`descendantsOf` read along the slot links) materializes the full list before folding.
For deep CDT trees this is a performance concern (O(n) allocation), not a
correctness issue; `revokeCdtStreamingTraversal` is the O(branching-factor)
alternative. -/
def revokeCdtFoldBody
    (acc : Except KernelError (List MappedPage × SystemState)) (node : SlotRef) :
    Except KernelError (List MappedPage × SystemState) :=
  match acc with
  | .error e => .error e
  | .ok (pages, stAcc) =>
      let destroyed : List MappedPage := slotMappedPages stAcc node
      match processRevokeNode stAcc node with
      | .error e => .error e
      | .ok stNext => .ok (destroyed ++ pages, stNext)

/-- Error propagation: `revokeCdtFoldBody` propagates errors unchanged. -/
theorem revokeCdtFoldBody_error (e : KernelError) (node : SlotRef) :
    revokeCdtFoldBody (.error e) node = .error e := by
  unfold revokeCdtFoldBody; rfl

/-- Fold error propagation: folding `revokeCdtFoldBody` from an error stays that
error — the traversal stops at its first failing descendant. -/
theorem revokeCdtFoldBody_foldl_error
    (nodes : List SlotRef) (e : KernelError) :
    nodes.foldl revokeCdtFoldBody (.error e) = .error e := by
  induction nodes with
  | nil => rfl
  | cons node rest ih => simp [List.foldl, revokeCdtFoldBody_error, ih]

/-- **The fold's induction, once, over any state predicate.**

Every preservation argument over a revocation traversal is this induction with a
different `P`.  It was the capability bundle's alone until `v0.35.190`, spelled
in that bundle's own preservation module; the IPC bundle needs the identical
induction, so it is stated here — predicate-free and beside the fold — rather
than run a second time.

`hNode` is the *only* part that differs between predicates, which is the same
division `revokeCdtScaffold_ok_decompose` makes one level up. -/
theorem revokeCdtFold_induct {P : SystemState → Prop}
    (hNode : ∀ (stA stB : SystemState) (node : SlotRef),
      P stA → processRevokeNode stA node = .ok stB → P stB)
    (nodes : List SlotRef) (psInit psFinal : List MappedPage)
    (stInit stFinal : SystemState) (hP : P stInit)
    (hFold : nodes.foldl revokeCdtFoldBody (.ok (psInit, stInit)) = .ok (psFinal, stFinal)) :
    P stFinal := by
  induction nodes generalizing psInit stInit with
  | nil => simp only [List.foldl_nil, Except.ok.injEq, Prod.mk.injEq] at hFold
           exact hFold.2 ▸ hP
  | cons node rest ih =>
    simp only [List.foldl_cons] at hFold
    cases hProc : processRevokeNode stInit node with
    | error e =>
      rw [show revokeCdtFoldBody (.ok (psInit, stInit)) node = .error e by
            unfold revokeCdtFoldBody; simp only [hProc]] at hFold
      rw [revokeCdtFoldBody_foldl_error] at hFold
      simp at hFold
    | ok stMid =>
      obtain ⟨ps1, h1⟩ : ∃ ps1, revokeCdtFoldBody (.ok (psInit, stInit)) node
          = .ok (ps1, stMid) := by
        unfold revokeCdtFoldBody; simp only [hProc]; exact ⟨_, rfl⟩
      rw [h1] at hFold
      exact ih ps1 stMid (hNode stInit stMid node hP hProc) hFold

/-- The traversal is that fold, with the descendant list reported as revoked.

`v0.35.190` gave the fold body a name here, beside the traversal, so the fold's
own lemmas are about a function rather than about an inlined lambda a proof has
to `change` its way into. -/
def revokeCdtMaterializedTraversal (stLocal : SystemState) (_rootNode : SlotRef)
    (descendants : List SlotRef)
    : Except KernelError (RevokeTraversalOutcome (List MappedPage)) :=
  match descendants.foldl revokeCdtFoldBody
      (.ok ([], stLocal) : Except KernelError (List MappedPage × SystemState)) with
  | .error e => .error e
  | .ok (pages, stDone) =>
      -- Reaching `.ok` means every descendant was processed, so the traversal
      -- revoked the whole list it was handed, and `pages` is what the
      -- capabilities it destroyed had mapped.
      .ok { report := pages, state := stDone }

/-- **The traversal's induction, over any state predicate.**

`revokeCdtFold_induct` at the traversal's own interface, so a caller need not
know the traversal is a fold. -/
theorem revokeCdtMaterializedTraversal_ok_induct {P : SystemState → Prop}
    (hNode : ∀ (stA stB : SystemState) (node : SlotRef),
      P stA → processRevokeNode stA node = .ok stB → P stB)
    (stLocal : SystemState) (rootNode : SlotRef) (descendants : List SlotRef)
    (out : RevokeTraversalOutcome (List MappedPage)) (hP : P stLocal)
    (hTrav : revokeCdtMaterializedTraversal stLocal rootNode descendants = .ok out) :
    P out.state := by
  unfold revokeCdtMaterializedTraversal at hTrav
  split at hTrav
  · simp at hTrav
  · rename_i pages stDone hFold
    simp only [Except.ok.injEq] at hTrav
    subst hTrav
    exact revokeCdtFold_induct hNode descendants [] pages stLocal stDone hP hFold

/-- WS-E4/C-04: Revoke all capabilities derived from the source capability
via CDT traversal, across all CNodes in the system.

Destroys exactly the source slot's CDT descendants, in every CNode (the
source's own included), and nothing else — seL4's `cteRevoke`:
1. Validate the source slot (a read; since `v0.36.1` this step is no longer the
   local same-target sweep, see `revokeCdtScaffold`)
2. Walk the CDT to find all descendants of the source slot
3. Delete each descendant's capability from its CNode
4. Clean up CDT edges for deleted slots
5. Consume the derivations that have not landed yet

Steps 1, 2 and 5 are `revokeCdtScaffold`'s and are shared with every other
revocation entry point; steps 3-4 are `revokeCdtMaterializedTraversal`.

**Error handling** (WS-R2/M-06): Descendant deletion errors are now propagated
to callers. If any descendant's `cspaceDeleteSlot` fails, the fold stops and
returns the error. For callers requiring structured failure reports,
use `cspaceRevokeCdtStrict`.

**AN4-I (LOW)**: a prior version of this docstring referenced a
`cspaceRevokeCdt_lenient` variant that swallowed descendant-deletion
errors. That variant no longer exists — the lenient behaviour was removed
as part of WS-R2 / M-06's error-propagation tightening. The reference is
retained in this note purely so a future reader searching the codebase
for the old symbol can find the explanation here rather than guess at a
missing helper. -/
def cspaceRevokeCdt (addr : CSpaceAddr) : Kernel (List MappedPage) :=
  revokeCdtScaffold revokeCdtMaterializedTraversal addr

-- ============================================================================
-- WS-BP BP7.1 (`v0.36.7`): the mapping record's writer
-- ============================================================================

/-- **Record a mapping on the capability in `addr`**, in place — the one write
`.vspaceMap` makes to a CNode.  The slot must hold a capability (the one the arm
resolved); every other field of that capability is kept.  The record is written
wholesale, so a stale record the mapping replaces is simply overwritten. -/
def cspaceRecordFrameMapping (addr : CSpaceAddr) (m : FrameMapping) : Kernel Unit :=
  fun st =>
    match st.getCNode? addr.cnode with
    | none => .error .objectNotFound
    | some cn =>
      match cn.lookup addr.slot with
      | none => .error .invalidCapability
      | some cap => storeObject addr.cnode (.cnode (cn.insert addr.slot { cap with mapping := some m })) st

/-- **What a successful record write is**: the slot held a capability, and the
CNode was stored back with that capability carrying the record. -/
theorem cspaceRecordFrameMapping_ok_decompose (addr : CSpaceAddr) (m : FrameMapping)
    (st st' : SystemState) (h : cspaceRecordFrameMapping addr m st = .ok ((), st')) :
    ∃ cn cap, st.getCNode? addr.cnode = some cn ∧ cn.lookup addr.slot = some cap ∧
      storeObject addr.cnode (.cnode (cn.insert addr.slot { cap with mapping := some m })) st
        = .ok ((), st') := by
  unfold cspaceRecordFrameMapping at h
  cases hCn : st.getCNode? addr.cnode with
  | none => rw [hCn] at h; cases h
  | some cn =>
    rw [hCn] at h
    simp only at h
    cases hLk : cn.lookup addr.slot with
    | none => rw [hLk] at h; cases h
    | some cap => rw [hLk] at h; exact ⟨cn, cap, rfl, hLk, h⟩

/-- **The fold's report records every page a destroyed capability
named.**  The report only grows (`ps ⊆ ps'`), and a step that deletes a slot
whose capability records a page adds that page. -/
theorem revokeCdtFoldBody_records
    (ps : List MappedPage) (st : SystemState) (node : SlotRef)
    (ps' : List MappedPage) (st' : SystemState)
    (h : revokeCdtFoldBody (.ok (ps, st)) node = .ok (ps', st')) :
    (∀ p ∈ ps, p ∈ ps') ∧
    (∀ p ∈ slotMappedPages st node, p ∈ ps') := by
  unfold revokeCdtFoldBody at h
  simp only at h
  cases hP : processRevokeNode st node with
  | error e => rw [hP] at h; cases h
  | ok stNext =>
    rw [hP] at h
    simp only [Except.ok.injEq, Prod.mk.injEq] at h
    obtain ⟨hPs, -⟩ := h
    subst hPs
    exact ⟨fun p hp => List.mem_append_right _ hp, fun p hp => List.mem_append_left _ hp⟩

/-- One revoked node writes neither the scheduler nor the machine. -/
theorem processRevokeNode_scheduler_machine (st st' : SystemState) (node : SlotRef)
    (h : processRevokeNode st node = .ok st') :
    st'.scheduler = st.scheduler ∧ st'.machine = st.machine := by
  unfold processRevokeNode at h
  cases hDel : cspaceDeleteSlotCore node st with
  | error e => rw [hDel] at h; cases h
  | ok pr =>
    obtain ⟨u, stDel⟩ := pr; cases u
    rw [hDel] at h
    simp only [Except.ok.injEq] at h
    subst h
    simpa using cspaceDeleteSlotCore_scheduler_machine node st stDel hDel

/-- **WS-BP BP7.1 (`v0.36.7`)**: the CDT revocation writes neither the scheduler
nor the machine — the shared scaffold's decomposition and the traversal's
induction at that pair. -/
theorem cspaceRevokeCdt_scheduler_machine (addr : CSpaceAddr) (st st' : SystemState)
    (pages : List MappedPage) (h : cspaceRevokeCdt addr st = .ok (pages, st')) :
    st'.scheduler = st.scheduler ∧ st'.machine = st.machine := by
  obtain ⟨_, out, hTrav, rfl⟩ := revokeCdtScaffold_ok_decompose revokeCdtMaterializedTraversal
    st st' addr pages h
  exact revokeCdtMaterializedTraversal_ok_induct
    (P := fun s => s.scheduler = st.scheduler ∧ s.machine = st.machine)
    (fun stA stB nd hP hSt => by
      obtain ⟨h1, h2⟩ := processRevokeNode_scheduler_machine stA stB nd hSt
      exact ⟨h1.trans hP.1, h2.trans hP.2⟩)
    st addr _ out ⟨rfl, rfl⟩ hTrav

-- ============================================================================
-- M-P04: Streaming CDT revocation (WS-M5)
-- ============================================================================

/-- M-P04: Streaming BFS loop — processes one node per step, discovering
children before removing the node from the CDT.

Each iteration:
1. Dequeues the head node from the BFS queue.
2. Reads the node's children off its links (`SystemState.linkChildrenOf`, before removal).
3. Delegates to `processRevokeNode` for the actual delete/detach/removeNode.
4. Appends newly-discovered children to the queue tail.

Fuel = initial edge count, guaranteeing termination since each step
removes at least one CDT node (shrinking the edge set).

Changed in WS-R2/M-05: fuel exhaustion now returns `.error .resourceExhausted`
instead of `.ok`, making incomplete revocation visible to callers. -/
def streamingRevokeBFS
    (fuel : Nat) (queue : List SlotRef)
    (st : SystemState) : Except KernelError (Unit × SystemState) :=
  match fuel, queue with
  | _, [] => .ok ((), st)
  | 0, _ :: _ => .error .resourceExhausted  -- WS-R2/M-05: fuel exhausted
  | fuel + 1, node :: rest =>
      match processRevokeNode st node with
      | .error e => .error e
      | .ok stNext =>
          let children := st.linkChildrenOf node
          streamingRevokeBFS fuel (rest ++ children) stNext

/-- M-P04: Interleave BFS discovery with deletion instead of materializing the
descendant list. Peak memory: O(max branching factor) instead of O(N).

Fuel = the CDT's edge count, which bounds the number of nodes reachable from the
root; running out is `.error .resourceExhausted` rather than a silent partial
revocation, so the scaffold discards the state. -/
def revokeCdtStreamingTraversal (stLocal : SystemState) (rootNode : SlotRef)
    (_descendants : List SlotRef)
    : Except KernelError (RevokeTraversalOutcome Unit) :=
  match streamingRevokeBFS stLocal.cdt.edgeBound
      (stLocal.linkChildrenOf rootNode) stLocal with
  | .error e => .error e
  | .ok ((), stDone) =>
      -- An empty BFS queue is the only `.ok`, so every node reachable from the
      -- root was processed: the same set the materialized fold walks.
      .ok { report := (), state := stDone }

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
  revokeCdtScaffold revokeCdtStreamingTraversal addr

/-- **One reporting step, shared by the two reporting variants.**

`cspaceRevokeCdtStrict` and `cspaceRevokeCdtTransactional` carried this fold
body twice, byte-identical apart from a comment, and the preservation proof
carried a third copy inline in a `suffices`. Named once, the two variants differ
only in the validation prologue — which is the whole of what "transactional"
means.

On a deletion failure the CDT node is deliberately **preserved** (AH3-A/L-04):
the capability slot still exists, and removing its CDT node would make it
unreachable by future revocation, creating an orphan. -/
def revokeCdtReportingStep (acc : RevokeCdtStrictReport × SystemState)
    (node : SlotRef) : RevokeCdtStrictReport × SystemState :=
  let (report, stAcc) := acc
  match report.firstFailure with
  | some _ => (report, stAcc)
  | none =>
      match cspaceDeleteSlotCore node stAcc with
      | .error err =>
          ({ report with firstFailure := some { offendingSlot := node, error := err } }, stAcc)
      | .ok ((), stDel) =>
          ({ report with deletedSlots := node :: report.deletedSlots },
           stDel.cdtRemove node)

/-- **The reporting traversal's outcome**, shared by both reporting variants. -/
def revokeCdtReportingOutcome (stLocal : SystemState) (descendants : List SlotRef)
    : RevokeTraversalOutcome RevokeCdtStrictReport :=
  match descendants.foldl revokeCdtReportingStep
      ({ deletedSlots := [], firstFailure := none }, stLocal) with
  | (report, stFinal) =>
      { report := { report with deletedSlots := report.deletedSlots.reverse }
        state := stFinal }

/-- Best-effort reporting traversal: fold, recording the first failure. -/
def revokeCdtStrictTraversal (stLocal : SystemState) (_rootNode : SlotRef)
    (descendants : List SlotRef)
    : Except KernelError (RevokeTraversalOutcome RevokeCdtStrictReport) :=
  .ok (revokeCdtReportingOutcome stLocal descendants)

/-- Strict WS-E4/C-04 revocation variant.

Compared to `cspaceRevokeCdt`, this variant is strict over descendant deletion:
it surfaces the first `cspaceDeleteSlot` failure and records the offending CDT
node + slot context in the returned report. Traversal halts at the first
failure; successfully deleted descendants before that point remain recorded in
`deletedSlots`.

Local (`same-CNode`) revoke failures are still reported via `.error`, matching
the base operation contract. -/
def cspaceRevokeCdtStrict (addr : CSpaceAddr) : Kernel RevokeCdtStrictReport :=
  revokeCdtScaffold revokeCdtStrictTraversal addr

/-- AK8-B (WS-AK / C-M02): Precondition check for transactional CDT revocation.

Verifies that every descendant slot names a CNode present in the object store. This mirrors
the only runtime-reachable failure path of `cspaceDeleteSlotCore` (which can
only emit `.objectNotFound` when `addr.cnode` is missing), so a `.ok ()`
result witnesses that every subsequent deletion in the transactional apply
phase will succeed. -/
def validateRevokeCdtDescendants (st : SystemState) (descendants : List SlotRef)
    : Except KernelError Unit :=
  descendants.foldlM (init := ()) (fun _ node =>
    match st.getCNode? node.cnode with
    | some _ => .ok ()
    | none => .error .objectNotFound)

/-- AK8-B (WS-AK / C-M02): validate-then-apply reporting traversal.

Identical to `revokeCdtStrictTraversal` behind a precondition check — which is
the whole of what "transactional" adds. Because validation proved every
descendant's CNode present, the shared step's failure branch is dead here, so
`revokeCdtReportingOutcome`'s completion test always reports the full descendant
list.

The formal "the fold never sets `firstFailure` to `some`" witness is tracked as
an AN12-B monotonicity lemma (a post-1.0 hardening candidate, registered in the *Registered debt index* (table C.1) in `docs/REGISTERED_DEBT.md`,
row 31). Until it exists the completion test is what keeps the
defensive branch honest: were validation ever weakened, a halted fold would
report `[]` rather than claim a revocation it did not perform. -/
def revokeCdtTransactionalTraversal (stLocal : SystemState) (_rootNode : SlotRef)
    (descendants : List SlotRef)
    : Except KernelError (RevokeTraversalOutcome RevokeCdtStrictReport) :=
  match validateRevokeCdtDescendants stLocal descendants with
  | .error err => .error err
  | .ok _ => .ok (revokeCdtReportingOutcome stLocal descendants)

/-- AK8-B (WS-AK / C-M02): **Transactional** CDT revocation variant.

Unlike `cspaceRevokeCdtStrict` (which uses best-effort partial-progress
semantics and surfaces failures via `firstFailure` in the return report),
this variant follows a strict **validate-then-apply** discipline:

1. **Local revoke phase.** Invoke `cspaceRevoke` on `addr`. If this fails,
   the transaction aborts and the pre-transaction state is preserved
   (the `Kernel` monad returns `.error` without committing a state update).
2. **Validation phase.** Walk the descendant list of the source CDT node.
   For each descendant slot, verify that its CNode is
   present in `stLocal.objects`. If *any* descendant fails validation,
   the entire transaction aborts with `.error` — no descendant is
   deleted, and the caller's `SystemState` is rolled back to the
   pre-transaction snapshot (since the `Kernel` monad discards the
   intermediate `stLocal` on `.error`).
3. **Apply phase.** If all descendants validate, each deletion in
   `revokeCdtReportingOutcome`'s fold is guaranteed to succeed —
   `cspaceDeleteSlotCore`'s sole failure path is `.objectNotFound` on the
   descendant's CNode, which we verified is present. The `firstFailure`
   field of the returned report is therefore always `none`.
4. **Consumption phase.** `revokeCdtScaffold` drops the derivations that
   have not landed yet, the same as every other revocation entry point.

This provides true all-or-nothing semantics for CDT revocation, at the
cost of a double walk (validation + apply). Callers who can tolerate
partial progress should continue to use `cspaceRevokeCdtStrict`. -/
def cspaceRevokeCdtTransactional (addr : CSpaceAddr) : Kernel RevokeCdtStrictReport :=
  revokeCdtScaffold revokeCdtTransactionalTraversal addr

/-- AK8-B: `validateRevokeCdtDescendants` on an empty descendant list succeeds. -/
theorem validateRevokeCdtDescendants_empty (st : SystemState) :
    validateRevokeCdtDescendants st [] = .ok () := rfl

/-- AN4-F.2 (CAP-M02): happy-path characterisation for the transactional
revoke when the source slot has no descendants. Under that pre-condition the
Phase-3 fold walks nothing and the function returns an empty report, witnessing
"no dead-branch fire" at the one case we can discharge substantively without the
full monotonicity lemma tracked for AN12-B. -/
theorem cspaceRevokeCdtTransactional_no_failure_no_descendants
    (addr : CSpaceAddr) (st : SystemState) (cap : Capability)
    (hLookup : cspaceLookupSlot addr st = .ok (cap, st))
    (hLinks : LinksAgree st.slotLinkAt st.cdt)
    (hNoDesc : st.cdt.descendantsOf addr = []) :
    cspaceRevokeCdtTransactional addr st
      = .ok ({ deletedSlots := [], firstFailure := none }, st) := by
  simp [cspaceRevokeCdtTransactional, revokeCdtScaffold, hLookup,
    SystemState.linkDescendantsOf_eq hLinks, hNoDesc,
    revokeCdtTransactionalTraversal, validateRevokeCdtDescendants_empty,
    revokeCdtReportingOutcome]

/-- AK8-B: the transactional variant runs only on a source slot that resolves —
the scaffold's prologue, shared with every other variant, so the four agree on
their refusal set and diverge only in how they treat descendant failures.

**Renamed at `v0.36.1`** from `cspaceRevokeCdtTransactional_requires_local_revoke_ok`:
the prologue it named was the local same-target sweep, which the scaffold no
longer runs (see `revokeCdtScaffold`, *what the prologue must not do*). -/
theorem cspaceRevokeCdtTransactional_requires_source_slot
    (addr : CSpaceAddr) (st : SystemState) (r : RevokeCdtStrictReport) (st' : SystemState)
    (hOk : cspaceRevokeCdtTransactional addr st = .ok (r, st')) :
    (cspaceLookupSlot addr st).isOk := by
  unfold cspaceRevokeCdtTransactional revokeCdtScaffold at hOk
  cases hLk : cspaceLookupSlot addr st with
  | error e => simp [hLk] at hOk
  | ok _ => simp [Except.isOk, Except.toBool]

/-- **Every revocation entry point is the scaffold at a traversal.**

Four `rfl`s, and they are the reason the prologue cannot be forgotten by a
fifth variant: there is nothing for it to forget, because it is not written at
the entry point.  A variant that
did not appear here would be a variant that reimplemented the walk — which is
what happened, and what these pin against.

Stated as definitional equations rather than as a table of claims: a table
records what someone remembered, `rfl` records what the definition is. -/
theorem cspaceRevokeCdt_routes_through_scaffold :
    cspaceRevokeCdt = revokeCdtScaffold revokeCdtMaterializedTraversal := rfl

/-- Streaming revocation is the scaffold at the BFS traversal. -/
theorem cspaceRevokeCdtStreaming_routes_through_scaffold :
    cspaceRevokeCdtStreaming = revokeCdtScaffold revokeCdtStreamingTraversal := rfl

/-- Strict revocation is the scaffold at the reporting traversal. -/
theorem cspaceRevokeCdtStrict_routes_through_scaffold :
    cspaceRevokeCdtStrict
      = revokeCdtScaffold revokeCdtStrictTraversal := rfl

/-- Transactional revocation is the scaffold at the validated reporting
traversal. -/
theorem cspaceRevokeCdtTransactional_routes_through_scaffold :
    cspaceRevokeCdtTransactional
      = revokeCdtScaffold revokeCdtTransactionalTraversal := rfl

-- ============================================================================
-- M-D01: IPC capability transfer operations
-- ============================================================================

/-- **Can a revocation still reach this slot?** (PR #873 round 18)

The condition `ipcTransferSingleCap` must decline on, defined by what revocation
*requires* rather than by what the install remembers about it.  Every CDT
revocation entry point is `revokeCdtScaffold`, which begins with
`cspaceLookupSlot` — and an empty slot is `.error` there.  So an emptied slot is
a node no revocation path can enter, and a capability installed beneath it is
authority nothing can destroy.

Since WS-ZA ZA5.3 part 2 the slot is the tree's node, so the question is the
store's alone: is the source slot occupied.

`revokeCdtScaffold_ok_implies_slot_occupied` is the tie that keeps this derived: a
change to what revocation requires breaks that theorem rather than silently
widening this check. -/
def cdtNodeIsRevocable (st : SystemState) (node : SlotRef) : Bool :=
  (SystemState.lookupSlotCap st node).isSome

/-- **A successful local revoke witnesses an occupied slot.**

`cspaceRevoke` opens with `cspaceLookupSlot`, whose `.ok` is exactly
`lookupSlotCap = some`.  Stated separately because it is what makes
`cdtNodeIsRevocable` revocation's own precondition rather than a second opinion
about it. -/
theorem cspaceRevoke_ok_implies_slot_occupied
    (addr : CSpaceAddr) (st st' : SystemState)
    (h : cspaceRevoke addr st = .ok ((), st')) :
    (SystemState.lookupSlotCap st addr).isSome := by
  cases hLk : SystemState.lookupSlotCap st addr with
  | none =>
    exfalso
    unfold cspaceRevoke cspaceLookupSlot at h
    cases hCn : st.getCNode? addr.cnode with
    | none => simp [hLk, hCn] at h
    | some _ => simp [hLk, hCn] at h
  | some _ => simp

/-- **A successful revocation witnesses an occupied slot — at every entry point.**

`revokeCdtScaffold` opens with `cspaceLookupSlot`, whose `.ok` is exactly
`lookupSlotCap = some`.  Stated over an arbitrary traversal, so it covers the four
variants that exist and any that does not yet; it is what makes
`cdtNodeIsRevocable` revocation's own precondition rather than a second opinion
about it.  (`cspaceRevoke_ok_implies_slot_occupied` above carried that role while
the scaffold opened with the local sweep, until `v0.36.1`.) -/
theorem revokeCdtScaffold_ok_implies_slot_occupied {ρ : Type}
    (traverse : SystemState → SlotRef → List SlotRef →
      Except KernelError (RevokeTraversalOutcome ρ))
    (addr : CSpaceAddr) (st st' : SystemState) (r : ρ)
    (h : revokeCdtScaffold traverse addr st = .ok (r, st')) :
    (SystemState.lookupSlotCap st addr).isSome := by
  obtain ⟨⟨cap, hLk⟩, _⟩ :=
    revokeCdtScaffold_ok_decompose traverse st st' addr r h
  rw [(cspaceLookupSlot_ok_iff_lookupSlotCap st addr cap).mp hLk]
  rfl

/-- **A node this check refuses is a node no revocation can enter.**

The consequence that makes declining the right answer: were the transfer to
install anyway, the resulting `.ipcTransfer` edge would hang beneath a node whose
slot cannot be revoked, so nothing could ever destroy the installed capability.

Quantified over **every** revocation entry point — the scaffold at any traversal —
since `v0.36.1`; it was stated of the local `cspaceRevoke`, which is no longer
what any of them runs. -/
theorem cdtNodeIsRevocable_false_revoke_refuses
    (st : SystemState) (node : SlotRef)
    (hNot : cdtNodeIsRevocable st node = false) :
    ∀ {ρ : Type}
      (traverse : SystemState → SlotRef → List SlotRef →
        Except KernelError (RevokeTraversalOutcome ρ)) (r : ρ) (st' : SystemState),
      revokeCdtScaffold traverse node st ≠ .ok (r, st') := by
  intro ρ traverse r st' hOk
  have hOcc := revokeCdtScaffold_ok_implies_slot_occupied traverse node st st' r hOk
  have hTrue : cdtNodeIsRevocable st node = true := by
    simp [cdtNodeIsRevocable, hOcc]
  rw [hTrue] at hNot
  exact Bool.noConfusion hNot

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
    (srcNode : SlotRef)
    (receiverCspaceRoot : SeLe4n.ObjId)
    (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) : Kernel CapTransferResult :=
  fun st =>
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration. The
    -- original `_ => .error .objectNotFound` arm collapsed wrong-variant
    -- and absent into the same error code, so migration is
    -- semantics-preserving.
    match st.getCNode? receiverCspaceRoot with
    | some cn =>
        -- **WS-RR RR8.16** (`v0.35.201`): the **radix-bounded** scan.  The
        -- unchecked `findFirstEmptySlot` walks `base, base+1, …` without
        -- consulting `radixWidth`, so on a receiver CNode with no free
        -- in-range slot it answered an index `cspaceInsertSlot` would then
        -- install at, outside anything a CPtr can name.  The checked variant
        -- AK8-F wrote for exactly this hazard answers `none` there, which is
        -- `.noSlot` — an outcome the transfer summary already models.
        match cn.findFirstEmptySlotChecked slotBase scanLimit with
        | none => .ok (.noSlot, st)
        | some emptySlot =>
            -- **The source must still be a live slot at the moment the edge is
            -- made.**
            --
            -- This is the one place an `.ipcTransfer` edge comes into existence.
            -- Since WS-ZA ZA4.7 it runs in the same step as the resolution that
            -- found the capability (a blocked sender keeps addresses, not
            -- capabilities), so no destroyer can run in between; the check is
            -- the install's own guarantee all the same, against any caller that
            -- hands it a capability whose source slot is gone.  Installing
            -- anyway would hand the receiver authority beneath a parent no
            -- revocation can reach, which nothing could subsequently destroy.
            --
            -- The condition is `cdtNodeIsRevocable`, which is revocation's own
            -- precondition rather than a restatement of it: the source slot is
            -- occupied.
            --
            -- Checking here rather than at each destroyer is deliberate.  The
            -- destroyers are open-ended — delete, CNode retype and revoke
            -- today, and whatever later transition frees a slot — and any one of
            -- them that forgets to take its slot out of the tree reopens the
            -- hole silently.  The creator is exactly one function.
            --
            -- Placed after the receiver-root and empty-slot resolution rather
            -- than before it, so that `.ok` still witnesses a CNode at the
            -- receiver root (`ipcTransferSingleCap_ok_implies_cnode_at_root`
            -- and the object-shape frames rest on that) — the check that
            -- declines to install belongs next to the install, not ahead of the
            -- checks the install already had.
            match cdtNodeIsRevocable st srcNode with
            | false => .ok (.sourceRevoked, st)
            | true =>
            let dstAddr : CSpaceAddr := { cnode := receiverCspaceRoot, slot := emptySlot }
            -- WS-BP BP7.1 (`v0.36.7`): the transferred capability is a
            -- derivation (the sender keeps its own), so it arrives with no
            -- frame-mapping record — seL4's `deriveCap`.  Were the sender's
            -- record carried, the receiver could unmap the sender's mapping by
            -- deleting its copy.
            match cspaceInsertSlot dstAddr cap.withoutMapping st with
            | .error e => .error e
            | .ok ((), st') =>
                .ok (.installed receiverCspaceRoot emptySlot,
                     st'.cdtAddChild srcNode dstAddr .ipcTransfer)
    | none => .error .objectNotFound

/-- **No capability is ever installed beneath a source no revocation can reach.**

The guarantee the whole revocation-precision series rests on, stated where the
only `.ipcTransfer` edge is made rather than at any of the operations that can
destroy a slot.  A revocation reaches a transferred capability by entering the
source slot's node, and `cdtNodeIsRevocable_false_revoke_refuses` says a node
this declines on is one no revocation can enter — so an install there would be
authority nothing could destroy.  Because the install is the single creator of
such an edge, this one statement covers every destroyer: the ones that exist
(delete, CNode retype, the revoke sweep, the local sibling sweep) and the ones a
later transition might add.

Round 18 strengthened the conclusion from "the node still maps to a slot" to
"the mapped slot is still occupied"; since WS-ZA ZA5.3 part 2 the slot is the
node, so the occupied slot is the whole of it. -/
theorem ipcTransferSingleCap_installed_implies_revocable_source
    (cap : Capability) (srcNode : SlotRef)
    (receiverCspaceRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (cnode : SeLe4n.ObjId) (slot : SeLe4n.Slot)
    (hStep : ipcTransferSingleCap cap srcNode receiverCspaceRoot slotBase scanLimit st
             = .ok (.installed cnode slot, st')) :
    cdtNodeIsRevocable st srcNode = true := by
  simp only [ipcTransferSingleCap] at hStep
  cases hSrc : cdtNodeIsRevocable st srcNode with
  | false =>
    -- The declining branch answers `.sourceRevoked`, never `.installed`.
    exfalso
    cases hCn : st.getCNode? receiverCspaceRoot with
    | none => simp [hCn] at hStep
    | some cn =>
      simp only [hCn] at hStep
      cases hSlot : cn.findFirstEmptySlotChecked slotBase scanLimit with
      | none => simp [hSlot] at hStep
      | some _ => simp [hSlot, hSrc] at hStep
  | true => rfl

/-- The declining branch is a no-op: a transfer that finds its source gone
leaves the state exactly as it was, so nothing is half-installed. -/
theorem ipcTransferSingleCap_sourceRevoked_preserves_state
    (cap : Capability) (srcNode : SlotRef)
    (receiverCspaceRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (hStep : ipcTransferSingleCap cap srcNode receiverCspaceRoot slotBase scanLimit st
             = .ok (.sourceRevoked, st')) :
    st' = st := by
  simp only [ipcTransferSingleCap] at hStep
  cases hCn : st.getCNode? receiverCspaceRoot with
  | none => simp [hCn] at hStep
  | some cn =>
    simp only [hCn] at hStep
    cases hSlot : cn.findFirstEmptySlotChecked slotBase scanLimit with
    | none => simp [hSlot] at hStep
    | some emptySlot =>
      simp only [hSlot] at hStep
      cases hSrc : cdtNodeIsRevocable st srcNode with
      | false => simp [hSrc] at hStep; exact hStep.symm
      | true =>
        simp only [hSrc] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverCspaceRoot, slot := emptySlot } cap.withoutMapping st with
        | error e => simp [hIns] at hStep
        | ok pair => simp [hIns] at hStep

theorem ipcTransferSingleCap_preserves_scheduler
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.scheduler = st.scheduler := by
  -- AN10-B: post-migration `ipcTransferSingleCap` reads via `getCNode?`.
  simp only [ipcTransferSingleCap] at hStep
  cases hCn : st.getCNode? receiverRoot with
  | none => simp [hCn] at hStep
  | some cn =>
    simp [hCn] at hStep
    cases hSlot : cn.findFirstEmptySlotChecked slotBase scanLimit with
    | none => simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
    | some emptySlot =>
        simp [hSlot] at hStep
        -- A source destroyed since resolution declines the install and leaves
        -- the state untouched, so this frame holds there by reflexivity.
        cases hSrc : cdtNodeIsRevocable st srcNode with
        | false => simp [hSrc] at hStep; obtain ⟨_, rfl⟩ := hStep; first | rfl | assumption
        | true =>
        simp only [hSrc] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have h1 := cspaceInsertSlot_preserves_scheduler st pair.2 _ cap.withoutMapping (by rw [show pair = (pair.1, pair.2) from by simp]; exact hIns)
          simp_all

/-- WS-SM SM8.B.2: capability transfer never touches the machine, and therefore
never touches any core's banked `RegisterFile` (SM5.I banks every core's
registers inside the one `MachineState`).  The scheduler companion above frames
the run queues; together they are what makes an IPC capability transfer
*per-core silent* — the second half of `observableSlotsConfinedToCores … []`,
which reads register banks as well as scheduler slots. -/
theorem ipcTransferSingleCap_preserves_machine
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.machine = st.machine := by
  simp only [ipcTransferSingleCap] at hStep
  cases hCn : st.getCNode? receiverRoot with
  | none => simp [hCn] at hStep
  | some cn =>
    simp [hCn] at hStep
    cases hSlot : cn.findFirstEmptySlotChecked slotBase scanLimit with
    | none => simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
    | some emptySlot =>
        simp [hSlot] at hStep
        -- A source destroyed since resolution declines the install and leaves
        -- the state untouched, so this frame holds there by reflexivity.
        cases hSrc : cdtNodeIsRevocable st srcNode with
        | false => simp [hSrc] at hStep; obtain ⟨_, rfl⟩ := hStep; first | rfl | assumption
        | true =>
        simp only [hSrc] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have h1 := cspaceInsertSlot_preserves_machine st pair.2 _ cap.withoutMapping
            (by rw [show pair = (pair.1, pair.2) from by simp]; exact hIns)
          simp_all

/-- ipcTransferSingleCap preserves objects at keys other than the receiver root CNode. -/
theorem ipcTransferSingleCap_preserves_objects_ne
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (oid : SeLe4n.ObjId)
    (hNe : oid ≠ receiverRoot)
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    SystemState.objectAgreesOffDerivationLinksAt st' st oid := by
  -- AN10-B: post-migration `ipcTransferSingleCap` reads via `getCNode?`.
  simp only [ipcTransferSingleCap] at hStep
  cases hCn : st.getCNode? receiverRoot with
  | none => simp [hCn] at hStep
  | some cn =>
    simp [hCn] at hStep
    cases hSlot : cn.findFirstEmptySlotChecked slotBase scanLimit with
    | none => simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; exact Or.inl rfl
    | some emptySlot =>
        simp [hSlot] at hStep
        -- A source destroyed since resolution declines the install and leaves
        -- the state untouched, so this frame holds there by reflexivity.
        cases hSrc : cdtNodeIsRevocable st srcNode with
        | false => simp [hSrc] at hStep; obtain ⟨_, rfl⟩ := hStep; exact Or.inl rfl
        | true =>
        simp only [hSrc] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have hIns' : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot }
              cap.withoutMapping st = .ok ((), pair.2) := by
            rw [show pair = (pair.1, pair.2) from by simp] at hIns; exact hIns
          have hObjIns := cspaceInsertSlot_preserves_objects_ne st pair.2 _ cap.withoutMapping oid
            hNe hObjInv hIns'
          have hInvMid := cspaceInsertSlot_preserves_objects_invExt st pair.2 _ cap.withoutMapping
            hObjInv hIns'
          rcases (SystemState.cdtAddChild_agreeObjects hInvMid srcNode
            { cnode := receiverRoot, slot := emptySlot } .ipcTransfer).1 oid with
            e | ⟨cn1, cn2, ha, hb, hw⟩
          · exact Or.inl (e.trans hObjIns)
          · exact Or.inr ⟨cn1, cn2, by rw [← hObjIns]; exact ha, hb, hw⟩

theorem ipcTransferSingleCap_preserves_services
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.services = st.services := by
  -- AN10-B: post-migration `ipcTransferSingleCap` reads via `getCNode?`.
  simp only [ipcTransferSingleCap] at hStep
  cases hCn : st.getCNode? receiverRoot with
  | none => simp [hCn] at hStep
  | some cn =>
    simp [hCn] at hStep
    cases hSlot : cn.findFirstEmptySlotChecked slotBase scanLimit with
    | none => simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; rfl
    | some emptySlot =>
        simp [hSlot] at hStep
        -- A source destroyed since resolution declines the install and leaves
        -- the state untouched, so this frame holds there by reflexivity.
        cases hSrc : cdtNodeIsRevocable st srcNode with
        | false => simp [hSrc] at hStep; obtain ⟨_, rfl⟩ := hStep; first | rfl | assumption
        | true =>
        simp only [hSrc] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have h1 := cspaceInsertSlot_preserves_services st pair.2 _ cap.withoutMapping (by rw [show pair = (pair.1, pair.2) from by simp]; exact hIns)
          simp_all

/-- ipcTransferSingleCap preserves `objects.invExt`. -/
theorem ipcTransferSingleCap_preserves_objects_invExt
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult)
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects.invExt := by
  -- AN10-B: post-migration `ipcTransferSingleCap` reads via `getCNode?`.
  simp only [ipcTransferSingleCap] at hStep
  cases hCn : st.getCNode? receiverRoot with
  | none => simp [hCn] at hStep
  | some cn =>
    simp [hCn] at hStep
    cases hSlot : cn.findFirstEmptySlotChecked slotBase scanLimit with
    | none => simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep; exact hObjInv
    | some emptySlot =>
        simp [hSlot] at hStep
        -- A source destroyed since resolution declines the install and leaves
        -- the state untouched, so this frame holds there by reflexivity.
        cases hSrc : cdtNodeIsRevocable st srcNode with
        | false => simp [hSrc] at hStep; obtain ⟨_, rfl⟩ := hStep; first | rfl | assumption
        | true =>
        simp only [hSrc] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep
          obtain ⟨_, rfl⟩ := hStep
          have hInvMid := cspaceInsertSlot_preserves_objects_invExt st pair.2 _ cap.withoutMapping hObjInv
            (by rw [show pair = (pair.1, pair.2) from by simp]; exact hIns)
          exact (SystemState.cdtAddChild_agreeObjects hInvMid _ _ _).2

/-- M3-E4 helper: ipcTransferSingleCap preserves all notification objects.
When `oid = receiverRoot` and the object is a notification, the function
returns `.error .objectNotFound` (expects a CNode), contradicting `.ok`.
When `oid ≠ receiverRoot`, use `ipcTransferSingleCap_preserves_objects_ne`. -/
theorem ipcTransferSingleCap_preserves_ntfn_objects
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hNtfn : st.objects[oid]? = some (.notification ntfn))
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects[oid]? = some (.notification ntfn) := by
  by_cases hNe : oid = receiverRoot
  · subst hNe
    simp only [ipcTransferSingleCap] at hStep
    -- AN10-B: post-migration `ipcTransferSingleCap` reads via `getCNode?`.
    have hCnNone : st.getCNode? oid = none := by
      unfold SystemState.getCNode?; rw [hNtfn]
    simp [hCnNone] at hStep
  · rcases ipcTransferSingleCap_preserves_objects_ne cap srcNode receiverRoot slotBase
      scanLimit st st' result oid hNe hObjInv hStep with e | ⟨_, _, ha, _, _⟩
    · rw [e]; exact hNtfn
    · rw [hNtfn] at ha; cases ha

/-- M3-E4 helper: receiverRoot is never a notification after ipcTransferSingleCap.
The only success path requires receiverRoot to be a CNode in st. On the noSlot
path state is unchanged (still a CNode); on the installed path cspaceInsertSlot
stores an updated CNode back. -/
theorem ipcTransferSingleCap_receiverRoot_not_ntfn
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult)
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    ∀ ntfn, st'.objects[receiverRoot]? ≠ some (.notification ntfn) := by
  -- AN10-B: post-migration `ipcTransferSingleCap` reads via `getCNode?`;
  -- case-split on the typed helper.
  simp only [ipcTransferSingleCap] at hStep
  cases hCn : st.getCNode? receiverRoot with
  | none => simp [hCn] at hStep
  | some cn =>
    -- Bridge to the raw lookup form so the existing post-condition holds.
    have hObj : st.objects[receiverRoot]? = some (.cnode cn) :=
      (SystemState.getCNode?_eq_some_iff st receiverRoot cn).mp hCn
    simp [hCn] at hStep
    cases hSlot : cn.findFirstEmptySlotChecked slotBase scanLimit with
    | none =>
      simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep
      intro ntfn h; rw [hObj] at h; exact absurd h (by simp)
    | some emptySlot =>
        simp [hSlot] at hStep
        -- A source destroyed since resolution declines the install and leaves
        -- the state untouched, so this frame holds there by reflexivity.
        cases hSrc : cdtNodeIsRevocable st srcNode with
        | false =>
          simp [hSrc] at hStep; obtain ⟨_, rfl⟩ := hStep
          intro ntfn h; rw [hObj] at h; exact absurd h (by simp)
        | true =>
        simp only [hSrc] at hStep
        cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping st with
        | error e => simp [hIns] at hStep
        | ok pair =>
          simp [hIns] at hStep; obtain ⟨_, rfl⟩ := hStep
          -- After cspaceInsertSlot: pair.2.objects[receiverRoot]? = some (.cnode cn')
          -- After { ... with cdt := cdt' }: objects preserved
          -- So final objects[receiverRoot]? = pair.2.objects[receiverRoot]?
          -- Need: pair.2.objects[receiverRoot]? = some (.cnode _)
          -- cspaceInsertSlot stores via storeObject receiverRoot (.cnode cn')
          intro ntfn h
          -- h is about the final state after the tree update
          -- Simplify: final objects = pair.2.objects (the tree update preserves objects)
          -- Now h : pair.2.objects[receiverRoot]? = some (.notification ntfn)
          -- But cspaceInsertSlot stored a CNode at receiverRoot via storeObject,
          -- so pair.2.objects[receiverRoot]? should be some (.cnode cn')
          -- Let's unfold cspaceInsertSlot SystemState.getCNode? at hIns to extract storeObject
          obtain ⟨cn', _, _, _, hStore⟩ :=
            cspaceInsertSlot_ok_decompose st pair.2
              { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping hIns
          have hStoreObj := storeObject_objects_eq' st receiverRoot _ pair hObjInv hStore
          have hInvMid := cspaceInsertSlot_preserves_objects_invExt st pair.2 _ cap.withoutMapping
            hObjInv (by rw [show pair = (pair.1, pair.2) from by simp] at hIns; exact hIns)
          obtain ⟨_, hC, _⟩ := (SystemState.cdtAddChild_agreeObjects hInvMid srcNode
            { cnode := receiverRoot, slot := emptySlot } .ipcTransfer).1.cnode_fwd hStoreObj
          rw [hC] at h
          exact absurd h (by simp)

/-- M3-E4 helper: ipcTransferSingleCap preserves all endpoint objects.
When `oid = receiverRoot` and the object is an endpoint, the function
returns `.error .objectNotFound` (expects a CNode), contradicting `.ok`.
When `oid ≠ receiverRoot`, use `ipcTransferSingleCap_preserves_objects_ne`. -/
theorem ipcTransferSingleCap_preserves_ep_objects
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (oid : SeLe4n.ObjId) (ep : Endpoint)
    (hEp : st.objects[oid]? = some (.endpoint ep))
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects[oid]? = some (.endpoint ep) := by
  by_cases hNe : oid = receiverRoot
  · subst hNe
    simp only [ipcTransferSingleCap] at hStep
    -- AN10-B: post-migration `ipcTransferSingleCap` reads via `getCNode?`.
    have hCnNone : st.getCNode? oid = none := by
      unfold SystemState.getCNode?; rw [hEp]
    simp [hCnNone] at hStep
  · rcases ipcTransferSingleCap_preserves_objects_ne cap srcNode receiverRoot slotBase
      scanLimit st st' result oid hNe hObjInv hStep with e | ⟨_, _, ha, _, _⟩
    · rw [e]; exact hEp
    · rw [hEp] at ha; cases ha

/-- M3-E4 helper: ipcTransferSingleCap preserves all TCB objects.
Same reasoning as endpoint preservation: TCBs at receiverRoot cause
`.error .objectNotFound`, contradicting `.ok` hypothesis. -/
theorem ipcTransferSingleCap_preserves_tcb_objects
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (oid : SeLe4n.ObjId) (tcb : TCB)
    (hTcb : st.objects[oid]? = some (.tcb tcb))
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects[oid]? = some (.tcb tcb) := by
  by_cases hNe : oid = receiverRoot
  · subst hNe
    simp only [ipcTransferSingleCap] at hStep
    -- AN10-B: post-migration `ipcTransferSingleCap` reads via `getCNode?`.
    -- `getCNode?` returns `none` when the slot holds a TCB, so the
    -- function's outer match falls into the `none` branch and returns
    -- `.error .objectNotFound` — contradicting `hStep`'s `.ok`.
    have hCnNone : st.getCNode? oid = none := by
      unfold SystemState.getCNode?; rw [hTcb]
    simp [hCnNone] at hStep
  · rcases ipcTransferSingleCap_preserves_objects_ne cap srcNode receiverRoot slotBase
      scanLimit st st' result oid hNe hObjInv hStep with e | ⟨_, _, ha, _, _⟩
    · rw [e]; exact hTcb
    · rw [hTcb] at ha; cases ha

/-- IPC de-threading D6 helper: ipcTransferSingleCap preserves all SchedContext objects.
Same reasoning as TCB/endpoint preservation: a SchedContext at `receiverRoot` makes
`getCNode?` return `none`, so the transfer falls into `.error .objectNotFound` — contradicting
`hStep`'s `.ok`; every other slot is framed by `ipcTransferSingleCap_preserves_objects_ne`. -/
theorem ipcTransferSingleCap_preserves_schedContext_objects
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (oid : SeLe4n.ObjId) (sc : SchedContext)
    (hSc : st.objects[oid]? = some (.schedContext sc))
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects[oid]? = some (.schedContext sc) := by
  by_cases hNe : oid = receiverRoot
  · subst hNe
    simp only [ipcTransferSingleCap] at hStep
    have hCnNone : st.getCNode? oid = none := by
      unfold SystemState.getCNode?; rw [hSc]
    simp [hCnNone] at hStep
  · rcases ipcTransferSingleCap_preserves_objects_ne cap srcNode receiverRoot slotBase
      scanLimit st st' result oid hNe hObjInv hStep with e | ⟨_, _, ha, _, _⟩
    · rw [e]; exact hSc
    · rw [hSc] at ha; cases ha

/-- IPC de-threading D3: ipcTransferSingleCap preserves all `.reply` objects.
Same reasoning as the endpoint/TCB family: a `.reply` at `receiverRoot` makes
`getCNode?` return `none`, so the function fails closed (`.objectNotFound`),
contradicting `.ok`; at every other slot use `_preserves_objects_ne`. -/
theorem ipcTransferSingleCap_preserves_reply_objects
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (oid : SeLe4n.ObjId) (r : SeLe4n.Kernel.Reply)
    (hReply : st.objects[oid]? = some (.reply r))
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    st'.objects[oid]? = some (.reply r) := by
  by_cases hNe : oid = receiverRoot
  · subst hNe
    simp only [ipcTransferSingleCap] at hStep
    have hCnNone : st.getCNode? oid = none := by
      unfold SystemState.getCNode?; rw [hReply]
    simp [hCnNone] at hStep
  · rcases ipcTransferSingleCap_preserves_objects_ne cap srcNode receiverRoot slotBase
      scanLimit st st' result oid hNe hObjInv hStep with e | ⟨_, _, ha, _, _⟩
    · rw [e]; exact hReply
    · rw [hReply] at ha; cases ha

/-- IPC de-threading D2: a successful `ipcTransferSingleCap` proves its `receiverRoot`
was a CNode — the transfer reads `getCNode? receiverRoot` and fails closed
(`.objectNotFound`) when it is `none`, so `.ok` rules out a non-CNode root. -/
theorem ipcTransferSingleCap_ok_implies_cnode_at_root
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState) (result : CapTransferResult)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    ∃ cn, st.objects[receiverRoot]? = some (.cnode cn) := by
  unfold ipcTransferSingleCap at hStep
  cases hGet : st.getCNode? receiverRoot with
  | none => simp [hGet] at hStep
  | some cn => exact ⟨cn, (SystemState.getCNode?_eq_some_iff st receiverRoot cn).mp hGet⟩

/-- M3-E4 helper: ipcTransferSingleCap keeps receiverRoot as a CNode.
The function only succeeds when receiverRoot is a CNode. On noSlot the state is
unchanged. On installed, cspaceInsertSlot stores an updated CNode back via
storeObject, and the CDT edge leaves objects untouched. -/
theorem ipcTransferSingleCap_receiverRoot_stays_cnode
    (cap : Capability) (srcNode : SlotRef)
    (receiverRoot : SeLe4n.ObjId) (slotBase : SeLe4n.Slot)
    (scanLimit : Nat) (st st' : SystemState)
    (result : CapTransferResult) (cn : CNode)
    (hCn : st.objects[receiverRoot]? = some (.cnode cn))
    (hObjInv : st.objects.invExt)
    (hStep : ipcTransferSingleCap cap srcNode receiverRoot slotBase scanLimit st
             = .ok (result, st')) :
    ∃ cn', st'.objects[receiverRoot]? = some (.cnode cn') := by
  -- AN10-B: bridge raw-lookup hypothesis to typed-helper form so the
  -- `simp` matches what `ipcTransferSingleCap` reads post-migration.
  have hCnTyped : st.getCNode? receiverRoot = some cn :=
    (SystemState.getCNode?_eq_some_iff st receiverRoot cn).mpr hCn
  simp only [ipcTransferSingleCap] at hStep
  simp [hCnTyped] at hStep
  cases hSlot : cn.findFirstEmptySlotChecked slotBase scanLimit with
  | none =>
    simp [hSlot] at hStep; obtain ⟨_, rfl⟩ := hStep
    exact ⟨cn, hCn⟩
  | some emptySlot =>
    simp [hSlot] at hStep
    -- A source destroyed since resolution declines the install and leaves
    -- the state untouched, so this frame holds there by reflexivity.
    cases hSrc : cdtNodeIsRevocable st srcNode with
    | false => simp [hSrc] at hStep; obtain ⟨_, rfl⟩ := hStep; exact ⟨cn, hCn⟩
    | true =>
    simp only [hSrc] at hStep
    cases hIns : cspaceInsertSlot { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping st with
    | error e => simp [hIns] at hStep
    | ok pair =>
      simp [hIns] at hStep; obtain ⟨_, rfl⟩ := hStep
      -- pair.2.objects[receiverRoot]? is a CNode from cspaceInsertSlot
      obtain ⟨cn', hCn', _, _, hStore⟩ :=
        cspaceInsertSlot_ok_decompose st pair.2
          { cnode := receiverRoot, slot := emptySlot } cap.withoutMapping hIns
      have hCnEq : cn' = cn := by
        simp only [hCnTyped] at hCn'; exact (Option.some.inj hCn').symm
      subst hCnEq
      have hStoreObj := storeObject_objects_eq' st receiverRoot _ pair hObjInv hStore
      have hInvMid := cspaceInsertSlot_preserves_objects_invExt st pair.2 _ cap.withoutMapping
        hObjInv (by rw [show pair = (pair.1, pair.2) from by simp] at hIns; exact hIns)
      obtain ⟨c2, hC, _⟩ := (SystemState.cdtAddChild_agreeObjects hInvMid srcNode
        { cnode := receiverRoot, slot := emptySlot } .ipcTransfer).1.cnode_fwd hStoreObj
      exact ⟨c2, hC⟩

end SeLe4n.Kernel
