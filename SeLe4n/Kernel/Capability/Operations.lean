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
        match st.objects addr.cnode with
        | some (.cnode _) => .error .invalidCapability
        | _ => .error .objectNotFound

/-- Resolve a CSpace path address into a concrete slot using CNode guard/radix semantics. -/
def cspaceResolvePath (addr : CSpacePathAddr) : Kernel CSpaceAddr :=
  fun st =>
    match st.objects addr.cnode with
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

/-- Insert a capability into an empty slot.

WS-E4/H-02: Guarded against occupied-slot overwrites. If the target slot
already contains a capability, returns `targetSlotOccupied`. The caller must
explicitly delete or revoke the existing capability before inserting. -/
def cspaceInsertSlot (addr : CSpaceAddr) (cap : Capability) : Kernel Unit :=
  fun st =>
    match st.objects addr.cnode with
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
  cases hObj : st.objects addr.cnode with
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
  cases hObj : st.objects addr.cnode with
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
    st'.objects oid = st.objects oid := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects addr.cnode with
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
                  rw [← hObjMid]; exact congrFun hObjRef oid

/-- WS-F3: `cspaceInsertSlot` preserves IRQ handler mappings. -/
theorem cspaceInsertSlot_preserves_irqHandlers
    (st st' : SystemState) (addr : CSpaceAddr) (cap : Capability)
    (hStep : cspaceInsertSlot addr cap st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  unfold cspaceInsertSlot at hStep
  cases hObj : st.objects addr.cnode with
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
    (hObj : st.objects addr.cnode = some (.cnode cn))
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
        cases hObj : st.objects addr.cnode with
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

/-- Requested rights must be contained in allowed rights. -/
def rightsSubset (requested allowed : List AccessRight) : Bool :=
  requested.all (fun right => right ∈ allowed)

theorem rightsSubset_sound
    (requested allowed : List AccessRight)
    (hSubset : rightsSubset requested allowed = true) :
    ∀ right, right ∈ requested → right ∈ allowed := by
  intro right hMem
  unfold rightsSubset at hSubset
  have hDec : decide (right ∈ allowed) = true := (List.all_eq_true.mp hSubset) right hMem
  simpa using hDec

/-- Build a mint-like derived capability with explicit rights attenuation. -/
def mintDerivedCap (parent : Capability) (rights : List AccessRight)
    (badge : Option SeLe4n.Badge := parent.badge) : Except KernelError Capability :=
  if rightsSubset rights parent.rights then
    .ok { target := parent.target, rights := rights, badge := badge }
  else
    .error .invalidCapability

/-- Mint from source slot and insert into destination slot under attenuation checks. -/
def cspaceMint
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
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
    match st.objects addr.cnode with
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

This first lifecycle transition is intentionally local to one CNode while derivation-tree state is
still out-of-scope for the active slice. The source slot remains present and sibling slots naming
the same target are removed. -/
def cspaceRevoke (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (parent, st') =>
        match st'.objects addr.cnode with
        | some (.cnode cn) =>
            let cn' := cn.revokeTargetLocal addr.slot parent.target
            let revokedRefs : List SlotRef :=
              (cn.slots.filter (fun entry => entry.fst ≠ addr.slot ∧ entry.snd.target = parent.target)).map
                (fun entry => { cnode := addr.cnode, slot := entry.fst })
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

/-- WS-E4/C-02: Mutate a capability's rights in place without creating a derivation.

The slot must already contain a capability, and the new rights must be a subset
of the existing rights (attenuation only). Badge can be overridden. -/
def cspaceMutate (addr : CSpaceAddr) (rights : List AccessRight)
    (badge : Option SeLe4n.Badge) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (cap, st') =>
        if rightsSubset rights cap.rights then
          let mutatedCap : Capability :=
            { cap with rights := rights, badge := badge.orElse (fun _ => cap.badge) }
          -- Direct overwrite: bypass H-02 guard since we are replacing in-place
          match st'.objects addr.cnode with
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
def cspaceMintWithCdt (src dst : CSpaceAddr) (rights : List AccessRight)
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
4. Clean up CDT edges for deleted slots -/
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
