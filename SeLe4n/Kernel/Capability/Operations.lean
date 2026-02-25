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
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
      | tcb _ | endpoint _ | notification _ | vspaceRoot _ => simp [hObj] at hStep
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
        | .ok (_, st') => storeCapabilityRef addr none st'
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
A CDT derivation edge of type `.copy` is created from source to destination. -/
def cspaceCopy (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') =>
        match cspaceInsertSlot dst cap st' with
        | .error e => .error e
        | .ok ((), st'') =>
            -- Record CDT derivation edge (copy)
            let cdt' := st''.cdt.addEdge (src.cnode, src.slot) (dst.cnode, dst.slot) .copy
            .ok ((), { st'' with cdt := cdt' })

/-- WS-E4/C-02: Move a capability from source to destination atomically.

The source slot is cleared and the capability is placed in the destination.
The destination must be empty (H-02). CDT edges are transferred: the moved
capability inherits the parent-child relationships of the source slot. -/
def cspaceMove (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') =>
        -- First insert into destination (which checks H-02 empty slot)
        match cspaceInsertSlot dst cap st' with
        | .error e => .error e
        | .ok ((), st'') =>
            -- Then delete from source
            match cspaceDeleteSlot src st'' with
            | .error e => .error e
            | .ok ((), st''') =>
                -- Transfer CDT edges: reparent children from src to dst
                let cdtBase := st'''.cdt
                let reparented := cdtBase.edges.map (fun e =>
                  if e.parent = (src.cnode, src.slot) then
                    { e with parent := (dst.cnode, dst.slot) }
                  else if e.child = (src.cnode, src.slot) then
                    { e with child := (dst.cnode, dst.slot) }
                  else e)
                .ok ((), { st''' with cdt := { edges := reparented } })

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
          -- Direct overwrite (bypass H-02 guard since we're replacing in-place)
          match st'.objects addr.cnode with
          | some (.cnode cn) =>
              let cn' := cn.insert addr.slot mutatedCap
              match storeObject addr.cnode (.cnode cn') st' with
              | .error e => .error e
              | .ok (_, st'') => storeCapabilityRef addr (some mutatedCap.target) st''
          | _ => .error .objectNotFound
        else .error .invalidCapability

-- ============================================================================
-- WS-E4/C-04: Cross-CNode CDT revocation
-- ============================================================================

/-- WS-E4/C-04: Revoke all capabilities derived from the source capability
via CDT traversal, across all CNodes in the system.

This extends the local revoke with a CDT-based global traversal:
1. Perform local revocation (same CNode siblings)
2. Walk the CDT to find all descendants of the source slot
3. Delete each descendant's capability from its CNode -/
def cspaceRevokeCdt (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (_parent, _st') =>
        -- First do local revocation
        match cspaceRevoke addr st with
        | .error e => .error e
        | .ok ((), stLocal) =>
            -- Then walk CDT descendants and delete each one
            let descendants := stLocal.cdt.descendantsOf addr.cnode addr.slot
            let result := descendants.foldl (fun acc desc =>
              match acc with
              | .error e => .error e
              | .ok ((), stAcc) =>
                  let descAddr : CSpaceAddr := { cnode := desc.1, slot := desc.2 }
                  match cspaceDeleteSlot descAddr stAcc with
                  | .error _ => .ok ((), stAcc)  -- skip if already deleted
                  | .ok ((), stDel) =>
                      -- Remove CDT edges for deleted slot
                      .ok ((), { stDel with cdt := stDel.cdt.removeSlot desc.1 desc.2 })
            ) (.ok ((), stLocal))
            result

end SeLe4n.Kernel
