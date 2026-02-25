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

/-- Insert or replace a capability in `(cnode, slot)`. -/
def cspaceInsertSlot (addr : CSpaceAddr) (cap : Capability) : Kernel Unit :=
  fun st =>
    match st.objects addr.cnode with
    | some (.cnode cn) =>
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
-- WS-E4/H-02: Guarded capability slot insert
-- ============================================================================

/-- WS-E4/H-02: Insert a capability only into an empty slot.

Returns `targetSlotOccupied` if the destination slot already holds a capability.
This prevents silent overwrites of existing capabilities during copy/move/mint. -/
def cspaceInsertSlotGuarded (addr : CSpaceAddr) (cap : Capability) : Kernel Unit :=
  fun st =>
    match st.objects addr.cnode with
    | some (.cnode cn) =>
        match cn.lookup addr.slot with
        | some _ => .error .targetSlotOccupied
        | none =>
            let cn' := cn.insert addr.slot cap
            match storeObject addr.cnode (.cnode cn') st with
            | .error e => .error e
            | .ok (_, st') => storeCapabilityRef addr (some cap.target) st'
    | _ => .error .objectNotFound

-- ============================================================================
-- WS-E4/C-02: CSpace copy, move, mutate operations
-- ============================================================================

/-- WS-E4/C-02: Copy a capability from source to destination.

Copies the capability at `src` into `dst` without modification. Uses guarded
insert (H-02) to prevent overwriting occupied slots. Does NOT create a CDT
edge — seL4 Copy produces an independent duplicate. -/
def cspaceCopy (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') => cspaceInsertSlotGuarded dst cap st'

/-- WS-E4/C-02: Move a capability from source to destination.

Atomically transfers the capability: guarded insert at destination, then
delete source. CDT edges are reparented from source to destination. -/
def cspaceMove (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') =>
        match cspaceInsertSlotGuarded dst cap st' with
        | .error e => .error e
        | .ok (_, st'') =>
            match cspaceDeleteSlot src st'' with
            | .error e => .error e
            | .ok (_, st''') =>
                .ok ((), { st''' with cdt := st'''.cdt.reparent src dst })

/-- WS-E4/C-02: Mutate a capability's rights in-place.

Replaces the capability at `addr` with an attenuated copy. The new rights
must be a subset of the original rights (checked via `rightsSubset`).
Badge can be overridden. Returns `invalidCapability` if rights are not
attenuated. -/
def cspaceMutate
    (addr : CSpaceAddr)
    (newRights : List AccessRight)
    (newBadge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (cap, st') =>
        match mintDerivedCap cap newRights newBadge with
        | .error e => .error e
        | .ok derived =>
            -- In-place mutation: delete old, insert derived at same slot
            match cspaceDeleteSlot addr st' with
            | .error e => .error e
            | .ok (_, st'') => cspaceInsertSlot addr derived st''

-- ============================================================================
-- WS-E4/C-03: CDT-aware mint (derivation tracking)
-- ============================================================================

/-- WS-E4/C-03: Mint with CDT edge creation.

Wraps `cspaceMint` and records a parent→child derivation edge in the CDT.
This is the CDT-aware variant that should be used when tracking capability
derivation lineage. -/
def cspaceMintWithDerivation
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    match cspaceMint src dst rights badge st with
    | .error e => .error e
    | .ok (_, st') =>
        .ok ((), { st' with cdt := st'.cdt.addEdge src dst })

-- ============================================================================
-- WS-E4/C-04: Cross-CNode CDT revocation
-- ============================================================================

/-- WS-E4/C-04: Revoke all transitive CDT descendants of a capability.

Performs local revocation first (same CNode siblings), then walks the CDT
to delete all transitive descendants across CNodes. The source capability
at `addr` is preserved. -/
def cspaceRevokeCdt (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    -- Step 1: local sibling revocation
    match cspaceRevoke addr st with
    | .error e => .error e
    | .ok (_, stLocal) =>
        -- Step 2: CDT descendant revocation
        let descendants := stLocal.cdt.descendantsOf addr
        let init : Except KernelError (Unit × SystemState) := .ok ((), stLocal)
        let result := descendants.foldl (fun (acc : Except KernelError (Unit × SystemState)) ref =>
          match acc with
          | .error e => .error e
          | .ok (_, stAcc) =>
              match cspaceDeleteSlot ref stAcc with
              | .error _ => Except.ok ((), stAcc)  -- skip already-deleted slots
              | .ok (_, stDel) => Except.ok ((), stDel)
        ) init
        match result with
        | .error e => .error e
        | .ok (_, stFinal) =>
            -- Step 3: Clean up CDT edges for all descendants + source children
            let cdt' := descendants.foldl (fun cdt ref => cdt.removeSlot ref) stFinal.cdt
            .ok ((), { stFinal with cdt := cdt' })

-- ============================================================================
-- WS-E4: Capability operation preservation theorems
-- ============================================================================

/-- WS-E4/H-02: Guarded insert rejects occupied slots. -/
theorem cspaceInsertSlotGuarded_rejects_occupied
    (st : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (cn : CNode)
    (existingCap : Capability)
    (hCNode : st.objects addr.cnode = some (.cnode cn))
    (hOccupied : cn.lookup addr.slot = some existingCap) :
    cspaceInsertSlotGuarded addr cap st = .error .targetSlotOccupied := by
  unfold cspaceInsertSlotGuarded
  simp [hCNode, hOccupied]

/-- WS-E4/H-02: Guarded insert preserves scheduler. -/
theorem cspaceInsertSlotGuarded_preserves_scheduler
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceInsertSlotGuarded addr cap st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold cspaceInsertSlotGuarded at hStep
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
                  have hSchedMid := storeObject_scheduler_eq st stMid addr.cnode _ hStore
                  have hSchedRef := storeCapabilityRef_preserves_scheduler stMid st' addr (some cap.target) hStep
                  rw [hSchedRef, hSchedMid]

/-- WS-E4/H-02: Guarded insert preserves services. -/
theorem cspaceInsertSlotGuarded_preserves_services
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (hStep : cspaceInsertSlotGuarded addr cap st = .ok ((), st')) :
    st'.services = st.services := by
  unfold cspaceInsertSlotGuarded at hStep
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
                  have hSvcMid := storeObject_preserves_services st stMid addr.cnode _ hStore
                  have hSvcRef := storeCapabilityRef_preserves_services stMid st' addr (some cap.target) hStep
                  rw [hSvcRef, hSvcMid]

/-- WS-E4/H-02: Guarded insert preserves objects at other ids. -/
theorem cspaceInsertSlotGuarded_preserves_objects_ne
    (st st' : SystemState)
    (addr : CSpaceAddr)
    (cap : Capability)
    (oid : SeLe4n.ObjId)
    (hNe : oid ≠ addr.cnode)
    (hStep : cspaceInsertSlotGuarded addr cap st = .ok ((), st')) :
    st'.objects oid = st.objects oid := by
  unfold cspaceInsertSlotGuarded at hStep
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
                  have hObjMid := storeObject_objects_ne st stMid addr.cnode oid _ hNe hStore
                  have hObjRef := storeCapabilityRef_preserves_objects stMid st' addr (some cap.target) hStep
                  rw [← hObjMid]; exact congrFun hObjRef oid

end SeLe4n.Kernel
