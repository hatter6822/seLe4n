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

/-- Insert a capability into an unoccupied `(cnode, slot)`.

H-02/WS-E4: Guards against silent overwrites of occupied slots. If the slot
already contains a capability, returns `illegalState` instead of silently
replacing it. Use `cspaceMove` or `cspaceMutate` for intentional replacement. -/
def cspaceInsertSlot (addr : CSpaceAddr) (cap : Capability) : Kernel Unit :=
  fun st =>
    match st.objects addr.cnode with
    | some (.cnode cn) =>
        match cn.lookup addr.slot with
        | some _ => .error .illegalState
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
              cases hStore : storeObject addr.cnode (.cnode (cn.insert addr.slot cap)) st with
              | error e => simp [hStore] at hStep
              | ok pair =>
                  obtain ⟨_, stMid⟩ := pair
                  simp [hStore] at hStep
                  have hSchedMid := storeObject_scheduler_eq st stMid addr.cnode _ hStore
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

/-- Revoke capabilities derived from the source via CDT traversal.

C-04/WS-E4: Extended from local-only to cross-CNode revocation via CDT.
Traverses the Capability Derivation Tree to find all transitive descendants
of the source slot and removes them from their respective CNodes. The source
slot itself is preserved. Falls back to local revocation when CDT has no
edges for the source. -/
def cspaceRevoke (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (parent, st') =>
        -- C-04: Collect CDT descendants for cross-CNode revocation
        let descendantSlots := st'.cdt.descendants addr (st'.cdt.edges.length + 1)
        -- Filter out the source slot itself
        let slotsToRevoke := descendantSlots.filter (· ≠ addr)
        -- Also include local siblings (for backward compatibility with pre-CDT behavior)
        match st'.objects addr.cnode with
        | some (.cnode cn) =>
            let localSiblings : List SlotRef :=
              (cn.slots.filter (fun entry =>
                entry.fst ≠ addr.slot ∧ entry.snd.target = parent.target)).map
                (fun entry => { cnode := addr.cnode, slot := entry.fst })
            let allSlotsToRevoke := slotsToRevoke ++ localSiblings.filter (· ∉ slotsToRevoke)
            -- Perform local CNode revocation first
            let cn' := cn.revokeTargetLocal addr.slot parent.target
            match storeObject addr.cnode (.cnode cn') st' with
            | .error e => .error e
            | .ok (_, st'') =>
                -- Clear cross-CNode descendant slots via CDT
                let crossCNodeSlots := allSlotsToRevoke.filter (fun s => s.cnode ≠ addr.cnode)
                let st''' := revokeCrossCNodeSlots crossCNodeSlots st''
                -- Update CDT: remove all revoked edges
                let cdt' := allSlotsToRevoke.foldl (fun cdt slot => cdt.removeSlot slot) st'''.cdt
                let st4 := { st''' with cdt := cdt' }
                clearCapabilityRefs allSlotsToRevoke st4
        | _ => .error .objectNotFound
where
  /-- Helper: remove capabilities from cross-CNode slots. Pure state fold. -/
  revokeCrossCNodeSlots : List SlotRef → SystemState → SystemState
  | [], st => st
  | ref :: rest, st =>
      match st.objects ref.cnode with
      | some (.cnode cn) =>
          let cn' := cn.remove ref.slot
          let objects' : SeLe4n.ObjId → Option KernelObject :=
            fun oid => if oid = ref.cnode then some (.cnode cn') else st.objects oid
          revokeCrossCNodeSlots rest { st with objects := objects' }
      | _ => revokeCrossCNodeSlots rest st

-- ============================================================================
-- C-02/WS-E4: Missing capability operations (copy, move, mutate)
-- ============================================================================

/-- Copy a capability from source to destination without rights change.

C-02/WS-E4: Duplicates the source capability at the destination slot with
identical rights and target. No CDT derivation edge is created (copies are
independent siblings, not children). The destination slot must be empty
(enforced by `cspaceInsertSlot` H-02 guard). -/
def cspaceCopy (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') => cspaceInsertSlot dst cap st'

/-- Move a capability from source to destination with atomic source clearing.

C-02/WS-E4: Transfers the capability from `src` to `dst` atomically.
After the move, the source slot is empty and the destination holds the
capability. The destination slot must be empty (H-02 guard). CDT edges
are updated to reflect the new location. -/
def cspaceMove (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') =>
        -- Insert at destination first (will fail if occupied via H-02)
        match cspaceInsertSlot dst cap st' with
        | .error e => .error e
        | .ok ((), st'') =>
            -- Then clear the source slot
            match cspaceDeleteSlot src st'' with
            | .error e => .error e
            | .ok ((), st''') =>
                -- Update CDT: re-parent edges from src to dst
                let cdt' := st'''.cdt.edges.map (fun e =>
                  if e.parentSlot = src then { e with parentSlot := dst }
                  else if e.childSlot = src then { e with childSlot := dst }
                  else e)
                .ok ((), { st''' with cdt := { edges := cdt' } })

/-- Mutate a capability in-place with rights restriction.

C-02/WS-E4: Modifies the capability at `addr` by restricting its rights to
`newRights`. The target is preserved and the new rights must be a subset of
the original rights (attenuation check). An optional new badge can be set. -/
def cspaceMutate (addr : CSpaceAddr)
    (newRights : List AccessRight)
    (newBadge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (cap, st') =>
        if rightsSubset newRights cap.rights then
          let cap' : Capability := {
            target := cap.target
            rights := newRights
            badge := newBadge
          }
          -- Direct update: remove old, insert new at same slot
          match st'.objects addr.cnode with
          | some (.cnode cn) =>
              let cn' := cn.insert addr.slot cap'
              match storeObject addr.cnode (.cnode cn') st' with
              | .error e => .error e
              | .ok (_, st'') => storeCapabilityRef addr (some cap'.target) st''
          | _ => .error .objectNotFound
        else
          .error .invalidCapability

end SeLe4n.Kernel
