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

/-- Insert a capability in `(cnode, slot)`.

WS-E4/H-02: Guarded against occupied-slot overwrites. Returns `.slotOccupied`
if the target slot already contains a capability. This prevents silently
breaking derivation chains once the CDT is in place. -/
def cspaceInsertSlot (addr : CSpaceAddr) (cap : Capability) : Kernel Unit :=
  fun st =>
    match st.objects addr.cnode with
    | some (.cnode cn) =>
        match cn.lookup addr.slot with
        | some _ => .error .slotOccupied
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

/-- WS-E4/H-02: Inserting into an occupied slot is rejected. -/
theorem cspaceInsertSlot_rejects_occupied_slot
    (st : SystemState)
    (addr : CSpaceAddr)
    (cap existingCap : Capability)
    (cn : CNode)
    (hObj : st.objects addr.cnode = some (.cnode cn))
    (hLookup : cn.lookup addr.slot = some existingCap) :
    ∃ e, cspaceInsertSlot addr cap st = .error e := by
  exists .slotOccupied
  unfold cspaceInsertSlot
  simp [hObj, hLookup]

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

/-- Delete the capability currently stored in `addr`.

WS-E4/C-03: Also removes the slot from the CDT (disconnects from parent
and all children). -/
def cspaceDeleteSlot (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match st.objects addr.cnode with
    | some (.cnode cn) =>
        let cn' := cn.remove addr.slot
        let cdtAddr : SlotAddr := { cnode := addr.cnode, slot := addr.slot }
        match storeObject addr.cnode (.cnode cn') st with
        | .error e => .error e
        | .ok (_, st') =>
            match storeCapabilityRef addr none st' with
            | .error e => .error e
            | .ok (_, st'') =>
                .ok ((), { st'' with cdt := st''.cdt.removeSlot cdtAddr })
    | _ => .error .objectNotFound

/-- WS-E4/C-02: Copy a capability from source to destination without creating
a CDT derivation edge.

Unlike `cspaceMint`, copy preserves the capability exactly (no rights
attenuation). The copy is independent — revocation of the source does NOT
revoke the copy. -/
def cspaceCopy (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') => cspaceInsertSlot dst cap st'

/-- WS-E4/C-02: Move a capability from source to destination.

Atomically inserts into destination and removes from source. The CDT edges
are reparented: the moved capability retains its derivation relationships
at the new location. -/
def cspaceMove (src dst : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (cap, st') =>
        match cspaceInsertSlot dst cap st' with
        | .error e => .error e
        | .ok ((), st'') =>
            -- Delete source after successful insert
            match st''.objects src.cnode with
            | some (.cnode cn) =>
                let cn' := cn.remove src.slot
                let srcAddr : SlotAddr := { cnode := src.cnode, slot := src.slot }
                let dstAddr : SlotAddr := { cnode := dst.cnode, slot := dst.slot }
                -- Reparent CDT edges: src → dst
                let cdt' := st''.cdt.edges.map (fun e =>
                  { parent := if e.parent = srcAddr then dstAddr else e.parent
                    child := if e.child = srcAddr then dstAddr else e.child })
                match storeObject src.cnode (.cnode cn') st'' with
                | .error e => .error e
                | .ok (_, st''') =>
                    match storeCapabilityRef src none st''' with
                    | .error e => .error e
                    | .ok (_, st4) =>
                        .ok ((), { st4 with cdt := { edges := cdt' } })
            | _ => .error .objectNotFound

/-- WS-E4/C-02: Mutate a capability in-place: delete source, then insert
derived cap at destination with attenuated rights.

Unlike mint, mutate does NOT create a CDT edge — it is an in-place
authority refinement. The source is consumed. -/
def cspaceMutate (src dst : CSpaceAddr) (rights : List AccessRight) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot src st with
    | .error e => .error e
    | .ok (parent, st') =>
        match mintDerivedCap parent rights with
        | .error e => .error e
        | .ok child =>
            -- Delete source first (ensures H-02 guard doesn't fire if src=dst)
            match cspaceDeleteSlot src st' with
            | .error e => .error e
            | .ok ((), st'') => cspaceInsertSlot dst child st''

/-- WS-E4/C-03+C-04: Revoke all capabilities derived from the source slot.

The source slot is preserved; same-target siblings in the source CNode are
removed via `revokeTargetLocal`. CDT descendant edges are cleaned up in the
metadata layer.

Cross-CNode capability deletion (traversing CDT descendants and deleting
their slots in remote CNodes) is a semantic extension deferred to a future
hardware-targeted slice. The current model provides local revoke + CDT
metadata cleanup, which is sufficient for the `lifecycleAuthorityMonotonicity`
invariant that governs the abstract model. -/
def cspaceRevoke (addr : CSpaceAddr) : Kernel Unit :=
  fun st =>
    match cspaceLookupSlot addr st with
    | .error e => .error e
    | .ok (parent, st') =>
        match st'.objects addr.cnode with
        | some (.cnode cn) =>
            let revokedRefs : List SlotRef :=
              (cn.slots.filter (fun entry =>
                entry.fst ≠ addr.slot ∧ entry.snd.target = parent.target)).map
                (fun entry => { cnode := addr.cnode, slot := entry.fst : SlotRef })
            let cn' := cn.revokeTargetLocal addr.slot parent.target
            match storeObject addr.cnode (.cnode cn') st' with
            | .error e => .error e
            | .ok (_, stStored) =>
                match clearCapabilityRefs revokedRefs stStored with
                | .error e => .error e
                | .ok (_, stCleared) =>
                    -- CDT cleanup: remove all descendant edges
                    let sourceAddr : SlotAddr := { cnode := addr.cnode, slot := addr.slot }
                    let descendants := stCleared.cdt.descendantsOf sourceAddr
                    let cdtClean := descendants.foldl
                      (fun cdt desc => cdt.removeSlot desc) stCleared.cdt
                    .ok ((), { stCleared with cdt := cdtClean })
        | _ => .error .objectNotFound

/-- WS-E4/C-03: Mint with CDT edge tracking.

Like `cspaceMint` but also records a CDT edge from source to destination,
establishing a parent-child derivation relationship. -/
def cspaceMintWithCdt
    (src dst : CSpaceAddr)
    (rights : List AccessRight)
    (badge : Option SeLe4n.Badge := none) : Kernel Unit :=
  fun st =>
    match cspaceMint src dst rights badge st with
    | .error e => .error e
    | .ok ((), st') =>
        let srcAddr : SlotAddr := { cnode := src.cnode, slot := src.slot }
        let dstAddr : SlotAddr := { cnode := dst.cnode, slot := dst.slot }
        .ok ((), { st' with cdt := st'.cdt.addEdge srcAddr dstAddr })

end SeLe4n.Kernel
