/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.IntermediateState

/-!
# Q3-B: Builder Operations — Invariant-Preserving State Construction

Builder operations apply targeted state mutations to an `IntermediateState`,
each carrying forward all four invariant witnesses. These are the only
sanctioned way to construct a non-empty `IntermediateState` during boot.

Each operation is a pure function `IntermediateState → IntermediateState`.
-/

namespace SeLe4n.Model.Builder

open SeLe4n.Kernel.RobinHood
open SeLe4n.Model

-- ============================================================================
-- Helper: allTablesInvExt decomposition/recomposition
-- ============================================================================

/-- Extract the objects invExt from allTablesInvExt. -/
private theorem allTablesInvExt_objects {st : SystemState}
    (h : st.allTablesInvExt) : st.objects.invExt := h.1

/-- Extract irqHandlers invExt from allTablesInvExt. -/
private theorem allTablesInvExt_irqHandlers {st : SystemState}
    (h : st.allTablesInvExt) : st.irqHandlers.invExt := h.2.1

/-- Extract services invExt from allTablesInvExt. -/
private theorem allTablesInvExt_services {st : SystemState}
    (h : st.allTablesInvExt) : st.services.invExt := h.2.2.2.2.2.2.2.2.2.1

/-- Extract serviceRegistry invExt from allTablesInvExt. -/
private theorem allTablesInvExt_serviceRegistry {st : SystemState}
    (h : st.allTablesInvExt) : st.serviceRegistry.invExt := h.2.2.2.2.2.2.2.2.2.2.2.1

/-- Extract interfaceRegistry invExt from allTablesInvExt. -/
private theorem allTablesInvExt_interfaceRegistry {st : SystemState}
    (h : st.allTablesInvExt) : st.interfaceRegistry.invExt := h.2.2.2.2.2.2.2.2.2.2.1

/-- Extract objectTypes invExt from allTablesInvExt. -/
private theorem allTablesInvExt_objectTypes {st : SystemState}
    (h : st.allTablesInvExt) : st.lifecycle.objectTypes.invExt := h.2.2.2.2.2.1

/-- Extract capabilityRefs invExt from allTablesInvExt. -/
private theorem allTablesInvExt_capabilityRefs {st : SystemState}
    (h : st.allTablesInvExt) : st.lifecycle.capabilityRefs.invExt := h.2.2.2.2.2.2.1

/-- Extract objectIndexSet invExt from allTablesInvExt. -/
private theorem allTablesInvExt_objectIndexSet {st : SystemState}
    (h : st.allTablesInvExt) : st.objectIndexSet.table.invExt := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Extract asidTable invExt from allTablesInvExt. -/
private theorem allTablesInvExt_asidTable {st : SystemState}
    (h : st.allTablesInvExt) : st.asidTable.invExt := h.2.2.1

-- ============================================================================
-- Q3-B.1: registerIrq — insert into irqHandlers
-- ============================================================================

/-- Q3-B: Register an IRQ handler in the builder state. Only modifies
`irqHandlers`; all other fields are unchanged. -/
def registerIrq (ist : IntermediateState) (irq : SeLe4n.Irq) (handler : SeLe4n.ObjId)
    : IntermediateState where
  state := { ist.state with irqHandlers := ist.state.irqHandlers.insert irq handler }
  hAllTables := by
    have h := ist.hAllTables
    unfold SystemState.allTablesInvExt at h ⊢
    refine ⟨h.1, ?_, h.2.2⟩
    exact RHTable.insert_preserves_invExt _ _ _ h.2.1
  hPerObjectSlots := by
    intro id cn hObj
    exact ist.hPerObjectSlots id cn hObj
  hPerObjectMappings := by
    intro id vs hObj
    exact ist.hPerObjectMappings id vs hObj
  hLifecycleConsistent := by
    rcases ist.hLifecycleConsistent with ⟨hObjType, hCapRef⟩
    exact ⟨hObjType, hCapRef⟩

-- ============================================================================
-- Q3-B.2: registerService — insert into serviceRegistry
-- ============================================================================

/-- Q3-B: Register a service in the builder state. Only modifies
`serviceRegistry`; all other fields are unchanged. -/
def registerService (ist : IntermediateState) (sid : ServiceId)
    (reg : ServiceRegistration) : IntermediateState where
  state := { ist.state with serviceRegistry := ist.state.serviceRegistry.insert sid reg }
  hAllTables := by
    have h := ist.hAllTables
    unfold SystemState.allTablesInvExt at h ⊢
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
           h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.2.1,
           RHTable.insert_preserves_invExt _ _ _ h.2.2.2.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.2.2.2⟩
  hPerObjectSlots := by
    intro id cn hObj; exact ist.hPerObjectSlots id cn hObj
  hPerObjectMappings := by
    intro id vs hObj; exact ist.hPerObjectMappings id vs hObj
  hLifecycleConsistent := by
    rcases ist.hLifecycleConsistent with ⟨hObjType, hCapRef⟩
    exact ⟨hObjType, hCapRef⟩

-- ============================================================================
-- Q3-B.3: addServiceGraph — insert into services
-- ============================================================================

/-- Q3-B: Add a service graph entry in the builder state. Only modifies
`services`; all other fields are unchanged. -/
def addServiceGraph (ist : IntermediateState) (sid : ServiceId)
    (entry : ServiceGraphEntry) : IntermediateState where
  state := { ist.state with services := ist.state.services.insert sid entry }
  hAllTables := by
    have h := ist.hAllTables
    unfold SystemState.allTablesInvExt at h ⊢
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
           h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.1,
           RHTable.insert_preserves_invExt _ _ _ h.2.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.2⟩
  hPerObjectSlots := by
    intro id cn hObj; exact ist.hPerObjectSlots id cn hObj
  hPerObjectMappings := by
    intro id vs hObj; exact ist.hPerObjectMappings id vs hObj
  hLifecycleConsistent := by
    rcases ist.hLifecycleConsistent with ⟨hObjType, hCapRef⟩
    exact ⟨hObjType, hCapRef⟩

-- ============================================================================
-- Q3-B.4: createObject — simplified boot-time object creation
-- ============================================================================

/-- Q3-B + T2-K (M-BLD-1): Insert a kernel object into the builder state
during boot.

This is a simplified builder-phase operation that inserts the object into the
store, updates lifecycle `objectTypes` metadata, and maintains `objectIndex`
and `objectIndexSet` for consistency with runtime `storeObject` semantics.
Unlike the full runtime `storeObject`, this does NOT update `capabilityRefs`
(which is empty during boot) and does NOT update `asidTable` (VSpace ASID
registration is separate).

Precondition: the inserted CNode (if any) must have `slotsUnique`, and the
inserted VSpaceRoot (if any) must have `mappings.invExt`. -/
def createObject (ist : IntermediateState)
    (id : SeLe4n.ObjId) (obj : KernelObject)
    (hSlots : ∀ cn, obj = KernelObject.cnode cn → cn.slotsUnique)
    (hMappings : ∀ vs, obj = KernelObject.vspaceRoot vs → vs.mappings.invExt)
    : IntermediateState where
  state := {
    ist.state with
      objects := ist.state.objects.insert id obj
      -- T2-K: Maintain objectIndex/objectIndexSet alongside objects
      objectIndex := if ist.state.objectIndexSet.contains id then ist.state.objectIndex
                     else id :: ist.state.objectIndex
      objectIndexSet := ist.state.objectIndexSet.insert id
      lifecycle := {
        ist.state.lifecycle with
          objectTypes := ist.state.lifecycle.objectTypes.insert id obj.objectType
      }
  }
  hAllTables := by
    have h := ist.hAllTables
    unfold SystemState.allTablesInvExt at h ⊢
    refine ⟨RHTable.insert_preserves_invExt _ _ _ h.1,
           h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
           RHTable.insert_preserves_invExt _ _ _ h.2.2.2.2.2.1,
           h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
           ?_, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
    exact RHSet.insert_preserves_invExt ist.state.objectIndexSet id h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  hPerObjectSlots := by
    unfold perObjectSlotsInvariant
    intro oid cn hObj
    have hObjInv := allTablesInvExt_objects ist.hAllTables
    simp only [RHTable_getElem?_eq_get?] at hObj
    by_cases hEq : id = oid
    · subst hEq
      rw [RHTable.getElem?_insert_self ist.state.objects id obj hObjInv] at hObj
      cases hObj; exact hSlots cn rfl
    · have hNe : ¬((id == oid) = true) := by intro heq; exact hEq (eq_of_beq heq)
      rw [RHTable.getElem?_insert_ne ist.state.objects id oid obj hNe hObjInv] at hObj
      exact ist.hPerObjectSlots oid cn (by simp only [RHTable_getElem?_eq_get?]; exact hObj)
  hPerObjectMappings := by
    unfold perObjectMappingsInvariant
    intro oid vs hObj
    have hObjInv := allTablesInvExt_objects ist.hAllTables
    simp only [RHTable_getElem?_eq_get?] at hObj
    by_cases hEq : id = oid
    · subst hEq
      rw [RHTable.getElem?_insert_self ist.state.objects id obj hObjInv] at hObj
      cases hObj; exact hMappings vs rfl
    · have hNe : ¬((id == oid) = true) := by intro heq; exact hEq (eq_of_beq heq)
      rw [RHTable.getElem?_insert_ne ist.state.objects id oid obj hNe hObjInv] at hObj
      exact ist.hPerObjectMappings oid vs (by simp only [RHTable_getElem?_eq_get?]; exact hObj)
  hLifecycleConsistent := by
    constructor
    · intro oid
      simp only [SystemState.lookupObjectTypeMeta]
      have hObjInv := allTablesInvExt_objects ist.hAllTables
      have hObjTypesInv := allTablesInvExt_objectTypes ist.hAllTables
      by_cases hEq : id = oid
      · subst hEq
        simp only [RHTable_getElem?_eq_get?]
        rw [RHTable.getElem?_insert_self _ _ _ hObjTypesInv,
            RHTable.getElem?_insert_self _ _ _ hObjInv]; simp
      · have hNe : ¬((id == oid) = true) := by intro heq; exact hEq (eq_of_beq heq)
        simp only [RHTable_getElem?_eq_get?]
        rw [RHTable.getElem?_insert_ne _ _ _ _ hNe hObjTypesInv,
            RHTable.getElem?_insert_ne _ _ _ _ hNe hObjInv]
        exact ist.hLifecycleConsistent.1 oid
    · intro ref
      simp [SystemState.lookupCapabilityRefMeta, SystemState.lookupSlotCap,
            SystemState.lookupCNode]

-- ============================================================================
-- Q3-B.5: deleteObject — erase from object store
-- ============================================================================

/-- Q3-B: Delete a kernel object from the builder state.
Erases the object and its objectTypes metadata entry.

Requires `size < capacity` for RHTable erase correctness. -/
def deleteObject (ist : IntermediateState)
    (id : SeLe4n.ObjId)
    (hObjSize : ist.state.objects.size < ist.state.objects.capacity)
    (hTypesSize : ist.state.lifecycle.objectTypes.size < ist.state.lifecycle.objectTypes.capacity)
    : IntermediateState where
  state := {
    ist.state with
      objects := ist.state.objects.erase id
      lifecycle := {
        ist.state.lifecycle with
          objectTypes := ist.state.lifecycle.objectTypes.erase id
      }
  }
  hAllTables := by
    have h := ist.hAllTables
    unfold SystemState.allTablesInvExt at h ⊢
    exact ⟨RHTable.erase_preserves_invExt _ _ h.1 hObjSize,
           h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
           RHTable.erase_preserves_invExt _ _ h.2.2.2.2.2.1 hTypesSize,
           h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩
  hPerObjectSlots := by
    unfold perObjectSlotsInvariant
    intro oid cn hObj
    have hObjInv := allTablesInvExt_objects ist.hAllTables
    simp only [RHTable_getElem?_eq_get?] at hObj
    by_cases hEq : id = oid
    · subst hEq
      rw [RHTable.getElem?_erase_self ist.state.objects id hObjInv] at hObj
      cases hObj
    · have hNe : ¬((id == oid) = true) := by intro heq; exact hEq (eq_of_beq heq)
      rw [RHTable.getElem?_erase_ne ist.state.objects id oid hNe hObjInv hObjSize] at hObj
      exact ist.hPerObjectSlots oid cn (by simp only [RHTable_getElem?_eq_get?]; exact hObj)
  hPerObjectMappings := by
    unfold perObjectMappingsInvariant
    intro oid vs hObj
    have hObjInv := allTablesInvExt_objects ist.hAllTables
    simp only [RHTable_getElem?_eq_get?] at hObj
    by_cases hEq : id = oid
    · subst hEq
      rw [RHTable.getElem?_erase_self ist.state.objects id hObjInv] at hObj
      cases hObj
    · have hNe : ¬((id == oid) = true) := by intro heq; exact hEq (eq_of_beq heq)
      rw [RHTable.getElem?_erase_ne ist.state.objects id oid hNe hObjInv hObjSize] at hObj
      exact ist.hPerObjectMappings oid vs (by simp only [RHTable_getElem?_eq_get?]; exact hObj)
  hLifecycleConsistent := by
    constructor
    · intro oid
      simp only [SystemState.lookupObjectTypeMeta]
      have hObjInv := allTablesInvExt_objects ist.hAllTables
      have hObjTypesInv := allTablesInvExt_objectTypes ist.hAllTables
      by_cases hEq : id = oid
      · subst hEq
        simp only [RHTable_getElem?_eq_get?]
        rw [RHTable.getElem?_erase_self _ _ hObjTypesInv,
            RHTable.getElem?_erase_self _ _ hObjInv]; simp
      · have hNe : ¬((id == oid) = true) := by intro heq; exact hEq (eq_of_beq heq)
        simp only [RHTable_getElem?_eq_get?]
        rw [RHTable.getElem?_erase_ne _ _ _ hNe hObjTypesInv hTypesSize,
            RHTable.getElem?_erase_ne _ _ _ hNe hObjInv hObjSize]
        exact ist.hLifecycleConsistent.1 oid
    · intro ref
      simp [SystemState.lookupCapabilityRefMeta, SystemState.lookupSlotCap,
            SystemState.lookupCNode]

-- ============================================================================
-- Q3-B.6: insertCap — insert a capability into a CNode's slots
-- ============================================================================

/-- Q3-B: Insert a capability into a CNode's slot table.

Looks up the CNode at `cnodeId`, inserts `cap` at `slot`, stores the updated
CNode back. Requires the slot to be initially empty for deterministic boot. -/
private theorem insert_capacity_ge4 [BEq α] [Hashable α]
    (t : RHTable α β) (k : α) (v : β) (hCapGe4 : 4 ≤ t.capacity) :
    4 ≤ (t.insert k v).capacity := by
  unfold RHTable.insert; split
  · rw [RHTable.insertNoResize_capacity, t.resize_fold_capacity]; omega
  · rw [RHTable.insertNoResize_capacity]; exact hCapGe4

def insertCap (ist : IntermediateState)
    (cnodeId : SeLe4n.ObjId) (slot : SeLe4n.Slot) (cap : Capability)
    (cn : CNode)
    (hLookup : ist.state.objects[cnodeId]? = some (KernelObject.cnode cn))
    (_hEmpty : cn.slots[slot]? = none)
    : IntermediateState :=
  createObject ist cnodeId (KernelObject.cnode { cn with slots := cn.slots.insert slot cap })
    (fun cn'' hEq => by
      cases hEq
      have hSU := ist.hPerObjectSlots cnodeId cn hLookup
      unfold CNode.slotsUnique at hSU ⊢
      exact ⟨RHTable.insert_preserves_invExt _ _ _ hSU.1,
             RHTable.insert_size_lt_capacity cn.slots slot cap hSU.1 hSU.2.1 hSU.2.2,
             insert_capacity_ge4 cn.slots slot cap hSU.2.2⟩)
    (fun vs hEq => by cases hEq)

-- ============================================================================
-- Q3-B.7: mapPage — insert a page mapping into a VSpaceRoot
-- ============================================================================

/-- Q3-B: Map a virtual address to a physical address in a VSpaceRoot.

Looks up the VSpaceRoot at `vsId`, inserts the mapping, stores back.
Requires the virtual address to be initially unmapped. -/
def mapPage (ist : IntermediateState)
    (vsId : SeLe4n.ObjId) (vaddr : SeLe4n.VAddr)
    (paddr : SeLe4n.PAddr) (perms : PagePermissions)
    (vs : VSpaceRoot)
    (hLookup : ist.state.objects[vsId]? = some (KernelObject.vspaceRoot vs))
    (_hEmpty : vs.mappings[vaddr]? = none)
    : IntermediateState :=
  let vs' : VSpaceRoot := { vs with mappings := vs.mappings.insert vaddr (paddr, perms) }
  createObject ist vsId (KernelObject.vspaceRoot vs')
    (fun cn hEq => by cases hEq)
    (fun vs'' hEq => by
      cases hEq
      exact RHTable.insert_preserves_invExt _ _ _ (ist.hPerObjectMappings vsId vs hLookup))

end SeLe4n.Model.Builder
