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
-- Helper: allTablesInvExtK decomposition/recomposition
-- ============================================================================

/-- Extract the objects invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_objects {st : SystemState}
    (h : st.allTablesInvExtK) : st.objects.invExtK := h.1

/-- Extract irqHandlers invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_irqHandlers {st : SystemState}
    (h : st.allTablesInvExtK) : st.irqHandlers.invExtK := h.2.1

/-- Extract services invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_services {st : SystemState}
    (h : st.allTablesInvExtK) : st.services.invExtK := h.2.2.2.2.2.2.2.2.2.1

/-- Extract serviceRegistry invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_serviceRegistry {st : SystemState}
    (h : st.allTablesInvExtK) : st.serviceRegistry.invExtK := h.2.2.2.2.2.2.2.2.2.2.2.1

/-- Extract interfaceRegistry invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_interfaceRegistry {st : SystemState}
    (h : st.allTablesInvExtK) : st.interfaceRegistry.invExtK := h.2.2.2.2.2.2.2.2.2.2.1

/-- Extract objectTypes invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_objectTypes {st : SystemState}
    (h : st.allTablesInvExtK) : st.lifecycle.objectTypes.invExtK := h.2.2.2.2.2.1

/-- Extract capabilityRefs invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_capabilityRefs {st : SystemState}
    (h : st.allTablesInvExtK) : st.lifecycle.capabilityRefs.invExtK := h.2.2.2.2.2.2.1

/-- Extract objectIndexSet invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_objectIndexSet {st : SystemState}
    (h : st.allTablesInvExtK) : st.objectIndexSet.table.invExtK := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Extract asidTable invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_asidTable {st : SystemState}
    (h : st.allTablesInvExtK) : st.asidTable.invExtK := h.2.2.1

/-- Y1-F: Extract cdtSlotNode invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_cdtSlotNode {st : SystemState}
    (h : st.allTablesInvExtK) : st.cdtSlotNode.invExtK := h.2.2.2.1

/-- Y1-F: Extract cdtNodeSlot invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_cdtNodeSlot {st : SystemState}
    (h : st.allTablesInvExtK) : st.cdtNodeSlot.invExtK := h.2.2.2.2.1

/-- Y1-F: Extract cdt.childMap invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_cdtChildMap {st : SystemState}
    (h : st.allTablesInvExtK) : st.cdt.childMap.invExtK := h.2.2.2.2.2.2.2.1

/-- Y1-F: Extract cdt.parentMap invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_cdtParentMap {st : SystemState}
    (h : st.allTablesInvExtK) : st.cdt.parentMap.invExtK := h.2.2.2.2.2.2.2.2.1

/-- Y1-F: Extract scheduler.runQueue.byPriority invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_byPriority {st : SystemState}
    (h : st.allTablesInvExtK) : st.scheduler.runQueue.byPriority.invExtK := h.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Y1-F: Extract scheduler.runQueue.threadPriority invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_threadPriority {st : SystemState}
    (h : st.allTablesInvExtK) : st.scheduler.runQueue.threadPriority.invExtK := h.2.2.2.2.2.2.2.2.2.2.2.2.2.1

/-- Y1-F: Extract scheduler.runQueue.membership.table invExtK from allTablesInvExtK. -/
private theorem allTablesInvExtK_membership {st : SystemState}
    (h : st.allTablesInvExtK) : st.scheduler.runQueue.membership.table.invExtK := h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

-- Y1-G: Completeness note — all 16 conjuncts of `allTablesInvExtK` have named
-- accessors. The full list (matching the definition order in State.lean:302-324):
--  1. allTablesInvExtK_objects         (objects)
--  2. allTablesInvExtK_irqHandlers     (irqHandlers)
--  3. allTablesInvExtK_asidTable       (asidTable)
--  4. allTablesInvExtK_cdtSlotNode     (cdtSlotNode)
--  5. allTablesInvExtK_cdtNodeSlot     (cdtNodeSlot)
--  6. allTablesInvExtK_objectTypes     (lifecycle.objectTypes)
--  7. allTablesInvExtK_capabilityRefs  (lifecycle.capabilityRefs)
--  8. allTablesInvExtK_cdtChildMap     (cdt.childMap)
--  9. allTablesInvExtK_cdtParentMap    (cdt.parentMap)
-- 10. allTablesInvExtK_services       (services)
-- 11. allTablesInvExtK_interfaceRegistry (interfaceRegistry)
-- 12. allTablesInvExtK_serviceRegistry (serviceRegistry)
-- 13. allTablesInvExtK_byPriority     (scheduler.runQueue.byPriority)
-- 14. allTablesInvExtK_threadPriority (scheduler.runQueue.threadPriority)
-- 15. allTablesInvExtK_objectIndexSet (objectIndexSet.table)
-- 16. allTablesInvExtK_membership     (scheduler.runQueue.membership.table)
-- WARNING: Do not use raw tuple projections (.2.2.2...) on allTablesInvExtK.
-- Use the named accessors above instead. Raw projections are fragile and break
-- silently when fields are added or reordered.

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
    unfold SystemState.allTablesInvExtK at h ⊢
    refine ⟨h.1, ?_, h.2.2⟩
    exact RHTable.insert_preserves_invExtK _ _ _ h.2.1
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
    unfold SystemState.allTablesInvExtK at h ⊢
    exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
           h.2.2.2.2.2.1, h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.2.1,
           RHTable.insert_preserves_invExtK _ _ _ h.2.2.2.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.2.2.2⟩
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
    unfold SystemState.allTablesInvExtK at h ⊢
    refine ⟨RHTable.insert_preserves_invExtK _ _ _ h.1,
           h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
           RHTable.insert_preserves_invExtK _ _ _ h.2.2.2.2.2.1,
           h.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2.1,
           h.2.2.2.2.2.2.2.2.2.2.2.2.2.1,
           ?_, h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2⟩
    exact RHSet.insert_preserves_invExtK ist.state.objectIndexSet id h.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  hPerObjectSlots := by
    unfold perObjectSlotsInvariant
    intro oid cn hObj
    have hObjK := allTablesInvExtK_objects ist.hAllTables
    simp only [RHTable_getElem?_eq_get?] at hObj
    by_cases hEq : id = oid
    · subst hEq
      rw [RHTable.getElem?_insert_self ist.state.objects id obj hObjK.1] at hObj
      cases hObj; exact hSlots cn rfl
    · have hNe : ¬((id == oid) = true) := by intro heq; exact hEq (eq_of_beq heq)
      rw [RHTable.getElem?_insert_ne ist.state.objects id oid obj hNe hObjK.1] at hObj
      exact ist.hPerObjectSlots oid cn (by simp only [RHTable_getElem?_eq_get?]; exact hObj)
  hPerObjectMappings := by
    unfold perObjectMappingsInvariant
    intro oid vs hObj
    have hObjK := allTablesInvExtK_objects ist.hAllTables
    simp only [RHTable_getElem?_eq_get?] at hObj
    by_cases hEq : id = oid
    · subst hEq
      rw [RHTable.getElem?_insert_self ist.state.objects id obj hObjK.1] at hObj
      cases hObj; exact hMappings vs rfl
    · have hNe : ¬((id == oid) = true) := by intro heq; exact hEq (eq_of_beq heq)
      rw [RHTable.getElem?_insert_ne ist.state.objects id oid obj hNe hObjK.1] at hObj
      exact ist.hPerObjectMappings oid vs (by simp only [RHTable_getElem?_eq_get?]; exact hObj)
  hLifecycleConsistent := by
    constructor
    · intro oid
      simp only [SystemState.lookupObjectTypeMeta]
      have hObjK := allTablesInvExtK_objects ist.hAllTables
      have hTypesK := allTablesInvExtK_objectTypes ist.hAllTables
      by_cases hEq : id = oid
      · subst hEq
        simp only [RHTable_getElem?_eq_get?]
        rw [RHTable.getElem?_insert_self _ _ _ hTypesK.1,
            RHTable.getElem?_insert_self _ _ _ hObjK.1]; simp
      · have hNe : ¬((id == oid) = true) := by intro heq; exact hEq (eq_of_beq heq)
        simp only [RHTable_getElem?_eq_get?]
        rw [RHTable.getElem?_insert_ne _ _ _ _ hNe hTypesK.1,
            RHTable.getElem?_insert_ne _ _ _ _ hNe hObjK.1]
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
      exact RHTable.insert_preserves_invExtK cn.slots slot cap hSU)
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
