-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.IntermediateState
import SeLe4n.Kernel.Scheduler.RunQueueLinkFrame
import SeLe4n.Kernel.InformationFlow.TaintPropagation

/-!
# Q3-B: Builder Operations — Invariant-Preserving State Construction

Builder operations apply targeted state mutations to an `IntermediateState`,
each carrying forward all four invariant witnesses. These are the only
sanctioned way to construct a non-empty `IntermediateState` during boot.

Each operation is a pure function `IntermediateState → IntermediateState`.
-/

namespace SeLe4n.Model.Builder

open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency (bootCoreId)
open SeLe4n.Model

-- ============================================================================
-- Helper: allTablesInvExtK decomposition/recomposition
-- ============================================================================

-- The named projections of `allTablesInvExtK` live beside it
-- (`SystemState.allTablesInvExtK.objects`, `.asidTable`,
-- `.objectTypes`, `.interfaceRegistry`, `.objectIndexSet`), so no proof here
-- counts conjuncts: a table added to or removed from the bundle shifts no
-- reader (WS-ZA ZA5.9 removed the service registry's, the registry being the
-- endpoints' records since).

-- ============================================================================
-- registerInterface — insert into interfaceRegistry
-- ============================================================================

/-- **WS-ZA ZA5.5**: install a service interface in the builder state, under
its own id.  Only modifies `interfaceRegistry`; all other fields are
unchanged. -/
def registerInterface (ist : IntermediateState) (spec : InterfaceSpec) : IntermediateState where
  state := { ist.state with
    interfaceRegistry := ist.state.interfaceRegistry.insert spec.ifaceId spec }
  hAllTables := by
    have h := ist.hAllTables
    exact ⟨h.objects, h.asidTable, h.objectTypes,
           RHTable.insert_preserves_invExtK _ _ _ h.interfaceRegistry, h.objectIndexSet⟩
  hPerObjectSlots := by
    intro id cn hObj; exact ist.hPerObjectSlots id cn hObj
  hPerObjectMappings := by
    intro id vs hObj; exact ist.hPerObjectMappings id vs hObj
  hLifecycleConsistent := ist.hLifecycleConsistent.of_frame rfl rfl (fun _ => rfl)
    ist.hLifecycleConsistent.types

-- ============================================================================
-- Q3-B.4: createObject — simplified boot-time object creation
-- ============================================================================

/-- Q3-B + T2-K (M-BLD-1): Insert a kernel object into the builder state
during boot.

This is a simplified builder-phase operation that inserts the object into the
store, updates lifecycle `objectTypes` metadata, and maintains `objectIndex`
and `objectIndexSet` for consistency with runtime `storeObject` semantics.
Unlike the full runtime `storeObject`, this does NOT update `asidTable`
(VSpace ASID registration is separate).

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
      -- T2-K / WS-UC UC2: the ghost bookkeeping, written as `storeObject` writes it
      objectIndexGhost :=
        if (ist.state.getObject? id).isSome then ist.state.objectIndexGhost
        else SeLe4n.Erased.mk (id :: ist.state.objectIndex)
      objectIndexSetGhost :=
        if (ist.state.getObject? id).isSome then ist.state.objectIndexSetGhost
        else SeLe4n.Erased.mk (ist.state.objectIndexSet.insert id)
      lifecycle :=
        if storeKeepsKind ist.state id obj.objectType then ist.state.lifecycle
        else { objectTypesGhost :=
          SeLe4n.Erased.mk (ist.state.lifecycle.objectTypes.insert id obj.objectType) }
  }
  hAllTables := by
    have h := ist.hAllTables
    refine ⟨RHTable.insert_preserves_invExtK _ _ _ h.objects, h.asidTable, ?_,
           h.interfaceRegistry, ?_⟩
    · show (if storeKeepsKind ist.state id obj.objectType then ist.state.lifecycle
        else _).objectTypes.invExtK
      split
      · exact h.objectTypes
      · simpa using RHTable.insert_preserves_invExtK _ id obj.objectType h.objectTypes
    · show (if (ist.state.getObject? id).isSome then ist.state.objectIndexSetGhost
        else _).out.table.invExtK
      split
      · exact h.objectIndexSet
      · simpa using RHSet.insert_preserves_invExtK ist.state.objectIndexSet id h.objectIndexSet
  hPerObjectSlots := perObjectSlotsInvariant_holds _
  hPerObjectMappings := by
    unfold perObjectMappingsInvariant
    intro oid vs hObj
    have hObjK := ist.hAllTables.objects
    simp only [RHTable_getElem?_eq_get?] at hObj
    by_cases hEq : id = oid
    · subst hEq
      rw [RHTable.getElem?_insert_self ist.state.objects id obj hObjK.1] at hObj
      cases hObj; exact hMappings vs rfl
    · have hNe : ¬((id == oid) = true) := by intro heq; exact hEq (eq_of_beq heq)
      rw [RHTable.getElem?_insert_ne ist.state.objects id oid obj hNe hObjK.1] at hObj
      exact ist.hPerObjectMappings oid vs (by simp only [RHTable_getElem?_eq_get?]; exact hObj)
  hLifecycleConsistent := by
    obtain ⟨st', hS⟩ := storeObject_isOk ist.state id obj
    have h := storeObject_preserves_bookkeepingAgreesUnbounded _ _ _ _ ist.hLifecycleConsistent
      ist.hAllTables.objects.1 hS
    unfold storeObject at hS; cases hS
    exact ⟨h.index, h.nodup, h.indexSet, h.types, h.indexSetInv, h.typesInv,
      ⟨h.presized.objectsBootSized, ist.hLifecycleConsistent.presized.asidBootSized⟩⟩

-- ============================================================================
-- Q3-B.6: insertCap — insert a capability into a CNode's slots
-- ============================================================================

-- ============================================================================
-- Make a thread runnable (PR #873 round 15)
-- ============================================================================

/-- **Put a thread in the boot core's run queue.**

The builder could create threads but not make any of them *runnable*, so every
state it could produce had an empty run queue — a shape the live kernel cannot
reach, since a thread only ever blocks from being runnable.  That gap is why the
frozen operations' failure to maintain `byPriority` stayed invisible for so long:
the frozen tests all started from states where the run queue was empty and
therefore could not show a wake failing to refill it.

The thread goes on through the kernel's own enqueue (`runEnqueueOnCore`, WS-ZA
ZA4.5), so its TCB carries the run-queue links the kernel reads and the queue
agrees with the threads, as on any state the kernel reaches; a builder that set
the queue alone produced a state where the kernel saw no runnable thread.  The
enqueue rewrites run-queue links in TCBs and nothing else, so the CNode,
VSpaceRoot and lifecycle obligations carry over, and the table invariant needs
only the object store's. -/
def markRunnable (ist : IntermediateState) (tid : SeLe4n.ThreadId)
    (prio : SeLe4n.Priority) : IntermediateState where
  state := ist.state.runEnqueueOnCore bootCoreId tid prio
  hAllTables :=
    (SystemState.runEnqueueOnCore_onlyObjectsSchedulerDiffer _ _ _ _).allTablesInvExtK
      (SystemState.runEnqueueOnCore_objects_invExtK _ _ _ _ ist.hAllTables.objects) ist.hAllTables
  hPerObjectSlots := perObjectSlotsInvariant_holds _
  hPerObjectMappings := fun id vs h => ist.hPerObjectMappings id vs
    ((SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _).get_vspaceRoot_iff.mp h)
  hLifecycleConsistent :=
    have hD := SystemState.runEnqueueOnCore_onlyObjectsSchedulerDiffer ist.state bootCoreId tid prio
    have hA := SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks ist.state bootCoreId tid prio
    ist.hLifecycleConsistent.of_frame (by rw [hD]) (by rw [hD])
      (fun x => SystemState.objects_isSome_of_getObjectType? (hA.getObjectType? x))
      (hD.objectTypeMetadataConsistent hA ist.hLifecycleConsistent.types) (by rw [hD])

/-- **Seed an object's declassification provenance.**

WS-ZA ZA5.12: the taint lives in the object it describes, so the seed writes
`t`'s words into the thread or notification at `oid` (`KernelObject.withTaintWords`);
every other kind holds none and is left as it is.  The write moves only taint
words (`SystemState.mapObjectAt_objectsAgreeOffTaint`), so the store keeps its
table invariant, every CNode's slots and every VSpaceRoot's mappings, and every
object keeps its kind.  Stated as its own operation rather than left to a record
update at the use site: updating `IntermediateState.state` in place makes Lean
re-check the whole nested `hAllTables` conjunction against the new term, which
does not terminate within the default heartbeat budget. -/
def withTaint (ist : IntermediateState) (oid : SeLe4n.ObjId)
    (t : SeLe4n.Kernel.DeclassificationTaint) : IntermediateState where
  state := ist.state.mapObjectAt oid (·.withTaintWords t.toWords)
  hAllTables :=
    SystemState.onlyObjectsSchedulerDiffer.allTablesInvExtK rfl
      ⟨SeLe4n.Kernel.RobinHood.RHTable.mapValueAt_invExt _ _ _ ist.hAllTables.objects.1,
       by simpa [SystemState.mapObjectAt] using ist.hAllTables.objects.2.1,
       by simpa [SystemState.mapObjectAt] using ist.hAllTables.objects.2.2⟩
      ist.hAllTables
  hPerObjectSlots := perObjectSlotsInvariant_holds _
  hPerObjectMappings := fun id vs h => ist.hPerObjectMappings id vs
    (((SystemState.mapObjectAt_objectsAgreeOffTaint ist.state oid _
      (KernelObject.eraseTaint_withTaintWords · _)).inert_iff id rfl).mp h)
  hLifecycleConsistent :=
    have hA := SystemState.mapObjectAt_objectsAgreeOffTaint ist.state oid _
      (KernelObject.eraseTaint_withTaintWords · t.toWords)
    have hTy := hA.objectTypeMetadataConsistent rfl ist.hLifecycleConsistent.types
    ist.hLifecycleConsistent.of_frame rfl rfl (fun x => by
      have := congrArg Option.isSome (hTy x)
      have h0 := congrArg Option.isSome (ist.hLifecycleConsistent.types x)
      simp only [Option.isSome_map] at this h0
      rw [← this, ← h0]; rfl) hTy

-- ============================================================================
-- Q3-B.7: mapPage — insert a page mapping into a VSpaceRoot
-- ============================================================================

set_option linter.unusedVariables false in
/-- AF2-C3: Every page mapped via builder-phase `mapPage` satisfies W^X.
    This is a direct consequence of the proof obligation parameter `_hWxSafe`.
    Callers must supply evidence that `perms.wxCompliant = true` at the call
    site — making W+X mappings statically impossible at the builder layer.

    The named permission constructor satisfies W^X by construction:
    - `PagePermissions.readOnly`:  `wxCompliant = true` (by `rfl`)
    - `PagePermissions.ofNat n`:   `wxCompliant` depends on bits 1 (write) and 2 (execute)

    Any `PagePermissions` value where `!(write && execute)` holds will satisfy
    the proof obligation via `by decide` or `by rfl`. This connects to
    kernel-layer enforcement at `vspaceMapPage` (Architecture/VSpace.lean:95)
    which checks `perms.wxCompliant` at runtime. -/
theorem mapPage_wxCompliant {ist : IntermediateState}
    {vsId : SeLe4n.ObjId} {vaddr : SeLe4n.VAddr}
    {paddr : SeLe4n.PAddr} {perms : PagePermissions}
    {vs : VSpaceRoot}
    {hLookup : ist.state.objects[vsId]? = some (KernelObject.vspaceRoot vs)}
    {hEmpty : vs.mappings[vaddr]? = none}
    (hWxSafe : perms.wxCompliant = true) :
    perms.wxCompliant = true := hWxSafe

end SeLe4n.Model.Builder
