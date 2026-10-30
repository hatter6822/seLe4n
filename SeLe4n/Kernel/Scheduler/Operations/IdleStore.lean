-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Model.IntermediateState
import SeLe4n.Kernel.Scheduler.IdleThread
import SeLe4n.Kernel.Scheduler.RunQueueLinkFrame

/-!
# The per-core idle store — one body for the kernel model and the boot

`storeIdleThreadOnCore` stores core `c`'s ready idle TCB at
`(idleThreadId c).toObjId` and writes nothing else: **an idle thread is never
queued**.  As in seL4, the idle thread runs only when its core's run queue holds
nothing to dispatch — the scheduling point's `idleFallbackOnCore` makes it
current then — and a preemption never puts it back on a queue
(`runEnqueueAdmits` refuses it).  So the queue a core selects from holds user
threads alone, and no scheduler proof has an idle member to step around
(`currentDequeuedUnique.idleOff`).

It is also **what the production boot runs**: `Platform.Boot.storeIdleThread
ist c` is this operation on `ist.state`, with the intermediate state's four
structural witnesses carried by the theorems in §3 below.  The definition lives
here, in a production module upstream of the boot, so the boot and the kernel
model share one body; `PerCoreIdle` keeps the per-core scheduler-invariant
surface and consumes this.

What is stated here is exactly what is stated over `Model` vocabulary: the
definitional frames (§1), the object-store frames and the run-queue agreement
(§2), and the four `IntermediateState` witnesses plus the index bound the boot's
capacity theorem reads (§3).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency (CoreId)

-- ============================================================================
-- §1  `storeIdleThreadOnCore` and its definitional frames
-- ============================================================================

/-- Store core `c`'s ready idle TCB.  Through the pure store
`SystemState.withObjectStored`, because the key may hold nothing and a store is
what registers a new object in `objectIndex`, `objectIndexSet` and the kind
table.  The TCB claims no run-queue place (`readyIdleThread` carries no run
links), and no queue is written.

Footprint: WRITES the object-store slot `(idleThreadId c).toObjId` alone,
guarded by the table-level `objStore` lock (`storeIdleThreadOnCoreLockSet`,
`PerCoreIdle`). -/
def storeIdleThreadOnCore (st : SystemState) (c : CoreId) : SystemState :=
  st.withObjectStored (idleThreadId c).toObjId (KernelObject.tcb (readyIdleThread c))

/-- WS-ZA ZA6.2: the compiled store.  The idle TCB is built from the defaults'
constants, its register file among them, which the compiled kernel holds as
shared values, so the first entry that saved a frame into it (the first tick on
a core running its idle thread) copied the file.  The store gives it its own
cells (`KernelObject.unshare`, the identity), as the boot does every initial
object (`createBootObject`).  Proven equal (`storeIdleThreadOnCore_eq_impl`). -/
def storeIdleThreadOnCoreImpl (st : SystemState) (c : CoreId) : SystemState :=
  st.withObjectStored (idleThreadId c).toObjId (KernelObject.tcb (readyIdleThread c)).unshare

@[csimp] theorem storeIdleThreadOnCore_eq_impl :
    @storeIdleThreadOnCore = @storeIdleThreadOnCoreImpl := rfl

/-- The store writes no scheduler field. -/
theorem storeIdleThreadOnCore_scheduler (st : SystemState) (c : CoreId) :
    (storeIdleThreadOnCore st c).scheduler = st.scheduler :=
  SystemState.withObjectStored_scheduler _ _ _

/-- The store frames the machine state. -/
theorem storeIdleThreadOnCore_machine (st : SystemState) (c : CoreId) :
    (storeIdleThreadOnCore st c).machine = st.machine :=
  storeObject_machine_eq _ _ _ _ (SystemState.storeObject_eq_withObjectStored _ _ _)

/-- The store's object table is the insert. -/
theorem storeIdleThreadOnCore_objects (st : SystemState) (c : CoreId) :
    (storeIdleThreadOnCore st c).objects =
      st.objects.insert (idleThreadId c).toObjId (KernelObject.tcb (readyIdleThread c)) :=
  SystemState.withObjectStored_objects _ _ _

/-- No core's run queue changes: the idle thread is placed on none. -/
theorem storeIdleThreadOnCore_runQueueOnCore (st : SystemState) (c c' : CoreId) :
    (storeIdleThreadOnCore st c).scheduler.runQueueOnCore c' =
      st.scheduler.runQueueOnCore c' := by
  rw [storeIdleThreadOnCore_scheduler]

/-- The store does not touch any core's active domain. -/
theorem storeIdleThreadOnCore_activeDomainOnCore (st : SystemState) (c c' : CoreId) :
    (storeIdleThreadOnCore st c).scheduler.activeDomainOnCore c' =
      st.scheduler.activeDomainOnCore c' := by
  rw [storeIdleThreadOnCore_scheduler]

/-- The store does not touch any core's current slot. -/
theorem storeIdleThreadOnCore_currentOnCore (st : SystemState) (c c' : CoreId) :
    (storeIdleThreadOnCore st c).scheduler.currentOnCore c' =
      st.scheduler.currentOnCore c' := by
  rw [storeIdleThreadOnCore_scheduler]

-- ============================================================================
-- §2  The object-store frames and the run-queue agreement
-- ============================================================================

/-- After the store, core `c`'s idle slot holds the ready idle TCB. -/
theorem storeIdleThreadOnCore_objects_self (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    (storeIdleThreadOnCore st c).objects[(idleThreadId c).toObjId]? =
      some (KernelObject.tcb (readyIdleThread c)) :=
  SystemState.withObjectStored_objects_self _ _ _ hInv

/-- The store frames the object-store slot of any distinct `ObjId`. -/
theorem storeIdleThreadOnCore_objects_ne (st : SystemState) (c : CoreId) (oid : SeLe4n.ObjId)
    (hInv : st.objects.invExt) (h : (idleThreadId c).toObjId ≠ oid) :
    (storeIdleThreadOnCore st c).objects[oid]? = st.objects[oid]? := by
  rw [storeIdleThreadOnCore_objects]
  have hNe : ¬(((idleThreadId c).toObjId == oid) = true) := fun heq => h (eq_of_beq heq)
  simp only [RHTable_getElem?_eq_get?]
  exact RHTable.getElem?_insert_ne st.objects (idleThreadId c).toObjId oid _ hNe hInv

/-- After the store, core `c`'s idle thread resolves to the ready idle TCB. -/
theorem storeIdleThreadOnCore_getTcb?_self (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    (storeIdleThreadOnCore st c).getTcb? (idleThreadId c) = some (readyIdleThread c) :=
  (SystemState.getTcb?_eq_some_iff _ _ _).mpr (storeIdleThreadOnCore_objects_self st c hInv)

/-- Every other thread resolves as before. -/
theorem storeIdleThreadOnCore_getTcb?_ne (st : SystemState) (c : CoreId)
    (other : SeLe4n.ThreadId) (hInv : st.objects.invExt) (hNe : other ≠ idleThreadId c) :
    (storeIdleThreadOnCore st c).getTcb? other = st.getTcb? other := by
  have hNeO : (idleThreadId c).toObjId ≠ other.toObjId := fun he =>
    hNe (ThreadId.toObjId_injective _ _ he).symm
  unfold SystemState.getTcb?
  rw [storeIdleThreadOnCore_objects_ne st c _ hInv hNeO]

/-- The store keeps every run queue in agreement with the threads' links,
provided no queue holds core `c`'s idle thread: the stored TCB claims no place
and no queue is written. -/
theorem storeIdleThreadOnCore_runQueueRefined (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hR : st.runQueueRefined)
    (hNone : ∀ c', (st.scheduler.runQueueOnCore c').contains (idleThreadId c) = false) :
    (storeIdleThreadOnCore st c).runQueueRefined :=
  SystemState.withObjectStored_tcb_runQueueRefined (t := readyIdleThread c) hInv rfl
    (fun c' => by rw [(hR c').contains]; exact hNone c') hR

/-- The store preserves the object-store RobinHood invariant. -/
theorem storeIdleThreadOnCore_preserves_objects_invExt (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) : (storeIdleThreadOnCore st c).objects.invExt :=
  SystemState.withObjectStored_preserves_objects_invExt _ _ _ hInv

-- ============================================================================
-- §3  The boot's structural witnesses
-- ============================================================================

/-- The store adds at most one index entry. -/
theorem storeIdleThreadOnCore_objectIndex_length_le (st : SystemState) (c : CoreId) :
    (storeIdleThreadOnCore st c).objectIndex.length ≤ st.objectIndex.length + 1 :=
  SystemState.withObjectStored_objectIndex_length_le _ _ _

/-- The store preserves `allTablesInvExtK`. -/
theorem storeIdleThreadOnCore_preserves_allTablesInvExtK (st : SystemState) (c : CoreId)
    (hAll : st.allTablesInvExtK) : (storeIdleThreadOnCore st c).allTablesInvExtK :=
  SystemState.withObjectStored_preserves_allTablesInvExtK _ _ _ hAll

/-- The store preserves the per-object slot invariant, which every slot store
satisfies by construction (`perObjectSlotsInvariant_holds`). -/
theorem storeIdleThreadOnCore_preserves_perObjectSlotsInvariant (st : SystemState)
    (c : CoreId) (_hInv : st.objects.invExt) (_hSlots : perObjectSlotsInvariant st) :
    perObjectSlotsInvariant (storeIdleThreadOnCore st c) :=
  perObjectSlotsInvariant_holds _

/-- The store preserves the per-object VSpace-mapping invariant, for the same
reason. -/
theorem storeIdleThreadOnCore_preserves_perObjectMappingsInvariant (st : SystemState)
    (c : CoreId) (hInv : st.objects.invExt) (hMappings : perObjectMappingsInvariant st) :
    perObjectMappingsInvariant (storeIdleThreadOnCore st c) := by
  intro oid vs hObj
  by_cases hEq : (idleThreadId c).toObjId = oid
  · subst hEq
    rw [storeIdleThreadOnCore_objects_self st c hInv] at hObj
    cases hObj
  · rw [storeIdleThreadOnCore_objects_ne st c oid hInv hEq] at hObj
    exact hMappings oid vs hObj

/-- The store preserves the lifecycle metadata's consistency with the object
store — the store's own theorem. -/
theorem storeIdleThreadOnCore_preserves_objectTypeMetadataConsistent (st : SystemState)
    (c : CoreId) (hAll : st.allTablesInvExtK)
    (hC : SystemState.objectTypeMetadataConsistent st) :
    SystemState.objectTypeMetadataConsistent (storeIdleThreadOnCore st c) :=
  SystemState.withObjectStored_preserves_objectTypeMetadataConsistent _ _ _
    hAll.objects.1 hAll.objectTypes.1 hC

end SeLe4n.Kernel
