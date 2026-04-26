-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.Cleanup

/-!
AN4-G.5 (LIF-M05) child module extracted from
`SeLe4n.Kernel.Lifecycle.Operations`. Contains the cleanup-primitive
preservation theorems, the `detachCNodeSlots` helper, the composite
`lifecyclePreRetypeCleanup` pipeline, the named `lifecycleCleanupPipeline`
wrapper (AN4-G.2), the `SeLe4n.Kernel.Internal.lifecycleRetypeObject`
primitive (AN4-A), and the `lifecycleRevokeDeleteRetype` composition. All
declarations retain their original names, order, and proofs. Private
helpers are promoted to file-boundary scope so the sibling
`ScrubAndUntyped` and `RetypeWrappers` modules can reference them.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- R4-A: Cleanup preservation theorems
-- ============================================================================

/-- W6-B: spliceOutMidQueueNode only modifies `objects`, preserving all other
    state fields. Bundles the scheduler, lifecycle, and serviceRegistry
    preservation proofs into a single conjunction. -/
theorem spliceOutMidQueueNode_preserves
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).scheduler = st.scheduler ∧
    (spliceOutMidQueueNode st tid).lifecycle = st.lifecycle ∧
    (spliceOutMidQueueNode st tid).serviceRegistry = st.serviceRegistry := by
  refine ⟨?_, ?_, ?_⟩ <;> (unfold spliceOutMidQueueNode; split <;> rfl)

/-- T5-E: spliceOutMidQueueNode preserves the scheduler. -/
theorem spliceOutMidQueueNode_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).scheduler = st.scheduler :=
  (spliceOutMidQueueNode_preserves st tid).1

/-- T5-E: spliceOutMidQueueNode preserves lifecycle metadata. -/
theorem spliceOutMidQueueNode_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).lifecycle = st.lifecycle :=
  (spliceOutMidQueueNode_preserves st tid).2.1

/-- T5-E: spliceOutMidQueueNode preserves serviceRegistry. -/
theorem spliceOutMidQueueNode_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).serviceRegistry = st.serviceRegistry :=
  (spliceOutMidQueueNode_preserves st tid).2.2

/-- W6-B: removeFromAllEndpointQueues only modifies `objects`, preserving
    scheduler, lifecycle, and serviceRegistry simultaneously. Reduces
    redundancy from 3 near-identical proofs to a single bundled theorem. -/
theorem removeFromAllEndpointQueues_preserves
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).scheduler = st.scheduler ∧
    (removeFromAllEndpointQueues st tid).lifecycle = st.lifecycle ∧
    (removeFromAllEndpointQueues st tid).serviceRegistry = st.serviceRegistry := by
  -- AN4-G.5 (LIF-M05): Apply `fold_preserves` directly against the whole
  -- triple invariant, seeded from the splice-preservation witness for the
  -- three fields we care about. Avoids the former `epFold` intermediate,
  -- which relied on syntactic `let ep' : Endpoint := ...` matching that
  -- reshaped to `have` when the def was imported from a sibling child
  -- module. Proving all three conjuncts at once in a bundled fold keeps
  -- the proof robust across the AN4-G.5 file-split boundary.
  have hSplice := spliceOutMidQueueNode_preserves st tid
  unfold removeFromAllEndpointQueues
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.scheduler = st.scheduler ∧
                acc.lifecycle = st.lifecycle ∧
                acc.serviceRegistry = st.serviceRegistry)
    hSplice
    (fun acc _ _ hAcc => by split <;> exact hAcc)

/-- R4-A.1 + T5-E: removeFromAllEndpointQueues preserves the scheduler. -/
theorem removeFromAllEndpointQueues_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).scheduler = st.scheduler :=
  (removeFromAllEndpointQueues_preserves st tid).1

/-- R4-A.1 + T5-E: removeFromAllEndpointQueues preserves lifecycle metadata. -/
theorem removeFromAllEndpointQueues_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).lifecycle = st.lifecycle :=
  (removeFromAllEndpointQueues_preserves st tid).2.1

/-- R4-A.1 + T5-E: removeFromAllEndpointQueues preserves serviceRegistry. -/
theorem removeFromAllEndpointQueues_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).serviceRegistry = st.serviceRegistry :=
  (removeFromAllEndpointQueues_preserves st tid).2.2

/-- W6-B: removeFromAllNotificationWaitLists only modifies `objects`, preserving
    scheduler, lifecycle, and serviceRegistry simultaneously. -/
theorem removeFromAllNotificationWaitLists_preserves
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllNotificationWaitLists st tid).scheduler = st.scheduler ∧
    (removeFromAllNotificationWaitLists st tid).lifecycle = st.lifecycle ∧
    (removeFromAllNotificationWaitLists st tid).serviceRegistry = st.serviceRegistry := by
  unfold removeFromAllNotificationWaitLists
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves st.objects st _
    (fun acc => acc.scheduler = st.scheduler ∧ acc.lifecycle = st.lifecycle ∧
                acc.serviceRegistry = st.serviceRegistry)
    ⟨rfl, rfl, rfl⟩
    (fun acc _ _ hAcc => by split <;> exact hAcc)

/-- R4-A.2: removeFromAllNotificationWaitLists preserves the scheduler. -/
theorem removeFromAllNotificationWaitLists_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllNotificationWaitLists st tid).scheduler = st.scheduler :=
  (removeFromAllNotificationWaitLists_preserves st tid).1

/-- R4-A.2: removeFromAllNotificationWaitLists preserves lifecycle metadata. -/
theorem removeFromAllNotificationWaitLists_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllNotificationWaitLists st tid).lifecycle = st.lifecycle :=
  (removeFromAllNotificationWaitLists_preserves st tid).2.1

/-- R4-A.2: removeFromAllNotificationWaitLists preserves serviceRegistry. -/
theorem removeFromAllNotificationWaitLists_serviceRegistry_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllNotificationWaitLists st tid).serviceRegistry = st.serviceRegistry :=
  (removeFromAllNotificationWaitLists_preserves st tid).2.2

/-- After cleanup, the cleaned thread is not in the run queue. -/
theorem cleanupTcbReferences_removes_from_runnable
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    ¬(tid ∈ (cleanupTcbReferences st tid).scheduler.runQueue) := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_scheduler_eq]
  rw [removeFromAllEndpointQueues_scheduler_eq]
  unfold removeRunnable
  exact RunQueue.not_mem_remove_self _ _

/-- Cleanup preserves lifecycle metadata. -/
theorem cleanupTcbReferences_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).lifecycle = st.lifecycle := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_lifecycle_eq]
  exact removeFromAllEndpointQueues_lifecycle_eq (removeRunnable st tid) tid

/-- CDT detach preserves the objects store. -/
theorem detachSlotFromCdt_objects_eq (st : SystemState) (ref : SlotRef) :
    (SystemState.detachSlotFromCdt st ref).objects = st.objects := by
  unfold SystemState.detachSlotFromCdt; split <;> rfl

/-- CDT detach preserves lifecycle metadata. -/
theorem detachSlotFromCdt_lifecycle_eq (st : SystemState) (ref : SlotRef) :
    (SystemState.detachSlotFromCdt st ref).lifecycle = st.lifecycle := by
  unfold SystemState.detachSlotFromCdt; split <;> rfl

/-- WS-H2/A-11: Detach all CDT slot references for a CNode being replaced.
    Iterates the CNode's slots and clears the cdtSlotNode/cdtNodeSlot
    bidirectional mappings for each slot, preventing orphaned CDT references. -/
def detachCNodeSlots (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) : SystemState :=
  cn.slots.fold st (fun acc slot _cap =>
    SystemState.detachSlotFromCdt acc { cnode := cnodeId, slot := slot }
  )

/-- `detachCNodeSlots` preserves the objects store (CDT-only operation). -/
theorem detachCNodeSlots_objects_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).objects = st.objects := by
  simp only [detachCNodeSlots]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots st _ (fun acc => acc.objects = st.objects)
    rfl (fun acc slot _cap hAcc => (detachSlotFromCdt_objects_eq acc
      { cnode := cnodeId, slot := slot }).trans hAcc)

/-- `detachCNodeSlots` preserves lifecycle metadata (CDT-only operation). -/
theorem detachCNodeSlots_lifecycle_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).lifecycle = st.lifecycle := by
  simp only [detachCNodeSlots]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots st _ (fun acc => acc.lifecycle = st.lifecycle)
    rfl (fun acc slot _cap hAcc => (detachSlotFromCdt_lifecycle_eq acc
      { cnode := cnodeId, slot := slot }).trans hAcc)

/-- WS-H2, R4-B.2 (M-13): Pre-retype cleanup combining TCB reference cleanup,
    CDT detach, and service registration cleanup.
    - If the current object is a TCB: clean up scheduler + IPC references.
    - If the current object is an endpoint: revoke service registrations
      backed by this endpoint to preserve `registryEndpointValid`.
    - If the current object is a CNode being replaced by a non-CNode: detach
      CDT slot mappings to prevent orphaned derivation tree references. -/
def lifecyclePreRetypeCleanup (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) : Except KernelError SystemState :=
  -- Z7-P / AJ1-A (M-14): Return donated SchedContext before destroying TCB.
  -- Error propagated — failed cleanup would leave dangling SchedContext refs.
  match (match currentObj with
    | .tcb tcb => cleanupDonatedSchedContext st tcb.tid
    | _ => .ok st) with
  | .error e => .error e
  | .ok st =>
  -- S-05/PERF-O1: Remove thread from scThreadIndex before destroying TCB.
  -- cleanupDonatedSchedContext handles .donated (via returnDonatedSchedContext);
  -- this handles .bound TCBs being retyped without prior suspension.
  let st := match currentObj with
    | .tcb tcb =>
      match tcb.schedContextBinding with
      | .bound scId => { st with scThreadIndex :=
          (scThreadIndexRemove st.scThreadIndex scId tcb.tid) }
      | _ => st  -- .donated already handled above; .unbound is a no-op
    | _ => st
  let st := match currentObj with
    | .tcb tcb => cleanupTcbReferences st tcb.tid
    | _ => st
  -- R4-B.2 (M-13): Clean up service registrations for endpoints being retyped
  let st := match currentObj with
    | .endpoint _ => cleanupEndpointServiceRegistrations st target
    | _ => st
  match currentObj with
  | .cnode cn =>
    match newObj with
    | .cnode _ => .ok st  -- CNode → CNode: no CDT cleanup needed
    | _ => .ok (detachCNodeSlots st target cn)
  | _ => .ok st

/-- AN4-G.2 (LIF-M02) — **named `lifecycleCleanupPipeline` wrapper** over
`lifecyclePreRetypeCleanup`. Takes a `RetypeTarget` (AN4-F.4 subtype) so
the caller must already carry the `cleanupHookDischarged` witness OR
establish it after a successful run. The wrapper composes the four
per-step primitives:

1. `cleanupDonatedSchedContext` (return donated SC before destroying TCB)
2. `cleanupTcbReferences` (scheduler + IPC reference scrub)
3. `cleanupEndpointServiceRegistrations` (service-endpoint detachment)
4. `detachCNodeSlots` (CDT slot-level detachment)

into a single named entry-point so consumers reading `API.lean` or the
`lifecycleRetypeWithCleanup` wrapper can reference the pipeline by name
rather than enumerating its steps. The per-step helpers remain public
because proof-chain callers (preservation theorems, cross-subsystem
bridge lemmas) reason about each step individually; the wrapper is a
**pure alias** for documentation consolidation. -/
def lifecycleCleanupPipeline (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) : Except KernelError SystemState :=
  lifecyclePreRetypeCleanup st target currentObj newObj

/-- AN4-G.2 (LIF-M02): The named wrapper is definitionally equal to
`lifecyclePreRetypeCleanup`. Use when proof contexts destructure the
wrapper by `unfold`. -/
@[simp] theorem lifecycleCleanupPipeline_eq
    (st : SystemState) (target : SeLe4n.ObjId) (currentObj newObj : KernelObject) :
    lifecycleCleanupPipeline st target currentObj newObj
      = lifecyclePreRetypeCleanup st target currentObj newObj := rfl

/-- Pre-retype cleanup only removes elements from the flat list, never adds. -/
theorem cleanupTcbReferences_flat_subset
    (st : SystemState) (tid x : SeLe4n.ThreadId)
    (h : x ∈ (cleanupTcbReferences st tid).scheduler.runQueue.flat) :
    x ∈ st.scheduler.runQueue.flat := by
  unfold cleanupTcbReferences at h
  rw [removeFromAllNotificationWaitLists_scheduler_eq] at h
  rw [removeFromAllEndpointQueues_scheduler_eq] at h
  unfold removeRunnable at h
  simp only [] at h
  exact (List.mem_filter.mp h).1

/-- CDT cleanup preserves the scheduler. -/
theorem detachCNodeSlots_scheduler_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).scheduler = st.scheduler := by
  simp only [detachCNodeSlots]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots st _ (fun acc => acc.scheduler = st.scheduler)
    rfl (fun acc slot _cap hAcc => by
      have : (SystemState.detachSlotFromCdt acc { cnode := cnodeId, slot := slot }).scheduler
          = acc.scheduler := by unfold SystemState.detachSlotFromCdt; split <;> rfl
      exact this.trans hAcc)

/-- Cleanup preserves the scheduler state. -/
theorem cleanupTcbReferences_scheduler_eq_removeRunnable
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).scheduler = (removeRunnable st tid).scheduler := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_scheduler_eq]
  exact removeFromAllEndpointQueues_scheduler_eq (removeRunnable st tid) tid

/-- Pre-retype cleanup flat list subset: any element in the post-cleanup flat
    list was in the pre-cleanup flat list. AJ1-A (M-14): conditional on `.ok`. -/
theorem lifecyclePreRetypeCleanup_flat_subset
    (st stClean : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) (x : SeLe4n.ThreadId)
    (hOk : lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean)
    (h : x ∈ stClean.scheduler.runQueue.flat) :
    x ∈ st.scheduler.runQueue.flat := by
  cases currentObj with
  | tcb tcb =>
    -- Unfold with known currentObj = .tcb tcb
    simp only [lifecyclePreRetypeCleanup] at hOk
    -- Inner match reduces to cleanupDonatedSchedContext st tcb.tid
    -- Outer match dispatches on the result
    cases hDon : cleanupDonatedSchedContext st tcb.tid with
    | error e => rw [hDon] at hOk; contradiction
    | ok stDon =>
      rw [hDon] at hOk
      have hDonSched : stDon.scheduler = st.scheduler :=
        cleanupDonatedSchedContext_scheduler_eq st stDon tcb.tid hDon
      injection hOk with hOk; subst hOk
      -- S-05/PERF-O1: scThreadIndex cleanup preserves scheduler (both branches)
      have hScIdxSched : (match tcb.schedContextBinding with
        | .bound scId => { stDon with scThreadIndex :=
            (scThreadIndexRemove stDon.scThreadIndex scId tcb.tid) }
        | _ => stDon).scheduler = stDon.scheduler := by
        cases tcb.schedContextBinding <;> rfl
      rw [cleanupTcbReferences_scheduler_eq_removeRunnable] at h
      unfold removeRunnable at h; rw [hScIdxSched, hDonSched] at h; simp only [] at h
      exact (List.mem_filter.mp h).1
  | cnode cn =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    cases newObj <;> (simp only [] at hOk; first
      | (injection hOk with hOk; subst hOk; exact h)
      | (injection hOk with hOk; subst hOk;
         have hSched := detachCNodeSlots_scheduler_eq st target cn;
         rw [show (detachCNodeSlots st target cn).scheduler.runQueue.flat =
               st.scheduler.runQueue.flat from by rw [hSched]] at h;
         exact h))
  | endpoint _ =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    injection hOk with hOk; subst hOk
    rw [cleanupEndpointServiceRegistrations_scheduler_eq] at h; exact h
  | notification _ | vspaceRoot _ | untyped _ | schedContext _ =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    injection hOk with hOk; subst hOk; exact h

namespace Internal

/-- **Internal building block — callers should use `lifecycleRetypeWithCleanup` instead.**

Retype an existing object id to a new typed object value.
This function skips `lifecyclePreRetypeCleanup` and `scrubObjectMemory`,
which means dangling references may persist and backing memory is not zeroed
(violating the H-05 safety guarantee and S6-C memory scrubbing guarantee).

AN4-A / H-02: Lives in the `SeLe4n.Kernel.Internal` namespace so a direct
reference from production dispatch code (`SeLe4n.Kernel.lifecycleRetypeObject`)
is a compile error. Proof-chain consumers, the cleanup-integrated wrappers
(`lifecycleRetypeWithCleanup`, `lifecycleRetypeDirectWithCleanup`), and the
test harness are permitted to `open SeLe4n.Kernel.Internal` — permitted
consumers are enumerated in `scripts/lifecycle_internal_allowlist.txt` and
the list is enforced by `scripts/test_tier0_hygiene.sh`.

T5-A (M-NEW-4): Marked as internal. All external retype operations must go
through `lifecycleRetypeWithCleanup` to ensure cleanup + scrubbing.

V5-B (M-DEF-2): **Internal only — do not call from new code.** This function
bypasses cleanup and memory scrubbing, violating the H-05 safety guarantee
and S6-C memory scrubbing guarantee. Production callers must use
`lifecycleRetypeWithCleanup` (CSpaceAddr path) or
`lifecycleRetypeDirectWithCleanup` (pre-resolved cap path). This definition
remains reachable only via `Internal` so the proof chain
(`lifecycleRetypeObject_ok_as_storeObject`,
`lifecycleRetypeObject_ok_lookup_preserved_ne`, etc.) can reference it by
name while production dispatch cannot.

Deterministic branch contract for M4-A step 2:
1. target object must exist,
2. lifecycle metadata for the target id must agree with object-store type (`illegalState` otherwise),
3. authority slot lookup must succeed,
4. authority must satisfy `lifecycleRetypeAuthority` (`illegalAuthority` otherwise),
5. object store + lifecycle object-type metadata are updated atomically on success. -/
def lifecycleRetypeObject
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    match st.objects[target]? with
    | none => .error .objectNotFound
    | some currentObj =>
        if st.lifecycle.objectTypes[target]? = some currentObj.objectType then
          match cspaceLookupSlot authority st with
          | .error e => .error e
          | .ok (authCap, st') =>
              if lifecycleRetypeAuthority authCap target then
                storeObject target newObj st'
              else
                .error .illegalAuthority
        else
          .error .illegalState

end Internal

-- AN4-A allowlist marker: the rest of this file may reference
-- `lifecycleRetypeObject` by bare name so the wrappers below and the associated
-- preservation theorems can compose without noisy `Internal.` prefixes.
open Internal

/-- Compose local revoke/delete cleanup with lifecycle retype.

Authority and state preconditions for deterministic success:
1. `authority ≠ cleanup` (delete-before-reuse ordering guard),
2. `cleanup` must resolve to a capability so revoke/delete can execute,
3. post-delete lookup of `cleanup` must return `invalidCapability`,
4. lifecycle retype preconditions from `lifecycleRetypeObject` must hold.

Failure branches remain explicit and ordered:
- aliasing `authority = cleanup` is rejected as `illegalState`,
- revoke/delete failures are propagated directly,
- unexpected post-delete lookup success is rejected as `illegalState`,
- final retype failures are propagated directly.

**S6-C note:** This is a low-level composition that does not perform memory
scrubbing. Callers requiring memory scrubbing (to prevent inter-domain
information leakage) should use `lifecycleRetypeWithCleanup`, which
integrates `scrubObjectMemory` between cleanup and retype.

**AN4-G.6 (LIF-M06) — partial-failure contract**: this pipeline is
**non-transactional**. An early `.error` return leaves the system state in
a partially-cleaned form — specifically:

* If `cspaceRevoke` fails, no mutations have committed; the caller's state
  is preserved.
* If `cspaceDeleteSlot` fails **after** a successful revoke, the revoked
  CDT edges remain stripped even though the slot itself is intact. The
  caller observes `.error` with the partial revoke side-effect.
* If the post-delete `cspaceLookupSlot` returns unexpectedly, both revoke
  and delete have committed; the retype is skipped but the slot was
  already scrubbed clean.
* If the final `lifecycleRetypeObject` fails, revoke + delete committed
  but the target object retains its old variant.

Callers must therefore treat `.error` from this function as a **best-effort
cleanup partially completed** outcome, NOT as a rollback. Callers needing
strict transactional semantics should invoke `cspaceRevokeCdtTransactional`
(AK8-B) separately before composing with this pipeline, or use
`lifecycleRetypeWithCleanup` which wraps the strict cleanup pipeline and
propagates errors before any retype is attempted. See `SELE4N_SPEC.md` §5
"Lifecycle partial-failure semantics" for the rollback-escalation
protocol. -/
def lifecycleRevokeDeleteRetype
    (authority cleanup : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    if authority = cleanup then
      .error .illegalState
    else
      match cspaceRevoke cleanup st with
      | .error e => .error e
      | .ok (_, stRevoked) =>
          match cspaceDeleteSlot cleanup stRevoked with
          | .error e => .error e
          | .ok (_, stDeleted) =>
              match cspaceLookupSlot cleanup stDeleted with
              | .ok _ => .error .illegalState
              | .error .invalidCapability =>
                  lifecycleRetypeObject authority target newObj stDeleted
              | .error e => .error e


end SeLe4n.Kernel
