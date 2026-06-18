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
open SeLe4n.Kernel.Concurrency (bootCoreId)

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
    ¬(tid ∈ ((cleanupTcbReferences st tid).scheduler.runQueueOnCore bootCoreId)) := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_scheduler_eq]
  rw [removeFromAllEndpointQueues_scheduler_eq]
  unfold removeRunnable
  simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
    SchedulerState.setRunQueueOnCore_runQueueOnCore_self]
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
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots.table st _ (fun acc => acc.objects = st.objects)
    rfl (fun acc slot _cap hAcc => (detachSlotFromCdt_objects_eq acc
      { cnode := cnodeId, slot := slot }).trans hAcc)

/-- `detachCNodeSlots` preserves lifecycle metadata (CDT-only operation). -/
theorem detachCNodeSlots_lifecycle_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).lifecycle = st.lifecycle := by
  simp only [detachCNodeSlots]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots.table st _ (fun acc => acc.lifecycle = st.lifecycle)
    rfl (fun acc slot _cap hAcc => (detachSlotFromCdt_lifecycle_eq acc
      { cnode := cnodeId, slot := slot }).trans hAcc)

/-- WS-SM SM6.D (PR #822 review): does any TCB stash `rid` in its
`pendingReceiveReply` (a *server-first* receive that is waiting to hand this Reply
object to its next `Call`)?  Such a Reply is "in use" even though its `caller` is
still `none` — retyping/deleting it would leave the waiting server pointing at a
removed Reply, so the next `Call` rendezvous rolls back and the server cannot
accept Call IPC.  Used by `lifecyclePreRetypeCleanup` to reject the retype. -/
def replyIsStashed (st : SystemState) (rid : SeLe4n.ReplyId) : Bool :=
  st.objects.fold (init := false) fun acc _oid obj =>
    acc || match obj with
      -- PR #822 review: a stash reserves the Reply only while the server is STILL
      -- blocked on its server-first receive, awaiting the next `Call` to link.  The
      -- moment the server is woken by anything *other* than that Call — a bound
      -- notification (`notificationSignalBoundOnCore`), a `Send` rendezvous, a
      -- cancellation — its receive is over and the Reply is free, even if the
      -- now-`.ready` TCB's `pendingReceiveReply` field has not yet been scrubbed.
      -- (A server woken *by* its Call is covered by `reply.caller`, set in the same
      -- atomic transition.)  Tying "stashed" to `.blockedOnReceive` makes the
      -- predicate robust to any wake path that does not eager-clear the stash, so a
      -- ready server never keeps the Reply permanently in use.
      | .tcb t =>
          match t.ipcState with
          | .blockedOnReceive _ => t.pendingReceiveReply == some rid
          | _ => false
      | _ => false

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
  | .reply r =>
    -- WS-SM SM6.D (PR #822 review): reject retyping/deleting a Reply object that
    -- is still in use.  Two in-use forms: (1) a caller is blocked awaiting its
    -- reply (`r.caller.isSome` — caller-first link); (2) a server-first receiver
    -- has stashed this Reply in its `pendingReceiveReply` awaiting its next Call
    -- (`replyIsStashed`, `r.caller` still `none`).  Either way, freeing it strands
    -- the caller / blocks the server (the later `.reply` / `linkServerFirstCaller`
    -- fails `.replyCapInvalid`).  Mirrors seL4's revoke/clear-before-destroy: the
    -- holder must first reply to (or cancel) the outstanding caller, or the server
    -- must re-`Recv`, clearing the link before the object is freed.
    -- PR #822 review: check stashes by the *target* ObjId's canonical ReplyId, not
    -- the reply's internal `r.replyId` field (which can be the `Reply.empty`
    -- sentinel on a freshly retyped object); a server-first receive stashes
    -- `pendingReceiveReply = some (ReplyId.ofNat target)`, so derive the id from
    -- `target` to avoid missing the stash and freeing a still-referenced Reply.
    if r.caller.isSome || replyIsStashed st (SeLe4n.ReplyId.ofNat target.toNat) then
      .error .revocationRequired
    else .ok st
  | .tcb tcb =>
    -- WS-SM SM6.D (PR #822 review): reject retyping a caller TCB that still holds a
    -- reply link (`replyObject = some rid`, a `blockedOnReply` caller awaiting its
    -- reply).  Freeing the TCB would leave the Reply with `caller = some tid`
    -- pointing at the gone thread, so the later `.reply` resolves a stale caller and
    -- never consumes the Reply.  Mirrors the Reply reject + seL4 revoke-before-
    -- destroy: the outstanding reply must be replied-to / cancelled first.
    if tcb.replyObject.isSome then .error .revocationRequired else .ok st
  | _ => .ok st

/-- AN4-G.2 (LIF-M02) — **named `lifecycleCleanupPipeline` wrapper** over
`lifecyclePreRetypeCleanup`. The companion `RetypeTarget` subtype
(AN4-F.4, defined in `Capability/Invariant/Defs.lean`) requires callers
to carry the `cleanupHookDischarged` witness; under WS-RC R4.B that
witness now demands a `ScrubToken` produced by a successful invocation
of this very pipeline (see `ScrubToken.fromCleanup`). External
discharge of the predicate by re-deriving observable post-state facts
alone is structurally impossible. The wrapper composes the four
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
    (h : x ∈ ((cleanupTcbReferences st tid).scheduler.runQueueOnCore bootCoreId).flat) :
    x ∈ (st.scheduler.runQueueOnCore bootCoreId).flat := by
  unfold cleanupTcbReferences at h
  rw [removeFromAllNotificationWaitLists_scheduler_eq] at h
  rw [removeFromAllEndpointQueues_scheduler_eq] at h
  unfold removeRunnable at h
  simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
    SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at h
  exact (List.mem_filter.mp h).1

/-- CDT cleanup preserves the scheduler. -/
theorem detachCNodeSlots_scheduler_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).scheduler = st.scheduler := by
  simp only [detachCNodeSlots]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots.table st _ (fun acc => acc.scheduler = st.scheduler)
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
    (h : x ∈ (stClean.scheduler.runQueueOnCore bootCoreId).flat) :
    x ∈ (st.scheduler.runQueueOnCore bootCoreId).flat := by
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
      -- PR #822 review: with the donation resolved, the final `.tcb` arm rejects a
      -- TCB still holding a reply link (`.error`, vacuous on `.ok`); reduce the
      -- reject-`if` away on the `.ok` path and finish the cleanup-identity proof.
      simp only [] at hOk
      have hRO : tcb.replyObject.isSome = false := by
        cases hr : tcb.replyObject.isSome with
        | false => rfl
        | true => rw [if_pos hr] at hOk; exact absurd hOk (by simp)
      rw [if_neg (by simp [hRO])] at hOk
      injection hOk with hOk; subst hOk
      -- S-05/PERF-O1: scThreadIndex cleanup preserves scheduler (both branches)
      have hScIdxSched : (match tcb.schedContextBinding with
        | .bound scId => { stDon with scThreadIndex :=
            (scThreadIndexRemove stDon.scThreadIndex scId tcb.tid) }
        | _ => stDon).scheduler = stDon.scheduler := by
        cases tcb.schedContextBinding <;> rfl
      rw [cleanupTcbReferences_scheduler_eq_removeRunnable] at h
      unfold removeRunnable at h; rw [hScIdxSched, hDonSched] at h
      simp only [SchedulerState.setCurrentOnCore_runQueueOnCore,
        SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at h
      exact (List.mem_filter.mp h).1
  | cnode cn =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    cases newObj <;> (simp only [] at hOk; first
      | (injection hOk with hOk; subst hOk; exact h)
      | (injection hOk with hOk; subst hOk;
         have hSched := detachCNodeSlots_scheduler_eq st target cn;
         rw [show ((detachCNodeSlots st target cn).scheduler.runQueueOnCore bootCoreId).flat =
               (st.scheduler.runQueueOnCore bootCoreId).flat from by rw [hSched]] at h;
         exact h))
  | endpoint _ =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    injection hOk with hOk; subst hOk
    rw [cleanupEndpointServiceRegistrations_scheduler_eq] at h; exact h
  | notification _ | vspaceRoot _ | untyped _ | schedContext _ =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    injection hOk with hOk; subst hOk; exact h
  | reply r =>
    -- WS-SM SM6.D (PR #822 review): an in-use reply errors (vacuous on `.ok`);
    -- a free reply is a scheduler-identity cleanup like the kinds above.
    simp only [lifecyclePreRetypeCleanup] at hOk
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk; exact h

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
