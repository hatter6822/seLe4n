-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations.Cleanup
-- WS-SM SM6.E: `returnDonatedSchedContext_preserves_objects_invExt` (AI4-A),
-- consumed by `cleanupDonatedSchedContext_preserves_objects_invExt`.
import SeLe4n.Kernel.IPC.Invariant.Defs

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

/-- WS-SM SM7.B: spliceOutMidQueueNode only modifies `objects` — the
TLB-shootdown state is framed (`pendingBounded` bundle-carriage leaf). -/
theorem spliceOutMidQueueNode_tlbShootdown_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).tlbShootdown = st.tlbShootdown := by
  unfold spliceOutMidQueueNode; split <;> rfl

/-- WS-SM SM8.B: spliceOutMidQueueNode only modifies `objects` — the machine
(and hence every core's register bank) is framed.  The information-flow
counterpart of `spliceOutMidQueueNode_scheduler_eq`: per-core confinement reads
the register banks as well as the scheduler slots, so the scheduler frame alone
does not bound a step's observable writes. -/
theorem spliceOutMidQueueNode_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (spliceOutMidQueueNode st tid).machine = st.machine := by
  unfold spliceOutMidQueueNode; split <;> rfl

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
    (fun acc _ _ hAcc => by split <;> first | exact hAcc | (split <;> exact hAcc))

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

/-- WS-SM SM7.B: removeFromAllEndpointQueues only modifies `objects` — the
TLB-shootdown state is framed.  Same fold-preservation argument as
`removeFromAllEndpointQueues_preserves`, seeded from the splice frame. -/
theorem removeFromAllEndpointQueues_tlbShootdown_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).tlbShootdown = st.tlbShootdown := by
  have hSplice := spliceOutMidQueueNode_tlbShootdown_eq st tid
  unfold removeFromAllEndpointQueues
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.tlbShootdown = st.tlbShootdown)
    hSplice
    (fun acc _ _ hAcc => by split <;> first | exact hAcc | (split <;> exact hAcc))

/-- WS-SM SM8.B: removeFromAllEndpointQueues only modifies `objects` — the
machine is framed.  Same fold-preservation argument as
`removeFromAllEndpointQueues_tlbShootdown_eq`, seeded from the splice frame. -/
theorem removeFromAllEndpointQueues_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllEndpointQueues st tid).machine = st.machine := by
  have hSplice := spliceOutMidQueueNode_machine_eq st tid
  unfold removeFromAllEndpointQueues
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.machine = st.machine)
    hSplice
    (fun acc _ _ hAcc => by split <;> first | exact hAcc | (split <;> exact hAcc))

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
    (fun acc _ _ hAcc => by split <;> first | exact hAcc | (split <;> exact hAcc))

/-- WS-SM SM8.B: removeFromAllNotificationWaitLists only modifies `objects` —
the machine is framed. -/
theorem removeFromAllNotificationWaitLists_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllNotificationWaitLists st tid).machine = st.machine := by
  unfold removeFromAllNotificationWaitLists
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves st.objects st _
    (fun acc => acc.machine = st.machine)
    rfl
    (fun acc _ _ hAcc => by split <;> first | exact hAcc | (split <;> exact hAcc))

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

/-- WS-SM SM7.B: removeFromAllNotificationWaitLists only modifies `objects`
— the TLB-shootdown state is framed. -/
theorem removeFromAllNotificationWaitLists_tlbShootdown_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (removeFromAllNotificationWaitLists st tid).tlbShootdown = st.tlbShootdown := by
  unfold removeFromAllNotificationWaitLists
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves st.objects st _
    (fun acc => acc.tlbShootdown = st.tlbShootdown)
    rfl
    (fun acc _ _ hAcc => by split <;> first | exact hAcc | (split <;> exact hAcc))

/-- WS-SM SM7.B: the composed TCB reference scrub only modifies scheduler
and `objects` — the TLB-shootdown state is framed. -/
theorem cleanupTcbReferences_tlbShootdown_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).tlbShootdown = st.tlbShootdown := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_tlbShootdown_eq,
      removeFromAllEndpointQueues_tlbShootdown_eq]
  -- Via the sweep's own frame.  Reducing through `removeRunnableFromAllCores`
  -- here would have to whnf the per-core guard at every core.
  exact removeRunnableFromAllCores_tlbShootdown st tid

-- ============================================================================
-- WS-SM SM6.E: cleanup primitives preserve `objects.invExt`
-- ============================================================================
-- The per-step Robin-Hood external invariant, needed by the SM6.E
-- cancellation invariant surface (`cancelIpcBlocking_preserves_objects_invExt`
-- composes these with `restoreToReady_invExt`).  Every mutation below is an
-- `objects.insert`, so each step is `RHTable.insert_preserves_invExt` and the
-- store-wide sweeps compose via `RHTable.fold_preserves`.

/-- WS-SM SM6.E: `spliceOutMidQueueNode` preserves `objects.invExt` — the two
link patches (predecessor `queueNext`, successor `queuePrev`) are each a
single conditional `objects.insert`. -/
theorem spliceOutMidQueueNode_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (spliceOutMidQueueNode st tid).objects.invExt := by
  unfold spliceOutMidQueueNode
  split
  · exact hInv
  · -- Some-TCB arm: the two link patches are each a conditional insert over
    -- the previous table.  Every match leaf is either the untouched table
    -- (`hInv`) or a chain of at most two `insert`s over it; the cascade
    -- closes leaves with `hInv`, peels `insert`s via
    -- `insert_preserves_invExt`, and splits stuck matches until done.
    dsimp only
    repeat' first
      | exact hInv
      | exact SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hInv
      | apply SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt
      | split

/-- WS-SM SM6.E: `removeFromAllEndpointQueues` preserves `objects.invExt` —
the splice preserves it, and the endpoint sweep is a fold whose every step
is an `objects.insert`. -/
theorem removeFromAllEndpointQueues_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (removeFromAllEndpointQueues st tid).objects.invExt := by
  unfold removeFromAllEndpointQueues
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.objects.invExt)
    (spliceOutMidQueueNode_preserves_objects_invExt st tid hInv)
    (fun acc _ _ hAcc => by
      split
      · split
        · exact SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hAcc
        · exact hAcc
      · exact hAcc)

/-- WS-SM SM6.E: `removeFromAllNotificationWaitLists` preserves
`objects.invExt` — the waiter-list sweep is a fold whose every step is an
`objects.insert`. -/
theorem removeFromAllNotificationWaitLists_preserves_objects_invExt
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (removeFromAllNotificationWaitLists st tid).objects.invExt := by
  unfold removeFromAllNotificationWaitLists
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves st.objects st _
    (fun acc => acc.objects.invExt) hInv
    (fun acc _ _ hAcc => by
      split
      · split
        · exact SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hAcc
        · exact hAcc
      · exact hAcc)


-- ============================================================================
-- WS-SM SM6.E: per-key lookup characterisation of the cleanup sweeps
-- ============================================================================
-- The frame facts the cross-core cancellation composite needs closed-form:
-- a key holding a TCB before the sweep holds a TCB with the **same
-- `cpuAffinity`** afterwards (the sweeps rewrite endpoints/notifications and
-- patch queue-link fields only), and a key holding no TCB never acquires
-- one.  Built on the SM6.E fold keystone
-- (`RHTable.fold_preserves_of_lookup`): the fold step learns the visited
-- key's stored value, so an endpoint-valued visit can never alias a
-- TCB-holding key.

/-- WS-SM SM6.E: re-inserting an affinity-preserving rewrite `q` of the TCB
`p` read at key `nid` preserves TCB-kind and `cpuAffinity` at every key that
held a TCB before the insert — the single-step frame instantiated by both
`spliceOutMidQueueNode` link patches and by every conditional TCB rewrite in
the suspend teardown (`restoreToReady`, `clearTcbReplyObject`). -/
theorem insert_tcb_rewrite_lookup
    (objs : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject)
    (nid k : SeLe4n.ObjId) (p q t0 : TCB)
    (hInv : objs.invExt)
    (hRead : objs[nid]? = some (.tcb p))
    (hAff : q.cpuAffinity = p.cpuAffinity)
    (hPre : objs[k]? = some (.tcb t0)) :
    ∃ t' : TCB, (objs.insert nid (.tcb q))[k]? = some (.tcb t')
      ∧ t'.cpuAffinity = t0.cpuAffinity := by
  by_cases hK : nid = k
  · -- The patched neighbour *is* `k`: the read value is `t0` (lookup
    -- determinism), and the rewrite preserves `cpuAffinity` by hypothesis.
    subst hK
    have hpt : p = t0 := by
      rw [hPre] at hRead
      injection hRead with h
      injection h with h
      exact h.symm
    subst hpt
    exact ⟨q, SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self _ _ _ hInv, hAff⟩
  · refine ⟨t0, ?_, rfl⟩
    show (objs.insert nid (.tcb q)).get? k = some (.tcb t0)
    rw [SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _
      (fun hbeq => hK (eq_of_beq hbeq)) hInv]
    exact hPre

/-- WS-SM SM6.E: `spliceOutMidQueueNode` preserves TCB-kind and `cpuAffinity`
at every key — the link patches write `.tcb` values that differ from the
values they read only in intrusive queue-link fields. -/
theorem spliceOutMidQueueNode_tcb_lookup
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    ∃ t' : TCB, (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t')
      ∧ t'.cpuAffinity = t0.cpuAffinity := by
  simp only [spliceOutMidQueueNode]
  cases lookupTcb st tid with
  | none => exact ⟨t0, hPre, rfl⟩
  | some tcb =>
    simp only []
    cases tcb.queuePrev with
    | none =>
      -- No predecessor patch: the successor patch acts on `st.objects`.
      simp only []
      cases tcb.queueNext with
      | none => exact ⟨t0, hPre, rfl⟩
      | some nextTid =>
        simp only []
        cases hL2 : st.objects[nextTid.toObjId]? with
        | none => exact ⟨t0, hPre, rfl⟩
        | some obj =>
          cases obj
          case tcb nextTcb =>
            exact insert_tcb_rewrite_lookup st.objects nextTid.toObjId k nextTcb
              _ t0 hInv hL2 rfl hPre
          all_goals exact ⟨t0, hPre, rfl⟩
    | some prevTid =>
      simp only []
      cases hL : st.objects[prevTid.toObjId]? with
      | none =>
        -- Absent predecessor entry: successor patch over `st.objects`.
        simp only []
        cases tcb.queueNext with
        | none => exact ⟨t0, hPre, rfl⟩
        | some nextTid =>
          simp only []
          cases hL2 : st.objects[nextTid.toObjId]? with
          | none => exact ⟨t0, hPre, rfl⟩
          | some obj =>
            cases obj
            case tcb nextTcb =>
              exact insert_tcb_rewrite_lookup st.objects nextTid.toObjId k nextTcb
                _ t0 hInv hL2 rfl hPre
            all_goals exact ⟨t0, hPre, rfl⟩
      | some obj =>
        cases obj
        case tcb prevTcb =>
          -- Predecessor patch applied: stage 2 acts on the patched table.
          simp only []
          cases tcb.queueNext with
          | none =>
            exact insert_tcb_rewrite_lookup st.objects prevTid.toObjId k prevTcb
              _ t0 hInv hL rfl hPre
          | some nextTid =>
            simp only []
            have hInv1 : (st.objects.insert prevTid.toObjId
                (.tcb { prevTcb with queueNext := some nextTid })).invExt :=
              SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hInv
            obtain ⟨t₁, hL1, hAff1⟩ :=
              insert_tcb_rewrite_lookup st.objects prevTid.toObjId k prevTcb
                { prevTcb with queueNext := some nextTid } t0 hInv hL rfl hPre
            cases hL2 : (st.objects.insert prevTid.toObjId
                (.tcb { prevTcb with queueNext := some nextTid }))[nextTid.toObjId]? with
            | none => exact ⟨t₁, hL1, hAff1⟩
            | some obj2 =>
              cases obj2
              case tcb nextTcb =>
                obtain ⟨t₂, hL2', hAff2⟩ :=
                  insert_tcb_rewrite_lookup
                    (st.objects.insert prevTid.toObjId
                      (.tcb { prevTcb with queueNext := some nextTid }))
                    nextTid.toObjId k nextTcb
                    { nextTcb with queuePrev := some prevTid } t₁ hInv1 hL2 rfl hL1
                exact ⟨t₂, hL2', hAff2.trans hAff1⟩
              all_goals exact ⟨t₁, hL1, hAff1⟩
        all_goals
          -- Non-TCB predecessor entry: successor patch over `st.objects`.
          (simp only []
           cases tcb.queueNext with
           | none => exact ⟨t0, hPre, rfl⟩
           | some nextTid =>
             simp only []
             cases hL2 : st.objects[nextTid.toObjId]? with
             | none => exact ⟨t0, hPre, rfl⟩
             | some obj2 =>
               cases obj2
               case tcb nextTcb =>
                 exact insert_tcb_rewrite_lookup st.objects nextTid.toObjId k nextTcb
                   _ t0 hInv hL2 rfl hPre
               all_goals exact ⟨t0, hPre, rfl⟩)

/-- WS-SM SM6.E: the endpoint sweep preserves TCB-kind and `cpuAffinity` at
every key (and `objects.invExt`) — every fold step rewrites an
`.endpoint`-valued key, which can never alias a TCB-holding key (the fold
keystone `RHTable.fold_preserves_of_lookup` supplies the visited key's
stored value, so the kind clash discharges the disequality). -/
theorem removeFromAllEndpointQueues_tcb_lookup
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    (removeFromAllEndpointQueues st tid).objects.invExt
    ∧ ∃ t' : TCB,
      (removeFromAllEndpointQueues st tid).objects[k]? = some (.tcb t')
      ∧ t'.cpuAffinity = t0.cpuAffinity := by
  obtain ⟨t₁, hL1, hAff1⟩ := spliceOutMidQueueNode_tcb_lookup st tid k t0 hInv hPre
  have hInvS := spliceOutMidQueueNode_preserves_objects_invExt st tid hInv
  unfold removeFromAllEndpointQueues
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.objects.invExt ∧ ∃ t' : TCB,
      acc.objects[k]? = some (.tcb t') ∧ t'.cpuAffinity = t0.cpuAffinity)
    hInvS
    ⟨hInvS, t₁, hL1, hAff1⟩
    (fun acc x v hV hAcc => by
      obtain ⟨hAccInv, t', hL', hAff'⟩ := hAcc
      split
      · -- `.endpoint` step: the visited key holds an endpoint, so it cannot
        -- be `k` (which holds a TCB in the fold source by `hL1`).  The
        -- write-set-honest sweep only inserts when the victim touches the
        -- endpoint's head/tail slots (PR #831 review 4); the untouched arm
        -- is the identity.
        split
        · have hNe : ¬(x == k) = true := fun hbeq => by
            have hxk : x = k := eq_of_beq hbeq
            subst hxk
            have hclash := hL1.symm.trans hV
            injection hclash with h
            injection h
          exact ⟨SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hAccInv,
            t',
            (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _
              hNe hAccInv).trans hL',
            hAff'⟩
        · exact ⟨hAccInv, t', hL', hAff'⟩
      · exact ⟨hAccInv, t', hL', hAff'⟩)

/-- WS-SM SM6.E: the notification sweep preserves TCB-kind and `cpuAffinity`
at every key (and `objects.invExt`) — every fold step rewrites a
`.notification`-valued key, which can never alias a TCB-holding key. -/
theorem removeFromAllNotificationWaitLists_tcb_lookup
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt)
    (hPre : st.objects[k]? = some (.tcb t0)) :
    (removeFromAllNotificationWaitLists st tid).objects.invExt
    ∧ ∃ t' : TCB,
      (removeFromAllNotificationWaitLists st tid).objects[k]? = some (.tcb t')
      ∧ t'.cpuAffinity = t0.cpuAffinity := by
  unfold removeFromAllNotificationWaitLists
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup st.objects st _
    (fun acc => acc.objects.invExt ∧ ∃ t' : TCB,
      acc.objects[k]? = some (.tcb t') ∧ t'.cpuAffinity = t0.cpuAffinity)
    hInv
    ⟨hInv, t0, hPre, rfl⟩
    (fun acc x v hV hAcc => by
      obtain ⟨hAccInv, t', hL', hAff'⟩ := hAcc
      split
      · -- write-set-honest sweep (PR #831 review 4): the insert arm is
        -- guarded by waiter membership; the untouched arm is the identity.
        split
        · have hNe : ¬(x == k) = true := fun hbeq => by
            have hxk : x = k := eq_of_beq hbeq
            subst hxk
            have hclash := hPre.symm.trans hV
            injection hclash with h
            injection h
          exact ⟨SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hAccInv,
            t',
            (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne _ _ _ _
              hNe hAccInv).trans hL',
            hAff'⟩
        · exact ⟨hAccInv, t', hL', hAff'⟩
      · exact ⟨hAccInv, t', hL', hAff'⟩)

/-- WS-SM SM6.E: a thread id whose key holds no TCB resolves to `none` under
`lookupTcb` — both the reserved-id guard and the kind-mismatch arm return
`none`. -/
theorem lookupTcb_eq_none_of_no_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hNo : ∀ t : TCB, st.objects[tid.toObjId]? ≠ some (.tcb t)) :
    lookupTcb st tid = none := by
  unfold lookupTcb
  split
  · rfl
  · split
    · rename_i t heq
      exact absurd heq (hNo t)
    · rfl

/-- WS-SM SM6.E: the mid-queue splice is the identity when the spliced thread
resolves to no TCB — the link patches are guarded on the victim's TCB read. -/
theorem spliceOutMidQueueNode_eq_self_of_lookupTcb_none
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (h : lookupTcb st tid = none) :
    spliceOutMidQueueNode st tid = st := by
  unfold spliceOutMidQueueNode
  rw [h]

/-- WS-SM SM6.E: the endpoint sweep never materialises a TCB at the swept
thread's key — when the key holds no TCB before the sweep, it holds no TCB
afterwards (the splice is guarded to the identity and every fold step writes
an `.endpoint` value). -/
theorem removeFromAllEndpointQueues_no_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hNo : ∀ t : TCB, st.objects[tid.toObjId]? ≠ some (.tcb t)) :
    (removeFromAllEndpointQueues st tid).objects.invExt
    ∧ ∀ t : TCB,
      (removeFromAllEndpointQueues st tid).objects[tid.toObjId]? ≠ some (.tcb t) := by
  have hSplice : spliceOutMidQueueNode st tid = st :=
    spliceOutMidQueueNode_eq_self_of_lookupTcb_none st tid
      (lookupTcb_eq_none_of_no_tcb st tid hNo)
  unfold removeFromAllEndpointQueues
  rw [hSplice]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup st.objects st _
    (fun acc => acc.objects.invExt ∧ ∀ t : TCB,
      acc.objects[tid.toObjId]? ≠ some (.tcb t))
    hInv
    ⟨hInv, hNo⟩
    (fun acc x v _ hAcc => by
      obtain ⟨hAccInv, hNoT⟩ := hAcc
      split
      · -- write-set-honest sweep (PR #831 review 4): the insert arm is
        -- guarded; the untouched arm is the identity.
        split
        · refine ⟨SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hAccInv,
            fun t h => ?_⟩
          by_cases hx : (x == tid.toObjId) = true
          · -- The swept key itself is rewritten to an `.endpoint` — not a TCB.
            have hxk : x = tid.toObjId := eq_of_beq hx
            subst hxk
            have hclash := (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self
              acc.objects tid.toObjId _ hAccInv).symm.trans h
            injection hclash with hclash
            injection hclash
          · exact hNoT t ((SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne
              acc.objects x tid.toObjId _ hx hAccInv).symm.trans h)
        · exact ⟨hAccInv, hNoT⟩
      · exact ⟨hAccInv, hNoT⟩)

/-- WS-SM SM6.E: the notification sweep never materialises a TCB at the swept
thread's key — every fold step writes a `.notification` value. -/
theorem removeFromAllNotificationWaitLists_no_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (hNo : ∀ t : TCB, st.objects[tid.toObjId]? ≠ some (.tcb t)) :
    (removeFromAllNotificationWaitLists st tid).objects.invExt
    ∧ ∀ t : TCB,
      (removeFromAllNotificationWaitLists st tid).objects[tid.toObjId]?
        ≠ some (.tcb t) := by
  unfold removeFromAllNotificationWaitLists
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup st.objects st _
    (fun acc => acc.objects.invExt ∧ ∀ t : TCB,
      acc.objects[tid.toObjId]? ≠ some (.tcb t))
    hInv
    ⟨hInv, hNo⟩
    (fun acc x v _ hAcc => by
      obtain ⟨hAccInv, hNoT⟩ := hAcc
      split
      · -- write-set-honest sweep (PR #831 review 4): the insert arm is
        -- guarded; the untouched arm is the identity.
        split
        · refine ⟨SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hAccInv,
            fun t h => ?_⟩
          by_cases hx : (x == tid.toObjId) = true
          · have hxk : x = tid.toObjId := eq_of_beq hx
            subst hxk
            have hclash := (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self
              acc.objects tid.toObjId _ hAccInv).symm.trans h
            injection hclash with hclash
            injection hclash
          · exact hNoT t ((SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne
              acc.objects x tid.toObjId _ hx hAccInv).symm.trans h)
        · exact ⟨hAccInv, hNoT⟩
      · exact ⟨hAccInv, hNoT⟩)

-- ============================================================================
-- WS-SM SM6.E: cleanup primitives preserve `ipcInvariant`
-- ============================================================================
-- The notification well-formedness invariant (`ipcInvariant`) across the
-- cancellation sweeps: the splice and the endpoint sweep write only
-- `.tcb`/`.endpoint` values (which can never be read back as a
-- notification), and the notification sweep's filter+state-correction
-- rewrite preserves the three-case well-formedness by construction.

/-- WS-SM SM6.E: a notification read through a non-notification insert was
already present in the base table — the table-level backward transport every
non-notification write in the cancellation path instantiates. -/
theorem notification_lookup_of_insert_no_notification
    (objs : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject)
    (nid : SeLe4n.ObjId) (v : KernelObject)
    (hInv : objs.invExt)
    (hV : ∀ n : Notification, v ≠ .notification n)
    (oid : SeLe4n.ObjId) (ntfn : Notification)
    (hL : (objs.insert nid v)[oid]? = some (.notification ntfn)) :
    objs[oid]? = some (.notification ntfn) := by
  by_cases hx : (nid == oid) = true
  · have hk : nid = oid := eq_of_beq hx
    subst hk
    have hclash := (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self
      objs nid v hInv).symm.trans hL
    injection hclash with hclash
    exact absurd hclash (hV ntfn)
  · exact (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne
      objs nid oid v hx hInv).symm.trans hL

/-- WS-SM SM6.E: inserting a non-notification value preserves `ipcInvariant`
— a notification read in the post-store either hits the inserted key (kind
clash, vacuous) or was already present. -/
theorem ipcInvariant_insert_no_notification
    (st : SystemState) (nid : SeLe4n.ObjId) (v : KernelObject)
    (hInv : st.objects.invExt)
    (hV : ∀ n : Notification, v ≠ .notification n)
    (hIpc : ipcInvariant st) :
    ipcInvariant { st with objects := st.objects.insert nid v } := by
  intro oid ntfn hL
  exact hIpc oid ntfn
    (notification_lookup_of_insert_no_notification st.objects nid v hInv hV oid ntfn hL)

/-- WS-SM SM6.E: `.tcb`-insert instance of
`ipcInvariant_insert_no_notification` (ctor-headed for robust inference). -/
theorem ipcInvariant_insert_tcb
    (st : SystemState) (nid : SeLe4n.ObjId) (t : TCB)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant { st with objects := st.objects.insert nid (.tcb t) } :=
  ipcInvariant_insert_no_notification st nid (.tcb t) hInv
    (fun _ h => KernelObject.noConfusion h) hIpc

/-- WS-SM SM6.E: `.endpoint`-insert instance of
`ipcInvariant_insert_no_notification`. -/
theorem ipcInvariant_insert_endpoint
    (st : SystemState) (nid : SeLe4n.ObjId) (e : Endpoint)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant { st with objects := st.objects.insert nid (.endpoint e) } :=
  ipcInvariant_insert_no_notification st nid (.endpoint e) hInv
    (fun _ h => KernelObject.noConfusion h) hIpc

/-- WS-SM SM6.E: `spliceOutMidQueueNode` preserves `ipcInvariant` — both link
patches write `.tcb` values, never a notification. -/
theorem spliceOutMidQueueNode_preserves_ipcInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant (spliceOutMidQueueNode st tid) := by
  simp only [spliceOutMidQueueNode]
  cases lookupTcb st tid with
  | none => exact hIpc
  | some tcb =>
    simp only []
    cases tcb.queuePrev with
    | none =>
      simp only []
      cases tcb.queueNext with
      | none => exact hIpc
      | some nextTid =>
        simp only []
        cases st.objects[nextTid.toObjId]? with
        | none => exact hIpc
        | some obj =>
          cases obj
          case tcb nextTcb => exact ipcInvariant_insert_tcb st nextTid.toObjId _ hInv hIpc
          all_goals exact hIpc
    | some prevTid =>
      simp only []
      cases st.objects[prevTid.toObjId]? with
      | none =>
        simp only []
        cases tcb.queueNext with
        | none => exact hIpc
        | some nextTid =>
          simp only []
          cases st.objects[nextTid.toObjId]? with
          | none => exact hIpc
          | some obj =>
            cases obj
            case tcb nextTcb =>
              exact ipcInvariant_insert_tcb st nextTid.toObjId _ hInv hIpc
            all_goals exact hIpc
      | some obj =>
        cases obj
        case tcb prevTcb =>
          simp only []
          cases tcb.queueNext with
          | none => exact ipcInvariant_insert_tcb st prevTid.toObjId _ hInv hIpc
          | some nextTid =>
            simp only []
            have hInv1 : (st.objects.insert prevTid.toObjId
                (.tcb { prevTcb with queueNext := some nextTid })).invExt :=
              SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hInv
            have hIpc1 : ipcInvariant { st with
                objects := st.objects.insert prevTid.toObjId
                  (.tcb { prevTcb with queueNext := some nextTid }) } :=
              ipcInvariant_insert_tcb st prevTid.toObjId _ hInv hIpc
            cases (st.objects.insert prevTid.toObjId
                (.tcb { prevTcb with queueNext := some nextTid }))[nextTid.toObjId]? with
            | none => exact hIpc1
            | some obj2 =>
              cases obj2
              case tcb nextTcb =>
                exact ipcInvariant_insert_tcb
                  { st with
                      objects := st.objects.insert prevTid.toObjId
                        (.tcb { prevTcb with queueNext := some nextTid }) }
                  nextTid.toObjId _ hInv1 hIpc1
              all_goals exact hIpc1
        all_goals
          (simp only []
           cases tcb.queueNext with
           | none => exact hIpc
           | some nextTid =>
             simp only []
             cases st.objects[nextTid.toObjId]? with
             | none => exact hIpc
             | some obj2 =>
               cases obj2
               case tcb nextTcb =>
                 exact ipcInvariant_insert_tcb st nextTid.toObjId _ hInv hIpc
               all_goals exact hIpc)

/-- WS-SM SM6.E: the endpoint sweep preserves `ipcInvariant` — the splice
writes `.tcb` values and every fold step writes an `.endpoint` value. -/
theorem removeFromAllEndpointQueues_preserves_ipcInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant (removeFromAllEndpointQueues st tid) := by
  have hInvS := spliceOutMidQueueNode_preserves_objects_invExt st tid hInv
  have hIpcS := spliceOutMidQueueNode_preserves_ipcInvariant st tid hInv hIpc
  unfold removeFromAllEndpointQueues
  exact (SeLe4n.Kernel.RobinHood.RHTable.fold_preserves
    (spliceOutMidQueueNode st tid).objects (spliceOutMidQueueNode st tid) _
    (fun acc => acc.objects.invExt ∧ ipcInvariant acc)
    ⟨hInvS, hIpcS⟩
    (fun acc _ _ hAcc => by
      split
      · split
        · exact ⟨SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hAcc.1,
            ipcInvariant_insert_endpoint acc _ _ hAcc.1 hAcc.2⟩
        · exact hAcc
      · exact hAcc)).2

/-- WS-SM SM6.E: the sweep's waiter filter with sole-waiter state correction
preserves notification well-formedness — filtering only shrinks the waiter
list, and the correction transitions `.waiting` to `.idle` exactly when the
filtered list is empty (a `.waiting` notification carries no pending badge,
so the `.idle` shape holds by construction). -/
theorem notificationQueueWellFormed_filter_correct
    (notif : Notification) (tid : SeLe4n.ThreadId)
    (hWF : notificationQueueWellFormed notif) :
    notificationQueueWellFormed
      { notif with
          waitingThreads := notif.waitingThreads.filter (· != tid)
          state := if notif.state = .waiting
              ∧ (notif.waitingThreads.filter (· != tid)).val.isEmpty then .idle
            else notif.state } := by
  unfold notificationQueueWellFormed at hWF ⊢
  cases hState : notif.state with
  | idle =>
    simp only [hState] at hWF
    rw [if_neg (fun hC => NotificationState.noConfusion hC.1)]
    exact ⟨by rw [NoDupList.val_filter, hWF.1]; rfl, hWF.2⟩
  | waiting =>
    simp only [hState] at hWF
    by_cases hE : (notif.waitingThreads.filter (· != tid)).val.isEmpty = true
    · -- Sole-waiter removal: the correction transitions to `.idle`.
      rw [if_pos ⟨rfl, hE⟩]
      exact ⟨List.isEmpty_iff.mp hE, hWF.2⟩
    · -- Waiters remain: still `.waiting`, with a nonempty filtered list.
      rw [if_neg (fun hC => hE hC.2)]
      refine ⟨fun hNil => hE ?_, hWF.2⟩
      rw [hNil]
      rfl
  | active =>
    simp only [hState] at hWF
    rw [if_neg (fun hC => NotificationState.noConfusion hC.1)]
    exact ⟨by rw [NoDupList.val_filter, hWF.1]; rfl, hWF.2⟩

/-- WS-SM SM6.E: the notification sweep preserves `ipcInvariant` — every fold
step rewrites a notification to its filter-corrected form, which is
well-formed from the source's invariant
(`notificationQueueWellFormed_filter_correct`). -/
theorem removeFromAllNotificationWaitLists_preserves_ipcInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st) :
    ipcInvariant (removeFromAllNotificationWaitLists st tid) := by
  unfold removeFromAllNotificationWaitLists
  exact (SeLe4n.Kernel.RobinHood.RHTable.fold_preserves_of_lookup st.objects st _
    (fun acc => acc.objects.invExt ∧ ipcInvariant acc)
    hInv ⟨hInv, hIpc⟩
    (fun acc x v hV hAcc => by
      obtain ⟨hAccInv, hAccIpc⟩ := hAcc
      split
      · -- `.notification notif` step: the corrected rewrite is well-formed
        -- from the SOURCE table's invariant (`hIpc` at the visited key).
        -- Write-set-honest sweep (PR #831 review 4): the insert arm is
        -- guarded by waiter membership; the untouched arm is the identity.
        rename_i notif
        split
        · refine ⟨SeLe4n.Kernel.RobinHood.RHTable.insert_preserves_invExt _ _ _ hAccInv,
            ?_⟩
          have hWF : notificationInvariant
              { notif with
                  waitingThreads := notif.waitingThreads.filter (· != tid)
                  state := if notif.state = .waiting
                      ∧ (notif.waitingThreads.filter (· != tid)).val.isEmpty then .idle
                    else notif.state } :=
            notificationQueueWellFormed_filter_correct notif tid (hIpc x notif hV)
          intro oid ntfn hL
          by_cases hx : (x == oid) = true
          · have hk : x = oid := eq_of_beq hx
            subst hk
            have hEq := (SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self
              acc.objects x _ hAccInv).symm.trans hL
            injection hEq with hEq
            injection hEq with hEq
            exact hEq ▸ hWF
          · exact hAccIpc oid ntfn
              ((SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne
                acc.objects x oid _ hx hAccInv).symm.trans hL)
        · exact ⟨hAccInv, hAccIpc⟩
      · exact ⟨hAccInv, hAccIpc⟩)).2

/-- WS-SM SM6.E: `cleanupDonatedSchedContext` preserves `objects.invExt` —
the identity arms are trivial and the `.donated` arm delegates to
`returnDonatedSchedContext` (three `storeObject` steps, AI4-A). -/
theorem cleanupDonatedSchedContext_preserves_objects_invExt
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt)
    (h : cleanupDonatedSchedContext st tid = .ok st') :
    st'.objects.invExt := by
  unfold cleanupDonatedSchedContext at h
  split at h
  · -- lookupTcb = none: identity.
    injection h with h; subst h; exact hInv
  · split at h
    · -- `.donated scId originalOwner`: delegate to returnDonatedSchedContext.
      exact returnDonatedSchedContext_preserves_objects_invExt _ _ _ _ _ hInv none h
    · -- `.bound` / `.unbound`: identity.
      injection h with h; subst h; exact hInv

/-- WS-SM SM6.E: `cleanupDonatedSchedContext` preserves `ipcInvariant` — the
identity arms are trivial and the `.donated` arm's three `storeObject` steps
write a SchedContext and two TCBs, never a notification
(`returnDonatedSchedContext_notification_backward`). -/
theorem cleanupDonatedSchedContext_preserves_ipcInvariant
    (st st' : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (hIpc : ipcInvariant st)
    (h : cleanupDonatedSchedContext st tid = .ok st') :
    ipcInvariant st' := by
  unfold cleanupDonatedSchedContext at h
  split at h
  · injection h with h; subst h; exact hIpc
  · split at h
    · intro oid ntfn hL
      exact hIpc oid ntfn
        (returnDonatedSchedContext_notification_backward _ _ _ _ _ hInv none h oid ntfn hL)
    · injection h with h; subst h; exact hIpc

/-- After cleanup, the cleaned thread is not in the run queue. -/
theorem cleanupTcbReferences_removes_from_runnable
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    ¬(tid ∈ ((cleanupTcbReferences st tid).scheduler.runQueueOnCore bootCoreId)) := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_scheduler_eq]
  rw [removeFromAllEndpointQueues_scheduler_eq]
  exact removeRunnableFromAllCores_not_mem st tid bootCoreId

/-- Cleanup preserves lifecycle metadata. -/
theorem cleanupTcbReferences_lifecycle_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).lifecycle = st.lifecycle := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_lifecycle_eq,
    removeFromAllEndpointQueues_lifecycle_eq (removeRunnableFromAllCores st tid) tid]
  exact removeRunnableFromAllCores_lifecycle st tid

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

-- WS-SM SM6.D (PR #827 review #6): `replyIsStashed` (the server-first stash query —
-- "does any blocked receiver reserve `rid`?") moved down to
-- `SeLe4n.Model.SystemState` (a Model-level object-store fold), so the
-- `endpointReceiveDual` stash guard (`replyStashValid`, below Lifecycle in the
-- import DAG) can reuse it without an IPC→Lifecycle import cycle.  Call it here as
-- `st.replyIsStashed rid` via the `SystemState` namespace.

/-- WS-H2, R4-B.2 (M-13): Pre-retype cleanup combining TCB reference cleanup,
    CDT detach, and service registration cleanup.
    - If the current object is a TCB: clean up scheduler + IPC references.
    - If the current object is an endpoint: revoke service registrations
      backed by this endpoint to preserve `registryEndpointValid`.
    - If the current object is a CNode: refuse when any slot is still a
      derivation parent, and otherwise detach that CNode's CDT slot mappings.
      Retype destroys every slot the CNode holds, so it owes what
      `cspaceDeleteSlot` owes for one — see the arm for why the refusal is not
      optional and why the detach no longer depends on the replacement's
      shape. -/
def lifecyclePreRetypeCleanup (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj _newObj : KernelObject) : Except KernelError SystemState :=
  -- Z7-P / AJ1-A (M-14): Return donated SchedContext before destroying TCB.
  -- Error propagated — failed cleanup would leave dangling SchedContext refs.
  match (match currentObj with
    | .tcb tcb =>
        -- WS-SM SM8.B (PR #861 review round 39): **refuse to destroy a running
        -- thread.**  The sweep below clears the current slot of whichever core
        -- runs the target — the executing core included, which is where the
        -- caller itself runs — and nothing schedules a successor there.  See
        -- `threadCurrentOnSomeCore`.  `.revocationRequired` is the error this
        -- path already uses for "clear this precondition first" (an in-use
        -- Reply, a TCB still holding a reply link), and reads correctly here as
        -- "suspend or switch away from this thread before destroying it".
        --
        -- Placed inside the arm that already cases on `currentObj`, and reading
        -- the **pre-state** `st`: every later `let` shadows `st` with the swept
        -- state, in which the slot this tests has already been cleared.
        if threadCurrentOnSomeCore st tcb.tid then
          (.error .revocationRequired : Except KernelError SystemState)
        else cleanupDonatedSchedContext st tcb.tid
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
    -- **Retype destroys every slot this CNode holds, so it owes what
    -- `cspaceDeleteSlot` owes — for all of them at once.**
    --
    -- A slot that is still a derivation parent cannot be destroyed: severing
    -- `cdtSlotNode` leaves the node and its edges behind, and `cspaceRevokeCdt`
    -- resolves *through* that mapping, so the derived capabilities keep their
    -- authority with nothing able to reach them.  `cspaceDeleteSlot` refuses one
    -- such slot; this refuses a CNode containing any, reading the same
    -- `slotIsDerivationParent` predicate so the two cannot diverge.
    -- `.revocationRequired` is the error both use: revoke the derived
    -- capabilities first, then retype.
    --
    -- Both target shapes then detach, which is why this arm no longer reads
    -- `newObj`.  CNode → CNode used to skip the detach on the grounds that no
    -- CDT cleanup was needed; that is wrong, because retype replaces the object
    -- wholesale and `objectOfKernelType` — the only thing the live
    -- `.lifecycleRetype` dispatch builds a replacement with — yields
    -- `slots := UniqueSlotMap.empty` for `.cnode`.  No slot survives, so
    -- skipping left every mapping pointing into a CNode that no longer holds
    -- the capability it was minted for: a capability later placed at such a
    -- slot inherits a destroyed one's derivation node, and revoking *that*
    -- node's ancestor takes the unrelated newcomer with it.  Past the guard the
    -- detach is unconditionally correct — every mapping it erases belongs to a
    -- node with no descendants and no transfer in flight.
    if cnodeHasDerivationParentSlot st target cn then
      .error .revocationRequired
    else
      .ok (detachCNodeSlots st target cn)
  | .reply r =>
    -- WS-SM SM6.D (PR #822 review): reject retyping/deleting a Reply object that
    -- is still in use.  Two in-use forms: (1) a caller is blocked awaiting its
    -- reply (`r.caller.isSome` — caller-first link); (2) a server-first receiver
    -- has stashed this Reply in its `pendingReceiveReply` awaiting its next Call
    -- (`replyIsStashed`, `r.caller` still `none`).  Either way, freeing it strands
    -- the caller / blocks the server (the later `.reply` / the folded server-first
    -- Call link `linkServerStashedReply` fails `.replyCapInvalid`).  Mirrors seL4's
    -- revoke/clear-before-destroy: the
    -- holder must first reply to (or cancel) the outstanding caller, or the server
    -- must re-`Recv`, clearing the link before the object is freed.
    -- PR #822 review: check stashes by the *target* ObjId's canonical ReplyId, not
    -- the reply's internal `r.replyId` field (which can be the `Reply.empty`
    -- sentinel on a freshly retyped object); a server-first receive stashes
    -- `pendingReceiveReply = some (ReplyId.ofNat target)`, so derive the id from
    -- `target` to avoid missing the stash and freeing a still-referenced Reply.
    if r.caller.isSome || st.replyIsStashed (SeLe4n.ReplyId.ofNat target.toNat) then
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
  exact removeRunnableFromAllCores_flat_subset st tid x bootCoreId h

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

/-- WS-SM SM8.B.2: CDT cleanup writes no register bank.

The `machine` companion of `detachCNodeSlots_scheduler_eq`, by the same
`RHTable.fold_preserves` argument: `detachSlotFromCdt` rewrites the CDT map and
nothing else, in both of its branches. -/
theorem detachCNodeSlots_machine_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).machine = st.machine := by
  simp only [detachCNodeSlots]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots.table st _
    (fun acc => acc.machine = st.machine)
    rfl (fun acc slot _cap hAcc => by
      have : (SystemState.detachSlotFromCdt acc { cnode := cnodeId, slot := slot }).machine
          = acc.machine := by unfold SystemState.detachSlotFromCdt; split <;> rfl
      exact this.trans hAcc)

/-- WS-SM SM7.B: CDT cleanup is CDT-only — the TLB-shootdown state is
framed. -/
theorem detachCNodeSlots_tlbShootdown_eq
    (st : SystemState) (cnodeId : SeLe4n.ObjId) (cn : CNode) :
    (detachCNodeSlots st cnodeId cn).tlbShootdown = st.tlbShootdown := by
  simp only [detachCNodeSlots]
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots.table st _
    (fun acc => acc.tlbShootdown = st.tlbShootdown)
    rfl (fun acc slot _cap hAcc =>
      (SystemState.detachSlotFromCdt_tlbShootdown_eq acc
        { cnode := cnodeId, slot := slot }).trans hAcc)

/-- Cleanup preserves the scheduler state. -/
theorem cleanupTcbReferences_scheduler_eq_removeRunnableFromAllCores
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).scheduler
      = (removeRunnableFromAllCores st tid).scheduler := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_scheduler_eq]
  exact removeFromAllEndpointQueues_scheduler_eq (removeRunnableFromAllCores st tid) tid

/-- **WS-SM SM8.B (PR #861 review round 40): the destroyed-remote-current case
is unreachable.**

A separate finding asked for a `.reschedule` SGI when a retype destroys a TCB
that is current on a **remote** core: the sweep clears that core's slot, the
object then stops being a TCB, and `crossCoreSgiBody` — which opens by matching
the post-state object against a TCB — re-derives nothing, leaving the remote
processor running scrubbed storage.

The round-39 guard closes it by construction rather than by adding a rule: the
cleanup rejects a target current on **any** core, so no retype ever reaches a
state in which a remote core's current slot held the destroyed thread.  Stated
as a theorem because "unreachable" is exactly the kind of claim that rots — if
the guard is ever narrowed to the executing core, this stops compiling. -/
theorem lifecyclePreRetypeCleanup_rejects_current_anywhere
    (st : SystemState) (target : SeLe4n.ObjId) (tcb : TCB) (newObj : KernelObject)
    (c : SeLe4n.Kernel.Concurrency.CoreId)
    (hCur : st.scheduler.currentOnCore c = some tcb.tid) :
    lifecyclePreRetypeCleanup st target (.tcb tcb) newObj = .error .revocationRequired := by
  unfold lifecyclePreRetypeCleanup
  simp only []
  rw [if_pos (threadCurrentOnSomeCore_iff st tcb.tid |>.mpr ⟨c, hCur⟩)]

/-- WS-SM SM8.B.2: the TCB reference scrub writes no register bank.

The `machine` companion of `cleanupTcbReferences_scheduler_eq_removeRunnableFromAllCores`.
Note the asymmetry, which is the whole point of the pair: the sweep *does* write
scheduler slots (on the cores the thread occupied) and writes `machine` on none,
so the retype's write set is bounded by the former while the latter contributes
nothing. -/
theorem cleanupTcbReferences_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) :
    (cleanupTcbReferences st tid).machine = st.machine := by
  unfold cleanupTcbReferences
  rw [removeFromAllNotificationWaitLists_machine_eq,
      removeFromAllEndpointQueues_machine_eq, removeRunnableFromAllCores_machine]

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
    -- Round 39: the running-target rejection is vacuous on the `.ok` path.
    rw [if_neg (by
      intro hRun
      rw [if_pos hRun] at hOk
      exact absurd hOk (by simp))] at hOk
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
      rw [cleanupTcbReferences_scheduler_eq_removeRunnableFromAllCores] at h
      -- Take the sweep off first (it handles its own per-core guard), then
      -- collapse the scheduler-preserving prefix.  The other order leaves the
      -- rewrites looking for a pattern under the guard's condition.
      have hSub := removeRunnableFromAllCores_flat_subset _ tcb.tid x bootCoreId h
      rw [hScIdxSched, hDonSched] at hSub
      exact hSub
  | cnode cn =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    -- The guard rejects (vacuous on the `.ok` path); past it the state is the
    -- detached one, whose scheduler is framed.
    split at hOk
    · exact absurd hOk (by simp)
    · injection hOk with hOk; subst hOk
      have hSched := detachCNodeSlots_scheduler_eq st target cn
      rw [show ((detachCNodeSlots st target cn).scheduler.runQueueOnCore bootCoreId).flat =
            (st.scheduler.runQueueOnCore bootCoreId).flat from by rw [hSched]] at h
      exact h
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

/-- WS-SM SM7.B: the pre-retype cleanup pipeline never touches the
TLB-shootdown state — every step (donated-SC return, scThreadIndex
trim, TCB reference scrub, endpoint service detachment, CDT slot
detachment, reply/TCB in-use rejects) is an objects/scheduler/CDT/
services-level mutation.  The `pendingBounded` bundle-carriage link for
the SM7.B.11 retype-with-shootdown wrapper; mirrors the case structure
of `lifecyclePreRetypeCleanup_flat_subset`. -/
theorem lifecyclePreRetypeCleanup_tlbShootdown_eq
    (st stClean : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject)
    (hOk : lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean) :
    stClean.tlbShootdown = st.tlbShootdown := by
  cases currentObj with
  | tcb tcb =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    -- Round 39: the running-target rejection is vacuous on the `.ok` path.
    rw [if_neg (by
      intro hRun
      rw [if_pos hRun] at hOk
      exact absurd hOk (by simp))] at hOk
    cases hDon : cleanupDonatedSchedContext st tcb.tid with
    | error e => rw [hDon] at hOk; contradiction
    | ok stDon =>
      rw [hDon] at hOk
      have hDonShoot : stDon.tlbShootdown = st.tlbShootdown :=
        cleanupDonatedSchedContext_tlbShootdown_eq st stDon tcb.tid hDon
      simp only [] at hOk
      have hRO : tcb.replyObject.isSome = false := by
        cases hr : tcb.replyObject.isSome with
        | false => rfl
        | true => rw [if_pos hr] at hOk; exact absurd hOk (by simp)
      rw [if_neg (by simp [hRO])] at hOk
      injection hOk with hOk; subst hOk
      have hScIdxShoot : (match tcb.schedContextBinding with
        | .bound scId => { stDon with scThreadIndex :=
            (scThreadIndexRemove stDon.scThreadIndex scId tcb.tid) }
        | _ => stDon).tlbShootdown = stDon.tlbShootdown := by
        cases tcb.schedContextBinding <;> rfl
      rw [cleanupTcbReferences_tlbShootdown_eq, hScIdxShoot]
      exact hDonShoot
  | cnode cn =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    -- Same shape as the scheduler frame: the guard's reject is vacuous here,
    -- and the detach frames the shootdown state.
    split at hOk
    · exact absurd hOk (by simp)
    · injection hOk with hOk; subst hOk
      exact detachCNodeSlots_tlbShootdown_eq st target cn
  | endpoint _ =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    injection hOk with hOk; subst hOk
    exact cleanupEndpointServiceRegistrations_tlbShootdown_eq st target
  | notification _ | vspaceRoot _ | untyped _ | schedContext _ =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    injection hOk with hOk; subst hOk; rfl
  | reply r =>
    simp only [lifecyclePreRetypeCleanup] at hOk
    split at hOk
    · cases hOk
    · injection hOk with hOk; subst hOk; rfl

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

/-- WS-SM SM7.B helper: a successful slot lookup returns the input
state unchanged (pair form). -/
private theorem cspaceLookupSlot_pair_state_eq
    (st : SystemState) (addr : CSpaceAddr)
    (pair : Capability × SystemState)
    (h : cspaceLookupSlot addr st = .ok pair) : pair.2 = st := by
  unfold cspaceLookupSlot at h
  split at h
  · simp only [Except.ok.injEq] at h
    rw [← h]
  · split at h <;> cases h

/-- WS-SM SM7.B: the raw retype primitive frames the TLB-shootdown
state — authority lookup is state-preserving and the replace bottoms
out in `storeObject` (`pendingBounded` bundle-carriage link for the
CSpaceAddr retype path). -/
theorem lifecycleRetypeObject_tlbShootdown_eq
    (authority : CSpaceAddr) (target : SeLe4n.ObjId) (newObj : KernelObject)
    (st st' : SystemState)
    (h : lifecycleRetypeObject authority target newObj st = .ok ((), st')) :
    st'.tlbShootdown = st.tlbShootdown := by
  unfold lifecycleRetypeObject at h
  revert h
  cases hObj : st.objects[target]? with
  | none => intro h; cases h
  | some currentObj =>
      simp only []
      split
      · cases hLook : cspaceLookupSlot authority st with
        | error e => intro h; cases h
        | ok pair =>
            simp only []
            split
            · intro h
              rw [SeLe4n.Model.storeObject_tlbShootdown_eq pair.2 target
                    newObj _ h,
                  cspaceLookupSlot_pair_state_eq st authority pair hLook]
            · intro h; cases h
      · intro h; cases h

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


-- ============================================================================
-- WS-RR RR7.22 (residual)  The endpoint sweep, characterised per key
-- ============================================================================
--
-- `removeFromAllEndpointQueues` is a fold over the *whole* object store, and
-- the fact its consumers need — "afterwards no endpoint still names the swept
-- thread at a queue boundary" — is not a fold invariant: it is false of the
-- accumulator at every key the fold has not reached.  It is a **pointwise**
-- fact, and `RHTable.fold_pointwise` is the lemma that establishes one.
--
-- Naming the fold body is what lets a proof quantify over it.  The equation
-- below is `rfl`, so the copy cannot drift: a change to the operation's body
-- that this one does not mirror fails to elaborate rather than silently
-- leaving the characterisation about a program the kernel no longer runs.

section EndpointSweep

open SeLe4n.Kernel.RobinHood

/-- **WS-RR RR7.22 (residual)**: `a` is `b` with (only) its three intrusive-queue
links rewritten.

Stated as an existential over the three link fields rather than as a list of the
fields that *agree*, which is the derive-don't-enumerate difference: a field added
to `TCB` is covered by construction, where an agreement list would silently stop
mentioning it. -/
def tcbQueueLinkRewrite (a b : TCB) : Prop :=
  ∃ qp qpp qn, a = { b with queuePrev := qp, queuePPrev := qpp, queueNext := qn }

theorem tcbQueueLinkRewrite.refl (a : TCB) : tcbQueueLinkRewrite a a :=
  ⟨a.queuePrev, a.queuePPrev, a.queueNext, rfl⟩

theorem tcbQueueLinkRewrite.trans {a b c : TCB}
    (h1 : tcbQueueLinkRewrite a b) (h2 : tcbQueueLinkRewrite b c) :
    tcbQueueLinkRewrite a c := by
  obtain ⟨p1, pp1, n1, rfl⟩ := h1
  obtain ⟨p2, pp2, n2, rfl⟩ := h2
  exact ⟨p1, pp1, n1, rfl⟩

/-- **WS-RR RR7.22 (residual)**: one neighbour patch of the mid-queue splice,
named — the guarded "rewrite this thread's links if it exists" step that
`spliceOutMidQueueNode` performs twice. -/
def queueNeighbourPatch (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB) : RHTable SeLe4n.ObjId KernelObject :=
  match nid? with
  | none => objs
  | some nid =>
    match objs[nid.toObjId]? with
    | some (.tcb t) => objs.insert nid.toObjId (.tcb (upd t))
    | _ => objs

/-- **WS-RR RR7.22 (residual)**: the mid-queue splice *is* those two patches.

`rfl`, the same pin `removeFromAllEndpointQueues_eq_fold` is: the decomposition
cannot drift from the operation without failing the build.  Naming the two steps
is what turns a four-deep nested match into two applications of one lemma. -/
theorem spliceOutMidQueueNode_eq_patches (st : SystemState) (tid : SeLe4n.ThreadId) :
    spliceOutMidQueueNode st tid =
      (match lookupTcb st tid with
       | none => st
       | some tcb =>
         { st with objects := (queueNeighbourPatch
             (queueNeighbourPatch st.objects tcb.queuePrev
               (fun p => { p with queueNext := tcb.queueNext }))
             tcb.queueNext (fun n => { n with queuePrev := tcb.queuePrev })) }) := rfl

theorem queueNeighbourPatch_invExt (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB) (hInv : objs.invExt) :
    (queueNeighbourPatch objs nid? upd).invExt := by
  unfold queueNeighbourPatch
  split
  · exact hInv
  · split
    · exact RHTable.insert_preserves_invExt _ _ _ hInv
    · exact hInv

/-- A neighbour patch installs only TCBs, so a non-TCB reading is the input's,
in both directions. -/
theorem queueNeighbourPatch_nonTcb (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB)
    (hInv : objs.invExt) (k : SeLe4n.ObjId) (o : KernelObject)
    (hNotTcb : ∀ t, o ≠ .tcb t) :
    ((queueNeighbourPatch objs nid? upd)[k]? = some o) ↔ (objs[k]? = some o) := by
  unfold queueNeighbourPatch
  split
  · exact Iff.rfl
  · rename_i nid
    split
    · rename_i t hRead
      by_cases hK : nid.toObjId = k
      · subst hK
        constructor
        · intro h
          have h' : (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? nid.toObjId
              = some o := h
          rw [RHTable.getElem?_insert_self objs nid.toObjId (.tcb (upd t)) hInv] at h'
          exact absurd (Option.some.inj h').symm (hNotTcb (upd t))
        · intro h
          rw [hRead] at h
          exact absurd (Option.some.inj h).symm (hNotTcb t)
      · constructor
        · intro h
          have h' : (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? k = some o := h
          rwa [RHTable.getElem?_insert_ne objs nid.toObjId k (.tcb (upd t))
            (fun hbeq => hK (eq_of_beq hbeq)) hInv] at h'
        · intro h
          show (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? k = some o
          rw [RHTable.getElem?_insert_ne objs nid.toObjId k (.tcb (upd t))
            (fun hbeq => hK (eq_of_beq hbeq)) hInv]
          exact h
    · exact Iff.rfl

/-- A neighbour patch read backwards: every TCB it leaves is a queue-link
rewrite of one the input held at the same key. -/
theorem queueNeighbourPatch_backward (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB)
    (hUpd : ∀ t, tcbQueueLinkRewrite (upd t) t)
    (hInv : objs.invExt) (k : SeLe4n.ObjId) (t' : TCB)
    (hPost : (queueNeighbourPatch objs nid? upd)[k]? = some (.tcb t')) :
    ∃ t0, objs[k]? = some (.tcb t0) ∧ tcbQueueLinkRewrite t' t0 := by
  unfold queueNeighbourPatch at hPost
  split at hPost
  · exact ⟨t', hPost, tcbQueueLinkRewrite.refl t'⟩
  · rename_i nid
    split at hPost
    · rename_i t hRead
      by_cases hK : nid.toObjId = k
      · subst hK
        have hPost' : (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? nid.toObjId
            = some (KernelObject.tcb t') := hPost
        rw [RHTable.getElem?_insert_self objs nid.toObjId (.tcb (upd t)) hInv] at hPost'
        obtain rfl : upd t = t' := KernelObject.tcb.inj (Option.some.inj hPost')
        exact ⟨t, hRead, hUpd t⟩
      · have hPost' : (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? k
            = some (KernelObject.tcb t') := hPost
        rw [RHTable.getElem?_insert_ne objs nid.toObjId k (.tcb (upd t))
          (fun hbeq => hK (eq_of_beq hbeq)) hInv] at hPost'
        exact ⟨t', hPost', tcbQueueLinkRewrite.refl t'⟩
    · exact ⟨t', hPost, tcbQueueLinkRewrite.refl t'⟩

/-- **WS-RR RR7.22 (residual)**: the mid-queue splice rewrites **only** intrusive
queue links — every TCB it leaves is a link rewrite of the one it found, and
every non-TCB object is untouched.

This is the whole of what the splice does to the object store, and it is what
lets the conjuncts that read `ipcState`, `schedContextBinding`, `replyObject`,
`pendingMessage`, `timeoutBudget` or `pendingReceiveReply` cross it for free. -/
theorem spliceOutMidQueueNode_tcb_backward
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.ObjId) (t' : TCB)
    (hInv : st.objects.invExt)
    (hPost : (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t')) :
    ∃ t0, st.objects[k]? = some (.tcb t0) ∧ tcbQueueLinkRewrite t' t0 := by
  rw [spliceOutMidQueueNode_eq_patches] at hPost
  split at hPost
  · exact ⟨t', hPost, tcbQueueLinkRewrite.refl t'⟩
  · rename_i tcb hT
    obtain ⟨t1, h1, r1⟩ := queueNeighbourPatch_backward _ tcb.queueNext _
      (fun n => ⟨tcb.queuePrev, n.queuePPrev, n.queueNext, rfl⟩)
      (queueNeighbourPatch_invExt _ _ _ hInv) k t' hPost
    obtain ⟨t0, h0, r0⟩ := queueNeighbourPatch_backward st.objects tcb.queuePrev _
      (fun p => ⟨p.queuePrev, p.queuePPrev, tcb.queueNext, rfl⟩) hInv k t1 h1
    exact ⟨t0, h0, r1.trans r0⟩

/-- **WS-RR RR7.22 (residual)**: the mid-queue splice leaves every non-TCB object
exactly as it found it. -/
theorem spliceOutMidQueueNode_nonTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) (k : SeLe4n.ObjId) (o : KernelObject)
    (hNotTcb : ∀ t, o ≠ .tcb t) :
    ((spliceOutMidQueueNode st tid).objects[k]? = some o) ↔ (st.objects[k]? = some o) := by
  rw [spliceOutMidQueueNode_eq_patches]
  split
  · exact Iff.rfl
  · rename_i tcb hT
    exact (queueNeighbourPatch_nonTcb _ tcb.queueNext _
        (queueNeighbourPatch_invExt _ _ _ hInv) k o hNotTcb).trans
      (queueNeighbourPatch_nonTcb st.objects tcb.queuePrev _ hInv k o hNotTcb)

-- The precise per-key readings of the two neighbour patches: what the splice
-- installs at each key it touches, and what it leaves at every key it does not.
-- These are what the queue-shape conjuncts read; the `tcbQueueLinkRewrite`
-- backward frame above is what every *other* conjunct reads.

theorem queueNeighbourPatch_at_self (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid : SeLe4n.ThreadId) (upd : TCB → TCB) (hInv : objs.invExt) (t0 : TCB)
    (hk : objs[nid.toObjId]? = some (.tcb t0)) :
    (queueNeighbourPatch objs (some nid) upd)[nid.toObjId]? = some (.tcb (upd t0)) := by
  unfold queueNeighbourPatch
  simp only
  rw [hk]
  exact RHTable.getElem?_insert_self objs nid.toObjId (.tcb (upd t0)) hInv

theorem queueNeighbourPatch_at_other (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB) (hInv : objs.invExt)
    (k : SeLe4n.ObjId) (hNe : ∀ nid, nid? = some nid → nid.toObjId ≠ k) :
    (queueNeighbourPatch objs nid? upd)[k]? = objs[k]? := by
  unfold queueNeighbourPatch
  split
  · rfl
  · rename_i nid
    have hn : nid.toObjId ≠ k := hNe nid rfl
    split
    · rename_i t hRead
      show (objs.insert nid.toObjId (KernelObject.tcb (upd t))).get? k = objs[k]?
      exact RHTable.getElem?_insert_ne objs nid.toObjId k _ (by simpa using hn) hInv
    · rfl

/-- **WS-RR RR7.22 (residual)**: the splice does not touch the swept thread's own
TCB.  It patches only that thread's two neighbours, and a thread that is its own
neighbour would close a one-step `queueNext` cycle. -/
theorem spliceOutMidQueueNode_victim_tcb (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : st.objects.invExt)
    (hLink : tcbQueueLinkIntegrity st) (hAcyc : tcbQueueChainAcyclic st)
    (hLookup : lookupTcb st tid = some tcb) :
    (spliceOutMidQueueNode st tid).objects[tid.toObjId]? = some (.tcb tcb) := by
  have hTcb : st.objects[tid.toObjId]? = some (.tcb tcb) :=
    lookupTcb_some_objects st tid tcb hLookup
  have hPrevNe : ∀ p, tcb.queuePrev = some p → p.toObjId ≠ tid.toObjId := by
    intro p hp hEq
    obtain ⟨tA, hA, hAN⟩ := hLink.2 tid tcb hTcb p hp
    rw [hEq, hTcb] at hA
    have hEqT : tA = tcb := (KernelObject.tcb.inj (Option.some.inj hA)).symm
    rw [hEqT] at hAN
    exact hAcyc tid (.single tid tid tcb hTcb hAN)
  have hNextNe : ∀ n, tcb.queueNext = some n → n.toObjId ≠ tid.toObjId := by
    intro n hn hEq
    have hn' : tcb.queueNext = some tid := by
      rw [hn]; exact congrArg some (SeLe4n.ThreadId.toObjId_injective _ _ hEq)
    exact hAcyc tid (.single tid tid tcb hTcb hn')
  rw [spliceOutMidQueueNode_eq_patches, hLookup]
  simp only
  rw [queueNeighbourPatch_at_other _ tcb.queueNext _
    (queueNeighbourPatch_invExt _ _ _ hInv) tid.toObjId hNextNe]
  rw [queueNeighbourPatch_at_other st.objects tcb.queuePrev _ hInv tid.toObjId hPrevNe]
  exact hTcb


theorem queueNeighbourPatch_at_self' (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (nid : SeLe4n.ThreadId) (upd : TCB → TCB)
    (hInv : objs.invExt) (t0 : TCB) (hn : nid? = some nid)
    (hk : objs[nid.toObjId]? = some (.tcb t0)) :
    (queueNeighbourPatch objs nid? upd)[nid.toObjId]? = some (.tcb (upd t0)) := by
  subst hn; exact queueNeighbourPatch_at_self objs nid upd hInv t0 hk

theorem queueNeighbourPatch_tcb_forward (objs : RHTable SeLe4n.ObjId KernelObject)
    (nid? : Option SeLe4n.ThreadId) (upd : TCB → TCB) (hInv : objs.invExt)
    (k : SeLe4n.ObjId) (t0 : TCB) (hk : objs[k]? = some (.tcb t0)) :
    ∃ t', (queueNeighbourPatch objs nid? upd)[k]? = some (.tcb t') ∧
      (t' = t0 ∨ t' = upd t0) := by
  cases hn : nid? with
  | none =>
    exact ⟨t0, by
      rw [queueNeighbourPatch_at_other objs none upd hInv k (by intro n h; cases h)]
      exact hk, Or.inl rfl⟩
  | some nid =>
    by_cases hK : nid.toObjId = k
    · subst hK
      exact ⟨upd t0, queueNeighbourPatch_at_self objs nid upd hInv t0 hk, Or.inr rfl⟩
    · exact ⟨t0, by
        rw [queueNeighbourPatch_at_other objs (some nid) upd hInv k
          (by intro n h; cases h; exact hK)]
        exact hk, Or.inl rfl⟩

/-- **WS-RR RR7.22 (residual)**: after the splice the swept thread's successor
points back **past** it — the skip the splice installs. -/
theorem spliceOutMidQueueNode_next_queuePrev (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (nextTid : SeLe4n.ThreadId) (nextTcb : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcb)
    (hN : tcb.queueNext = some nextTid)
    (hNext : st.objects[nextTid.toObjId]? = some (.tcb nextTcb)) :
    ∃ t', (spliceOutMidQueueNode st tid).objects[nextTid.toObjId]? = some (.tcb t') ∧
      t'.queuePrev = tcb.queuePrev := by
  obtain ⟨t1, h1, _⟩ := queueNeighbourPatch_tcb_forward st.objects tcb.queuePrev
    (fun p => { p with queueNext := tcb.queueNext }) hInv nextTid.toObjId nextTcb hNext
  refine ⟨{ t1 with queuePrev := tcb.queuePrev }, ?_, rfl⟩
  rw [spliceOutMidQueueNode_eq_patches, hLookup]
  simp only
  exact queueNeighbourPatch_at_self' _ tcb.queueNext nextTid _
    (queueNeighbourPatch_invExt _ _ _ hInv) t1 hN h1

/-- **WS-RR RR7.22 (residual)**: after the splice the swept thread's predecessor
points **past** it. -/
theorem spliceOutMidQueueNode_prev_queueNext (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (prevTid : SeLe4n.ThreadId) (prevTcb : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcb)
    (hP : tcb.queuePrev = some prevTid)
    (hPrev : st.objects[prevTid.toObjId]? = some (.tcb prevTcb)) :
    ∃ t', (spliceOutMidQueueNode st tid).objects[prevTid.toObjId]? = some (.tcb t') ∧
      t'.queueNext = tcb.queueNext := by
  have hInner : (queueNeighbourPatch st.objects tcb.queuePrev
      (fun p => { p with queueNext := tcb.queueNext }))[prevTid.toObjId]?
      = some (.tcb { prevTcb with queueNext := tcb.queueNext }) :=
    queueNeighbourPatch_at_self' st.objects tcb.queuePrev prevTid _ hInv prevTcb hP hPrev
  obtain ⟨t1, h1, hcase⟩ := queueNeighbourPatch_tcb_forward _ tcb.queueNext
    (fun m => { m with queuePrev := tcb.queuePrev })
    (queueNeighbourPatch_invExt _ _ _ hInv) prevTid.toObjId
    { prevTcb with queueNext := tcb.queueNext } hInner
  refine ⟨t1, ?_, ?_⟩
  · rw [spliceOutMidQueueNode_eq_patches, hLookup]
    simp only
    exact h1
  · rcases hcase with rfl | rfl <;> rfl

/-- Every thread that is not the swept thread's successor keeps its `queuePrev`. -/
theorem spliceOutMidQueueNode_queuePrev_frame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcb)
    (hk : st.objects[k]? = some (.tcb t0))
    (hNe : ∀ n, tcb.queueNext = some n → n.toObjId ≠ k) :
    ∃ t', (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t') ∧
      t'.queuePrev = t0.queuePrev := by
  obtain ⟨t1, h1, hcase⟩ := queueNeighbourPatch_tcb_forward st.objects tcb.queuePrev
    (fun p => { p with queueNext := tcb.queueNext }) hInv k t0 hk
  refine ⟨t1, ?_, ?_⟩
  · rw [spliceOutMidQueueNode_eq_patches, hLookup]
    simp only
    rw [queueNeighbourPatch_at_other _ tcb.queueNext _
      (queueNeighbourPatch_invExt _ _ _ hInv) k hNe]
    exact h1
  · rcases hcase with rfl | rfl <;> rfl

/-- Every thread that is not the swept thread's predecessor keeps its `queueNext`. -/
theorem spliceOutMidQueueNode_queueNext_frame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (k : SeLe4n.ObjId) (t0 : TCB)
    (hInv : st.objects.invExt) (hLookup : lookupTcb st tid = some tcb)
    (hk : st.objects[k]? = some (.tcb t0))
    (hNe : ∀ p, tcb.queuePrev = some p → p.toObjId ≠ k) :
    ∃ t', (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t') ∧
      t'.queueNext = t0.queueNext := by
  have hInner : (queueNeighbourPatch st.objects tcb.queuePrev
      (fun p => { p with queueNext := tcb.queueNext }))[k]? = some (.tcb t0) := by
    rw [queueNeighbourPatch_at_other st.objects tcb.queuePrev _ hInv k hNe]; exact hk
  obtain ⟨t1, h1, hcase⟩ := queueNeighbourPatch_tcb_forward _ tcb.queueNext
    (fun n => { n with queuePrev := tcb.queuePrev })
    (queueNeighbourPatch_invExt _ _ _ hInv) k t0 hInner
  refine ⟨t1, ?_, ?_⟩
  · rw [spliceOutMidQueueNode_eq_patches, hLookup]
    simp only
    exact h1
  · rcases hcase with rfl | rfl <;> rfl

/-- **WS-RR RR7.22 (residual)**: `removeFromAllEndpointQueues`'s fold body,
named.

Rewrites an endpoint only when one of its four queue boundaries names the swept
thread — the PR #831 write-set-honesty guard — and installs the two
`removeThreadFromQueue` results when it does.  Both queue rewrites read the
**spliced** pre-state, not the accumulator, so the value installed at a key does
not depend on the fold's iteration order. -/
def endpointSweepBody (stSpliced : SystemState) (tid : SeLe4n.ThreadId)
    (acc : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject) : SystemState :=
  match obj with
  | .endpoint ep =>
      if ep.sendQ.head == some tid || ep.sendQ.tail == some tid
          || ep.receiveQ.head == some tid || ep.receiveQ.tail == some tid then
        let ep' : Endpoint := {
          sendQ := removeThreadFromQueue stSpliced ep.sendQ tid,
          receiveQ := removeThreadFromQueue stSpliced ep.receiveQ tid }
        { acc with objects := acc.objects.insert oid (.endpoint ep') }
      else acc
  | _ => acc

/-- **WS-RR RR7.22 (residual)**: the sweep *is* the fold of that body.

`rfl`, deliberately: this is the pin that keeps the named body and the
operation's own from diverging.  AN4-G.5's earlier `epFold` intermediate broke
because a proof matched the body **syntactically**; a definitional equation
fails the build instead. -/
theorem removeFromAllEndpointQueues_eq_fold (st : SystemState) (tid : SeLe4n.ThreadId) :
    removeFromAllEndpointQueues st tid =
      (spliceOutMidQueueNode st tid).objects.fold (spliceOutMidQueueNode st tid)
        (endpointSweepBody (spliceOutMidQueueNode st tid) tid) := rfl

/-- **WS-RR RR7.22 (residual)**: the notification purge's fold body, named.

Its guard is what makes the write set honest: a notification the swept thread
does not wait on is left alone rather than re-inserted, so the purge's footprint
is the notifications it actually changes.  The `.waiting → .idle` correction is
part of the body because emptying the wait list is what makes the old state
ill-formed. -/
def notificationPurgeBody (tid : SeLe4n.ThreadId)
    (acc : SystemState) (oid : SeLe4n.ObjId) (obj : KernelObject) : SystemState :=
  match obj with
  | .notification notif =>
    if notif.waitingThreads.val.contains tid then
      let wt' := notif.waitingThreads.filter (· != tid)
      let notif' : Notification := {
        notif with
          waitingThreads := wt'
          state := if notif.state = .waiting ∧ wt'.val.isEmpty then .idle
                   else notif.state }
      { acc with objects := acc.objects.insert oid (.notification notif') }
    else acc
  | _ => acc

/-- The purge *is* that fold.  `rfl`, the pin — same discipline as the endpoint
sweep's above. -/
theorem removeFromAllNotificationWaitLists_eq_fold (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    removeFromAllNotificationWaitLists st tid =
      st.objects.fold st (notificationPurgeBody tid) := rfl

/-- **WS-RR RR7.22 (residual)**: a thread sits at neither boundary of either of
an endpoint's queues.

The shape `queueHeadBlockedConsistent` and `endpointQueueTailBlockedConsistent`
read, collected once so the sweep's payoff and its consumers name the same
thing. -/
def threadOffQueueBoundaries (tid : SeLe4n.ThreadId) (ep : Endpoint) : Prop :=
  ep.sendQ.head ≠ some tid ∧ ep.sendQ.tail ≠ some tid ∧
  ep.receiveQ.head ≠ some tid ∧ ep.receiveQ.tail ≠ some tid

/-- **WS-RR RR7.22 (residual)**: `removeThreadFromQueue` is the identity on a
queue neither of whose boundaries names the thread — which is exactly the sweep
guard's negation, and so the reason the guard's two arms agree. -/
theorem removeThreadFromQueue_id_of_off_boundary (s : SystemState) (q : IntrusiveQueue)
    (tid : SeLe4n.ThreadId) (hH : q.head ≠ some tid) (hT : q.tail ≠ some tid) :
    removeThreadFromQueue s q tid = q := by
  unfold removeThreadFromQueue
  simp only [if_neg hH, if_neg hT]

/-- **WS-RR RR7.22 (residual)**: `removeThreadFromQueue` never leaves the removed
thread at a boundary.

The head advances to the thread's `queueNext` and the tail retreats to its
`queuePrev`, so the only way the result could still name it is a self-link —
which `tcbQueueChainAcyclic` forbids and which the two hypotheses state
directly.  The `lookupTcb`-absent branch clears both boundaries outright
(AN4-G.1's defensive clamp), so it needs no hypothesis at all. -/
theorem removeThreadFromQueue_off_boundary (s : SystemState) (q : IntrusiveQueue)
    (tid : SeLe4n.ThreadId)
    (hNext : ∀ tcb, lookupTcb s tid = some tcb → tcb.queueNext ≠ some tid)
    (hPrev : ∀ tcb, lookupTcb s tid = some tcb → tcb.queuePrev ≠ some tid) :
    (removeThreadFromQueue s q tid).head ≠ some tid ∧
      (removeThreadFromQueue s q tid).tail ≠ some tid := by
  unfold removeThreadFromQueue
  cases hT : lookupTcb s tid with
  | none => simp only; constructor <;> (split <;> simp_all)
  | some tcb =>
    simp only
    constructor
    · split
      · exact hNext tcb hT
      · assumption
    · split
      · exact hPrev tcb hT
      · assumption

/-- **WS-RR RR7.22 (residual)**: after the sweep, every endpoint's two queues are
exactly `removeThreadFromQueue` of the ones it had — uniformly, whether the
guard fired or declined.

The declining arm is the interesting one: the guard's negation says no boundary
names the swept thread, which is precisely when `removeThreadFromQueue` is the
identity, so "rewritten" and "left alone" agree there. -/
theorem removeFromAllEndpointQueues_endpoint_value (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (k : SeLe4n.ObjId) (ep0 : Endpoint)
    (hEp0 : (spliceOutMidQueueNode st tid).objects[k]? = some (.endpoint ep0)) :
    ((removeFromAllEndpointQueues st tid).objects.invExt) ∧
      ∀ ep, (removeFromAllEndpointQueues st tid).objects[k]? = some (.endpoint ep) →
        ep.sendQ = removeThreadFromQueue (spliceOutMidQueueNode st tid) ep0.sendQ tid ∧
        ep.receiveQ = removeThreadFromQueue (spliceOutMidQueueNode st tid) ep0.receiveQ tid := by
  rw [removeFromAllEndpointQueues_eq_fold]
  refine RHTable.fold_pointwise (spliceOutMidQueueNode st tid).objects
    (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
    (Pre := fun o acc => acc.objects.invExt ∧
      acc.objects[o]? = (spliceOutMidQueueNode st tid).objects[o]?)
    (Q := fun o acc => acc.objects.invExt ∧
      ∀ e, acc.objects[o]? = some (.endpoint e) →
        ∀ e0, (spliceOutMidQueueNode st tid).objects[o]? = some (.endpoint e0) →
          e.sendQ = removeThreadFromQueue (spliceOutMidQueueNode st tid) e0.sendQ tid ∧
          e.receiveQ = removeThreadFromQueue (spliceOutMidQueueNode st tid) e0.receiveQ tid)
    hExt ?_ ?_ ?_ ?_ k (.endpoint ep0) hEp0 |>.imp id (fun h e he => h e he ep0 hEp0)
  · exact fun _ => ⟨hExt, rfl⟩
  · rintro acc o o' v' hne ⟨hE, hA⟩
    unfold endpointSweepBody
    cases v' with
    | endpoint ep =>
      simp only
      split
      · exact ⟨RHTable.insert_preserves_invExt _ _ _ hE, by
          show (acc.objects.insert o' _).get? o = _
          rw [RHTable.getElem?_insert_ne acc.objects o' o _
            (by simpa using fun h => hne h.symm) hE]
          exact hA⟩
      · exact ⟨hE, hA⟩
    | _ => exact ⟨hE, hA⟩
  · rintro acc o v hGet ⟨hE, hA⟩
    unfold endpointSweepBody
    cases v with
    | endpoint ep =>
      simp only
      split
      · refine ⟨RHTable.insert_preserves_invExt _ _ _ hE, ?_⟩
        intro e he e0 he0
        have he' : (acc.objects.insert o (KernelObject.endpoint
            { sendQ := removeThreadFromQueue (spliceOutMidQueueNode st tid) ep.sendQ tid,
              receiveQ := removeThreadFromQueue (spliceOutMidQueueNode st tid) ep.receiveQ tid })).get? o
            = some (KernelObject.endpoint e) := he
        rw [RHTable.getElem?_insert_self acc.objects o _ hE] at he'
        obtain rfl := KernelObject.endpoint.inj (Option.some.inj he')
        have hGet' : (spliceOutMidQueueNode st tid).objects[o]?
            = some (KernelObject.endpoint ep) := hGet
        rw [he0] at hGet'
        obtain rfl : e0 = ep := KernelObject.endpoint.inj (Option.some.inj hGet')
        exact ⟨rfl, rfl⟩
      · refine ⟨hE, ?_⟩
        intro e he e0 he0
        rw [hA, he0] at he
        obtain rfl : e0 = e := KernelObject.endpoint.inj (Option.some.inj he)
        have hGet' : (spliceOutMidQueueNode st tid).objects[o]?
            = some (KernelObject.endpoint ep) := hGet
        rw [he0] at hGet'
        obtain rfl : e0 = ep := KernelObject.endpoint.inj (Option.some.inj hGet')
        rename_i hGuard
        simp only [Bool.or_eq_true, beq_iff_eq, not_or] at hGuard
        exact ⟨(removeThreadFromQueue_id_of_off_boundary _ _ tid hGuard.1.1.1 hGuard.1.1.2).symm,
          (removeThreadFromQueue_id_of_off_boundary _ _ tid hGuard.1.2 hGuard.2).symm⟩
    | _ =>
      refine ⟨hE, ?_⟩
      intro e he e0 he0
      rw [hA, he0] at he
      exact absurd (hGet.symm.trans he0) (by simp)
  · rintro acc o o' v' hne ⟨hE, hQ⟩
    unfold endpointSweepBody
    cases v' with
    | endpoint ep =>
      simp only
      split
      · refine ⟨RHTable.insert_preserves_invExt _ _ _ hE, ?_⟩
        intro e he
        have he' : (acc.objects.insert o' (KernelObject.endpoint
            { sendQ := removeThreadFromQueue (spliceOutMidQueueNode st tid) ep.sendQ tid,
              receiveQ := removeThreadFromQueue (spliceOutMidQueueNode st tid) ep.receiveQ tid })).get? o
            = some (KernelObject.endpoint e) := he
        rw [RHTable.getElem?_insert_ne acc.objects o' o _
          (by simpa using fun h => hne h.symm) hE] at he'
        exact hQ e he'
      · exact ⟨hE, hQ⟩
    | _ => exact ⟨hE, hQ⟩

/-- **WS-RR RR7.22 (residual)**: the sweep's headline consequence — **no endpoint
still names the swept thread at a queue boundary**.

A corollary of the value description rather than a second fold argument: the
queues are `removeThreadFromQueue` outputs, and those never name the removed
thread at a boundary. -/
theorem removeFromAllEndpointQueues_off_boundary
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (hNext : ∀ tcb, lookupTcb (spliceOutMidQueueNode st tid) tid = some tcb →
      tcb.queueNext ≠ some tid)
    (hPrev : ∀ tcb, lookupTcb (spliceOutMidQueueNode st tid) tid = some tcb →
      tcb.queuePrev ≠ some tid)
    (oid : SeLe4n.ObjId) (ep0 : Endpoint)
    (hEp0 : (spliceOutMidQueueNode st tid).objects[oid]? = some (.endpoint ep0)) :
    ((removeFromAllEndpointQueues st tid).objects.invExt) ∧
      ∀ ep, (removeFromAllEndpointQueues st tid).objects[oid]? = some (.endpoint ep) →
        threadOffQueueBoundaries tid ep := by
  obtain ⟨hInv2, hVal⟩ := removeFromAllEndpointQueues_endpoint_value st tid hExt oid ep0 hEp0
  refine ⟨hInv2, fun ep hep => ?_⟩
  obtain ⟨hS, hR⟩ := hVal ep hep
  obtain ⟨h1, h2⟩ := removeThreadFromQueue_off_boundary (spliceOutMidQueueNode st tid)
    ep0.sendQ tid hNext hPrev
  obtain ⟨h3, h4⟩ := removeThreadFromQueue_off_boundary (spliceOutMidQueueNode st tid)
    ep0.receiveQ tid hNext hPrev
  exact ⟨by rw [hS]; exact h1, by rw [hS]; exact h2, by rw [hR]; exact h3, by rw [hR]; exact h4⟩


/-- **WS-RR RR7.22 (residual)**: the endpoint sweep writes only endpoints, so
every TCB survives it verbatim. -/
theorem removeFromAllEndpointQueues_tcb_frame (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (k : SeLe4n.ObjId) (t0 : TCB)
    (h : (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t0)) :
    (removeFromAllEndpointQueues st tid).objects[k]? = some (.tcb t0) := by
  rw [removeFromAllEndpointQueues_eq_fold]
  exact (RHTable.fold_preserves_of_lookup (spliceOutMidQueueNode st tid).objects
    (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
    (fun acc => acc.objects.invExt ∧ acc.objects[k]? = some (.tcb t0)) hExt ⟨hExt, h⟩
    (by
      rintro acc k' v' hGet ⟨hE, hA⟩
      unfold endpointSweepBody
      cases v' with
      | endpoint ep =>
        simp only
        split
        · have hNe : k' ≠ k := by
            intro hEq
            have h2 : (spliceOutMidQueueNode st tid).objects.get? k'
                = some (KernelObject.endpoint ep) := hGet
            rw [hEq] at h2
            have h3 : (spliceOutMidQueueNode st tid).objects.get? k
                = some (KernelObject.tcb t0) := h
            rw [h3] at h2
            cases h2
          refine ⟨RHTable.insert_preserves_invExt _ _ _ hE, ?_⟩
          show (acc.objects.insert k' _).get? k = _
          rw [RHTable.getElem?_insert_ne acc.objects k' k _ (by simpa using hNe) hE]
          exact hA
        · exact ⟨hE, hA⟩
      | _ => exact ⟨hE, hA⟩)).2

/-- **WS-RR RR7.22 (residual)**: a TCB reading after the sweep is the one the
sweep started from — the converse of the frame above, and what a conjunct stated
over the post-state needs to reach back. -/
theorem removeFromAllEndpointQueues_tcb_source (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (k : SeLe4n.ObjId) (t' : TCB)
    (h : (removeFromAllEndpointQueues st tid).objects[k]? = some (.tcb t')) :
    (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t') := by
  rw [removeFromAllEndpointQueues_eq_fold] at h
  refine ((RHTable.fold_preserves_of_lookup (spliceOutMidQueueNode st tid).objects
    (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
    (fun acc => acc.objects.invExt ∧ ∀ t, acc.objects[k]? = some (.tcb t) →
      (spliceOutMidQueueNode st tid).objects[k]? = some (.tcb t)) hExt
    ⟨hExt, fun _ ht => ht⟩ ?_).2 t' h)
  rintro acc k' v' hGet ⟨hE, hA⟩
  unfold endpointSweepBody
  cases v' with
  | endpoint ep' =>
    simp only
    split
    · refine ⟨RHTable.insert_preserves_invExt _ _ _ hE, ?_⟩
      intro t ht
      by_cases hK : k' = k
      · subst hK
        have ht' : (acc.objects.insert k' _).get? k' = some (KernelObject.tcb t) := ht
        rw [RHTable.getElem?_insert_self acc.objects k' _ hE] at ht'
        cases ht'
      · have ht' : (acc.objects.insert k' _).get? k = some (KernelObject.tcb t) := ht
        rw [RHTable.getElem?_insert_ne acc.objects k' k _ (by simpa using hK) hE] at ht'
        exact hA t ht'
    · exact ⟨hE, hA⟩
  | _ => exact ⟨hE, hA⟩

/-- **WS-RR RR7.22 (residual)**: an endpoint reading after the sweep had an
endpoint at the same key before it — the sweep invents no endpoints. -/
theorem removeFromAllEndpointQueues_endpoint_source (st : SystemState) (tid : SeLe4n.ThreadId)
    (hExt : (spliceOutMidQueueNode st tid).objects.invExt)
    (k : SeLe4n.ObjId) (ep : Endpoint)
    (h : (removeFromAllEndpointQueues st tid).objects[k]? = some (.endpoint ep)) :
    ∃ ep0, (spliceOutMidQueueNode st tid).objects[k]? = some (.endpoint ep0) := by
  rw [removeFromAllEndpointQueues_eq_fold] at h
  refine ((RHTable.fold_preserves_of_lookup (spliceOutMidQueueNode st tid).objects
    (spliceOutMidQueueNode st tid) (endpointSweepBody (spliceOutMidQueueNode st tid) tid)
    (fun acc => acc.objects.invExt ∧ ∀ e, acc.objects[k]? = some (.endpoint e) →
      ∃ e0, (spliceOutMidQueueNode st tid).objects[k]? = some (.endpoint e0)) hExt
    ⟨hExt, fun e he => ⟨e, he⟩⟩ ?_).2 ep h)
  rintro acc k' v' hGet ⟨hE, hA⟩
  unfold endpointSweepBody
  cases v' with
  | endpoint ep' =>
    simp only
    split
    · refine ⟨RHTable.insert_preserves_invExt _ _ _ hE, ?_⟩
      intro e he
      by_cases hK : k' = k
      · subst hK
        exact ⟨ep', hGet⟩
      · have he' : (acc.objects.insert k' _).get? k = some (KernelObject.endpoint e) := he
        rw [RHTable.getElem?_insert_ne acc.objects k' k _ (by simpa using hK) hE] at he'
        exact hA e he'
    · exact ⟨hE, hA⟩
  | _ => exact ⟨hE, hA⟩

end EndpointSweep

end SeLe4n.Kernel
