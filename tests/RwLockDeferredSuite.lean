-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Locks.RwLock
import SeLe4n.Kernel.Concurrency.Locks.RwLockRefinement

/-!
# WS-SM SM2.C-defer — RwLock deferred-completion test suite

Surface anchors + decidable examples + runtime assertions for the
D-1..D-4 deferred-completion theorems landed at SM2.C-defer.

See `docs/planning/SMP_RWLOCK_DEFERRED_COMPLETION_PLAN.md`.
-/

namespace SeLe4n.Tests.RwLockDeferred

open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- Surface anchors (D-1 / D-2 / D-3 / D-4)
-- ============================================================================

-- §4.1 Execution / Reachable infrastructure
#check @RwLockKernelStep
#check @RwLockReachable
#check @RwLockReachable_implies_wf
#check @RwLockExecution
#check @RwLockExecution.stateAt
#check @RwLockExecution.stateAt_zero
#check @RwLockExecution.stateAt_succ
#check @RwLockExecution.stateAt_reachable
#check @RwLockExecution.stateAt_wf
#check @RwLockExecution.initial_wf

-- §4.2 Waiter / Holder predicates + enqueueStep / admissionStep
#check @RwLockExecution.waiterAt
#check @RwLockExecution.holderAt
#check @RwLockExecution.enqueueStep
#check @RwLockExecution.admissionStep
#check @RwLockExecution.enqueueStep_characterization
#check @RwLockExecution.admissionStep_characterization

-- §4.3 + D-2 writerWaitDepth
#check @writerWaitDepth
#check @writerWaitDepth_simp
#check @writerWaitDepth_bounded
#check @writerWaitDepth_componentBounded
#check @rwLock_bounded_wait_write_distinct_weak

-- D-2.4 effective release predicate + counter
#check @RwLockState.isEffectiveRelease
#check @RwLockExecution.isEffectiveReleaseAt
#check @RwLockExecution.countEffectiveReleases
#check @RwLockExecution.countEffectiveReleases_le_window

-- D-1.6 append-to-tail
#check @tryAcquireRead_waiters_append_or_noop
#check @tryAcquireWrite_waiters_append_or_noop

-- D-1.7 drop-prefix
#check @releaseRead_waiters_sublist
#check @releaseWrite_waiters_sublist
#check @release_waiters_sublist
#check @acquire_waiters_super_or_eq

-- D-1.8 single-step order preservation
#check @applyOp_preserves_waiter_order

-- D-1.9 partial: structural sublist form
#check @rwLock_fifo_admission_temporal_structural

-- D-2.4 full substantive monotonicity (NEW)
#check @writerWaitDepth_monotone_under_effective_release

-- D-1.9 operational invariants (NEW — closes D-1.9 partial gap)
#check @leave_waiters_implies_holder
#check @promote_prefix_inclusion
#check @c_in_waiters_through_admission

-- D-1.9 FULL MAIN THEOREM (NEW)
#check @rwLock_fifo_admission_temporal

-- §4.5 FairTrace + D-3 liveness building blocks
#check @FairTrace
#check @MAX_RELEASE_DELAY
#check @rwLock_writer_no_starvation_step
#check @writer_at_head_promoted
#check @reader_at_head_promoted
#check @promote_noop_on_empty_waiters

-- D-4 concrete event model
#check @ConcreteRwLockOp
#check @concreteApplyOp
#check @opCorresponds
#check @concreteApplyOp_preserves_sim_load
#check @concreteApplyOp_preserves_sim_wfe
#check @concreteApplyOp_preserves_sim_sev
#check @concreteApplyOp_preserves_sim_cas_acquire_read_fail
#check @concreteApplyOp_cas_acquire_read_success
#check @concreteApplyOp_preserves_sim_cas_acquire_write_fail
#check @concreteApplyOp_cas_acquire_write_success
#check @encodeRwLock_at_least_one_when_reader
#check @tryAcquireRead_direct_acquire_shape
#check @tryAcquireWrite_direct_acquire_shape

-- RwLockRefinement: D-4 bisimulation infrastructure
#check @ListCorresponds
#check @rustImplementsRwLock
#check @rust_rwLock_refines_lean_nil
#check @concreteApplyOp_load_preserves_state
#check @concreteApplyOp_wfeWait_preserves_state
#check @concreteApplyOp_sev_preserves_state
#check @concreteApplyOp_fetch_sub_no_underflow
#check @rwLockSim_preserved_by_direct_acquire_read
#check @rwLockSim_preserved_by_direct_acquire_write
#check @rwLockSim_preserved_by_noop_chain

-- ============================================================================
-- Decidable examples (operational sanity checks)
-- ============================================================================

private def c0 : CoreId := ⟨0, by decide⟩
private def c1 : CoreId := ⟨1, by decide⟩
private def c2 : CoreId := ⟨2, by decide⟩
private def c3 : CoreId := ⟨3, by decide⟩

-- D-2.3: writerWaitDepth bounded by numCores - 1 = 3 on RPi5.
example :
    let s : RwLockState :=
      { writerHeld := some c0, readers := [],
        waiters := [(c1, .write), (c2, .write), (c3, .write)] }
    writerWaitDepth s c1 = 1 := by decide

example :
    let s : RwLockState :=
      { writerHeld := some c0, readers := [],
        waiters := [(c1, .write), (c2, .write), (c3, .write)] }
    writerWaitDepth s c2 = 2 := by decide

example :
    let s : RwLockState :=
      { writerHeld := some c0, readers := [],
        waiters := [(c1, .write), (c2, .write), (c3, .write)] }
    writerWaitDepth s c3 = 3 := by decide

-- D-1.6: tryAcquireRead on unheld grows readers, not waiters.
example :
    (RwLockState.unheld.applyOp (.tryAcquireRead c0)).waiters = [] := by decide

example :
    (RwLockState.unheld.applyOp (.tryAcquireRead c0)).readers = [c0] := by decide

-- D-1.6: tryAcquireRead while writer holds → enqueue.
example :
    let s := RwLockState.unheld.applyOp (.tryAcquireWrite c0)
    s.applyOp (.tryAcquireRead c1) |>.waiters = [(c1, .read)] := by decide

-- D-3.5: writer at head gets admitted to writerHeld.
example :
    let s : RwLockState :=
      { writerHeld := none, readers := [],
        waiters := [(c0, .write)] }
    s.promoteWaitersOnWriterRelease.writerHeld = some c0 := by decide

-- D-3.5: reader at head batch-promoted to readers.
example :
    let s : RwLockState :=
      { writerHeld := none, readers := [],
        waiters := [(c0, .read), (c1, .read), (c2, .write)] }
    let s' := s.promoteWaitersOnWriterRelease
    s'.readers = [c0, c1] ∧ s'.waiters = [(c2, .write)] := by decide

-- D-4.4: load doesn't change state.
example : (concreteApplyOp 0xDEADBEEF (.load c0)).1 = 0xDEADBEEF := by decide

-- D-4.4: wfeWait doesn't change state.
example : (concreteApplyOp 42 (.wfeWait c0)).1 = 42 := by decide

-- D-4.4: sev doesn't change state.
example : (concreteApplyOp 7 (.sev c0)).1 = 7 := by decide

-- D-4.5: successful CAS produces the new value.
example :
    (concreteApplyOp 0 (.casAcquireRead c0 0 5)).1 = 5 := by decide

-- D-4.5: failed CAS preserves state.
example :
    (concreteApplyOp 1 (.casAcquireRead c0 0 5)).1 = 1 := by decide

-- §4.5: FairTrace placeholder constant.
example : MAX_RELEASE_DELAY = 1024 := by decide

-- ============================================================================
-- Runtime assertion harness
-- ============================================================================

/-- Mini `assertBool` helper. -/
private def assertBool (label : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {label}"
  else
    IO.println s!"  FAIL: {label}"
    IO.Process.exit 1

def runDeferredChecks : IO Unit := do
  IO.println "=== WS-SM SM2.C-defer D-1..D-4 deferred-completion checks ==="

  IO.println "--- §4.1 Execution primitives ---"
  -- Smoke test: unheld is reachable, hence wf.
  assertBool "RwLockReachable.base : RwLockReachable unheld"
    (RwLockState.unheld.wf)

  IO.println "--- §4.3 + D-2 writerWaitDepth ---"
  let s0 : RwLockState :=
    { writerHeld := some c0, readers := [],
      waiters := [(c1, .write), (c2, .write)] }
  -- writerWaitDepth s c1 = idxOf(c1) + readers + writer_bit = 0 + 0 + 1 = 1.
  assertBool "writerWaitDepth(c1) = 1 in 2-writer-queue + held"
    (decide (writerWaitDepth s0 c1 = 1))
  assertBool "writerWaitDepth(c2) = 2 in 2-writer-queue + held"
    (decide (writerWaitDepth s0 c2 = 2))

  IO.println "--- D-1.6 append-to-tail (acquires) ---"
  -- tryAcquireRead on unheld → no waiters appended (direct acquire).
  assertBool "tryAcquireRead unheld → waiters = []"
    (decide ((RwLockState.unheld.applyOp (.tryAcquireRead c0)).waiters = []))
  -- tryAcquireRead under writer-held → appends to waiters.
  let s_w := RwLockState.unheld.applyOp (.tryAcquireWrite c0)
  assertBool "tryAcquireRead under writer-held → appends 1 waiter"
    (decide ((s_w.applyOp (.tryAcquireRead c1)).waiters.length = 1))

  IO.println "--- D-3.5 head promotion ---"
  -- Writer at head with no holders → promoted.
  let s_head_w : RwLockState :=
    { writerHeld := none, readers := [], waiters := [(c0, .write)] }
  assertBool "writer head promoted to writerHeld"
    (decide (s_head_w.promoteWaitersOnWriterRelease.writerHeld = some c0))
  -- Reader head batch-promoted.
  let s_head_r : RwLockState :=
    { writerHeld := none, readers := [],
      waiters := [(c0, .read), (c1, .read), (c2, .write)] }
  let s_head_r_post := s_head_r.promoteWaitersOnWriterRelease
  assertBool "reader head batch: 2 readers admitted"
    (decide (s_head_r_post.readers.length = 2))
  assertBool "reader head batch: writer remains queued"
    (decide (s_head_r_post.waiters = [(c2, .write)]))

  IO.println "--- D-4 concrete event model ---"
  assertBool "load preserves state (UInt64 modular)"
    (decide ((concreteApplyOp 0xCAFE (.load c0)).1 = 0xCAFE))
  assertBool "successful CAS produces new value"
    (decide ((concreteApplyOp 0 (.casAcquireRead c0 0 1)).1 = 1))
  assertBool "failed CAS preserves state"
    (decide ((concreteApplyOp 1 (.casAcquireRead c0 0 1)).1 = 1))

  IO.println "--- §4.5 FairTrace structure ---"
  assertBool "MAX_RELEASE_DELAY = 1024"
    (decide (MAX_RELEASE_DELAY = 1024))

  IO.println "--- D-2.4 substantive monotonicity (concrete instance) ---"
  -- writerWaitDepth_monotone_under_effective_release: depth decreases by ≥ 1
  -- under any effective release op where the writer remains queued.
  -- Concrete instance: pre = {writerHeld := some c0, readers := [],
  --                          waiters := [(c1, .write), (c2, .write)]}.
  --   pre depth(c1) = 0 (idxOf) + 0 (readers) + 1 (writer_bit) = 1.
  -- Apply releaseWrite c0: post = {writerHeld := some c1, readers := [],
  --                                waiters := [(c2, .write)]}.
  --   post depth(c1) — c1 ∈ writerHeld, NOT in waiters.  Tests the
  --   "c1 still queued" precondition: this case doesn't apply (c1 admitted).
  -- Instead, test depth(c2):
  --   pre depth(c2) = 1 + 0 + 1 = 2.
  --   post depth(c2) = 0 + 0 + 1 = 1.
  --   1 + 1 = 2 ≤ 2. ✓ (monotone with strict decrease.)
  let pre_state : RwLockState :=
    { writerHeld := some c0, readers := [],
      waiters := [(c1, .write), (c2, .write)] }
  let post_state := pre_state.applyOp (.releaseWrite c0)
  assertBool "D-2.4: pre depth(c2) = 2"
    (decide (writerWaitDepth pre_state c2 = 2))
  assertBool "D-2.4: post depth(c2) = 1"
    (decide (writerWaitDepth post_state c2 = 1))
  assertBool "D-2.4: monotone: post(c2) + 1 ≤ pre(c2)"
    (decide (writerWaitDepth post_state c2 + 1 ≤ writerWaitDepth pre_state c2))

  IO.println "==============================="
  IO.println "All SM2.C-defer D-1..D-4 checks PASS."

end SeLe4n.Tests.RwLockDeferred

/-- Lake-callable entry point. -/
def main : IO Unit := SeLe4n.Tests.RwLockDeferred.runDeferredChecks
