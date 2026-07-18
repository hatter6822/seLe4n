-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.TlbShootdown
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Model.State

/-!
# WS-SM SM7.A — TLB shootdown descriptor + state test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase
SM7.A "Shootdown descriptor + state" deliverable
(`docs/planning/SMP_TLB_SHOOTDOWN_PLAN.md` §5, sub-tasks SM7.A.1–A.6).
The suite is the SM7.E.1 `SmpTlbShootdownSuite` seed; the SM7.B/SM7.C
scenario groups (protocol round trips, per-core TLB invalidation) land
here as those phases arrive.

* **§1 Surface anchors** — every public SM7.A symbol resolves at
  elaboration time (rename/removal fails the build).
* **§2 Elaboration-time examples** — decidable examples + theorem
  application witnesses for the headline SM7.A facts (quiescent boot
  state, capacity bound, FIFO append, fold-to-`allAcked`).
* **§3 Runtime assertions** — `lake exe smp_tlb_shootdown_suite`
  exercises the actual `enqueueShootdown` / `drainShootdowns` /
  `acknowledgeShootdown` / `beginShootdownRound` computations on the
  SM7.A scenarios: descriptor operand round-trips, the quiescent boot
  state, FIFO enqueue + cross-core framing, the fail-closed capacity
  bound, exhaustive drains, the ack-round lifecycle, and a full
  4-core state-level shootdown round trip.
-/

namespace SeLe4n.Testing.SmpTlbShootdown

open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM7.A public symbol resolves
-- ============================================================================

-- SM7.A.1 descriptor:
#check @TlbShootdownDescriptor
#check @TlbShootdownDescriptor.op
#check @TlbShootdownDescriptor.initiator

-- SM7.A.2 + SM7.A.3 state, boot state, path-a accessors:
#check @TlbShootdownState
#check @TlbShootdownState.pendingShootdowns
#check @TlbShootdownState.shootdownAck
#check @TlbShootdownState.initial
#check @TlbShootdownState.pendingOnCore
#check @TlbShootdownState.ackOnCore
#check @TlbShootdownState.setPendingOnCore
#check @TlbShootdownState.setAckOnCore

-- SM7.A.2 store/load reduction algebra + extensionality:
#check @TlbShootdownState.setPendingOnCore_pendingOnCore_self
#check @TlbShootdownState.setPendingOnCore_pendingOnCore_ne
#check @TlbShootdownState.setPendingOnCore_ackOnCore
#check @TlbShootdownState.setAckOnCore_ackOnCore_self
#check @TlbShootdownState.setAckOnCore_ackOnCore_ne
#check @TlbShootdownState.setAckOnCore_pendingOnCore
#check @TlbShootdownState.ext_perCore
#check @TlbShootdownState.initial_pendingOnCore
#check @TlbShootdownState.initial_ackOnCore

-- SM7.A.6 capacity bound + invariants:
#check @maxPendingPerCore
#check @maxPendingPerCore_pos
#check @pendingBounded
#check @allAcked
#check @shootdownQuiescent
#check @initial_pendingBounded
#check @initial_allAcked
#check @initial_shootdownQuiescent
#check @pendingBounded_of_shootdownQuiescent

-- SM7.A.4 enqueueShootdown + theorems:
#check @enqueueShootdown
#check @enqueueShootdown_isSome_iff
#check @enqueueShootdown_eq_none_iff
#check @enqueueShootdown_eq_none_of_full
#check @enqueueShootdown_pending_target
#check @enqueueShootdown_mem
#check @enqueueShootdown_length
#check @enqueueShootdown_frame_pending
#check @enqueueShootdown_frame_ack
#check @enqueueShootdown_preserves_pendingBounded

-- SM7.A.5 drainShootdowns + theorems:
#check @drainShootdowns
#check @drainShootdowns_fst
#check @mem_drainShootdowns_fst_iff
#check @drainShootdowns_pending_self
#check @drainShootdowns_frame_pending
#check @drainShootdowns_frame_ack
#check @drainShootdowns_preserves_pendingBounded
#check @drainShootdowns_drain_twice
#check @enqueueShootdown_isSome_after_drain
#check @drainShootdowns_after_enqueue

-- SM7.A.3 acknowledgment ops + round initialization:
#check @acknowledgeShootdown
#check @acknowledgeShootdown_ackOnCore_self
#check @acknowledgeShootdown_ackOnCore_ne
#check @acknowledgeShootdown_frame_pending
#check @acknowledgeShootdown_preserves_pendingBounded
#check @acknowledgeShootdown_monotone
#check @foldl_acknowledgeShootdown_monotone
#check @foldl_acknowledgeShootdown_sets
#check @allCores_foldl_acknowledgeShootdown_allAcked
#check @beginShootdownRound
#check @beginShootdownRound_ackOnCore_initiator
#check @beginShootdownRound_ackOnCore_target
#check @beginShootdownRound_ackOnCore_iff
#check @beginShootdownRound_frame_pending
#check @beginShootdownRound_preserves_pendingBounded

-- SM7.A completion cut — pure operand module (extracted from
-- TlbiForSharing; fully-qualified names unchanged):
#check @TlbInvalidation
#check @TlbInvalidation.toOpTag
#check @TlbInvalidation.toAsid
#check @TlbInvalidation.toVaddr
#check @TlbInvalidation.toOpTag_in_range
#check @TlbInvalidation.toOpTag_distinct_constructors

-- SM7.A completion cut — capacity sufficiency for a serialised round:
#check @enqueueShootdown_isSome_of_empty
#check @foldlM_enqueueShootdown_isSome
#check @foldlM_enqueueShootdown_frame_ack
#check @foldlM_enqueueShootdown_frame_pending

-- SM7.A completion cut — overflow-coalescing enqueue:
#check @enqueueShootdownOrCoalesce
#check @enqueueShootdownOrCoalesce_eq_enqueue
#check @enqueueShootdownOrCoalesce_of_full
#check @enqueueShootdownOrCoalesce_request_covered
#check @enqueueShootdownOrCoalesce_pending_covered
#check @enqueueShootdownOrCoalesce_preserves_pendingBounded
#check @enqueueShootdownOrCoalesce_frame_pending
#check @enqueueShootdownOrCoalesce_frame_ack

-- SM7.A audit cut — the global round-lock seam (the round-serialisation
-- contract's serialiser):
#check @ShootdownRoundLockId
#check @ShootdownRoundLockId.singleton

-- SM7.A completion cut — round-level composition + the quiescence
-- capstone:
#check @completeShootdownOnCore
#check @completeShootdownOnCore_eq
#check @completeShootdownOnCore_pendingOnCore_self
#check @completeShootdownOnCore_ackOnCore_self
#check @completeShootdownOnCore_frame_pending
#check @completeShootdownOnCore_frame_ack
#check @foldl_completeShootdownOnCore_pendingOnCore
#check @foldl_completeShootdownOnCore_ackOnCore
#check @beginRound_foldlM_enqueueShootdown_isSome
#check @shootdownRound_restores_quiescent

-- SM7.A completion cut — per-core pending-queue lock identifier (the
-- SM7.B.7 seam):
#check @ShootdownQueueLockId
#check @ShootdownQueueLockId.core
#check @ShootdownQueueLockId.le_refl
#check @ShootdownQueueLockId.le_trans
#check @ShootdownQueueLockId.le_antisymm
#check @ShootdownQueueLockId.le_total
#check @ShootdownQueueLockId.lt_or_gt_of_ne

-- SM7.A completion cut — SystemState mount (the plan §4.1
-- "ConcurrencyState" placement) + default-state theorems:
#check @SeLe4n.Model.SystemState.tlbShootdown
#check @SeLe4n.Model.default_tlbShootdown_initial
#check @SeLe4n.Model.default_tlbShootdown_quiescent
#check @SeLe4n.Model.default_tlbShootdown_pendingBounded

-- SM7.A completion cut — FFI seam (Rust SHOOTDOWN_ACK realisation):
#check @SeLe4n.Platform.FFI.ffiShootdownAckSet
#check @SeLe4n.Platform.FFI.ffiShootdownAckIsSet
#check @SeLe4n.Platform.FFI.ffiShootdownResetForRound
#check @SeLe4n.Platform.FFI.ffiShootdownAllAcked
#check @SeLe4n.Kernel.Concurrency.shootdownAckSet
#check @SeLe4n.Kernel.Concurrency.shootdownAckIsSet
#check @SeLe4n.Kernel.Concurrency.shootdownResetForRound
#check @SeLe4n.Kernel.Concurrency.shootdownAllAcked
#check @SeLe4n.Kernel.Concurrency.shootdownAckSet_eq_ffi
#check @SeLe4n.Kernel.Concurrency.shootdownResetForRound_eq_ffi
#check @SeLe4n.Kernel.Concurrency.shootdownAck_ffi_core_in_range

-- ============================================================================
-- §2  Elaboration-time examples
-- ============================================================================

-- SM7.A.6: the capacity bound is the plan §4.1 literal.
example : maxPendingPerCore = 16 := rfl

-- SM7.A.2/A.3: the boot state is quiescent, fully acknowledged, and
-- bounded — evaluated by the Decidable instances over all 4 cores.
example : shootdownQuiescent TlbShootdownState.initial := by decide
example : allAcked TlbShootdownState.initial := by decide
example : pendingBounded TlbShootdownState.initial := by decide

-- SM7.A.2/A.3: theorem-application witnesses for the boot-state facts
-- (the general proofs, not just the `decide` evaluations).
example : shootdownQuiescent TlbShootdownState.initial :=
  initial_shootdownQuiescent
example : pendingBounded TlbShootdownState.initial :=
  pendingBounded_of_shootdownQuiescent initial_shootdownQuiescent

-- SM7.A.3: acknowledging every core reaches `allAcked` from ANY state —
-- the SM7.B.5 wait-loop-termination anchor applied to a worst-case
-- start (a fresh round opened by core 0, so three flags are down).
example :
    allAcked (allCores.foldl acknowledgeShootdown
      (beginShootdownRound TlbShootdownState.initial bootCoreId)) :=
  allCores_foldl_acknowledgeShootdown_allAcked _

-- SM7.A.4: enqueue-success is exactly the strict capacity test.
example (st : TlbShootdownState) (c : CoreId) (d : TlbShootdownDescriptor) :
    (enqueueShootdown st c d).isSome ↔
      (st.pendingOnCore c).length < maxPendingPerCore :=
  enqueueShootdown_isSome_iff st c d

-- SM7.A.5: draining a just-enqueued descriptor returns it FIFO-appended.
example {st st' : TlbShootdownState} {c : CoreId} {d : TlbShootdownDescriptor}
    (h : enqueueShootdown st c d = some st') :
    (drainShootdowns st' c).1 = st.pendingOnCore c ++ [d] :=
  drainShootdowns_after_enqueue h

-- SM7.A completion cut: a round's posting fold from a quiescent state
-- always succeeds (the formal plan-§4.1 capacity argument) …
example {st : TlbShootdownState} (hq : shootdownQuiescent st)
    (initiator : CoreId) {targets : List CoreId} (hnd : targets.Nodup)
    (d : TlbShootdownDescriptor) :
    (targets.foldlM (fun s c => enqueueShootdown s c d)
      (beginShootdownRound st initiator)).isSome :=
  beginRound_foldlM_enqueueShootdown_isSome hq initiator hnd d

-- … and a complete round restores quiescence (the SM7.A capstone), so
-- the *next* round's posting fold succeeds too — the induction that
-- keeps maxPendingPerCore sufficient forever.
example {st : TlbShootdownState} (hq : shootdownQuiescent st)
    (initiator : CoreId) {targets : List CoreId}
    (hcov : ∀ c : CoreId, c ≠ initiator → c ∈ targets)
    {d : TlbShootdownDescriptor} {posted : TlbShootdownState}
    (hpost : targets.foldlM (fun s c => enqueueShootdown s c d)
      (beginShootdownRound st initiator) = some posted) :
    shootdownQuiescent (targets.foldl completeShootdownOnCore posted) :=
  shootdownRound_restores_quiescent hq initiator hcov hpost

-- SM7.A completion cut: the coalescing enqueue keeps the capacity
-- invariant with no success hypothesis.
example {st : TlbShootdownState} (hB : pendingBounded st) (target : CoreId)
    (d : TlbShootdownDescriptor) :
    pendingBounded (enqueueShootdownOrCoalesce st target d) :=
  enqueueShootdownOrCoalesce_preserves_pendingBounded hB target d

-- SM7.A audit cut: the coalescing enqueue loses neither the new
-- request nor any previously queued descriptor.
example (st : TlbShootdownState) (target : CoreId)
    (d : TlbShootdownDescriptor) :
    ∀ dOld ∈ st.pendingOnCore target,
      dOld ∈ (enqueueShootdownOrCoalesce st target d).pendingOnCore target ∨
        ∃ d' ∈ (enqueueShootdownOrCoalesce st target d).pendingOnCore target,
          d'.op = TlbInvalidation.vmalle1 :=
  enqueueShootdownOrCoalesce_pending_covered st target d

-- SM7.A audit cut: the global shootdown-round lock is provably unique —
-- "at most one round in flight" is structural.
example (a b : ShootdownRoundLockId) : a = b :=
  ShootdownRoundLockId.singleton a b

-- SM7.A completion cut: the default SystemState mounts the quiescent
-- shootdown state (decidable + theorem forms).
example : SeLe4n.Model.SystemState.tlbShootdown default =
    TlbShootdownState.initial := SeLe4n.Model.default_tlbShootdown_initial
example : shootdownQuiescent (SeLe4n.Model.SystemState.tlbShootdown default) := by
  decide

-- SM7.A completion cut: the FFI seam's typed wrappers hand the Rust
-- side only in-range core ids (the fail-closed panic arm is
-- structurally unreachable).
example : ∀ c : CoreId, (UInt64.ofNat c.val).toNat < numCores :=
  SeLe4n.Kernel.Concurrency.shootdownAck_ffi_core_in_range

-- ============================================================================
-- §3  Runtime assertions
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

-- Concrete cores of the 4-core RPi5 topology.
private def core0 : CoreId := ⟨0, by decide⟩
private def core1 : CoreId := ⟨1, by decide⟩
private def core2 : CoreId := ⟨2, by decide⟩
private def core3 : CoreId := ⟨3, by decide⟩

-- Concrete descriptors covering every `TlbInvalidation` flavour the
-- SM7.B callers will post: page unmap, last-level unmap, ASID
-- retirement, full flush.
private def descUnmapPage : TlbShootdownDescriptor :=
  { op := .vae1 5 0x1000, initiator := core0 }
private def descLastLevel : TlbShootdownDescriptor :=
  { op := .vale1 5 0x2000, initiator := core0 }
private def descAsidRetire : TlbShootdownDescriptor :=
  { op := .aside1 7, initiator := core2 }
private def descFullFlush : TlbShootdownDescriptor :=
  { op := .vmalle1, initiator := core1 }

/-- Enqueue a batch of descriptors onto one target, failing (`none`) as
soon as any single enqueue fails — the shape of an SM7.B initiator
posting a round's descriptors. -/
private def enqueueMany (st : TlbShootdownState) (target : CoreId)
    (ds : List TlbShootdownDescriptor) : Option TlbShootdownState :=
  ds.foldlM (fun s d => enqueueShootdown s target d) st

-- ----------------------------------------------------------------------------
-- §3.1  Descriptor construction + operand round-trips (SM7.A.1)
-- ----------------------------------------------------------------------------

private def runDescriptorChecks : IO Unit := do
  IO.println "-- §3.1 descriptor construction + operand round-trips"
  assertBool "page-unmap descriptor carries its ASID operand"
    (descUnmapPage.op.toAsid == 5)
  assertBool "page-unmap descriptor carries its VAddr operand"
    (descUnmapPage.op.toVaddr == 0x1000)
  assertBool "page-unmap descriptor encodes op tag 1 (vae1)"
    (descUnmapPage.op.toOpTag == 1)
  assertBool "ASID-retire descriptor carries its ASID, zero VAddr"
    (descAsidRetire.op.toAsid == 7 && descAsidRetire.op.toVaddr == 0)
  assertBool "full-flush descriptor has zero operands (vmalle1)"
    (descFullFlush.op.toAsid == 0 && descFullFlush.op.toVaddr == 0)
  assertBool "last-level descriptor encodes op tag 3 (vale1)"
    (descLastLevel.op.toOpTag == 3)
  assertBool "descriptor records its initiating core"
    (descAsidRetire.initiator == core2 && descUnmapPage.initiator == core0)
  assertBool "descriptor equality is decidable and structural"
    (descUnmapPage == descUnmapPage && !(descUnmapPage == descLastLevel))

-- ----------------------------------------------------------------------------
-- §3.2  Quiescent boot state (SM7.A.2 + SM7.A.3)
-- ----------------------------------------------------------------------------

private def runInitialStateChecks : IO Unit := do
  IO.println "-- §3.2 quiescent boot state"
  let st := TlbShootdownState.initial
  assertBool "every core boots with an empty pending queue"
    (allCores.all fun c => st.pendingOnCore c == [])
  assertBool "every core boots acknowledged"
    (allCores.all fun c => st.ackOnCore c)
  assertBool "boot state is quiescent (decidable instance)"
    (decide (shootdownQuiescent st))
  assertBool "boot state satisfies the capacity invariant"
    (decide (pendingBounded st))
  assertBool "boot state is fully acknowledged (decidable instance)"
    (decide (allAcked st))

-- ----------------------------------------------------------------------------
-- §3.3  FIFO enqueue + cross-core framing (SM7.A.4)
-- ----------------------------------------------------------------------------

private def runEnqueueChecks : IO Unit := do
  IO.println "-- §3.3 FIFO enqueue + cross-core framing"
  let st0 := TlbShootdownState.initial
  match enqueueShootdown st0 core1 descUnmapPage with
  | none => assertBool "enqueue onto an empty queue succeeds" false
  | some st1 => do
    assertBool "enqueued descriptor lands on the target queue"
      (st1.pendingOnCore core1 == [descUnmapPage])
    assertBool "other cores' queues are framed"
      ([core0, core2, core3].all fun c => st1.pendingOnCore c == [])
    assertBool "no ack flag is touched by an enqueue"
      (allCores.all fun c => st1.ackOnCore c == st0.ackOnCore c)
    match enqueueShootdown st1 core1 descAsidRetire with
    | none => assertBool "second enqueue onto the same queue succeeds" false
    | some st2 => do
      assertBool "second enqueue appends at the tail (FIFO)"
        (st2.pendingOnCore core1 == [descUnmapPage, descAsidRetire])
      assertBool "post-enqueue state stays bounded (decidable instance)"
        (decide (pendingBounded st2))
      match enqueueShootdown st2 core3 descFullFlush with
      | none => assertBool "enqueue onto a different core succeeds" false
      | some st3 => do
        assertBool "cross-core enqueues are independent"
          (st3.pendingOnCore core1 == [descUnmapPage, descAsidRetire] &&
           st3.pendingOnCore core3 == [descFullFlush] &&
           st3.pendingOnCore core0 == [] && st3.pendingOnCore core2 == [])

-- ----------------------------------------------------------------------------
-- §3.4  Fail-closed capacity bound (SM7.A.6)
-- ----------------------------------------------------------------------------

private def runCapacityChecks : IO Unit := do
  IO.println "-- §3.4 fail-closed capacity bound"
  let st0 := TlbShootdownState.initial
  match enqueueMany st0 core2 (List.replicate maxPendingPerCore descUnmapPage) with
  | none => assertBool "filling a queue to capacity succeeds" false
  | some full => do
    assertBool "queue holds exactly maxPendingPerCore descriptors"
      ((full.pendingOnCore core2).length == maxPendingPerCore)
    assertBool "the state at capacity still satisfies the invariant"
      (decide (pendingBounded full))
    assertBool "the 17th enqueue is rejected fail-closed"
      ((enqueueShootdown full core2 descAsidRetire).isNone)
    assertBool "a full queue on one core does not block another core"
      ((enqueueShootdown full core0 descAsidRetire).isSome)
    let (drained, cleared) := drainShootdowns full core2
    assertBool "the drain returns all 16 pending descriptors"
      (drained.length == maxPendingPerCore)
    assertBool "draining restores capacity: enqueue succeeds again"
      ((enqueueShootdown cleared core2 descAsidRetire).isSome)
  assertBool "over-filling by one descriptor fails the whole batch"
    ((enqueueMany st0 core2
      (List.replicate (maxPendingPerCore + 1) descUnmapPage)).isNone)

-- ----------------------------------------------------------------------------
-- §3.5  Exhaustive drain (SM7.A.5)
-- ----------------------------------------------------------------------------

private def runDrainChecks : IO Unit := do
  IO.println "-- §3.5 exhaustive drain"
  let st0 := TlbShootdownState.initial
  match enqueueMany st0 core1 [descUnmapPage, descAsidRetire, descFullFlush] with
  | none => assertBool "three-descriptor setup enqueue succeeds" false
  | some st => do
    let (drained, st') := drainShootdowns st core1
    assertBool "drain returns the whole queue in FIFO order"
      (drained == [descUnmapPage, descAsidRetire, descFullFlush])
    assertBool "the drained core's queue is empty"
      (st'.pendingOnCore core1 == [])
    assertBool "draining core 1 frames every other core's queue"
      ([core0, core2, core3].all fun c =>
        st'.pendingOnCore c == st.pendingOnCore c)
    assertBool "draining touches no ack flag"
      (allCores.all fun c => st'.ackOnCore c == st.ackOnCore c)
    assertBool "a second drain returns nothing (exhaustive)"
      ((drainShootdowns st' core1).1 == [])
    assertBool "the post-drain state stays bounded"
      (decide (pendingBounded st'))
  assertBool "draining a quiescent core returns nothing"
    ((drainShootdowns st0 core3).1 == [])

-- ----------------------------------------------------------------------------
-- §3.6  Acknowledgment round lifecycle (SM7.A.3)
-- ----------------------------------------------------------------------------

private def runAckRoundChecks : IO Unit := do
  IO.println "-- §3.6 acknowledgment round lifecycle"
  let st0 := TlbShootdownState.initial
  let opened := beginShootdownRound st0 core0
  assertBool "the initiator is born-acknowledged"
    (opened.ackOnCore core0)
  assertBool "every target starts the round unacknowledged"
    ([core1, core2, core3].all fun c => !(opened.ackOnCore c))
  assertBool "an open round is not allAcked"
    (!(decide (allAcked opened)))
  assertBool "opening a round touches no pending queue"
    (allCores.all fun c => opened.pendingOnCore c == st0.pendingOnCore c)
  let ackedTwo := acknowledgeShootdown opened core2
  assertBool "a target acknowledgment sets exactly its own flag"
    (ackedTwo.ackOnCore core2 && !(ackedTwo.ackOnCore core1) &&
     !(ackedTwo.ackOnCore core3) && ackedTwo.ackOnCore core0)
  assertBool "acknowledgment is monotone (initiator flag survives)"
    ((acknowledgeShootdown ackedTwo core1).ackOnCore core0)
  assertBool "acknowledging every remaining target reaches allAcked"
    (decide (allAcked
      (acknowledgeShootdown (acknowledgeShootdown ackedTwo core1) core3)))
  assertBool "folding acknowledgments over allCores reaches allAcked"
    (decide (allAcked (allCores.foldl acknowledgeShootdown opened)))
  assertBool "a round opened by a non-boot core marks only that core"
    (allCores.all fun c =>
      (beginShootdownRound st0 core3).ackOnCore c == (c == core3))

-- ----------------------------------------------------------------------------
-- §3.7  Full 4-core state-level shootdown round trip (SM7.A.1–A.6)
-- ----------------------------------------------------------------------------

private def runFullRoundTripChecks : IO Unit := do
  IO.println "-- §3.7 full 4-core state-level shootdown round trip"
  -- Core 0 unmaps a page of ASID 5: open the round, post one page-unmap
  -- descriptor per remote core (the plan §3.2 step-2 loop).
  let desc : TlbShootdownDescriptor := { op := .vae1 5 0x1000, initiator := core0 }
  let opened := beginShootdownRound TlbShootdownState.initial core0
  let posted? := [core1, core2, core3].foldlM
    (fun s c => enqueueShootdown s c desc) opened
  match posted? with
  | none => assertBool "posting one descriptor per target succeeds" false
  | some posted => do
    assertBool "each target sees exactly the round's descriptor"
      ([core1, core2, core3].all fun c => posted.pendingOnCore c == [desc])
    assertBool "the initiator's own queue stays empty"
      (posted.pendingOnCore core0 == [])
    assertBool "only the initiator is acknowledged while targets pend"
      (allCores.all fun c => posted.ackOnCore c == (c == core0))
    -- Each target's SGI handler: drain, (TLBI per descriptor — SM7.B),
    -- then acknowledge.
    let step := fun (s : TlbShootdownState) (c : CoreId) =>
      let (drained, s') := drainShootdowns s c
      (drained, acknowledgeShootdown s' c)
    let (d1, s1) := step posted core1
    let (d2, s2) := step s1 core2
    let (d3, s3) := step s2 core3
    assertBool "every handler drained exactly the posted descriptor"
      (d1 == [desc] && d2 == [desc] && d3 == [desc])
    assertBool "every drained descriptor carries the unmap operands"
      ((d1 ++ d2 ++ d3).all fun d =>
        d.op.toAsid == 5 && d.op.toVaddr == 0x1000 && d.initiator == core0)
    assertBool "after all handlers ran, the wait loop's exit holds"
      (decide (allAcked s3))
    assertBool "the completed round leaves the state quiescent"
      (decide (shootdownQuiescent s3))
    assertBool "the completed round satisfies the capacity invariant"
      (decide (pendingBounded s3))

-- ----------------------------------------------------------------------------
-- §3.8  Overflow-coalescing enqueue (SM7.A.6 completion cut)
-- ----------------------------------------------------------------------------

private def runCoalescingChecks : IO Unit := do
  IO.println "-- §3.8 overflow-coalescing enqueue"
  let st0 := TlbShootdownState.initial
  match enqueueShootdown st0 core1 descUnmapPage with
  | none => assertBool "baseline enqueue below capacity succeeds" false
  | some viaEnqueue =>
    assertBool "below capacity the coalescing enqueue is exactly enqueueShootdown"
      (enqueueShootdownOrCoalesce st0 core1 descUnmapPage == viaEnqueue)
  match enqueueMany st0 core2 (List.replicate maxPendingPerCore descUnmapPage) with
  | none => assertBool "filling a queue to capacity succeeds" false
  | some full => do
    let collapsed := enqueueShootdownOrCoalesce full core2 descAsidRetire
    assertBool "at capacity the queue collapses to a single full flush"
      (collapsed.pendingOnCore core2 ==
        [{ op := .vmalle1, initiator := descAsidRetire.initiator }])
    assertBool "the collapsed descriptor carries the requesting initiator"
      ((collapsed.pendingOnCore core2).all fun d => d.initiator == core2)
    assertBool "the collapse frames every other core's queue"
      ([core0, core1, core3].all fun c =>
        collapsed.pendingOnCore c == full.pendingOnCore c)
    assertBool "the collapse touches no ack flag"
      (allCores.all fun c => collapsed.ackOnCore c == full.ackOnCore c)
    assertBool "the collapsed state satisfies the capacity invariant"
      (decide (pendingBounded collapsed))
    assertBool "dropped descriptors are superseded: a full flush is pending"
      ((collapsed.pendingOnCore core2).any fun d =>
        d.op == TlbInvalidation.vmalle1)
    assertBool "after the collapse a normal enqueue succeeds again"
      ((enqueueShootdown collapsed core2 descUnmapPage).isSome)

-- ----------------------------------------------------------------------------
-- §3.9  Round-level composition (the generic capstone, exercised)
-- ----------------------------------------------------------------------------

private def runRoundCompositionChecks : IO Unit := do
  IO.println "-- §3.9 round-level composition"
  -- completeShootdownOnCore is the drain+acknowledge composition.
  match enqueueShootdown (beginShootdownRound TlbShootdownState.initial core0)
      core2 descUnmapPage with
  | none => assertBool "round-step setup enqueue succeeds" false
  | some st => do
    let done := completeShootdownOnCore st core2
    assertBool "a completed core's queue is empty"
      (done.pendingOnCore core2 == [])
    assertBool "a completed core's flag is acknowledged"
      (done.ackOnCore core2)
    assertBool "completing a core equals drain-then-acknowledge"
      (done == acknowledgeShootdown (drainShootdowns st core2).2 core2)
    assertBool "completing core 2 frames core 1's flag (still down)"
      (!(done.ackOnCore core1))
  -- The full generic pipeline: begin → post (foldlM) → complete (foldl).
  let opened := beginShootdownRound TlbShootdownState.initial core0
  let targets := [core1, core2, core3]
  match targets.foldlM (fun s c => enqueueShootdown s c descUnmapPage) opened with
  | none => assertBool "the round's posting fold succeeds from quiescence" false
  | some posted => do
    let final := targets.foldl completeShootdownOnCore posted
    assertBool "the folded round ends quiescent (the capstone, computed)"
      (decide (shootdownQuiescent final))
    assertBool "the folded round ends exactly at the boot state"
      (final == TlbShootdownState.initial)
    assertBool "the closed form: visited cores' queues empty, initiator's untouched"
      (targets.all (fun c => final.pendingOnCore c == []) &&
        final.pendingOnCore core0 == opened.pendingOnCore core0)
  assertBool "a duplicate target is harmless (drained twice, still quiescent)"
    (match [core1, core1, core2, core3].foldlM
        (fun s c => enqueueShootdown s c descUnmapPage)
        (beginShootdownRound TlbShootdownState.initial core0) with
      | none => false
      | some posted =>
        decide (shootdownQuiescent
          ([core1, core1, core2, core3].foldl completeShootdownOnCore posted)))

-- ----------------------------------------------------------------------------
-- §3.10  Pending-queue lock identifiers (the SM7.B.7 seam)
-- ----------------------------------------------------------------------------

private def runLockOrderChecks : IO Unit := do
  IO.println "-- §3.10 pending-queue lock identifiers"
  let l0 : ShootdownQueueLockId := ⟨core0⟩
  let l1 : ShootdownQueueLockId := ⟨core1⟩
  let l3 : ShootdownQueueLockId := ⟨core3⟩
  assertBool "queue locks order by core (0 ≤ 1, 1 ≤ 3)"
    (decide (l0 ≤ l1) && decide (l1 ≤ l3))
  assertBool "the order is strict across distinct cores"
    (decide (l0 < l1) && !(decide (l1 < l0)) && !(decide (l1 ≤ l0)))
  assertBool "every pair of queue locks is comparable (total order)"
    (allCores.all fun a => allCores.all fun b =>
      decide ((⟨a⟩ : ShootdownQueueLockId) ≤ ⟨b⟩) ||
      decide ((⟨b⟩ : ShootdownQueueLockId) ≤ ⟨a⟩))
  assertBool "distinct queue locks are strictly ordered one way"
    (allCores.all fun a => allCores.all fun b =>
      a == b ||
      (decide ((⟨a⟩ : ShootdownQueueLockId) < ⟨b⟩) ^^
        decide ((⟨b⟩ : ShootdownQueueLockId) < ⟨a⟩)))
  assertBool "the global round lock has exactly one value"
    ((⟨⟩ : ShootdownRoundLockId) == default &&
      default == (⟨⟩ : ShootdownRoundLockId))

-- ----------------------------------------------------------------------------
-- §3.11  SystemState mount (the plan §4.1 "ConcurrencyState" placement)
-- ----------------------------------------------------------------------------

private def runMountChecks : IO Unit := do
  IO.println "-- §3.11 SystemState mount"
  let st : SeLe4n.Model.SystemState := default
  assertBool "the default SystemState mounts the quiescent boot state"
    (st.tlbShootdown == TlbShootdownState.initial)
  assertBool "the mounted state is quiescent (decidable instance)"
    (decide (shootdownQuiescent st.tlbShootdown))
  assertBool "the mounted state satisfies the capacity invariant"
    (decide (pendingBounded st.tlbShootdown))
  assertBool "record updates elsewhere frame the mounted state"
    (({ st with tlb := SeLe4n.Model.TlbState.empty }).tlbShootdown ==
      st.tlbShootdown)

-- ----------------------------------------------------------------------------
-- Runner
-- ----------------------------------------------------------------------------

def runSmpTlbShootdownChecks : IO Unit := do
  IO.println "WS-SM SM7.A — TLB shootdown descriptor + state suite"
  IO.println "===================================================="
  runDescriptorChecks
  runInitialStateChecks
  runEnqueueChecks
  runCapacityChecks
  runDrainChecks
  runAckRoundChecks
  runFullRoundTripChecks
  runCoalescingChecks
  runRoundCompositionChecks
  runLockOrderChecks
  runMountChecks
  IO.println "===================================================="
  IO.println "All SM7.A TLB shootdown descriptor + state checks PASS."

end SeLe4n.Testing.SmpTlbShootdown

def main : IO Unit :=
  SeLe4n.Testing.SmpTlbShootdown.runSmpTlbShootdownChecks
