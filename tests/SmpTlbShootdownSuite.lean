-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.TlbShootdown

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
  IO.println "===================================================="
  IO.println "All SM7.A TLB shootdown descriptor + state checks PASS."

end SeLe4n.Testing.SmpTlbShootdown

def main : IO Unit :=
  SeLe4n.Testing.SmpTlbShootdown.runSmpTlbShootdownChecks
