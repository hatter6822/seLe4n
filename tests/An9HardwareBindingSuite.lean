/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.BarrierComposition
import SeLe4n.Kernel.Architecture.TlbCacheComposition
import SeLe4n.Kernel.Architecture.TlbModel
import SeLe4n.Kernel.Lifecycle.Suspend

/-!
# AN9 Hardware Binding regression suite

Exercises the v1.0.0 closure of every hardware-binding deferred item
from `AUDIT_v0.29.0_DEFERRED.md` (DEF-A-M04, DEF-A-M06, DEF-A-M08,
DEF-A-M09, DEF-C-M04, DEF-P-L9 cross-ref, DEF-R-HAL-L14, DEF-R-HAL-L17,
DEF-R-HAL-L18, DEF-R-HAL-L19, DEF-R-HAL-L20).

Each test produces a single `[PASS]` / `[FAIL]` line; the executable
exits non-zero if any test fails.  Wired into `test_tier2_negative.sh`.
-/

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Lifecycle.Suspend

private def passLine (name : String) : IO Unit :=
  IO.println s!"[PASS] {name}"

private def failLine (name : String) (reason : String) : IO Unit := do
  IO.eprintln s!"[FAIL] {name}: {reason}"
  IO.Process.exit 1

private def expect (name : String) (cond : Bool) (reason : String) : IO Unit :=
  if cond then passLine name else failLine name reason

def main : IO Unit := do
  -- AN9-C: BarrierKind algebra
  expect "an9c_barrier_subsumes_refl"
    (decide (BarrierKind.dsbIsh.subsumes BarrierKind.dsbIsh))
    "BarrierKind reflexivity"

  -- The following are decidable by `decide`; we exercise the
  -- decision procedure directly so the algebra's runtime semantics
  -- are checked, not just typechecked.
  expect "an9c_pageTableUpdate_subsumes_dsbIshst"
    (decide (BarrierKind.armv8PageTableUpdateSequence.subsumes BarrierKind.dsbIshst))
    "page-table sequence must subsume dsbIshst leaf"

  expect "an9c_pageTableUpdate_subsumes_isb"
    (decide (BarrierKind.armv8PageTableUpdateSequence.subsumes BarrierKind.isb))
    "page-table sequence must subsume isb leaf"

  expect "an9c_pageTableUpdate_subsumes_dcCvacDsbIsh"
    (decide (BarrierKind.armv8PageTableUpdateSequence.subsumes BarrierKind.dcCvacDsbIsh))
    "page-table sequence must subsume dcCvacDsbIsh leaf"

  expect "an9c_mmioWrite_subsumes_dsbIshst"
    (decide (BarrierKind.mmioWriteOrderingSequence.subsumes BarrierKind.dsbIshst))
    "MMIO write sequence must subsume dsbIshst leaf"

  -- AN9-I: outer-shareable widening
  expect "an9i_mmioWriteCrossCluster_subsumes_dsbOshst"
    (decide (BarrierKind.mmioWriteOrderingSequenceOuterShareable.subsumes BarrierKind.dsbOshst))
    "outer-shareable MMIO sequence must subsume dsbOshst"

  expect "an9i_storeBarrierClosure_covers_both"
    (decide (BarrierKind.storeBarrierClosure.subsumes BarrierKind.dsbIshst) ∧
     decide (BarrierKind.storeBarrierClosure.subsumes BarrierKind.dsbOshst))
    "storeBarrierClosure must cover both dsbIshst and dsbOshst"

  -- AN9-B: tlbBarrierComplete substantive
  expect "an9b_tlbBarrierComplete_default"
    (decide (default : SystemState).machine.tlbBarrierEmitted)
    "default state must satisfy tlbBarrierEmitted"

  expect "an9b_tlbBarrierComplete_default_bitmask"
    (decide ((default : SystemState).machine.lastTlbBarrierKind &&& 0x05 = 0x05))
    "default state must include dsbIsh|isb leaves in lastTlbBarrierKind"

  -- AN9-A: TLB+Cache composition theorem witness
  expect "an9a_pageTableUpdate_full_coherency_default_witness"
    (decide ((default : SystemState).machine.tlbBarrierEmitted))
    "default state must witness page-table update coherency precondition"

  expect "an9a_armv8DCacheToICacheSequence_covers_dsb_ish"
    (decide (armv8DCacheToICacheSequence.covers CacheBarrierKind.dsb_ish))
    "D→I sequence must include dsb_ish leaf"

  expect "an9a_armv8DCacheToICacheSequence_covers_isb"
    (decide (armv8DCacheToICacheSequence.covers CacheBarrierKind.isb))
    "D→I sequence must include isb leaf"

  expect "an9a_barrierKind_pt_update_aligns"
    (decide (BarrierKind.armv8PageTableUpdateSequence.subsumes BarrierKind.isb)
      ∧ decide (armv8DCacheToICacheSequence.covers CacheBarrierKind.isb))
    "BarrierKind page-table sequence must align with cache D→I sequence"

  -- AN9-D: precondition predicate is decidable — default state has
  -- interrupts disabled (PSTATE.I = 1), matching the FFI bracket
  -- precondition shape.
  expect "an9d_atomicity_precondition_default"
    (decide (! (default : SystemState).machine.interruptsEnabled))
    "default state has interrupts disabled (FFI bracket precondition)"

  -- AN9-D: transient-window invariant theorem proved unconditionally
  -- for the default state (typechecks, no decide needed).
  let _ := suspendThread_transientWindowInvariant_default (SeLe4n.ThreadId.ofNat 1)
  passLine "an9d_transientWindowInvariant_default_proven"

  -- All AN9 substantive surface anchors verified.
  IO.println ""
  IO.println "========================================"
  IO.println "AN9 Hardware Binding suite: ALL PASS"
  IO.println "========================================"
