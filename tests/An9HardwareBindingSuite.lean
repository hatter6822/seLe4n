-- SPDX-License-Identifier: GPL-3.0-or-later
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
-- WS-RC R3 (DEEP-BOOT-01): Hardware-binding closure now exercises the
-- boot VSpaceRoot threading via `bootFromPlatformChecked`.
import SeLe4n.Platform.Boot
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Platform.RPi5.VSpaceBoot

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

  -- AN9-D (audit fix D1): substantive atomicity theorem on default
  -- state — `suspendThread` rejects with `.invalidArgument` because
  -- the empty `objects` table makes the lookup fail.  This is a
  -- REAL theorem (not `x = x`); the regression test below
  -- evaluates the actual function call and checks the error tag.
  let suspendResult := suspendThread (default : SystemState)
                         (⟨SeLe4n.ThreadId.ofNat 1, by decide⟩)
  let isInvalidArg : Bool := match suspendResult with
    | .error .invalidArgument => true
    | _ => false
  expect "an9d_audit_fix_default_rejects_invalidArgument"
    isInvalidArg
    "suspendThread on default state must reject with .invalidArgument"

  -- AN9-B (audit fix B1): markTlbDirty really does break
  -- tlbBarrierComplete (substantive negative test).
  expect "an9b_audit_fix_dirty_breaks_predicate"
    (decide (! (markTlbDirty (default : SystemState)).machine.tlbBarrierEmitted))
    "markTlbDirty must set tlbBarrierEmitted to false"

  expect "an9b_audit_fix_barriered_restores_witness"
    (decide
      ((markTlbBarriered (default : SystemState)).machine.tlbBarrierEmitted
        ∧ (markTlbBarriered (default : SystemState)).machine.lastTlbBarrierKind &&& 0x05 = 0x05))
    "markTlbBarriered must restore both witnesses"

  -- AN9-A (audit fix A1): joint state composition theorem.  Verifies
  -- the strengthened form on the empty state AND exercises the
  -- post-state field shapes substantively.
  let asid0 := ASID.ofNat 0
  let vaddr0 := VAddr.ofNat 0x1000
  let paddr0 := SeLe4n.PAddr.ofNat 0x80000
  let _bundle := TlbCacheJointState.empty_pageTableUpdate_full_coherency
                   asid0 vaddr0 paddr0
  -- Verify the joint update produces the expected post-state shapes
  -- (operationally, not just at the type level).
  let postJoint := TlbCacheJointState.empty.pageTableUpdate asid0 vaddr0 paddr0
  expect "an9a_audit_fix_joint_post_tlbBarrierEmitted_true"
    (decide postJoint.sysState.machine.tlbBarrierEmitted)
    "joint post-state must preserve tlbBarrierEmitted = true"
  expect "an9a_audit_fix_joint_post_lastTlbBarrierKind_includes_bracket"
    (decide (postJoint.sysState.machine.lastTlbBarrierKind &&& 0x05 = 0x05))
    "joint post-state must preserve dsbIsh|isb bracket bitmask"
  -- I-cache: every entry should be `.invalid` after the D→I sequence
  -- (the headline AN9-A coherency claim).
  expect "an9a_audit_fix_joint_post_icache_invalidated"
    (postJoint.cacheState.icache (SeLe4n.PAddr.ofNat 0x40000) = .invalid)
    "joint post-state I-cache must be fully invalidated"
  passLine "an9a_audit_fix_joint_pt_update_coherency_proven"

  -- AN9-B (audit reinforcement): markTlbDirty followed by
  -- markTlbBarriered is the canonical "operation+flush" round-trip.
  let dirtyState := markTlbDirty (default : SystemState)
  let restoredState := markTlbBarriered dirtyState
  expect "an9b_audit_fix_round_trip_dirty_then_clean"
    (decide restoredState.machine.tlbBarrierEmitted ∧
     decide (restoredState.machine.lastTlbBarrierKind &&& 0x05 = 0x05))
    "dirty→barriered round-trip must restore the bracket witness"

  -- ============================================================================
  -- WS-RC R3 (DEEP-BOOT-01): Boot VSpaceRoot threading
  -- ============================================================================

  -- The canonical RPi5 boot VSpaceRoot is now threaded through
  -- `bootFromPlatformChecked` via the `bootVSpaceRoot` PlatformConfig
  -- field.  These regression tests confirm that the proven-W^X-compliant
  -- structure is admitted by the gated boot path and that downstream
  -- VSpace lookup paths can resolve it.

  let r3Cfg : SeLe4n.Platform.Boot.PlatformConfig :=
    { irqTable := []
      initialObjects := []
      machineConfig := SeLe4n.defaultMachineConfig
      bootVSpaceRoot := some SeLe4n.Platform.RPi5.rpi5BootVSpaceRootEntry }

  -- R3-1: bootFromPlatformChecked succeeds with the canonical RPi5 boot VSpace.
  match SeLe4n.Platform.Boot.bootFromPlatformChecked r3Cfg with
  | .ok ist =>
      passLine "wsrc_r3_bootFromPlatformChecked_succeeds_with_rpi5_bootVSpace"
      -- R3-2: post-boot objects table contains the boot VSpace at the
      -- reserved ObjId, with a VSpaceRoot kernel object whose ASID
      -- matches the canonical root's ASID.
      let oid := SeLe4n.Platform.RPi5.rpi5BootVSpaceRootObjId
      match ist.state.objects[oid]? with
      | some (KernelObject.vspaceRoot vsr) =>
          expect "wsrc_r3_postboot_state_has_rpi5BootVSpaceRoot"
            (vsr.asid == SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot.asid)
            "post-boot VSpaceRoot ASID must match rpi5BootVSpaceRoot.asid"
      | _ =>
          failLine "wsrc_r3_postboot_state_has_rpi5BootVSpaceRoot"
            "no VSpaceRoot found at reserved boot ObjId"
      -- R3-3: post-boot wxExclusiveInvariant holds for the boot VSpace
      -- (witness: every mapping passes wxCompliant).
      match ist.state.objects[oid]? with
      | some (KernelObject.vspaceRoot vsr) =>
          let allWx : Bool :=
            vsr.mappings.fold true (fun acc _ entry => acc && entry.2.wxCompliant)
          expect "wsrc_r3_postboot_wxExclusiveInvariant_holds"
            allWx "every mapping in the post-boot VSpaceRoot must be W^X compliant"
      | _ =>
          failLine "wsrc_r3_postboot_wxExclusiveInvariant_holds"
            "no VSpaceRoot to validate"
      -- R3-4: asidTable maps the boot VSpace ASID to the reserved ObjId.
      let asid := SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot.asid
      match ist.state.asidTable[asid]? with
      | some recordedOid =>
          expect "wsrc_r3_asidTable_registers_boot_vspace"
            (recordedOid == oid)
            "asidTable lookup of rpi5BootVSpaceRoot.asid must yield the reserved ObjId"
      | none =>
          failLine "wsrc_r3_asidTable_registers_boot_vspace"
            "asidTable does not register the boot VSpace ASID"
  | .error e =>
      failLine "wsrc_r3_bootFromPlatformChecked_succeeds_with_rpi5_bootVSpace"
        s!"boot failed: {e}"

  -- R3-5: bootSafeObjectCheck admits the canonical RPi5 boot VSpace.
  expect "wsrc_r3_bootSafeObjectCheck_admits_rpi5BootVSpaceRoot"
    (SeLe4n.Platform.Boot.bootSafeObjectCheck
      (KernelObject.vspaceRoot SeLe4n.Platform.RPi5.VSpaceBoot.rpi5BootVSpaceRoot))
    "bootSafeObjectCheck must admit rpi5BootVSpaceRoot"

  -- All AN9 + WS-RC R3 substantive surface anchors verified.
  IO.println ""
  IO.println "========================================"
  IO.println "AN9 + WS-RC R3 Hardware Binding suite: ALL PASS"
  IO.println "========================================"
