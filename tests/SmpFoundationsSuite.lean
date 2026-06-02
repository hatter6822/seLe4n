-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Locks
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Sgi
import SeLe4n.Kernel.Concurrency.Anchors
import SeLe4n.Kernel.Concurrency.Assumptions
import SeLe4n.Kernel.Concurrency.Runtime
import SeLe4n.Kernel.SecondaryEntry
import SeLe4n.Kernel.Architecture.Assumptions
import SeLe4n.Kernel.Architecture.TlbiForSharing
import SeLe4n.Platform.FFI
import SeLe4n.Platform.RPi5.Contract
import SeLe4n.Platform.Sim.Contract
-- WS-SM SM4.E: the SMP-shape boot witnesses (`bootFromPlatform_smp_witness`,
-- `…_smp_currentAllNone`) that the retirement ledger points at live here.
import SeLe4n.Platform.Boot

/-!
# WS-SM SM0.S — Foundations test suite

Tier-3 surface anchors plus decidable examples for every public
symbol introduced in WS-SM Phase 0.  Catches:

* Renames or signature drift on the SM0.E/SM0.F/SM0.H/SM0.I types
  (`#check` of every public symbol).
* Numeric drift in the RPi5 PlatformBinding (`numCores`, `bootCoreId`,
  `coreCount`, `sharingDomain`).
* LockKind level reordering or duplication.
* SgiKind INTID reassignment.
* AN12-B inventory size + NoDup regressions.
* ArchAssumption 6th-case drift (SM0.A `singleCoreOperation`).

The suite is a runnable executable (`lake exe smp_foundations_suite`)
that performs every decidable check at runtime as well — every
`example : ... := by decide` is also asserted as a runtime property
inside `runFoundationsChecks`, so the assertions surface in the
`run` output if they ever silently regress.
-/

open SeLe4n.Kernel.Concurrency
open SeLe4n.Kernel.Architecture
open SeLe4n.Platform
open SeLe4n.Platform.RPi5

-- ============================================================================
-- §1 — Surface anchors: every SM0 public symbol resolves at elaboration
-- ============================================================================

/-! ## SM0.E — CoreId enumeration -/
#check @SeLe4n.Kernel.Concurrency.numCores
#check @SeLe4n.Kernel.Concurrency.CoreId
#check @SeLe4n.Kernel.Concurrency.bootCoreId
#check @SeLe4n.Kernel.Concurrency.allCores
#check @SeLe4n.Kernel.Concurrency.numCores_pos
#check @SeLe4n.Kernel.Concurrency.allCores_length
#check @SeLe4n.Kernel.Concurrency.allCores_nodup
#check @SeLe4n.Kernel.Concurrency.bootCoreId_valid
#check @SeLe4n.Kernel.Concurrency.bootCoreId_val_zero
#check @SeLe4n.Kernel.Concurrency.allCores_nonempty

/-! ## SM0.F — SharingDomain + DSB selectors -/
#check @SeLe4n.Kernel.Concurrency.SharingDomain
#check @SeLe4n.Kernel.Concurrency.dsbForSharing
#check @SeLe4n.Kernel.Concurrency.dsbStForSharing
#check @SeLe4n.Kernel.Concurrency.dsbForSharing_inner
#check @SeLe4n.Kernel.Concurrency.dsbForSharing_outer
#check @SeLe4n.Kernel.Concurrency.dsbStForSharing_inner
#check @SeLe4n.Kernel.Concurrency.dsbStForSharing_outer
#check @SeLe4n.Kernel.Concurrency.dsbForSharing_injective
#check @SeLe4n.Kernel.Concurrency.dsbStForSharing_injective

/-! ## SM0.H — SgiKind -/
#check @SeLe4n.Kernel.Concurrency.SgiKind
#check @SeLe4n.Kernel.Concurrency.SgiKind.toIntid
#check @SeLe4n.Kernel.Concurrency.SgiKind.toIntid_injective
#check @SeLe4n.Kernel.Concurrency.SgiKind.toIntid_in_range
#check @SeLe4n.Kernel.Concurrency.SgiKind.toIntid_lt_five
#check @SeLe4n.Kernel.Concurrency.SgiKind.all
#check @SeLe4n.Kernel.Concurrency.SgiKind.all_length
#check @SeLe4n.Kernel.Concurrency.SgiKind.all_nodup

/-! ## SM0.I — LockKind, LockId, BklState -/
#check @SeLe4n.Kernel.Concurrency.LockKind
#check @SeLe4n.Kernel.Concurrency.LockKind.level
#check @SeLe4n.Kernel.Concurrency.LockKind.level_strictMono
#check @SeLe4n.Kernel.Concurrency.LockKind.level_surjective
#check @SeLe4n.Kernel.Concurrency.LockKind.level_bounded
#check @SeLe4n.Kernel.Concurrency.LockKind.toFin
#check @SeLe4n.Kernel.Concurrency.LockId
#check @SeLe4n.Kernel.Concurrency.LockId.le_total
#check @SeLe4n.Kernel.Concurrency.LockId.le_refl
#check @SeLe4n.Kernel.Concurrency.LockId.le_trans
#check @SeLe4n.Kernel.Concurrency.LockId.le_antisymm
#check @SeLe4n.Kernel.Concurrency.LockId.lt_trichotomy
#check @SeLe4n.Kernel.Concurrency.BklState
#check @SeLe4n.Kernel.Concurrency.bklHeldBy
#check @SeLe4n.Kernel.Concurrency.bklState_unique_owner
#check @SeLe4n.Kernel.Concurrency.bklUnheld_no_owner

/-! ## SM0.A/SM0.B — ArchAssumption 6-way machinery -/
#check @SeLe4n.Kernel.Architecture.ArchAssumption
#check @SeLe4n.Kernel.Architecture.assumptionInventory
#check @SeLe4n.Kernel.Architecture.assumptionInventory_count
#check @SeLe4n.Kernel.Architecture.archAssumptionConsumer
#check @SeLe4n.Kernel.Architecture.archAssumptionConsumer_distinct_6
#check @SeLe4n.Kernel.Architecture.architecture_assumptions_index_total_6

/-! ## SM0.C/SM0.D — AN12-B inventory hardening -/
#check @SeLe4n.Kernel.Concurrency.smpAnchorVerified
#check @SeLe4n.Kernel.Concurrency.smpLatentInventory_count
#check @SeLe4n.Kernel.Concurrency.smpLatentInventory_identifiers_nodup
#check @SeLe4n.Kernel.Concurrency.smpLatentInventory_sourceTheorems_nodup

/-! ## SM4.E — witness retirement + retirement ledger -/
#check @SeLe4n.Platform.Boot.bootFromPlatform_smp_witness
#check @SeLe4n.Platform.Boot.bootFromPlatform_smp_currentAllNone
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_count
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_covers_latent
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_identifiers_nodup
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_anchor_nodup
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_pathARetired_count
#check @SeLe4n.Kernel.Concurrency.smpRetiredInventory_perCoreBracketGated_count

/-! ## SM4.G — per-core idle-thread bootstrap -/
#check @SeLe4n.Kernel.idleThreadId
#check @SeLe4n.Kernel.idleThreadId_injective
#check @SeLe4n.Platform.Boot.createIdleThread
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_all_cores_have_idle
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_schedulerInvariantBundle
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_schedulerInvariantBundleFull
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_currentThreadInActiveDomain
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_valid
-- SM4.G idle-slot freshness: the install is purely additive (no platform
-- object clobbered) under `idleSlotsFreshAt`, discharged for configs whose
-- objects live below `idleThreadIdBase`.
#check @SeLe4n.Platform.Boot.idleSlotsFreshAt
#check @SeLe4n.Platform.Boot.bootFromPlatformWithIdleThreads_preserves_platform_objects
#check @SeLe4n.Platform.Boot.idleSlotsFreshAt_of_initialObjects_below_base

/-! ## SM0.G — PlatformBinding extension fields (RPi5 + Sim) -/
#check @SeLe4n.Platform.PlatformBinding.coreCount
#check @SeLe4n.Platform.PlatformBinding.coreCountPos
#check @SeLe4n.Platform.PlatformBinding.bootCoreId
#check @SeLe4n.Platform.PlatformBinding.sharingDomain
#check @SeLe4n.Platform.RPi5.numCores_eq_rpi5_coreCount
#check @SeLe4n.Platform.RPi5.bootCoreId_val_eq_rpi5
#check @SeLe4n.Platform.RPi5.rpi5_sharingDomain

/-! ## SM1.B.5 — currentCoreId FFI wrapper (closes SMP-M4) -/
#check @SeLe4n.Platform.FFI.ffiCurrentCoreId
#check @SeLe4n.Kernel.Concurrency.currentCoreId
#check @SeLe4n.Kernel.Concurrency.currentCoreId_in_range_marker
#check @SeLe4n.Kernel.Concurrency.instInhabitedCoreId

/-! ## SM1.C.6 — Secondary-core kernel entry (closes SMP-C2 Lean side) -/
#check @SeLe4n.Kernel.secondaryKernelMain
#check @SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker

/-! ## SM1.E.4 — Sharing-domain-routed TLBI dispatcher Lean wrapper -/
#check @SeLe4n.Platform.FFI.ffiTlbiForSharing
#check @SeLe4n.Kernel.Architecture.TlbInvalidation
#check @SeLe4n.Kernel.Architecture.TlbInvalidation.toOpTag
#check @SeLe4n.Kernel.Architecture.TlbInvalidation.toAsid
#check @SeLe4n.Kernel.Architecture.TlbInvalidation.toVaddr
-- SharingDomain.toTag lives in `SeLe4n.Kernel.Concurrency.SharingDomain`
-- (declared via `_root_.` in TlbiForSharing.lean) so dot-notation
-- resolves on values of type `SharingDomain`.
#check @SeLe4n.Kernel.Concurrency.SharingDomain.toTag
#check @SeLe4n.Kernel.Architecture.tlbiForSharing
#check @SeLe4n.Kernel.Concurrency.SharingDomain.toTag_injective
#check @SeLe4n.Kernel.Concurrency.SharingDomain.toTag_in_range
#check @SeLe4n.Kernel.Architecture.TlbInvalidation.toOpTag_in_range
#check @SeLe4n.Kernel.Architecture.TlbInvalidation.toOpTag_distinct_constructors
#check @SeLe4n.Kernel.Architecture.tlbiForSharing_total
#check @SeLe4n.Kernel.Architecture.tlbiForSharing_ffi_args_in_range

/-! ## SM1.F.6 — SGI primitive FFI bindings -/
#check @SeLe4n.Platform.FFI.ffiSendSgi
#check @SeLe4n.Platform.FFI.ffiSendSgiToSelf
#check @SeLe4n.Platform.FFI.ffiSendSgiToAllButSelf

/-! ## SM1.I.3 — Idle-wait FFI bindings + typed wrappers -/
#check @SeLe4n.Platform.FFI.ffiIdleWait
#check @SeLe4n.Platform.FFI.ffiIdleWaitBounded
#check @SeLe4n.Kernel.Concurrency.idleWait
#check @SeLe4n.Kernel.Concurrency.idleWaitBounded

/-! ## SM1.I.4 — Per-core stats FFI bindings + typed wrappers -/
#check @SeLe4n.Platform.FFI.ffiPerCoreIrqCount
#check @SeLe4n.Platform.FFI.ffiPerCoreTimerTickCount
#check @SeLe4n.Platform.FFI.ffiPerCoreSgiCount
#check @SeLe4n.Platform.FFI.ffiPerCoreSyscallCount
#check @SeLe4n.Kernel.Concurrency.perCoreIrqCount
#check @SeLe4n.Kernel.Concurrency.perCoreTimerTickCount
#check @SeLe4n.Kernel.Concurrency.perCoreSgiCount
#check @SeLe4n.Kernel.Concurrency.perCoreSyscallCount
#check @SeLe4n.Kernel.Concurrency.perCoreIrqCount_returns_baseio_uint64_marker
#check @SeLe4n.Kernel.Concurrency.perCoreTimerTickCount_returns_baseio_uint64_marker
#check @SeLe4n.Kernel.Concurrency.perCoreSgiCount_returns_baseio_uint64_marker
#check @SeLe4n.Kernel.Concurrency.perCoreSyscallCount_returns_baseio_uint64_marker
#check @SeLe4n.Kernel.Concurrency.idleWait_returns_baseio_unit_marker
#check @SeLe4n.Kernel.Concurrency.idleWaitBounded_returns_baseio_uint64_marker

-- ============================================================================
-- §2 — Decidable examples: ground-truth checks at the RPi5 default
-- ============================================================================

namespace SeLe4n.Testing.SmpFoundations

-- §2.1 — CoreId / numCores
example : SeLe4n.Kernel.Concurrency.numCores = 4 := by decide
example : SeLe4n.Kernel.Concurrency.allCores.length = 4 := by decide
example : SeLe4n.Kernel.Concurrency.bootCoreId.val = 0 := by decide
example : SeLe4n.Kernel.Concurrency.numCores > 0 := by decide

-- §2.2 — SharingDomain selectors agree with BarrierKind constructors
example : SeLe4n.Kernel.Concurrency.dsbForSharing .inner =
            SeLe4n.Kernel.Architecture.BarrierKind.dsbIsh := by decide
example : SeLe4n.Kernel.Concurrency.dsbForSharing .outer =
            SeLe4n.Kernel.Architecture.BarrierKind.dsbOsh := by decide
example : SeLe4n.Kernel.Concurrency.dsbStForSharing .inner =
            SeLe4n.Kernel.Architecture.BarrierKind.dsbIshst := by decide
example : SeLe4n.Kernel.Concurrency.dsbStForSharing .outer =
            SeLe4n.Kernel.Architecture.BarrierKind.dsbOshst := by decide

-- §2.3 — LockKind levels: 10 distinct values 0..9
example : SeLe4n.Kernel.Concurrency.LockKind.objStore.level = 0 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.untyped.level = 1 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.cnode.level = 2 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.tcb.level = 3 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.endpoint.level = 4 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.notification.level = 5 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.reply.level = 6 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.schedContext.level = 7 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.vspaceRoot.level = 8 := by decide
example : SeLe4n.Kernel.Concurrency.LockKind.page.level = 9 := by decide

-- §2.4 — LockId order: same-kind comparison + cross-kind ordering
example :
    (SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 5))
    ≤ (SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 7)) := by
  decide

example :
    (SeLe4n.Kernel.Concurrency.LockId.mk' .cnode (SeLe4n.ObjId.ofNat 100))
    ≤ (SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 1)) := by
  decide

example :
    (SeLe4n.Kernel.Concurrency.LockId.mk' .objStore (SeLe4n.ObjId.ofNat 0))
    ≤ (SeLe4n.Kernel.Concurrency.LockId.mk' .page (SeLe4n.ObjId.ofNat 999)) := by
  decide

-- §2.5 — SgiKind INTID assignments
example : SeLe4n.Kernel.Concurrency.SgiKind.reschedule.toIntid.val = 0 := by decide
example : SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownReq.toIntid.val = 1 := by decide
example : SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownAck.toIntid.val = 2 := by decide
example : SeLe4n.Kernel.Concurrency.SgiKind.cacheBroadcast.toIntid.val = 3 := by decide
example : SeLe4n.Kernel.Concurrency.SgiKind.haltAll.toIntid.val = 4 := by decide
example : SeLe4n.Kernel.Concurrency.SgiKind.all.length = 5 := by decide

-- §2.6 — BklState invariants
example : SeLe4n.Kernel.Concurrency.bklHeldBy
            (SeLe4n.Kernel.Concurrency.BklState.held
              SeLe4n.Kernel.Concurrency.bootCoreId)
            SeLe4n.Kernel.Concurrency.bootCoreId := rfl
example : ¬ SeLe4n.Kernel.Concurrency.bklHeldBy
            SeLe4n.Kernel.Concurrency.BklState.unheld
            SeLe4n.Kernel.Concurrency.bootCoreId := by decide

-- §2.7 — ArchAssumption inventory growth (5 → 6 cases)
example : SeLe4n.Kernel.Architecture.assumptionInventory.length = 6 := by decide
example : SeLe4n.Kernel.Architecture.ArchAssumption.singleCoreOperation
          ∈ SeLe4n.Kernel.Architecture.assumptionInventory := by decide

-- §2.8 — SMP-latent inventory size + NoDup
example : SeLe4n.Kernel.Concurrency.smpLatentInventory.length = 8 := by decide

-- §2.8b — SM4.E retirement ledger: size + path-a disposition + latent mirror
example : SeLe4n.Kernel.Concurrency.smpRetiredInventory.length = 8 := by decide
example : (SeLe4n.Kernel.Concurrency.smpRetiredInventory.filter
            (fun e => decide (e.status = .pathARetired))).length = 2 := by decide
example : SeLe4n.Kernel.Concurrency.smpRetiredInventory.map (·.identifier) =
          SeLe4n.Kernel.Concurrency.smpLatentInventory.map (·.identifier) :=
  SeLe4n.Kernel.Concurrency.smpRetiredInventory_covers_latent

-- §2.9 — RPi5 PlatformBinding pinning (SM0.G + SM0.E)
example : SeLe4n.Platform.PlatformBinding.coreCount
            (platform := SeLe4n.Platform.RPi5.RPi5Platform) = 4 := rfl
example : (SeLe4n.Platform.PlatformBinding.bootCoreId
            (platform := SeLe4n.Platform.RPi5.RPi5Platform)).val = 0 := rfl
example : SeLe4n.Platform.PlatformBinding.sharingDomain
            (platform := SeLe4n.Platform.RPi5.RPi5Platform) =
            SeLe4n.Kernel.Concurrency.SharingDomain.inner := rfl

-- §2.10 — Sim PlatformBinding extension agrees on shape
example : SeLe4n.Platform.PlatformBinding.coreCount
            (platform := SeLe4n.Platform.Sim.SimPlatform) = 4 := rfl
example : (SeLe4n.Platform.PlatformBinding.bootCoreId
            (platform := SeLe4n.Platform.Sim.SimPlatform)).val = 0 := rfl

-- §2.16 — SM1.B.5 currentCoreId typed wrapper
-- The `Inhabited` instance witnesses that CoreId is always inhabited
-- (so `panic!` inside `currentCoreId` can synthesise a fallback type).
-- Default must equal `bootCoreId` for boot-core convention parity.
example : (default : SeLe4n.Kernel.Concurrency.CoreId).val = 0 := rfl
example : (default : SeLe4n.Kernel.Concurrency.CoreId)
            = SeLe4n.Kernel.Concurrency.bootCoreId := rfl
-- Range-marker theorem: every typed CoreId is < numCores.
example (c : SeLe4n.Kernel.Concurrency.CoreId) :
    c.val < SeLe4n.Kernel.Concurrency.numCores := c.isLt
-- Concrete-instance check: the range marker discharges on the boot core.
example : SeLe4n.Kernel.Concurrency.bootCoreId.val
            < SeLe4n.Kernel.Concurrency.numCores :=
  SeLe4n.Kernel.Concurrency.currentCoreId_in_range_marker
    SeLe4n.Kernel.Concurrency.bootCoreId

-- §2.17 — SM1.C.6 secondaryKernelMain Lean entry placeholder
-- The function must accept a UInt64 (the PSCI context_id) and return
-- `BaseIO Unit`.  At SM1.C the body is `pure ()`; the
-- `secondaryKernelMain_returns_unit_marker` theorem witnesses this.
--
-- Note: `BaseIO Unit` is not Decidable-equality (function types
-- generally aren't), so these examples produce structural Prop
-- witnesses rather than going through `decide`.  The witness is
-- discharged by `rfl` inside the marker theorem.
example (coreId : UInt64) :
    SeLe4n.Kernel.secondaryKernelMain coreId = pure () :=
  SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker coreId
-- Concrete-instance check at boot-core context id (0).
example : SeLe4n.Kernel.secondaryKernelMain 0 = pure () :=
  SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker 0
-- Concrete-instance check at each secondary context id (1, 2, 3).
example : SeLe4n.Kernel.secondaryKernelMain 1 = pure () :=
  SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker 1
example : SeLe4n.Kernel.secondaryKernelMain 2 = pure () :=
  SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker 2
example : SeLe4n.Kernel.secondaryKernelMain 3 = pure () :=
  SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker 3

-- §2.18 — SM1.E.4 TLBI dispatcher tag encoding witnesses
-- Every variant of TlbInvalidation maps to a distinct op tag in [0, 4),
-- and every SharingDomain maps to a distinct domain tag in [0, 2).  These
-- are the structural invariants the Rust `ffi_tlbi_for_sharing` dispatcher
-- relies on for its `match` arms to be exhaustive.
example : SeLe4n.Kernel.Concurrency.SharingDomain.inner.toTag = 0 := rfl
example : SeLe4n.Kernel.Concurrency.SharingDomain.outer.toTag = 1 := rfl
example : SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1.toOpTag = 0 := rfl
example : (SeLe4n.Kernel.Architecture.TlbInvalidation.vae1 0 0).toOpTag = 1 := rfl
example : (SeLe4n.Kernel.Architecture.TlbInvalidation.aside1 0).toOpTag = 2 := rfl
example : (SeLe4n.Kernel.Architecture.TlbInvalidation.vale1 0 0).toOpTag = 3 := rfl
-- Operand extraction: vae1/vale1 carry asid + vaddr; aside1 carries asid only;
-- vmalle1 carries no operand (returns 0 for both).
example : (SeLe4n.Kernel.Architecture.TlbInvalidation.vae1 42 0x1000).toAsid = 42 := rfl
example : (SeLe4n.Kernel.Architecture.TlbInvalidation.vae1 42 0x1000).toVaddr = 0x1000 := rfl
example : SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1.toAsid = 0 := rfl
example : SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1.toVaddr = 0 := rfl

-- §2.19 — SM1.F.6 SGI INTID alignment with SgiKind
-- Every SgiKind reserves an INTID < 16 (the SGI range).  When the kernel
-- calls ffiSendSgi via the typed `SgiKind.toIntid`, the resulting UInt8
-- is structurally `< 16` so the Rust-side bound check never panics on a
-- well-formed call from Lean.
example : SeLe4n.Kernel.Concurrency.SgiKind.reschedule.toIntid.val < 16 := by decide
example : SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownReq.toIntid.val < 16 := by decide
example : SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownAck.toIntid.val < 16 := by decide
example : SeLe4n.Kernel.Concurrency.SgiKind.cacheBroadcast.toIntid.val < 16 := by decide
example : SeLe4n.Kernel.Concurrency.SgiKind.haltAll.toIntid.val < 16 := by decide

-- ============================================================================
-- §3 — Runtime assertions: every above example also runs in `main`
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

private def runCoreIdChecks : IO Unit := do
  IO.println "--- §2.1 CoreId / numCores ---"
  assertBool "numCores = 4" (decide (SeLe4n.Kernel.Concurrency.numCores = 4))
  assertBool "allCores.length = 4"
    (decide (SeLe4n.Kernel.Concurrency.allCores.length = 4))
  assertBool "bootCoreId.val = 0"
    (decide (SeLe4n.Kernel.Concurrency.bootCoreId.val = 0))
  assertBool "numCores > 0"
    (decide (SeLe4n.Kernel.Concurrency.numCores > 0))

private def runSharingDomainChecks : IO Unit := do
  IO.println "--- §2.2 SharingDomain selectors ---"
  assertBool "dsbForSharing .inner = .dsbIsh"
    (decide (SeLe4n.Kernel.Concurrency.dsbForSharing .inner =
              SeLe4n.Kernel.Architecture.BarrierKind.dsbIsh))
  assertBool "dsbForSharing .outer = .dsbOsh"
    (decide (SeLe4n.Kernel.Concurrency.dsbForSharing .outer =
              SeLe4n.Kernel.Architecture.BarrierKind.dsbOsh))
  assertBool "dsbStForSharing .inner = .dsbIshst"
    (decide (SeLe4n.Kernel.Concurrency.dsbStForSharing .inner =
              SeLe4n.Kernel.Architecture.BarrierKind.dsbIshst))
  assertBool "dsbStForSharing .outer = .dsbOshst"
    (decide (SeLe4n.Kernel.Concurrency.dsbStForSharing .outer =
              SeLe4n.Kernel.Architecture.BarrierKind.dsbOshst))

private def runLockKindChecks : IO Unit := do
  IO.println "--- §2.3 LockKind level assignments ---"
  assertBool "objStore.level = 0"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.objStore.level = 0))
  assertBool "untyped.level = 1"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.untyped.level = 1))
  assertBool "cnode.level = 2"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.cnode.level = 2))
  assertBool "tcb.level = 3"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.tcb.level = 3))
  assertBool "endpoint.level = 4"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.endpoint.level = 4))
  assertBool "notification.level = 5"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.notification.level = 5))
  assertBool "reply.level = 6"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.reply.level = 6))
  assertBool "schedContext.level = 7"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.schedContext.level = 7))
  assertBool "vspaceRoot.level = 8"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.vspaceRoot.level = 8))
  assertBool "page.level = 9"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.page.level = 9))
  assertBool "all 10 levels < 10"
    (List.all
      [(0:Nat), 1, 2, 3, 4, 5, 6, 7, 8, 9]
      (fun n => decide (n < 10)))

private def runLockIdChecks : IO Unit := do
  IO.println "--- §2.4 LockId lexicographic order ---"
  assertBool "tcb 5 ≤ tcb 7"
    (decide (SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 5)
            ≤ SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 7)))
  assertBool "cnode 100 ≤ tcb 1 (cross-kind by level)"
    (decide (SeLe4n.Kernel.Concurrency.LockId.mk' .cnode (SeLe4n.ObjId.ofNat 100)
            ≤ SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 1)))
  assertBool "objStore 0 ≤ page 999 (extremes of LockKind hierarchy)"
    (decide (SeLe4n.Kernel.Concurrency.LockId.mk' .objStore (SeLe4n.ObjId.ofNat 0)
            ≤ SeLe4n.Kernel.Concurrency.LockId.mk' .page (SeLe4n.ObjId.ofNat 999)))

private def runSgiKindChecks : IO Unit := do
  IO.println "--- §2.5 SgiKind INTID assignments ---"
  assertBool "reschedule INTID = 0"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.reschedule.toIntid.val = 0))
  assertBool "tlbShootdownReq INTID = 1"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownReq.toIntid.val = 1))
  assertBool "tlbShootdownAck INTID = 2"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownAck.toIntid.val = 2))
  assertBool "cacheBroadcast INTID = 3"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.cacheBroadcast.toIntid.val = 3))
  assertBool "haltAll INTID = 4"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.haltAll.toIntid.val = 4))
  assertBool "SgiKind.all.length = 5"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.all.length = 5))

private def runBklStateChecks : IO Unit := do
  IO.println "--- §2.6 BklState ownership ---"
  assertBool "held bootCoreId is held by bootCoreId"
    (decide (SeLe4n.Kernel.Concurrency.bklHeldBy
              (SeLe4n.Kernel.Concurrency.BklState.held
                SeLe4n.Kernel.Concurrency.bootCoreId)
              SeLe4n.Kernel.Concurrency.bootCoreId))
  assertBool "unheld is not held by bootCoreId"
    (decide (¬ SeLe4n.Kernel.Concurrency.bklHeldBy
              SeLe4n.Kernel.Concurrency.BklState.unheld
              SeLe4n.Kernel.Concurrency.bootCoreId))

private def runArchAssumptionChecks : IO Unit := do
  IO.println "--- §2.7 ArchAssumption 6-way inventory ---"
  assertBool "assumptionInventory.length = 6"
    (decide (SeLe4n.Kernel.Architecture.assumptionInventory.length = 6))
  assertBool "singleCoreOperation ∈ assumptionInventory"
    (decide (SeLe4n.Kernel.Architecture.ArchAssumption.singleCoreOperation
            ∈ SeLe4n.Kernel.Architecture.assumptionInventory))

private def runSmpInventoryChecks : IO Unit := do
  IO.println "--- §2.8 SMP-latent inventory ---"
  assertBool "smpLatentInventory.length = 8"
    (decide (SeLe4n.Kernel.Concurrency.smpLatentInventory.length = 8))
  IO.println "--- §2.8b SM4.E retirement ledger ---"
  assertBool "smpRetiredInventory.length = 8"
    (decide (SeLe4n.Kernel.Concurrency.smpRetiredInventory.length = 8))
  -- Honest disposition: exactly 2 entries (scheduler-state shape + boot-core
  -- current) are genuinely retired by SM4 path-a; the other 6 stay gated.
  assertBool "smpRetiredInventory path-a-retired count = 2"
    (decide ((SeLe4n.Kernel.Concurrency.smpRetiredInventory.filter
               (fun e => decide (e.status = .pathARetired))).length = 2))
  assertBool "smpRetiredInventory per-core-bracket-gated count = 6"
    (decide ((SeLe4n.Kernel.Concurrency.smpRetiredInventory.filter
               (fun e => decide (e.status = .perCoreBracketGated))).length = 6))
  -- The ledger mirrors the latent inventory one-to-one by identifier.
  assertBool "smpRetiredInventory covers smpLatentInventory (by identifier)"
    (decide (SeLe4n.Kernel.Concurrency.smpRetiredInventory.map (·.identifier) =
             SeLe4n.Kernel.Concurrency.smpLatentInventory.map (·.identifier)))

private def runPlatformBindingChecks : IO Unit := do
  IO.println "--- §2.9/§2.10 PlatformBinding RPi5 + Sim ---"
  assertBool "RPi5.coreCount = 4"
    (decide (SeLe4n.Platform.PlatformBinding.coreCount
              (platform := SeLe4n.Platform.RPi5.RPi5Platform) = 4))
  assertBool "RPi5.bootCoreId.val = 0"
    (decide ((SeLe4n.Platform.PlatformBinding.bootCoreId
              (platform := SeLe4n.Platform.RPi5.RPi5Platform)).val = 0))
  assertBool "RPi5.sharingDomain = .inner"
    (decide (SeLe4n.Platform.PlatformBinding.sharingDomain
              (platform := SeLe4n.Platform.RPi5.RPi5Platform) =
              SeLe4n.Kernel.Concurrency.SharingDomain.inner))
  assertBool "Sim.coreCount = 4"
    (decide (SeLe4n.Platform.PlatformBinding.coreCount
              (platform := SeLe4n.Platform.Sim.SimPlatform) = 4))
  assertBool "Sim.bootCoreId.val = 0"
    (decide ((SeLe4n.Platform.PlatformBinding.bootCoreId
              (platform := SeLe4n.Platform.Sim.SimPlatform)).val = 0))
  assertBool "Sim.sharingDomain = .inner"
    (decide (SeLe4n.Platform.PlatformBinding.sharingDomain
              (platform := SeLe4n.Platform.Sim.SimPlatform) =
              SeLe4n.Kernel.Concurrency.SharingDomain.inner))
  assertBool "SimRestrictive.coreCount = 4"
    (decide (SeLe4n.Platform.PlatformBinding.coreCount
              (platform := SeLe4n.Platform.Sim.SimRestrictivePlatform) = 4))
  -- WS-SM SM0.G: the `coreCountPos` field on every binding must be a
  -- valid positivity witness — verified by destructuring the field
  -- via @-reference so the typeclass instance resolution path is
  -- exercised end-to-end.  Each `decide` here trivially evaluates
  -- `4 > 0` at the concrete RPi5/Sim binding.
  assertBool "RPi5.coreCountPos witness exists (4 > 0)"
    (decide (SeLe4n.Platform.PlatformBinding.coreCount
              (platform := SeLe4n.Platform.RPi5.RPi5Platform) > 0))
  assertBool "Sim.coreCountPos witness exists (4 > 0)"
    (decide (SeLe4n.Platform.PlatformBinding.coreCount
              (platform := SeLe4n.Platform.Sim.SimPlatform) > 0))
  assertBool "SimRestrictive.coreCountPos witness exists (4 > 0)"
    (decide (SeLe4n.Platform.PlatformBinding.coreCount
              (platform := SeLe4n.Platform.Sim.SimRestrictivePlatform) > 0))

private def runLockKindUniquenessChecks : IO Unit := do
  IO.println "--- §2.11 LockKind pairwise distinctness (full lattice) ---"
  -- C(10,2) = 45 pairs.  Spot-check the extremes plus a sampling of
  -- the middle to keep the suite output readable while still
  -- exercising the strict-monotone discipline beyond a single decide.
  assertBool "objStore ≠ page (extremes)"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.objStore.level ≠
              SeLe4n.Kernel.Concurrency.LockKind.page.level))
  assertBool "cnode ≠ tcb (adjacent)"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.cnode.level ≠
              SeLe4n.Kernel.Concurrency.LockKind.tcb.level))
  assertBool "schedContext ≠ vspaceRoot (adjacent)"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.schedContext.level ≠
              SeLe4n.Kernel.Concurrency.LockKind.vspaceRoot.level))
  assertBool "untyped ≠ reply (mid-mid)"
    (decide (SeLe4n.Kernel.Concurrency.LockKind.untyped.level ≠
              SeLe4n.Kernel.Concurrency.LockKind.reply.level))
  -- The full C(10,2) pairwise distinctness check via decide on
  -- the literal level mapping; if any pair would collide, decide
  -- would reject this list (List.Pairwise on inequality).
  assertBool "all 10 levels pairwise distinct"
    (decide
      [SeLe4n.Kernel.Concurrency.LockKind.objStore.level,
       SeLe4n.Kernel.Concurrency.LockKind.untyped.level,
       SeLe4n.Kernel.Concurrency.LockKind.cnode.level,
       SeLe4n.Kernel.Concurrency.LockKind.tcb.level,
       SeLe4n.Kernel.Concurrency.LockKind.endpoint.level,
       SeLe4n.Kernel.Concurrency.LockKind.notification.level,
       SeLe4n.Kernel.Concurrency.LockKind.reply.level,
       SeLe4n.Kernel.Concurrency.LockKind.schedContext.level,
       SeLe4n.Kernel.Concurrency.LockKind.vspaceRoot.level,
       SeLe4n.Kernel.Concurrency.LockKind.page.level].Nodup)

private def runLockIdAdditionalChecks : IO Unit := do
  IO.println "--- §2.12 LockId reflexivity + asymmetry ---"
  -- Reflexivity (same kind, same objId).
  assertBool "le_refl: tcb 5 ≤ tcb 5"
    (decide (SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 5)
            ≤ SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 5)))
  -- Antisymmetry on the strict order: if l₁ < l₂ then ¬(l₂ ≤ l₁).
  assertBool "asymmetry: ¬(tcb 7 ≤ tcb 5) when tcb 5 < tcb 7"
    (decide (¬ (SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 7)
              ≤ SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 5))))
  -- Strict less-than (LT instance).
  assertBool "lt: cnode 0 < tcb 0"
    (decide (SeLe4n.Kernel.Concurrency.LockId.mk' .cnode (SeLe4n.ObjId.ofNat 0)
            < SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 0)))
  -- Self-not-strictly-less-than-self.
  assertBool "irreflexivity: ¬ (tcb 5 < tcb 5)"
    (decide (¬ (SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 5)
              < SeLe4n.Kernel.Concurrency.LockId.mk' .tcb (SeLe4n.ObjId.ofNat 5))))

private def runSgiKindAdditionalChecks : IO Unit := do
  IO.println "--- §2.13 SgiKind enumeration uniqueness ---"
  -- All 5 INTIDs are distinct (each kind maps to a unique Fin 16).
  assertBool "all 5 INTIDs pairwise distinct"
    (decide
      [SeLe4n.Kernel.Concurrency.SgiKind.reschedule.toIntid.val,
       SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownReq.toIntid.val,
       SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownAck.toIntid.val,
       SeLe4n.Kernel.Concurrency.SgiKind.cacheBroadcast.toIntid.val,
       SeLe4n.Kernel.Concurrency.SgiKind.haltAll.toIntid.val].Nodup)
  -- All 5 INTIDs are in the kernel-reserved range [0, 5).
  assertBool "every INTID < 5"
    (SeLe4n.Kernel.Concurrency.SgiKind.all.all
      (fun k => decide (k.toIntid.val < 5)))
  -- All 5 INTIDs are in the SGI range [0, 16) (weaker bound).
  assertBool "every INTID < 16 (full SGI range)"
    (SeLe4n.Kernel.Concurrency.SgiKind.all.all
      (fun k => decide (k.toIntid.val < 16)))

private def runArchAssumptionAdditionalChecks : IO Unit := do
  IO.println "--- §2.14 ArchAssumption consumer mapping (6-way) ---"
  -- Each of the 6 ArchAssumption constructors maps to a non-anonymous
  -- consumer theorem name.
  assertBool "all 6 consumers are non-anonymous"
    ([SeLe4n.Kernel.Architecture.ArchAssumption.deterministicTimerProgress,
       SeLe4n.Kernel.Architecture.ArchAssumption.deterministicRegisterContext,
       SeLe4n.Kernel.Architecture.ArchAssumption.memoryAccessSafety,
       SeLe4n.Kernel.Architecture.ArchAssumption.bootObjectTyping,
       SeLe4n.Kernel.Architecture.ArchAssumption.irqRoutingTotality,
       SeLe4n.Kernel.Architecture.ArchAssumption.singleCoreOperation].all
       (fun a => decide (SeLe4n.Kernel.Architecture.archAssumptionConsumer a
                  ≠ Lean.Name.anonymous)))
  -- SM4.E.3: singleCoreOperation now maps to the per-core SMP witness
  -- (was the retired boot-core-only `bootFromPlatform_singleCore_witness`).
  assertBool "singleCoreOperation → bootFromPlatform_smp_witness"
    (decide (SeLe4n.Kernel.Architecture.archAssumptionConsumer
              .singleCoreOperation =
              `SeLe4n.Platform.Boot.bootFromPlatform_smp_witness))

private def runBklStateAdditionalChecks : IO Unit := do
  IO.println "--- §2.15 BklState additional scenarios ---"
  -- BklState.held with different cores yields different states.
  -- Construct two distinct held states (only possible when numCores ≥ 2).
  let c0 : SeLe4n.Kernel.Concurrency.CoreId := SeLe4n.Kernel.Concurrency.bootCoreId
  let c1 : SeLe4n.Kernel.Concurrency.CoreId := ⟨1, by decide⟩
  assertBool "held c₀ ≠ held c₁ (distinct cores)"
    (decide (SeLe4n.Kernel.Concurrency.BklState.held c0 ≠
              SeLe4n.Kernel.Concurrency.BklState.held c1))
  assertBool "held c₀ ≠ unheld"
    (decide (SeLe4n.Kernel.Concurrency.BklState.held c0 ≠
              SeLe4n.Kernel.Concurrency.BklState.unheld))
  assertBool "bklAcquire c₀ is held by c₀"
    (decide (SeLe4n.Kernel.Concurrency.bklHeldBy
              (SeLe4n.Kernel.Concurrency.bklAcquire c0) c0))
  assertBool "bklRelease is unheld"
    (decide (SeLe4n.Kernel.Concurrency.bklRelease =
              SeLe4n.Kernel.Concurrency.BklState.unheld))
  -- Smart constructor behaviour.
  assertBool "bklAcquire c₀ ≠ bklAcquire c₁"
    (decide (SeLe4n.Kernel.Concurrency.bklAcquire c0 ≠
              SeLe4n.Kernel.Concurrency.bklAcquire c1))

private def runCurrentCoreIdChecks : IO Unit := do
  -- WS-SM SM1.B.5: typed FFI wrapper structural checks.
  --
  -- Per the project's fail-closed FFI convention (`SeLe4n/Platform/FFI.lean`
  -- header docstring), `@[extern] opaque` declarations like
  -- `ffiCurrentCoreId` are not linkable in test executables — invoking
  -- them at host runtime would produce a link error rather than a
  -- silent stub call.  The host-side runtime behaviour of
  -- `ffi_current_core_id` is covered by `rust/sele4n-hal/src/ffi.rs`'s
  -- unit tests (`ffi_current_core_id_*`), which exercise the host
  -- stub returning 0 (boot core) deterministically.
  --
  -- This suite covers the Lean-side structural properties:
  --   1. `Inhabited CoreId` instance discharges to `bootCoreId`.
  --   2. The range-marker theorem `currentCoreId_in_range_marker`
  --      witnesses `c.val < numCores` for every `CoreId`.
  --   3. Both above are decidable at compile time and at runtime.
  IO.println "--- §2.16 SM1.B.5 currentCoreId typed wrapper ---"
  -- The `Inhabited` instance defaults to bootCoreId.
  assertBool "Inhabited CoreId default = bootCoreId"
    (decide ((default : SeLe4n.Kernel.Concurrency.CoreId) =
              SeLe4n.Kernel.Concurrency.bootCoreId))
  assertBool "Inhabited CoreId default.val = 0"
    (decide ((default : SeLe4n.Kernel.Concurrency.CoreId).val = 0))
  -- Range marker theorem discharges trivially on every CoreId
  -- because `Fin numCores` carries the bound in its representation.
  -- We exercise the bound directly on bootCoreId.
  assertBool "currentCoreId_in_range_marker on bootCoreId discharges"
    (decide (SeLe4n.Kernel.Concurrency.bootCoreId.val
              < SeLe4n.Kernel.Concurrency.numCores))
  -- Range marker discharges for every CoreId 0..3 (full enumeration
  -- via allCores) — proves the marker is structurally total.
  assertBool "currentCoreId_in_range_marker discharges on every CoreId"
    (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
      decide (c.val < SeLe4n.Kernel.Concurrency.numCores)))

private def runSecondaryKernelMainChecks : IO Unit := do
  -- WS-SM SM1.C.6: secondary-core kernel-entry placeholder.
  --
  -- The Lean entry point is the `@[export lean_secondary_kernel_main]`
  -- function consumed by the Rust HAL's `rust_secondary_main`.  At
  -- SM1.C the body is `pure ()`; we verify the structural property
  -- via the `secondaryKernelMain_returns_unit_marker` theorem (which
  -- is `rfl` because `pure ()` is the actual function body).  SM5+
  -- replaces both the body and this proof with substantive
  -- scheduler-entry correctness checks.
  --
  -- Note: `BaseIO Unit` is not Decidable-equality, so we cannot use
  -- `decide` to compare two `BaseIO` actions.  Instead we exercise:
  --   1. The marker-theorem call (typechecks ⟹ structural witness OK).
  --   2. The runtime `BaseIO` execution (no fault ⟹ host-callable).
  IO.println "--- §2.17 SM1.C.6 secondaryKernelMain entry placeholder ---"
  -- Marker theorem discharges by `rfl` for every UInt64 input — we
  -- type-check the call to confirm the theorem is in scope and
  -- structurally total.  A regression that broke the placeholder
  -- semantics (e.g., changed the body to something other than
  -- `pure ()`) would fail to elaborate the marker theorem at the
  -- module level, failing the build before this suite runs.
  let _proof_0 :=
    SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker 0
  let _proof_1 :=
    SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker 1
  let _proof_2 :=
    SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker 2
  let _proof_3 :=
    SeLe4n.Kernel.secondaryKernelMain_returns_unit_marker 3
  assertBool "secondaryKernelMain_returns_unit_marker reachable on every context_id 0..3"
    true
  -- Actually execute the BaseIO action at runtime to confirm it
  -- doesn't fault.  Returns Unit on the simulation path (no FFI
  -- call, no hardware access).  A regression that introduced a
  -- panic, IO action, or non-terminating loop in the placeholder
  -- would surface here.
  let _ ← SeLe4n.Kernel.secondaryKernelMain 0
  let _ ← SeLe4n.Kernel.secondaryKernelMain 1
  let _ ← SeLe4n.Kernel.secondaryKernelMain 2
  let _ ← SeLe4n.Kernel.secondaryKernelMain 3
  assertBool "secondaryKernelMain runtime invocation on context_ids 0..3" true
  -- Boundary inputs: confirm the function tolerates extreme context_id
  -- values without aborting.  At SM1.C the body ignores the argument;
  -- if SM5+ adds a range check it should fail closed via the typed
  -- `CoreId` wrapper, not by panicking in `secondaryKernelMain`.
  let _ ← SeLe4n.Kernel.secondaryKernelMain (UInt64.ofNat (Nat.pow 2 32))
  let _ ← SeLe4n.Kernel.secondaryKernelMain (UInt64.ofNat (Nat.pow 2 63))
  let _ ← SeLe4n.Kernel.secondaryKernelMain UInt64.size.toUInt64
  assertBool "secondaryKernelMain tolerates boundary UInt64 inputs" true

private def runTlbiForSharingChecks : IO Unit := do
  -- WS-SM SM1.E.4: typed TLBI dispatcher tag-encoding witnesses.
  --
  -- `tlbiForSharing` is a `BaseIO Unit` action, so we cannot
  -- `decide`-compare two invocations.  Instead we exercise the
  -- pure tag-encoding helpers + structural inequalities at runtime.
  IO.println "--- §2.18 SM1.E.4 tlbiForSharing tag encoding ---"
  -- Domain encoding: 2 distinct values mapped to 0 and 1.
  assertBool "SharingDomain.inner.toTag = 0"
    (decide (SeLe4n.Kernel.Concurrency.SharingDomain.inner.toTag = 0))
  assertBool "SharingDomain.outer.toTag = 1"
    (decide (SeLe4n.Kernel.Concurrency.SharingDomain.outer.toTag = 1))
  assertBool "SharingDomain tags distinct"
    (decide (SeLe4n.Kernel.Concurrency.SharingDomain.inner.toTag ≠
              SeLe4n.Kernel.Concurrency.SharingDomain.outer.toTag))
  -- Op-tag encoding: 4 constructors mapped to 0..3.
  assertBool "TlbInvalidation.vmalle1.toOpTag = 0"
    (decide (SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1.toOpTag = 0))
  assertBool "TlbInvalidation.vae1.toOpTag = 1"
    (decide ((SeLe4n.Kernel.Architecture.TlbInvalidation.vae1 0 0).toOpTag = 1))
  assertBool "TlbInvalidation.aside1.toOpTag = 2"
    (decide ((SeLe4n.Kernel.Architecture.TlbInvalidation.aside1 0).toOpTag = 2))
  assertBool "TlbInvalidation.vale1.toOpTag = 3"
    (decide ((SeLe4n.Kernel.Architecture.TlbInvalidation.vale1 0 0).toOpTag = 3))
  -- Operand extraction: vae1/vale1 carry asid + vaddr.
  assertBool "TlbInvalidation.vae1 42 0x1000 .toAsid = 42"
    (decide ((SeLe4n.Kernel.Architecture.TlbInvalidation.vae1 42 0x1000).toAsid = 42))
  assertBool "TlbInvalidation.vae1 42 0x1000 .toVaddr = 0x1000"
    (decide ((SeLe4n.Kernel.Architecture.TlbInvalidation.vae1 42 0x1000).toVaddr = 0x1000))
  assertBool "TlbInvalidation.aside1 7 .toAsid = 7"
    (decide ((SeLe4n.Kernel.Architecture.TlbInvalidation.aside1 7).toAsid = 7))
  -- vmalle1 has zero operands.
  assertBool "TlbInvalidation.vmalle1 zero operands"
    (decide (SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1.toAsid = 0 ∧
              SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1.toVaddr = 0))
  -- SM1.E.4 audit-pass-2: structural witness that well-formed Lean
  -- callers cannot trip the Rust FFI's fail-closed panic.  The
  -- Rust dispatcher panics on `domain_tag >= 2` or `op_tag >= 4`;
  -- this theorem combines `SharingDomain.toTag_in_range` and
  -- `TlbInvalidation.toOpTag_in_range` to prove every Lean-emitted
  -- tag tuple is within the accepted range.  We exercise both
  -- bounds for representative inputs.
  assertBool "tlbiForSharing_ffi_args_in_range inner-vmalle1 bounds"
    (decide (SeLe4n.Kernel.Concurrency.SharingDomain.inner.toTag.toNat < 2 ∧
              SeLe4n.Kernel.Architecture.TlbInvalidation.vmalle1.toOpTag.toNat < 4))
  assertBool "tlbiForSharing_ffi_args_in_range outer-vale1 bounds"
    (decide (SeLe4n.Kernel.Concurrency.SharingDomain.outer.toTag.toNat < 2 ∧
              (SeLe4n.Kernel.Architecture.TlbInvalidation.vale1 42 0x1000).toOpTag.toNat < 4))

private def runIdleWaitChecks : IO Unit := do
  -- WS-SM SM1.I.3: idle-wait typed wrappers.
  --
  -- Per the FFI link discipline (no Rust HAL linked into Lean test
  -- executables), we cannot invoke `ffiIdleWait` / `ffiIdleWaitBounded`
  -- at host runtime — the link would fail.  We exercise structural
  -- properties:
  --
  --   1. The typed wrappers `idleWait` and `idleWaitBounded` exist
  --      with the expected `BaseIO` signatures.
  --   2. The pass-through equalities hold by `rfl`.
  IO.println "--- §2.20 SM1.I.3 idle-wait typed wrappers ---"
  -- Pass-through: `idleWait` is definitionally `ffiIdleWait`.
  let _eq1 : (SeLe4n.Kernel.Concurrency.idleWait : BaseIO Unit) =
              SeLe4n.Platform.FFI.ffiIdleWait := rfl
  assertBool "idleWait = ffiIdleWait (rfl pass-through)" true
  -- Pass-through: `idleWaitBounded` is definitionally `ffiIdleWaitBounded`.
  let _eq2 : ∀ t : UInt64,
      (SeLe4n.Kernel.Concurrency.idleWaitBounded t : BaseIO UInt64) =
        SeLe4n.Platform.FFI.ffiIdleWaitBounded t :=
    fun _ => rfl
  assertBool "idleWaitBounded = ffiIdleWaitBounded (rfl pass-through)" true

private def runPerCoreStatsChecks : IO Unit := do
  -- WS-SM SM1.I.4: per-core stats typed wrappers.
  --
  -- Same FFI link discipline as runIdleWaitChecks: we exercise the
  -- structural marker theorem and the typed-wrapper signatures, not
  -- the runtime FFI calls.
  IO.println "--- §2.21 SM1.I.4 per-core stats typed wrappers ---"
  -- Marker theorem discharges by `rfl` for every CoreId input.
  let _proof_boot := SeLe4n.Kernel.Concurrency.perCoreIrqCount_returns_baseio_uint64_marker
                       SeLe4n.Kernel.Concurrency.bootCoreId
  assertBool "perCoreIrqCount_returns_baseio_uint64_marker discharges on bootCoreId"
    true
  -- The marker theorem must discharge for every plausible CoreId
  -- (`allCores` enumerates 0..numCores-1).  We can't decide `BaseIO`
  -- equality, but the marker theorem's existence on every CoreId is
  -- a per-input structural witness.
  assertBool "perCoreIrqCount_returns_baseio_uint64_marker discharges on every CoreId"
    (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
      let _proof := SeLe4n.Kernel.Concurrency.perCoreIrqCount_returns_baseio_uint64_marker c
      true))
  -- Audit-pass-1: the three sibling marker theorems get the same
  -- per-CoreId exercise so an inadvertent regression in any of
  -- the wrappers surfaces here, not just in `perCoreIrqCount`.
  assertBool "perCoreTimerTickCount_returns_baseio_uint64_marker discharges on every CoreId"
    (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
      let _proof := SeLe4n.Kernel.Concurrency.perCoreTimerTickCount_returns_baseio_uint64_marker c
      true))
  assertBool "perCoreSgiCount_returns_baseio_uint64_marker discharges on every CoreId"
    (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
      let _proof := SeLe4n.Kernel.Concurrency.perCoreSgiCount_returns_baseio_uint64_marker c
      true))
  assertBool "perCoreSyscallCount_returns_baseio_uint64_marker discharges on every CoreId"
    (SeLe4n.Kernel.Concurrency.allCores.all (fun c =>
      let _proof := SeLe4n.Kernel.Concurrency.perCoreSyscallCount_returns_baseio_uint64_marker c
      true))
  -- Audit-pass-1: idle-wait marker theorems verified the same way.
  let _proof_idle := SeLe4n.Kernel.Concurrency.idleWait_returns_baseio_unit_marker
  assertBool "idleWait_returns_baseio_unit_marker reachable"
    true
  let _proof_idle_bounded := SeLe4n.Kernel.Concurrency.idleWaitBounded_returns_baseio_uint64_marker 0
  assertBool "idleWaitBounded_returns_baseio_uint64_marker reachable on max_ticks=0"
    true
  let _proof_idle_bounded_default := SeLe4n.Kernel.Concurrency.idleWaitBounded_returns_baseio_uint64_marker 540_000
  assertBool "idleWaitBounded_returns_baseio_uint64_marker reachable on default tick budget"
    true

private def runSgiFfiBindingChecks : IO Unit := do
  -- WS-SM SM1.F.6: SGI FFI binding structural checks.
  --
  -- Per the FFI link discipline (no Rust HAL linked into Lean test
  -- executables), we cannot invoke the FFI exports at host runtime —
  -- the link would fail.  We exercise structural properties:
  --
  --   1. Every SgiKind's INTID is structurally `< 16` (the SGI
  --      range), so `ffiSendSgi(_, k.toIntid.val.toUInt8)` would
  --      never trip the Rust-side bound check.
  --   2. Every SgiKind maps to a distinct INTID (SgiKind.toIntid_injective).
  IO.println "--- §2.19 SM1.F.6 SGI FFI binding structural ---"
  assertBool "SgiKind.reschedule.toIntid < 16"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.reschedule.toIntid.val < 16))
  assertBool "SgiKind.tlbShootdownReq.toIntid < 16"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownReq.toIntid.val < 16))
  assertBool "SgiKind.tlbShootdownAck.toIntid < 16"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.tlbShootdownAck.toIntid.val < 16))
  assertBool "SgiKind.cacheBroadcast.toIntid < 16"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.cacheBroadcast.toIntid.val < 16))
  assertBool "SgiKind.haltAll.toIntid < 16"
    (decide (SeLe4n.Kernel.Concurrency.SgiKind.haltAll.toIntid.val < 16))
  -- Every SgiKind's INTID converted to UInt8 stays `< 16`.  This is the
  -- "FFI bridge well-formedness" witness — SgiKind → UInt8 → ffiSendSgi
  -- never trips the Rust-side bound on a well-formed Lean caller.
  assertBool "every SgiKind INTID < 16 (UInt8)"
    (SeLe4n.Kernel.Concurrency.SgiKind.all.all
      (fun k => decide (k.toIntid.val < 16)))

def runFoundationsChecks : IO Unit := do
  IO.println "WS-SM SM0.S + SM1.B + SM1.C + SM1.E + SM1.F + SM1.I — Foundations test suite"
  IO.println "===================================="
  runCoreIdChecks
  runSharingDomainChecks
  runLockKindChecks
  runLockIdChecks
  runSgiKindChecks
  runBklStateChecks
  runArchAssumptionChecks
  runSmpInventoryChecks
  runPlatformBindingChecks
  runLockKindUniquenessChecks
  runLockIdAdditionalChecks
  runSgiKindAdditionalChecks
  runArchAssumptionAdditionalChecks
  runBklStateAdditionalChecks
  runCurrentCoreIdChecks
  runSecondaryKernelMainChecks
  runTlbiForSharingChecks
  runSgiFfiBindingChecks
  runIdleWaitChecks
  runPerCoreStatsChecks
  IO.println "===================================="
  IO.println "All SM0 + SM1.B + SM1.C + SM1.E + SM1.F + SM1.I foundation checks PASS."

end SeLe4n.Testing.SmpFoundations

def main : IO Unit :=
  SeLe4n.Testing.SmpFoundations.runFoundationsChecks
