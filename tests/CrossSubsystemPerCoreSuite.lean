-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.CrossSubsystemPerCore

/-!
# WS-SM SM4.D — Cross-subsystem per-core invariant migration test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase
SM4.D "Cross-subsystem migrations" deliverable (plan §5.4).  Each section
exercises a layer of the per-core cross-subsystem invariant migration:

* **§1 Surface anchors** — every public SM4.D symbol (per-core predicate
  forms, boot-core bridges, frame lemmas, default-state witnesses, ∀c SMP
  aggregates, the capstone bundles) resolves at elaboration time, so a
  rename or removal fails the build immediately.
* **§2 Elaboration-time examples** — apply each headline theorem to
  verified inputs (default-state witnesses, boot-core bridges, frame
  lemmas with `rfl` hypotheses, SMP-aggregate projections).
* **§3 Runtime assertions** — `lake exe cross_subsystem_per_core_suite`
  re-exercises the decidable facts and theorem applications on the
  freshly-booted system across every core in `allCores`.  A silent
  regression surfaces in the Tier-2 trace pass.
-/

namespace SeLe4n.Testing.CrossSubsystemPerCore

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM4.D public symbol resolves
-- ============================================================================

-- §1.1  IPC per-core predicate forms (12) + bridges + frames + defaults
#check @runnableThreadIpcReady_perCore
#check @blockedOnSendNotRunnable_perCore
#check @blockedOnReceiveNotRunnable_perCore
#check @blockedOnCallNotRunnable_perCore
#check @blockedOnReplyNotRunnable_perCore
#check @blockedOnNotificationNotRunnable_perCore
#check @currentThreadIpcReady_perCore
#check @currentNotEndpointQueueHead_perCore
#check @currentNotOnNotificationWaitList_perCore
#check @passiveServerIdle_perCore
#check @ipcSchedulerContractPredicates_perCore
#check @currentThreadDequeueCoherent_perCore
#check @runnableThreadIpcReady_perCore_bootCore_iff
#check @passiveServerIdle_perCore_bootCore_iff
#check @ipcSchedulerContractPredicates_perCore_bootCore_iff
#check @currentThreadDequeueCoherent_perCore_bootCore_iff
#check @runnableThreadIpcReady_perCore_frame
#check @currentThreadIpcReady_perCore_frame
#check @passiveServerIdle_perCore_frame
#check @default_ipcSchedulerContractPredicates_perCore
#check @default_currentThreadDequeueCoherent_perCore
#check @default_passiveServerIdle_perCore
-- §1.2  IPC SMP aggregates + extractors
#check @ipcSchedulerContractPredicates_smp
#check @currentThreadDequeueCoherent_smp
#check @passiveServerIdle_smp
#check @ipcSchedulerContractPredicates_smp_at
#check @ipcSchedulerContractPredicates_smp_to_singleCore
#check @currentThreadDequeueCoherent_smp_to_singleCore
#check @passiveServerIdle_smp_to_singleCore
#check @default_ipcSchedulerContractPredicates_smp
#check @default_currentThreadDequeueCoherent_smp
#check @default_passiveServerIdle_smp
#check @ipcSchedulerContractPredicates_perCore_to_runnableThreadIpcReady
#check @currentThreadDequeueCoherent_perCore_to_currentThreadIpcReady
-- §1.3  Capability per-core
#check @cleanupNoStaleSchedRef_perCore
#check @cleanupHookDischarged_perCore
#check @cleanupNoStaleSchedRef_perCore_bootCore_iff
#check @cleanupHookDischarged_perCore_bootCore_iff
#check @cleanupNoStaleSchedRef_perCore_frame
#check @default_cleanupNoStaleSchedRef_perCore
#check @cleanupNoStaleSchedRef_smp
#check @cleanupNoStaleSchedRef_smp_to_singleCore
#check @default_cleanupNoStaleSchedRef_smp
-- §1.4  Architecture per-core
#check @registerDecodeConsistent_perCore
#check @registerDecodeConsistent_perCore_bootCore_iff
#check @registerDecodeConsistent_perCore_frame
#check @default_registerDecodeConsistent_perCore
#check @registerDecodeConsistent_smp
#check @registerDecodeConsistent_smp_to_singleCore
#check @default_registerDecodeConsistent_smp
-- §1.5  InformationFlow per-core projections
#check @projectRunnableOnCore
#check @projectCurrentOnCore
#check @projectActiveDomainOnCore
#check @projectDomainTimeRemainingOnCore
#check @projectDomainScheduleIndexOnCore
#check @projectMachineRegsOnCore
#check @projectStateOnCore
#check @projectRunnableOnCore_bootCore
#check @projectCurrentOnCore_bootCore
#check @projectMachineRegsOnCore_bootCore
#check @projectStateOnCore_bootCore
#check @projectRunnableOnCore_frame
#check @projectMachineRegsOnCore_frame
#check @projectStateOnCore_congr
-- §1.6  CrossSubsystem capstone
#check @crossSubsystemInvariant_perCore
#check @crossSubsystemInvariant_perCore_bootCore_iff
#check @crossSubsystemInvariant_smp
#check @crossSubsystemInvariant_smp_to_singleCore
#check @default_crossSubsystemInvariant_perCore
#check @default_crossSubsystemInvariant_smp
#check @crossSubsystemInvariant_perCore_to_schedContextRunQueueConsistent
#check @crossSubsystemSchedulerContract_perCore
#check @crossSubsystemSchedulerContract_perCore_bootCore_iff
#check @crossSubsystemSchedulerContract_smp
#check @crossSubsystemSchedulerContract_smp_at
#check @default_crossSubsystemSchedulerContract_perCore
#check @default_crossSubsystemSchedulerContract_smp
#check @crossSubsystemSchedulerContract_perCore_to_passiveServerIdle
#check @crossSubsystemSchedulerContract_perCore_to_registerDecodeConsistent
-- §1.7  Audit-pass-1 additions: passiveServerIdle natural-SMP theorem,
-- per-core low-equivalence (SM4.D.13 NI substrate), full SMP cleanup-hook.
#check @passiveServerIdle_smp_not_scheduled_anywhere
#check @lowEquivalentOnCore
#check @lowEquivalentOnCore_bootCore
#check @lowEquivalentOnCore_refl
#check @lowEquivalentOnCore_symm
#check @lowEquivalentOnCore_trans
#check @lowEquivalent_smp
#check @lowEquivalent_smp_aggregateForall
#check @lowEquivalent_smp_at
#check @lowEquivalent_smp_to_singleCore
#check @cleanupHookDischarged_smp
#check @cleanupHookDischarged_smp_to_singleCore
#check @cleanupHookDischarged_smp_to_noStaleSchedRef

-- ============================================================================
-- §2  Elaboration-time examples (apply each headline theorem)
-- ============================================================================

-- IPC: per-core defaults, SMP defaults, boot-core bridges, SMP→single-core.
example (c : CoreId) : ipcSchedulerContractPredicates_perCore (default : SystemState) c :=
  default_ipcSchedulerContractPredicates_perCore c
example : ipcSchedulerContractPredicates_smp (default : SystemState) :=
  default_ipcSchedulerContractPredicates_smp
example : passiveServerIdle_smp (default : SystemState) := default_passiveServerIdle_smp
example (st : SystemState) :
    ipcSchedulerContractPredicates_perCore st bootCoreId ↔
      ipcSchedulerContractPredicates st :=
  ipcSchedulerContractPredicates_perCore_bootCore_iff st
example (st : SystemState) (h : passiveServerIdle_smp st) : passiveServerIdle st :=
  passiveServerIdle_smp_to_singleCore st h
-- IPC frame with rfl hypotheses (a no-op write preserves the predicate).
example (st : SystemState) (c : CoreId) :
    runnableThreadIpcReady_perCore st c ↔ runnableThreadIpcReady_perCore st c :=
  runnableThreadIpcReady_perCore_frame rfl rfl

-- Capability: SMP "no stale ref on any core" default + SMP→single-core.
example (target : SeLe4n.ObjId) :
    cleanupNoStaleSchedRef_smp (default : SystemState) target :=
  default_cleanupNoStaleSchedRef_smp target

-- Architecture: per-core default + SMP→single-core.
example (c : CoreId) : registerDecodeConsistent_perCore (default : SystemState) c :=
  default_registerDecodeConsistent_perCore c
example (st : SystemState) (h : registerDecodeConsistent_smp st) :
    registerDecodeConsistent st :=
  registerDecodeConsistent_smp_to_singleCore st h

-- InformationFlow: boot-core projection bridges + frame.
example (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) :
    projectStateOnCore ctx observer st bootCoreId = projectState ctx observer st :=
  projectStateOnCore_bootCore ctx observer st
example (ctx : LabelingContext) (observer : IfObserver) (st : SystemState) (c : CoreId) :
    projectRunnableOnCore ctx observer st c = projectRunnableOnCore ctx observer st c :=
  projectRunnableOnCore_frame ctx observer rfl
-- InformationFlow: per-core low-equivalence bridge + SMP→single-core.
example (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState) :
    lowEquivalentOnCore ctx observer s₁ s₂ bootCoreId ↔ lowEquivalent ctx observer s₁ s₂ :=
  lowEquivalentOnCore_bootCore ctx observer s₁ s₂
example (ctx : LabelingContext) (observer : IfObserver) (s₁ s₂ : SystemState)
    (h : lowEquivalent_smp ctx observer s₁ s₂) : lowEquivalent ctx observer s₁ s₂ :=
  lowEquivalent_smp_to_singleCore ctx observer s₁ s₂ h
-- Capability: full SMP cleanup-hook → single-core.
example (st : SystemState) (target : SeLe4n.ObjId) (h : cleanupHookDischarged_smp st target) :
    cleanupHookDischarged st target :=
  cleanupHookDischarged_smp_to_singleCore st target h
-- IPC: passiveServerIdle natural-SMP "not scheduled anywhere ⟹ passive".
example (st : SystemState) (h : passiveServerIdle_smp st) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hUnbound : tcb.schedContextBinding = .unbound)
    (hNoQueue : ∀ c : CoreId, tid ∉ (st.scheduler.runQueueOnCore c))
    (hNoCurrent : ∀ c : CoreId, st.scheduler.currentOnCore c ≠ some tid) :
    tcb.ipcState = .ready ∨
      ∃ epId, tcb.ipcState = .blockedOnReceive epId ∨
              tcb.ipcState = .blockedOnNotification epId :=
  passiveServerIdle_smp_not_scheduled_anywhere h tid tcb hTcb hUnbound hNoQueue hNoCurrent

-- CrossSubsystem capstone: per-core master invariant + contract bundle.
example (c : CoreId) : crossSubsystemInvariant_perCore (default : SystemState) c :=
  default_crossSubsystemInvariant_perCore c
example : crossSubsystemSchedulerContract_smp (default : SystemState) :=
  default_crossSubsystemSchedulerContract_smp
example (st : SystemState) (h : crossSubsystemInvariant_smp st) : crossSubsystemInvariant st :=
  crossSubsystemInvariant_smp_to_singleCore st h
example (st : SystemState) :
    crossSubsystemSchedulerContract_perCore st bootCoreId ↔
      (ipcSchedulerContractPredicates st ∧ currentThreadDequeueCoherent st ∧
       passiveServerIdle st ∧ Architecture.registerDecodeConsistent st ∧
       schedContextRunQueueConsistent st) :=
  crossSubsystemSchedulerContract_perCore_bootCore_iff st

-- ============================================================================
-- §3  Runtime assertions (Tier-2): re-exercise on default across allCores
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- A concrete observer + the canonical default labeling context, used for
    value-level projection checks below.  Under `defaultLabelingContext`
    every entity is `publicLabel`, so `threadObservable` is `true` for all
    threads — but the per-core run queue / current slot is empty / `none`
    on the default state, so the projections still reduce to `[]` / `none`. -/
private def probeObserver : IfObserver := { clearance := SecurityLabel.publicLabel }

/-- §3.1  IPC: every per-core IPC↔scheduler predicate holds on the default
    state across every core; the SMP aggregates and bridges apply. -/
private def runIpcChecks : IO Unit := do
  IO.println "--- §3.1 IPC per-core scheduler-contract predicates ---"
  assertBool "default_ipcSchedulerContractPredicates_perCore applies on every core"
    (allCores.all (fun c =>
      have _h : ipcSchedulerContractPredicates_perCore (default : SystemState) c :=
        default_ipcSchedulerContractPredicates_perCore c
      true))
  assertBool "default_currentThreadDequeueCoherent_perCore applies on every core"
    (allCores.all (fun c =>
      have _h : currentThreadDequeueCoherent_perCore (default : SystemState) c :=
        default_currentThreadDequeueCoherent_perCore c
      true))
  assertBool "default_passiveServerIdle_perCore applies on every core"
    (allCores.all (fun c =>
      have _h : passiveServerIdle_perCore (default : SystemState) c :=
        default_passiveServerIdle_perCore c
      true))
  assertBool "ipcSchedulerContractPredicates_smp_at extracts every core"
    (allCores.all (fun c =>
      have _h : ipcSchedulerContractPredicates_perCore (default : SystemState) c :=
        ipcSchedulerContractPredicates_smp_at _ c default_ipcSchedulerContractPredicates_smp
      true))
  assertBool "ipcSchedulerContractPredicates_smp_to_singleCore applies"
    (have _h : ipcSchedulerContractPredicates (default : SystemState) :=
      ipcSchedulerContractPredicates_smp_to_singleCore _
        default_ipcSchedulerContractPredicates_smp
     true)

/-- §3.2  Capability: the SMP "no stale scheduler ref on any core" retype
    precondition holds vacuously on the default state for any target. -/
private def runCapabilityChecks : IO Unit := do
  IO.println "--- §3.2 capability cleanup no-stale-ref ---"
  let target : SeLe4n.ObjId := SeLe4n.ObjId.ofNat 1
  assertBool "default_cleanupNoStaleSchedRef_perCore applies on every core"
    (allCores.all (fun c =>
      have _h : cleanupNoStaleSchedRef_perCore (default : SystemState) target c :=
        default_cleanupNoStaleSchedRef_perCore target c
      true))
  assertBool "default_cleanupNoStaleSchedRef_smp applies (no stale ref on any core)"
    (have _h : cleanupNoStaleSchedRef_smp (default : SystemState) target :=
      default_cleanupNoStaleSchedRef_smp target
     true)

/-- §3.3  Architecture: per-core register-decode consistency. -/
private def runArchitectureChecks : IO Unit := do
  IO.println "--- §3.3 architecture register-decode consistency ---"
  assertBool "default_registerDecodeConsistent_perCore applies on every core"
    (allCores.all (fun c =>
      have _h : registerDecodeConsistent_perCore (default : SystemState) c :=
        default_registerDecodeConsistent_perCore c
      true))
  assertBool "registerDecodeConsistent_smp_to_singleCore applies"
    (have _h : registerDecodeConsistent (default : SystemState) :=
      registerDecodeConsistent_smp_to_singleCore _ default_registerDecodeConsistent_smp
     true)

/-- §3.4  InformationFlow: per-core projections reduce to the empty/none
    observable on the default state, and equal their single-core forms at
    `bootCoreId` (genuine value-level decidable checks). -/
private def runInformationFlowChecks : IO Unit := do
  IO.println "--- §3.4 information-flow per-core projections ---"
  assertBool "projectRunnableOnCore = [] on every core (default state)"
    (allCores.all (fun c =>
      decide (projectRunnableOnCore defaultLabelingContext probeObserver
        (default : SystemState) c = [])))
  assertBool "projectCurrentOnCore = none on every core (default state)"
    (allCores.all (fun c =>
      decide (projectCurrentOnCore defaultLabelingContext probeObserver
        (default : SystemState) c = none)))
  assertBool "projectMachineRegsOnCore = none on every core (default state)"
    (allCores.all (fun c =>
      decide (projectMachineRegsOnCore defaultLabelingContext probeObserver
        (default : SystemState) c = none)))
  assertBool "projectRunnableOnCore at bootCoreId = projectRunnable (default state)"
    (decide (projectRunnableOnCore defaultLabelingContext probeObserver (default : SystemState)
      bootCoreId = projectRunnable defaultLabelingContext probeObserver (default : SystemState)))
  assertBool "projectStateOnCore_bootCore bridge applies"
    (have _h : projectStateOnCore defaultLabelingContext probeObserver (default : SystemState)
        bootCoreId = projectState defaultLabelingContext probeObserver (default : SystemState) :=
      projectStateOnCore_bootCore _ _ _
     true)

/-- §3.5  CrossSubsystem capstone: the per-core master invariant and the
    cross-subsystem scheduler-contract bundle hold on the default state. -/
private def runCrossSubsystemChecks : IO Unit := do
  IO.println "--- §3.5 cross-subsystem capstone ---"
  assertBool "default_crossSubsystemInvariant_perCore applies on every core"
    (allCores.all (fun c =>
      have _h : crossSubsystemInvariant_perCore (default : SystemState) c :=
        default_crossSubsystemInvariant_perCore c
      true))
  assertBool "default_crossSubsystemSchedulerContract_perCore applies on every core"
    (allCores.all (fun c =>
      have _h : crossSubsystemSchedulerContract_perCore (default : SystemState) c :=
        default_crossSubsystemSchedulerContract_perCore c
      true))
  assertBool "crossSubsystemInvariant_smp_to_singleCore applies"
    (have _h : crossSubsystemInvariant (default : SystemState) :=
      crossSubsystemInvariant_smp_to_singleCore _ default_crossSubsystemInvariant_smp
     true)
  assertBool "crossSubsystemSchedulerContract_smp_at extracts every core"
    (allCores.all (fun c =>
      have _h : crossSubsystemSchedulerContract_perCore (default : SystemState) c :=
        crossSubsystemSchedulerContract_smp_at _ c default_crossSubsystemSchedulerContract_smp
      true))

/-- §3.6  Cross-core independence (value-level): writing core 1's scheduler
    slot leaves core 0's per-core projection unchanged and core 1's updated.
    This genuinely exercises the SM4.B per-core `Vector` indexing through
    the SM4.D projection layer (a `decide`-evaluated runtime computation,
    not a mere elaboration witness), confirming the per-core forms observe
    only their own core's slot. -/
private def runCrossCoreIndependenceChecks : IO Unit := do
  IO.println "--- §3.6 cross-core independence (value-level through projections) ---"
  let c0 : CoreId := ⟨0, by decide⟩
  let c1 : CoreId := ⟨1, by decide⟩
  -- Write only core 1's domainTimeRemaining (default is 5 on every core).
  let st1 : SystemState :=
    { (default : SystemState) with
      scheduler := (default : SystemState).scheduler.setDomainTimeRemainingOnCore c1 99 }
  assertBool "writing core 1's domainTimeRemaining leaves core 0's projection = 5"
    (decide (projectDomainTimeRemainingOnCore defaultLabelingContext probeObserver st1 c0 = 5))
  assertBool "writing core 1's domainTimeRemaining sets core 1's projection = 99"
    (decide (projectDomainTimeRemainingOnCore defaultLabelingContext probeObserver st1 c1 = 99))
  -- Write only core 1's activeDomain; core 0's projectActiveDomain stays ⟨0⟩.
  let st2 : SystemState :=
    { (default : SystemState) with
      scheduler := (default : SystemState).scheduler.setActiveDomainOnCore c1 ⟨3⟩ }
  assertBool "writing core 1's activeDomain leaves core 0's projection = ⟨0⟩"
    (decide (projectActiveDomainOnCore defaultLabelingContext probeObserver st2 c0 = ⟨0⟩))
  assertBool "writing core 1's activeDomain sets core 1's projection = ⟨3⟩"
    (decide (projectActiveDomainOnCore defaultLabelingContext probeObserver st2 c1 = ⟨3⟩))
  -- The frame lemma confirms (theorem-level) core 0's projection is framed
  -- by a write that only touches core 1's domainTimeRemaining slot; the
  -- per-core-slot-equality hypothesis is discharged by `decide` (both
  -- sides evaluate to 5 through the `Vector` get/set).
  assertBool "projectDomainTimeRemainingOnCore_frame applies under cross-core write"
    (have _h : projectDomainTimeRemainingOnCore defaultLabelingContext probeObserver st1 c0 =
        projectDomainTimeRemainingOnCore defaultLabelingContext probeObserver
          (default : SystemState) c0 :=
      projectDomainTimeRemainingOnCore_frame defaultLabelingContext probeObserver (by decide)
     true)
  -- lowEquivalentOnCore is reflexive (the per-core NI substrate is an
  -- equivalence); exercised at every core.
  assertBool "lowEquivalentOnCore reflexive on every core"
    (allCores.all (fun c =>
      have _h : lowEquivalentOnCore defaultLabelingContext probeObserver
          (default : SystemState) (default : SystemState) c :=
        lowEquivalentOnCore_refl defaultLabelingContext probeObserver (default : SystemState) c
      true))

def runCrossSubsystemPerCoreChecks : IO Unit := do
  IO.println "WS-SM SM4.D — Cross-subsystem per-core invariant migration suite"
  IO.println "===================================="
  runIpcChecks
  runCapabilityChecks
  runArchitectureChecks
  runInformationFlowChecks
  runCrossSubsystemChecks
  runCrossCoreIndependenceChecks
  IO.println "===================================="
  IO.println "All SM4.D cross-subsystem per-core invariant migration checks PASS."

end SeLe4n.Testing.CrossSubsystemPerCore

def main : IO Unit :=
  SeLe4n.Testing.CrossSubsystemPerCore.runCrossSubsystemPerCoreChecks
