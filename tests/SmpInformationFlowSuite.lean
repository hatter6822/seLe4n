-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.ObservableStatePerCore
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM8.A — Per-core observable state test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for WS-SM Phase SM8.A
(plan `docs/planning/SMP_INFORMATION_FLOW_PLAN.md` §5, sub-task SM8.A.6).

* **§1 Surface anchors** — every public SM8.A symbol resolves at
  elaboration time, so a rename or removal fails the build.
* **§2 Elaboration-time examples** — each headline theorem applied to
  verified inputs.
* **§3 Runtime assertions** — `lake exe smp_information_flow_suite`
  computes the per-core observable state on a real four-thread /
  four-core fixture with a non-trivial labeling (two low threads, two
  high threads, low and high endpoints / services / IRQ handlers) and
  decides every claim that is decidable.

Every group carries at least one **load-bearing negative**: an assertion
that fails if the property being tested is weakened.  In particular
§3.4 shows the same write applied to the observer's *own* core does
change its view (so the `c ≠ c'` hypothesis of the cross-core frames is
necessary, not decorative), and §3.5 shows the high observer strictly
outsees the low one (so monotonicity is not equality in disguise).
-/

namespace SeLe4n.Testing.SmpInformationFlow

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId allCores)

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM8.A public symbol resolves
-- ============================================================================

-- §1.1  SM8.A.1 — the observer and its view
#check @IfObserver.ofLabel
#check @IfObserver.ofLabel_clearance
#check PerCoreObserver
#check @PerCoreObserver.core
#check @PerCoreObserver.clearance
#check @PerCoreObserver.toIfObserver
#check @PerCoreObserver.toIfObserver_clearance
#check @PerCoreObserver.onBootCore
#check @ObservableState.onCore
#check @onCore_eq_projectStateOnCore
#check @onCore_bootCore
#check @PerCoreObserver.view
#check @lowEquivalentForObserver
#check @lowEquivalentForObserver_iff_lowEquivalentOnCore
#check @lowEquivalentForObserver_bootCore
#check @lowEquivalentForObserver_refl
#check @lowEquivalentForObserver_symm
#check @lowEquivalentForObserver_trans
#check @lowEquivalent_smp_iff_forall_observer

-- §1.2  SM8.A.2 — the shared / per-core field partition
#check @SharedObservableFragment
#check @PerCoreObservableFragment
#check @ObservableState.sharedFragment
#check @ObservableState.perCoreFragment
#check @ObservableState.ext_fragments
#check @onCore_sharedFragment
#check @onCore_perCoreFragment
#check @onCore_objects
#check @onCore_services
#check @onCore_irqHandlers
#check @onCore_objectIndex
#check @onCore_domainSchedule
#check @onCore_memory
#check @onCore_serviceRegistry
#check @onCore_runnable
#check @onCore_current
#check @onCore_activeDomain
#check @onCore_domainTimeRemaining
#check @onCore_domainScheduleIndex
#check @onCore_machineRegs
#check @onCore_sharedFragment_eq_globalProjection
#check @onCore_sharedFragment_determined_by_globalProjection
#check @onCore_sharedFragment_core_independent
#check @onCore_isProjection_of_globalProjection

-- §1.3  SM8.A.3 — the decidable fragment
#check @PerCoreObservableSlice
#check @ObservableState.perCoreSlice
#check @ObservableState.sliceOnCore
#check @lowEquivalentSliceOnCore
#check @onCore_decidable
#check @lowEquivalentSliceOnCore_of_lowEquivalentOnCore
#check @perCoreSlice_erases_register_content
#check @perCoreSlice_erases_shared_content
#check @onCore_perCoreSlice

-- §1.4  SM8.A.4 — per-core independence
#check @onCore_perCore_independence
#check @onCore_setCurrentOnCore_ne
#check @onCore_setRunQueueOnCore_ne
#check @onCore_setActiveDomainOnCore_ne
#check @onCore_setDomainTimeRemainingOnCore_ne
#check @onCore_setDomainScheduleIndexOnCore_ne
#check @onCore_setRegsOnCore_ne
#check @onCore_setReplenishQueueOnCore
#check @onCore_setLastTimeoutErrorsOnCore
#check @onCore_scThreadIndex
#check @onCore_machineTimer
#check @onCore_perCoreTlb

-- §1.5  SM8.A.5 — label monotonicity
#check @objectObservable_monotone
#check @threadObservable_monotone
#check @serviceObservable_monotone
#check @capTargetObservable_monotone
#check @memoryAddressObservable_monotone
#check @projectCNode
#check @projectKernelObject_cnode
#check @projectCNode_lookup_monotone
#check @projectKernelObject_observer_independent_off_cnode
#check @onCore_objects_label_invariant_off_cnode
#check @ObservableState.visibilityLe
#check @ObservableState.visibilityLe_refl
#check @ObservableState.visibilityLe_trans
#check @onCore_label_monotone
#check @observerView_label_monotone
#check @onCore_schedulingTransparency
#check @onCore_label_monotone_strict

-- §1.6  The RobinHood filter characterisation SM8.A.5 completed
#check @SeLe4n.Kernel.RobinHood.RHTable.filter_getElem?_of_pred
#check @SeLe4n.Kernel.RobinHood.RHTable.filter_getElem?_iff

-- ============================================================================
-- §2  Elaboration-time examples: each headline theorem applied
-- ============================================================================

-- SM8.A.1: the boot-core observer's view is the live single-core projection.
example (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) :
    ObservableState.onCore ctx bootCoreId L s = projectState ctx (IfObserver.ofLabel L) s :=
  onCore_bootCore ctx L s

-- SM8.A.1: observer low-equivalence at the boot core is the live `lowEquivalent`.
example (ctx : LabelingContext) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (h : lowEquivalentForObserver ctx (PerCoreObserver.onBootCore L) s₁ s₂) :
    lowEquivalent ctx (IfObserver.ofLabel L) s₁ s₂ :=
  (lowEquivalentForObserver_bootCore ctx L s₁ s₂).mp h

-- SM8.A.2: the two fragments determine the observable state (partition totality).
example (v₁ v₂ : ObservableState) (hShared : v₁.sharedFragment = v₂.sharedFragment)
    (hPerCore : v₁.perCoreFragment = v₂.perCoreFragment) : v₁ = v₂ :=
  ObservableState.ext_fragments hShared hPerCore

-- SM8.A.2: the shared fragment is a function of the global projection alone.
example (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (h : projectState ctx (IfObserver.ofLabel L) s₁ = projectState ctx (IfObserver.ofLabel L) s₂) :
    (ObservableState.onCore ctx c L s₁).sharedFragment =
      (ObservableState.onCore ctx c L s₂).sharedFragment :=
  onCore_sharedFragment_determined_by_globalProjection ctx c L h

-- SM8.A.2: the per-core view is a projection of the global projection.
example (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (hGlobal : projectState ctx (IfObserver.ofLabel L) s₁
      = projectState ctx (IfObserver.ofLabel L) s₂)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hCur : s₁.scheduler.currentOnCore c = s₂.scheduler.currentOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c)
    (hDTR : s₁.scheduler.domainTimeRemainingOnCore c = s₂.scheduler.domainTimeRemainingOnCore c)
    (hDSI : s₁.scheduler.domainScheduleIndexOnCore c = s₂.scheduler.domainScheduleIndexOnCore c)
    (hRegs : s₁.machine.regsOnCore c = s₂.machine.regsOnCore c) :
    ObservableState.onCore ctx c L s₁ = ObservableState.onCore ctx c L s₂ :=
  onCore_isProjection_of_globalProjection ctx c L hGlobal hRQ hCur hAD hDTR hDSI hRegs

-- SM8.A.3: observable equality at the observer implies slice equality (sound refuter).
example (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (h : lowEquivalentOnCore ctx (IfObserver.ofLabel L) s₁ s₂ c) :
    lowEquivalentSliceOnCore ctx c L s₁ s₂ :=
  lowEquivalentSliceOnCore_of_lowEquivalentOnCore ctx c L h

-- SM8.A.4: the read-set characterisation names only shared state and core `c`.
example (ctx : LabelingContext) (L : SecurityLabel) (s₁ s₂ : SystemState) (c : CoreId)
    (hObjects : s₁.objects = s₂.objects) (hServices : s₁.services = s₂.services)
    (hIrq : s₁.irqHandlers = s₂.irqHandlers) (hIndex : s₁.objectIndex = s₂.objectIndex)
    (hDomSched : s₁.scheduler.domainSchedule = s₂.scheduler.domainSchedule)
    (hMem : s₁.machine.memory = s₂.machine.memory)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hCur : s₁.scheduler.currentOnCore c = s₂.scheduler.currentOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c)
    (hDTR : s₁.scheduler.domainTimeRemainingOnCore c = s₂.scheduler.domainTimeRemainingOnCore c)
    (hDSI : s₁.scheduler.domainScheduleIndexOnCore c = s₂.scheduler.domainScheduleIndexOnCore c)
    (hRegs : s₁.machine.regsOnCore c = s₂.machine.regsOnCore c) :
    ObservableState.onCore ctx c L s₁ = ObservableState.onCore ctx c L s₂ :=
  onCore_perCore_independence ctx L hObjects hServices hIrq hIndex hDomSched hMem
    hRQ hCur hAD hDTR hDSI hRegs

-- SM8.A.4: a write to a different core's current slot is invisible.
example (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) (c c' : CoreId)
    (hne : c ≠ c') (v : Option SeLe4n.ThreadId) :
    ObservableState.onCore ctx c L { s with scheduler := s.scheduler.setCurrentOnCore c' v }
      = ObservableState.onCore ctx c L s :=
  onCore_setCurrentOnCore_ne ctx L s hne v

-- SM8.A.4: a write to a different core's register bank is invisible.
example (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) (c c' : CoreId)
    (hne : c ≠ c') (v : RegisterFile) :
    ObservableState.onCore ctx c L { s with machine := s.machine.setRegsOnCore c' v }
      = ObservableState.onCore ctx c L s :=
  onCore_setRegsOnCore_ne ctx L s hne v

-- SM8.A.4: the machine timer is invisible on every core (the excluded channel).
example (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) (c : CoreId) (t : Nat) :
    ObservableState.onCore ctx c L { s with machine := { s.machine with timer := t } }
      = ObservableState.onCore ctx c L s :=
  onCore_machineTimer ctx L s c t

-- SM8.A.5: monotonicity, extracted at the `current` component.
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel)
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) (t : SeLe4n.ThreadId)
    (ht : (ObservableState.onCore ctx c L₁ s).current = some t) :
    (ObservableState.onCore ctx c L₂ s).current = some t :=
  (onCore_label_monotone ctx c hFlow s).2.2.1 t ht

-- SM8.A.5: monotonicity, extracted at the `objects` component (visibility only).
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel)
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) (oid : SeLe4n.ObjId)
    (h : ((ObservableState.onCore ctx c L₁ s).objects oid).isSome = true) :
    ((ObservableState.onCore ctx c L₂ s).objects oid).isSome = true :=
  (onCore_label_monotone ctx c hFlow s).1 oid h

-- SM8.A.5: a CNode slot visible at the narrower clearance survives at the wider one.
example (ctx : LabelingContext) (L₁ L₂ : SecurityLabel) (hFlow : securityFlowsTo L₁ L₂ = true)
    (cn : CNode) (slot : SeLe4n.Slot) (cap : Capability)
    (h : (projectCNode ctx (IfObserver.ofLabel L₁) cn).lookup slot = some cap) :
    (projectCNode ctx (IfObserver.ofLabel L₂) cn).lookup slot = some cap :=
  projectCNode_lookup_monotone ctx hFlow cn slot cap h

-- SM8.A.5: off the CNode arm, a visible object projects to the SAME value at
-- the wider clearance — the widening is confined to CNode slot redaction.
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel)
    (hFlow : securityFlowsTo L₁ L₂ = true) (s : SystemState) (oid : SeLe4n.ObjId)
    (obj : KernelObject) (hGet : s.objects[oid]? = some obj)
    (hNotCNode : ∀ cn, obj ≠ .cnode cn)
    (hVisible : ((ObservableState.onCore ctx c L₁ s).objects oid).isSome = true) :
    (ObservableState.onCore ctx c L₂ s).objects oid
      = (ObservableState.onCore ctx c L₁ s).objects oid :=
  onCore_objects_label_invariant_off_cnode ctx c hFlow s oid obj hGet hNotCNode hVisible

-- SM8.A.5: the scheduling components are label-invariant (accepted channel CC-1).
example (ctx : LabelingContext) (c : CoreId) (L₁ L₂ : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L₁ s).activeDomain =
      (ObservableState.onCore ctx c L₂ s).activeDomain :=
  (onCore_schedulingTransparency ctx c L₁ L₂ s).1

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the four-thread / four-core IF fixture
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- The four RPi5 cores. -/
private def c0 : CoreId := bootCoreId
private def c1 : CoreId := ⟨1, by decide⟩
private def c2 : CoreId := ⟨2, by decide⟩

/-- The two clearances.  `securityFlowsTo lowLabel highLabel = true` and
`securityFlowsTo highLabel lowLabel = false`, so the pair is a genuine
strict step of the flow order (checked in §3.5). -/
private def lowLabel : SecurityLabel := SecurityLabel.publicLabel
private def highLabel : SecurityLabel := SecurityLabel.kernelTrusted

/-- The fixture's clearance step, as a reusable term.  A `by decide` written
inside a `fun c => …` cannot discharge this goal: the observer record carries
the free core component `c`, and `decide` refuses a goal with free variables
even when (as here) the statement does not depend on it. -/
private theorem lowLabel_flowsTo_highLabel : securityFlowsTo lowLabel highLabel = true := by
  decide

-- Fixture OIDs (range 1000–1020 — see the range table in SeLe4n/Testing/Helpers.lean).
private def cnRoot : SeLe4n.ObjId := ⟨1000⟩
private def vsRoot : SeLe4n.ObjId := ⟨1001⟩
private def lowEndpoint : SeLe4n.ObjId := ⟨1002⟩
private def highEndpoint : SeLe4n.ObjId := ⟨1003⟩
private def lowService : ServiceId := ⟨1004⟩
private def highService : ServiceId := ⟨1005⟩
private def lowIrq : SeLe4n.Irq := ⟨11⟩
private def highIrq : SeLe4n.Irq := ⟨12⟩
private def lowCurrent : SeLe4n.ThreadId := ⟨1010⟩
private def highCurrent : SeLe4n.ThreadId := ⟨1011⟩
private def lowQueued : SeLe4n.ThreadId := ⟨1012⟩
private def highQueued : SeLe4n.ThreadId := ⟨1013⟩

/-- The suite's labeling context: the high endpoint, the two high threads (and
their backing objects) and the high service carry `kernelTrusted`; everything
else carries `publicLabel`.

Deliberately **not** `defaultLabelingContext`, under which every observability
gate is unconditionally `true` (`defaultLabelingContext_insecure`) and every
label assertion below would be vacuous. -/
private def probeLabeling : LabelingContext :=
  { objectLabelOf := fun oid =>
      if oid = highEndpoint then highLabel
      else if oid = highCurrent.toObjId then highLabel
      else if oid = highQueued.toObjId then highLabel
      else lowLabel
    threadLabelOf := fun tid =>
      if tid = highCurrent then highLabel
      else if tid = highQueued then highLabel
      else lowLabel
    endpointLabelOf := fun oid => if oid = highEndpoint then highLabel else lowLabel
    serviceLabelOf := fun sid => if sid = highService then highLabel else lowLabel }

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := vsRoot, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
    cpuAffinity := aff }

private def mkServiceEntry (sid : ServiceId) (backing : SeLe4n.ObjId) : ServiceGraphEntry :=
  { identity := { sid := sid, backingObject := backing, owner := backing }
    dependencies := []
    isolatedFrom := [] }

/-- The fixture: **core 0 runs low, core 1 runs high.**

* core 0 — current `lowCurrent`, run queue `[lowQueued]` (both low-labelled);
* core 1 — current `highCurrent`, run queue `[highQueued]` (both high-labelled);
* cores 2 and 3 — idle;
* shared — a low and a high endpoint, a low and a high service, a low and a
  high IRQ handler.

Every thread is dequeue-on-dispatch consistent (a core's current thread is not
in that core's run queue).  The two cores' contents are label-disjoint, which
is what makes the cross-core (§3.4) and label (§3.5) assertions independent of
each other. -/
private def probeState : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject lowEndpoint (.endpoint {})
      |>.withObject highEndpoint (.endpoint {})
      |>.withObject lowCurrent.toObjId (.tcb (mkTcb 1010 40 none))
      |>.withObject highCurrent.toObjId (.tcb (mkTcb 1011 50 (some c1)))
      |>.withObject lowQueued.toObjId (.tcb (mkTcb 1012 40 none))
      |>.withObject highQueued.toObjId (.tcb (mkTcb 1013 50 (some c1)))
      |>.withService lowService (mkServiceEntry lowService lowEndpoint)
      |>.withService highService (mkServiceEntry highService highEndpoint)
      |>.withIrqHandler lowIrq lowEndpoint
      |>.withIrqHandler highIrq highEndpoint
      |>.build)
  { base with scheduler :=
      ((((base.scheduler.setRunQueueOnCore c0 (RunQueue.ofList [(lowQueued, ⟨40⟩)])).setRunQueueOnCore
        c1 (RunQueue.ofList [(highQueued, ⟨50⟩)])).setCurrentOnCore
        c0 (some lowCurrent)).setCurrentOnCore c1 (some highCurrent)) }

/-- The two observers the suite compares. -/
private def lowObserver : IfObserver := IfObserver.ofLabel lowLabel
private def highObserver : IfObserver := IfObserver.ofLabel highLabel

/-- §3.0  Fixture non-vacuity.  Every later group reads this state; if the
builder had silently produced an empty one (the `buildChecked` panic-to-default
failure mode) every assertion below would pass vacuously.  These checks fail
first and loudly instead. -/
private def runFixtureChecks : IO Unit := do
  IO.println "--- §3.0 fixture non-vacuity ---"
  assertBool "both endpoints are in the object store"
    (decide ((probeState.objects[lowEndpoint]?).isSome = true ∧
             (probeState.objects[highEndpoint]?).isSome = true))
  assertBool "all four threads are in the object store"
    (decide ((probeState.objects[lowCurrent.toObjId]?).isSome = true ∧
             (probeState.objects[highCurrent.toObjId]?).isSome = true ∧
             (probeState.objects[lowQueued.toObjId]?).isSome = true ∧
             (probeState.objects[highQueued.toObjId]?).isSome = true))
  assertBool "core 0 runs the low thread, core 1 runs the high thread"
    (decide (probeState.scheduler.currentOnCore c0 = some lowCurrent ∧
             probeState.scheduler.currentOnCore c1 = some highCurrent))
  assertBool "core 0 queues the low thread, core 1 queues the high thread"
    (decide ((probeState.scheduler.runQueueOnCore c0).toList = [lowQueued] ∧
             (probeState.scheduler.runQueueOnCore c1).toList = [highQueued]))
  assertBool "cores 2 and 3 are idle (no current, empty queue)"
    (decide (probeState.scheduler.currentOnCore c2 = none ∧
             (probeState.scheduler.runQueueOnCore c2).toList = []))
  -- The labeling must be non-trivial: it has to separate the two clearances.
  --
  -- Note this is *not* checked with `isInsecureDefaultContext`.  That detector
  -- samples entity ids 0, 1 and 42 and reports "insecure default" when all of
  -- them are `publicLabel`; this fixture's labels live in the reserved
  -- 1000–1020 band, so the detector fires on it.  That is the heuristic being
  -- conservative in its safe direction (over-flagging a context that *looks*
  -- all-public at the probes), exactly as its docstring describes — not a
  -- property of this context.  The substantive gate is the separation below:
  -- there are entities the low observer provably cannot see, and none that the
  -- high observer cannot.
  assertBool "the probe labeling genuinely separates the two clearances"
    (decide (securityFlowsTo (probeLabeling.threadLabelOf highCurrent) lowLabel = false ∧
             securityFlowsTo (probeLabeling.threadLabelOf lowCurrent) lowLabel = true ∧
             securityFlowsTo (probeLabeling.objectLabelOf highEndpoint) lowLabel = false ∧
             securityFlowsTo (probeLabeling.serviceLabelOf highService) lowLabel = false))
  assertBool "low entities are observable to the low observer, high ones are not"
    (decide (objectObservable probeLabeling lowObserver lowEndpoint = true ∧
             objectObservable probeLabeling lowObserver highEndpoint = false ∧
             threadObservable probeLabeling lowObserver lowCurrent = true ∧
             threadObservable probeLabeling lowObserver highCurrent = false))
  assertBool "every entity is observable to the high observer"
    (decide (objectObservable probeLabeling highObserver lowEndpoint = true ∧
             objectObservable probeLabeling highObserver highEndpoint = true ∧
             threadObservable probeLabeling highObserver lowCurrent = true ∧
             threadObservable probeLabeling highObserver highCurrent = true))

/-- §3.1  The observer and its view: the boot-core bridge to the live
single-core projection, and observer low-equivalence as an equivalence. -/
private def runObserverChecks : IO Unit := do
  IO.println "--- §3.1 the (core, label) observer and its view ---"
  assertBool "onCore_bootCore: the boot-core view is the live projectState"
    (have _h : ObservableState.onCore probeLabeling bootCoreId lowLabel probeState
        = projectState probeLabeling lowObserver probeState :=
      onCore_bootCore probeLabeling lowLabel probeState
     true)
  assertBool "the observer view is the SM4.D per-core projection on every core"
    (allCores.all (fun c =>
      have _h : ObservableState.onCore probeLabeling c lowLabel probeState
          = projectStateOnCore probeLabeling lowObserver probeState c :=
        onCore_eq_projectStateOnCore probeLabeling c lowLabel probeState
      true))
  assertBool "lowEquivalentForObserver is reflexive at every (core, label)"
    (allCores.all (fun c =>
      have _h₁ : lowEquivalentForObserver probeLabeling ⟨c, lowLabel⟩ probeState probeState :=
        lowEquivalentForObserver_refl probeLabeling ⟨c, lowLabel⟩ probeState
      have _h₂ : lowEquivalentForObserver probeLabeling ⟨c, highLabel⟩ probeState probeState :=
        lowEquivalentForObserver_refl probeLabeling ⟨c, highLabel⟩ probeState
      true))
  assertBool "the ∀-observer SMP form is the SM4.D lowEquivalent_smp"
    (have _h : lowEquivalent_smp probeLabeling lowObserver probeState probeState ↔
        ∀ c : CoreId, lowEquivalentForObserver probeLabeling ⟨c, lowLabel⟩ probeState probeState :=
      lowEquivalent_smp_iff_forall_observer probeLabeling lowLabel probeState probeState
     true)

/-- §3.2  The field partition: the per-core components are core-restricted and
the shared components are not.  Every claim here is *computed* on the fixture,
so a projection re-pointed at the wrong core fails the run. -/
private def runPartitionChecks : IO Unit := do
  IO.println "--- §3.2 the shared / per-core field partition ---"
  -- Per-core half: each core sees its own current thread and its own queue.
  assertBool "the low observer sees core 0's low current thread"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).current
      = some lowCurrent))
  assertBool "the low observer sees core 0's low run queue"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).runnable
      = [lowQueued]))
  assertBool "the low observer sees nothing of core 1 (its threads are high)"
    (decide ((ObservableState.onCore probeLabeling c1 lowLabel probeState).current = none ∧
             (ObservableState.onCore probeLabeling c1 lowLabel probeState).runnable = []))
  assertBool "the high observer sees core 1's high current thread and queue"
    (decide ((ObservableState.onCore probeLabeling c1 highLabel probeState).current
        = some highCurrent ∧
             (ObservableState.onCore probeLabeling c1 highLabel probeState).runnable
        = [highQueued]))
  assertBool "core 0's view never shows core 1's thread (per-core restriction)"
    (decide ((ObservableState.onCore probeLabeling c0 highLabel probeState).current
      = some lowCurrent))
  assertBool "the idle cores project empty per-core components at both clearances"
    (decide ((ObservableState.onCore probeLabeling c2 lowLabel probeState).current = none ∧
             (ObservableState.onCore probeLabeling c2 highLabel probeState).current = none ∧
             (ObservableState.onCore probeLabeling c2 highLabel probeState).runnable = []))
  -- Shared half: the same on every core, at a fixed clearance.
  assertBool "the shared objectIndex component is identical on every core"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel probeState).objectIndex
        = (ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).objectIndex)))
  assertBool "the shared services component is identical on every core"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel probeState).services lowService
          = (ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).services
              lowService ∧
        (ObservableState.onCore probeLabeling c lowLabel probeState).services highService
          = (ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).services
              highService)))
  assertBool "the shared irqHandlers component is identical on every core"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel probeState).irqHandlers lowIrq
          = (ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).irqHandlers
              lowIrq ∧
        (ObservableState.onCore probeLabeling c lowLabel probeState).irqHandlers highIrq
          = (ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).irqHandlers
              highIrq)))
  assertBool "the shared objects component is identical on every core"
    (allCores.all (fun c =>
      decide (((ObservableState.onCore probeLabeling c lowLabel probeState).objects
            lowEndpoint).isSome
          = ((ObservableState.onCore probeLabeling bootCoreId lowLabel probeState).objects
              lowEndpoint).isSome)))
  -- `ext_fragments` used substantively: two *different* states whose fragments
  -- coincide have the same view.  Here the second state differs only in the
  -- machine timer, which no projection reads, so both fragments are `rfl`-equal
  -- and the theorem delivers the whole observable state.  (A `v = v` instance
  -- would prove nothing about the partition.)
  assertBool "ext_fragments derives view equality between two distinct states"
    (allCores.all (fun c =>
      have _h : ObservableState.onCore probeLabeling c lowLabel
            { probeState with machine := { probeState.machine with timer := 987654 } }
          = ObservableState.onCore probeLabeling c lowLabel probeState :=
        ObservableState.ext_fragments rfl rfl
      true))

/-- §3.3  The decidable slice: it decides, it refutes soundly, and it is
strictly weaker than observable equality. -/
private def runDecidableSliceChecks : IO Unit := do
  IO.println "--- §3.3 the decidable per-core slice ---"
  assertBool "slice low-equivalence decides reflexively at every (core, label)"
    (allCores.all (fun c =>
      decide (lowEquivalentSliceOnCore probeLabeling c lowLabel probeState probeState) &&
      decide (lowEquivalentSliceOnCore probeLabeling c highLabel probeState probeState)))
  assertBool "the slice records core 0's low current thread and queue"
    (decide ((ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState).current
        = some lowCurrent ∧
      (ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState).runnable
        = [lowQueued]))
  assertBool "the slice records that core 0's register bank is observable to low"
    (decide ((ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState).registersObservable
      = true))
  assertBool "the slice records that core 1's register bank is NOT observable to low"
    (decide ((ObservableState.sliceOnCore probeLabeling c1 lowLabel probeState).registersObservable
      = false))
  assertBool "…but IS observable to high (the negative above is not vacuous)"
    (decide ((ObservableState.sliceOnCore probeLabeling c1 highLabel probeState).registersObservable
      = true))
  assertBool "the low and high slices of core 1 genuinely differ (decidable refutation)"
    (!decide (ObservableState.sliceOnCore probeLabeling c1 lowLabel probeState
      = ObservableState.sliceOnCore probeLabeling c1 highLabel probeState))
  assertBool "observable equality implies slice equality (sound refuter)"
    (allCores.all (fun c =>
      have _h : lowEquivalentSliceOnCore probeLabeling c lowLabel probeState probeState :=
        lowEquivalentSliceOnCore_of_lowEquivalentOnCore probeLabeling c lowLabel
          (lowEquivalentOnCore_refl probeLabeling lowObserver probeState c)
      true))
  assertBool "the slice is a STRICT fragment: it erases register content"
    (have _h : ∃ v₁ v₂ : ObservableState,
        v₁.perCoreSlice = v₂.perCoreSlice ∧ v₁.machineRegs ≠ v₂.machineRegs :=
      perCoreSlice_erases_register_content
     true)
  assertBool "the slice is a STRICT fragment: it erases shared content"
    (have _h : ∃ v₁ v₂ : ObservableState, v₁.perCoreSlice = v₂.perCoreSlice ∧ v₁ ≠ v₂ :=
      perCoreSlice_erases_shared_content
     true)

/-- §3.4  Per-core independence — the read-set bound, computed.

The **load-bearing negative** is the last pair: the very same write applied to
the observer's own core *does* change its slice, so the `c ≠ c'` hypothesis of
the cross-core frames is necessary rather than decorative.  A regression that
made the per-core projections read a fixed core would fail there. -/
private def runIndependenceChecks : IO Unit := do
  IO.println "--- §3.4 per-core independence (cross-core writes) ---"
  -- Write only core 1's current slot.
  let stRemoteCurrent : SystemState :=
    { probeState with
      scheduler := probeState.scheduler.setCurrentOnCore c1 (some lowQueued) }
  assertBool "a write to core 1's current slot leaves core 0's slice unchanged"
    (decide (ObservableState.sliceOnCore probeLabeling c0 lowLabel stRemoteCurrent
      = ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState))
  assertBool "onCore_setCurrentOnCore_ne applies (theorem level, c0 ≠ c1)"
    (have _h : ObservableState.onCore probeLabeling c0 lowLabel
        { probeState with
          scheduler := probeState.scheduler.setCurrentOnCore c1 (some lowQueued) }
        = ObservableState.onCore probeLabeling c0 lowLabel probeState :=
      onCore_setCurrentOnCore_ne probeLabeling lowLabel probeState (by decide) (some lowQueued)
     true)
  -- Write only core 1's run queue.
  let stRemoteQueue : SystemState :=
    { probeState with
      scheduler := probeState.scheduler.setRunQueueOnCore c1 (RunQueue.ofList [(lowQueued, ⟨40⟩)]) }
  assertBool "a write to core 1's run queue leaves core 0's slice unchanged"
    (decide (ObservableState.sliceOnCore probeLabeling c0 lowLabel stRemoteQueue
      = ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState))
  assertBool "…and DOES change core 1's own low view (the write is not a no-op)"
    (!decide (ObservableState.sliceOnCore probeLabeling c1 lowLabel stRemoteQueue
      = ObservableState.sliceOnCore probeLabeling c1 lowLabel probeState))
  -- Write only core 1's active domain / domain timing.
  let stRemoteDomain : SystemState :=
    { probeState with
      scheduler := (probeState.scheduler.setActiveDomainOnCore c1 ⟨3⟩).setDomainTimeRemainingOnCore
        c1 99 }
  assertBool "a remote domain switch leaves core 0's slice unchanged"
    (decide (ObservableState.sliceOnCore probeLabeling c0 lowLabel stRemoteDomain
      = ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState))
  assertBool "…and IS visible on core 1 (scheduling transparency, per core)"
    (decide ((ObservableState.onCore probeLabeling c1 lowLabel stRemoteDomain).activeDomain
        = ⟨3⟩ ∧
      (ObservableState.onCore probeLabeling c1 lowLabel stRemoteDomain).domainTimeRemaining = 99))
  -- Write only core 1's register bank.
  let stRemoteRegs : SystemState :=
    { probeState with
      machine := probeState.machine.setRegsOnCore c1 { pc := ⟨7⟩, sp := ⟨9⟩, gpr := fun _ => ⟨1⟩ } }
  -- `Option RegisterFile` has no `DecidableEq` (the `gpr` field is a function
  -- over an unbounded domain), so the value-level check uses `RegisterFile`'s
  -- structural `BEq` — the ARM64 comparison over `pc`, `sp` and the 32
  -- architectural GPRs, which the model documents as the sanctioned test-time
  -- equality (`RegisterFile.not_lawfulBEq` records why it is not propositional
  -- equality).  The propositional statement is the theorem-level assertion
  -- immediately below.
  assertBool "a write to core 1's register bank leaves core 0's projected regs unchanged"
    (projectMachineRegsOnCore probeLabeling lowObserver stRemoteRegs c0
      == projectMachineRegsOnCore probeLabeling lowObserver probeState c0)
  assertBool "…while writing core 0's OWN bank DOES change them (not a vacuous BEq)"
    (!(projectMachineRegsOnCore probeLabeling lowObserver
        { probeState with
          machine := probeState.machine.setRegsOnCore c0
            { pc := ⟨7⟩, sp := ⟨9⟩, gpr := fun _ => ⟨1⟩ } } c0
      == projectMachineRegsOnCore probeLabeling lowObserver probeState c0))
  assertBool "onCore_setRegsOnCore_ne applies (theorem level, c0 ≠ c1)"
    (have _h : ObservableState.onCore probeLabeling c0 lowLabel
        { probeState with
          machine := probeState.machine.setRegsOnCore c1
            { pc := ⟨7⟩, sp := ⟨9⟩, gpr := fun _ => ⟨1⟩ } }
        = ObservableState.onCore probeLabeling c0 lowLabel probeState :=
      onCore_setRegsOnCore_ne probeLabeling lowLabel probeState (by decide)
        { pc := ⟨7⟩, sp := ⟨9⟩, gpr := fun _ => ⟨1⟩ }
     true)
  -- Fields outside the read set: invisible on EVERY core, including the one written.
  assertBool "the CBS replenishment queue is invisible on every core"
    (allCores.all (fun c =>
      have _h : ObservableState.onCore probeLabeling c lowLabel
          { probeState with
            scheduler := probeState.scheduler.setReplenishQueueOnCore c ReplenishQueue.empty }
          = ObservableState.onCore probeLabeling c lowLabel probeState :=
        onCore_setReplenishQueueOnCore probeLabeling lowLabel probeState c c ReplenishQueue.empty
      true))
  assertBool "the machine timer is invisible on every core (the excluded channel)"
    (allCores.all (fun c =>
      decide (ObservableState.sliceOnCore probeLabeling c lowLabel
          { probeState with machine := { probeState.machine with timer := 123456 } }
        = ObservableState.sliceOnCore probeLabeling c lowLabel probeState)))
  assertBool "onCore_machineTimer applies on every core (theorem level)"
    (allCores.all (fun c =>
      have _h : ObservableState.onCore probeLabeling c lowLabel
          { probeState with machine := { probeState.machine with timer := 123456 } }
          = ObservableState.onCore probeLabeling c lowLabel probeState :=
        onCore_machineTimer probeLabeling lowLabel probeState c 123456
      true))
  -- LOAD-BEARING NEGATIVE: the same write on the observer's OWN core is visible.
  let stLocalCurrent : SystemState :=
    { probeState with
      scheduler := probeState.scheduler.setCurrentOnCore c0 (some lowQueued) }
  assertBool "the SAME current-slot write on core 0 DOES change core 0's slice"
    (!decide (ObservableState.sliceOnCore probeLabeling c0 lowLabel stLocalCurrent
      = ObservableState.sliceOnCore probeLabeling c0 lowLabel probeState))
  assertBool "…while still leaving core 1's slice unchanged (the frame is symmetric)"
    (decide (ObservableState.sliceOnCore probeLabeling c1 lowLabel stLocalCurrent
      = ObservableState.sliceOnCore probeLabeling c1 lowLabel probeState))

/-- §3.5  Label monotonicity — the high observer outsees the low one, strictly.

The **load-bearing negative** is the strictness pair: if the projections ever
stopped filtering by label, the low and high views would coincide and the
`!decide` assertions would fail. -/
private def runMonotonicityChecks : IO Unit := do
  IO.println "--- §3.5 clearance monotonicity ---"
  assertBool "the clearance pair is a strict step of the flow order"
    (decide (securityFlowsTo lowLabel highLabel = true ∧
             securityFlowsTo highLabel lowLabel = false))
  assertBool "every gate is monotone on the fixture's entities"
    (decide (objectObservable probeLabeling lowObserver lowEndpoint = true ∧
             objectObservable probeLabeling highObserver lowEndpoint = true ∧
             serviceObservable probeLabeling lowObserver lowService = true ∧
             serviceObservable probeLabeling highObserver lowService = true ∧
             threadObservable probeLabeling lowObserver lowQueued = true ∧
             threadObservable probeLabeling highObserver lowQueued = true))
  assertBool "onCore_label_monotone applies on every core"
    (allCores.all (fun c =>
      have _h : (ObservableState.onCore probeLabeling c lowLabel probeState).visibilityLe
          (ObservableState.onCore probeLabeling c highLabel probeState) :=
        onCore_label_monotone probeLabeling c lowLabel_flowsTo_highLabel probeState
      true))
  assertBool "the observer form applies (same core, ordered clearances)"
    (allCores.all (fun c =>
      have _h : ((⟨c, lowLabel⟩ : PerCoreObserver).view probeLabeling probeState).visibilityLe
          ((⟨c, highLabel⟩ : PerCoreObserver).view probeLabeling probeState) :=
        observerView_label_monotone (o₁ := ⟨c, lowLabel⟩) (o₂ := ⟨c, highLabel⟩)
          probeLabeling rfl lowLabel_flowsTo_highLabel probeState
      true))
  -- Strictness, component by component.
  assertBool "STRICT: the high observer sees core 1's current thread, the low one does not"
    (decide ((ObservableState.onCore probeLabeling c1 lowLabel probeState).current = none ∧
             (ObservableState.onCore probeLabeling c1 highLabel probeState).current
               = some highCurrent))
  assertBool "STRICT: the high observer sees core 1's run queue, the low one does not"
    (decide ((ObservableState.onCore probeLabeling c1 lowLabel probeState).runnable = [] ∧
             (ObservableState.onCore probeLabeling c1 highLabel probeState).runnable
               = [highQueued]))
  assertBool "STRICT: the high endpoint is in the high objectIndex only"
    (decide (highEndpoint ∉
        (ObservableState.onCore probeLabeling c0 lowLabel probeState).objectIndex ∧
      highEndpoint ∈ (ObservableState.onCore probeLabeling c0 highLabel probeState).objectIndex))
  assertBool "MONOTONE: the low endpoint is in BOTH object indices"
    (decide (lowEndpoint ∈
        (ObservableState.onCore probeLabeling c0 lowLabel probeState).objectIndex ∧
      lowEndpoint ∈ (ObservableState.onCore probeLabeling c0 highLabel probeState).objectIndex))
  assertBool "STRICT: the high service is present only to the high observer"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).services highService
        = false ∧
      (ObservableState.onCore probeLabeling c0 highLabel probeState).services highService = true))
  assertBool "STRICT: the high IRQ handler is routed only for the high observer"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).irqHandlers highIrq
        = none ∧
      (ObservableState.onCore probeLabeling c0 highLabel probeState).irqHandlers highIrq
        = some highEndpoint))
  assertBool "MONOTONE: the low IRQ handler is routed for BOTH observers"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).irqHandlers lowIrq
        = some lowEndpoint ∧
      (ObservableState.onCore probeLabeling c0 highLabel probeState).irqHandlers lowIrq
        = some lowEndpoint))
  assertBool "STRICT: the high endpoint object is visible only to the high observer"
    (decide (((ObservableState.onCore probeLabeling c0 lowLabel probeState).objects
          highEndpoint).isSome = false ∧
      ((ObservableState.onCore probeLabeling c0 highLabel probeState).objects
          highEndpoint).isSome = true))
  -- `onCore_objects_label_invariant_off_cnode` (an equality of
  -- `Option KernelObject` values) has no runtime form: `KernelObject` carries
  -- RHTable-backed and function-typed components, so the equality is not
  -- decidable.  Its witness is the §2 elaboration-time example; what §3 can
  -- decide is the visibility half, immediately above and below.
  assertBool "STRICT: the low observer's object index is strictly smaller"
    (decide ((ObservableState.onCore probeLabeling c0 lowLabel probeState).objectIndex.length <
      (ObservableState.onCore probeLabeling c0 highLabel probeState).objectIndex.length))

/-- §3.6  Scheduling transparency (accepted covert channel CC-1) restated per
core: the four scheduling components are label-invariant, and each core carries
its own copy — so the channel exists once per core, not once per system. -/
private def runSchedulingTransparencyChecks : IO Unit := do
  IO.println "--- §3.6 scheduling transparency, per core (CC-1) ---"
  let stSplitDomains : SystemState :=
    { probeState with
      scheduler := (probeState.scheduler.setActiveDomainOnCore c1 ⟨3⟩).setDomainScheduleIndexOnCore
        c1 2 }
  assertBool "the four scheduling components are label-invariant on every core"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel stSplitDomains).activeDomain
          = (ObservableState.onCore probeLabeling c highLabel stSplitDomains).activeDomain ∧
        (ObservableState.onCore probeLabeling c lowLabel stSplitDomains).domainTimeRemaining
          = (ObservableState.onCore probeLabeling c highLabel stSplitDomains).domainTimeRemaining ∧
        (ObservableState.onCore probeLabeling c lowLabel stSplitDomains).domainSchedule
          = (ObservableState.onCore probeLabeling c highLabel stSplitDomains).domainSchedule ∧
        (ObservableState.onCore probeLabeling c lowLabel stSplitDomains).domainScheduleIndex
          = (ObservableState.onCore probeLabeling c highLabel stSplitDomains).domainScheduleIndex)))
  assertBool "onCore_schedulingTransparency applies on every core (theorem level)"
    (allCores.all (fun c =>
      have _h := onCore_schedulingTransparency probeLabeling c lowLabel highLabel stSplitDomains
      true))
  assertBool "the channel is PER CORE: cores 0 and 1 report different domains"
    (!decide ((ObservableState.onCore probeLabeling c0 lowLabel stSplitDomains).activeDomain
      = (ObservableState.onCore probeLabeling c1 lowLabel stSplitDomains).activeDomain))
  assertBool "…and different schedule indices"
    (!decide ((ObservableState.onCore probeLabeling c0 lowLabel stSplitDomains).domainScheduleIndex
      = (ObservableState.onCore probeLabeling c1 lowLabel stSplitDomains).domainScheduleIndex))
  assertBool "the system-wide domain schedule is shared by every core"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel stSplitDomains).domainSchedule
        = (ObservableState.onCore probeLabeling bootCoreId lowLabel stSplitDomains).domainSchedule)))

/-- §3.7  The SM8.B seed: a high thread scheduled on a remote core is invisible
to a low observer on **every** core — the shape `crossCoreNonInterference` will
generalise from a fixed pair of states to an arbitrary transition. -/
private def runCrossCoreInvisibilityChecks : IO Unit := do
  IO.println "--- §3.7 cross-core invisibility of a high remote thread ---"
  -- Schedule a second high thread on core 2 and re-queue core 1: a purely
  -- high-labelled reshuffle on cores 1 and 2.
  let stHighReshuffle : SystemState :=
    { probeState with
      scheduler := ((probeState.scheduler.setCurrentOnCore c2 (some highQueued)).setRunQueueOnCore
        c1 RunQueue.empty).setCurrentOnCore c1 none }
  assertBool "the low observer's slice is unchanged on EVERY core"
    (allCores.all (fun c =>
      decide (ObservableState.sliceOnCore probeLabeling c lowLabel stHighReshuffle
        = ObservableState.sliceOnCore probeLabeling c lowLabel probeState)))
  assertBool "…and the low observer's shared objectIndex is unchanged too"
    (allCores.all (fun c =>
      decide ((ObservableState.onCore probeLabeling c lowLabel stHighReshuffle).objectIndex
        = (ObservableState.onCore probeLabeling c lowLabel probeState).objectIndex)))
  assertBool "NON-VACUITY: the HIGH observer's slice DOES change (cores 1 and 2)"
    (!decide (ObservableState.sliceOnCore probeLabeling c1 highLabel stHighReshuffle
        = ObservableState.sliceOnCore probeLabeling c1 highLabel probeState) &&
     !decide (ObservableState.sliceOnCore probeLabeling c2 highLabel stHighReshuffle
        = ObservableState.sliceOnCore probeLabeling c2 highLabel probeState))
  assertBool "the high observer's core 0 slice is still unchanged (per-core locality)"
    (decide (ObservableState.sliceOnCore probeLabeling c0 highLabel stHighReshuffle
      = ObservableState.sliceOnCore probeLabeling c0 highLabel probeState))

def runSmpInformationFlowChecks : IO Unit := do
  IO.println "WS-SM SM8.A — Per-core observable state suite"
  IO.println "===================================="
  runFixtureChecks
  runObserverChecks
  runPartitionChecks
  runDecidableSliceChecks
  runIndependenceChecks
  runMonotonicityChecks
  runSchedulingTransparencyChecks
  runCrossCoreInvisibilityChecks
  IO.println "===================================="
  IO.println "All SM8.A per-core observable-state checks PASS."

end SeLe4n.Testing.SmpInformationFlow

def main : IO Unit :=
  SeLe4n.Testing.SmpInformationFlow.runSmpInformationFlowChecks
