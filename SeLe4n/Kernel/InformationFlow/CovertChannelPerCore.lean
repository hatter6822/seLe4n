-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

-- STATUS: staged for WS-SM SM8.B — the per-core enforcement boundary and the
-- SMP covert-channel inventory (docs/planning/SMP_INFORMATION_FLOW_PLAN.md
-- §3.4 / §3.5 / §5 SM8.B.6 … SM8.B.12).

import SeLe4n.Kernel.InformationFlow.NonInterferencePerCore
import SeLe4n.Kernel.API
import SeLe4n.Kernel.Scheduler.Operations.PerCoreDomain

/-!
# WS-SM SM8.B — the per-core enforcement boundary and the SMP covert channels

Plan `docs/planning/SMP_INFORMATION_FLOW_PLAN.md` §3.4 / §3.5 / §5 sub-tasks
SM8.B.6 … SM8.B.12.  `NonInterferencePerCore.lean` proves what the SMP kernel
*does not* leak; this module records what it *does*, and where the enforcement
that bounds it lives.

* §1 (SM8.B.6 / SM8.B.7) — `enforcementBoundaryPerCore`: the canonical
  enforcement-boundary classification extended by the one operation SMP adds,
  the two-phase-locking bracket, plus the completeness witness.
* §2 (SM8.B.8 / SM8.B.9 / SM8.B.10) — the accepted covert-channel inventory as
  data rather than prose, one entry per channel, each carrying the theorem that
  makes its status a checked fact: for a channel the model *does* carry, the
  transparency theorem; for one it does not, the exclusion theorem that says the
  channel is hardware-level and therefore outside a kernel projection's reach.
* §3 (SM8.B.11) — `endpointPolicyRestricted_perCore`.
* §4 (SM8.B.12) — the bridge from the release-grade (single-core) dispatch
  non-interference witnesses to the per-core statement.

Axiom-clean: every declaration depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`), checked exhaustively.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

-- ============================================================================
-- §1  SM8.B.6 / SM8.B.7 — the per-core enforcement boundary
-- ============================================================================
--
-- The canonical `enforcementBoundary` classifies every operation whose
-- authority the kernel derives, as policy-gated (a `securityFlowsTo` check),
-- capability-only (authority from capability possession) or read-only.  SMP
-- adds exactly one operation to that surface: the SM3 two-phase-locking
-- bracket `withLockSet`, which every `@[export]` body wraps its transition in
-- once SM3.C.9 lands.
--
-- Its class is **capability-only**, and for the same reason as `storeObject`'s
-- and `lifecycleRetypeObject`'s: it is an internal building block invoked under
-- an already-capability-guarded context, and it consults no information-flow
-- policy — the bracket cannot admit a flow the guarded transition would not
-- admit, because it does not carry data across a label boundary at all
-- (`withLockSet_preserves_projection`).  What it *does* add is the
-- lock-contention timing channel §2 registers as CC-5.
--
-- The plan's SM8.B.6 figure ("23 entries") was written against the `v0.31.2`
-- audited cut.  The live canonical boundary is 38 entries
-- (`enforcementBoundaryExtended_count`), so the per-core boundary is 39 —
-- re-anchored against the theorem, exactly as the plan's own SM8.A note
-- directs.  This module deliberately introduces a *separate* list rather than
-- editing the canonical one: SM8.E.3 is the sub-task that promotes the entry
-- into `enforcementBoundary` itself, and doing it here would move a count that
-- SM8.E has still to reconcile.

/-- SM8.B.6: **the operations the live SMP dispatch actually reaches**, for the
syscalls whose arm SM6 re-routed through a cross-core wrapper.

Read off `API.dispatchWithCapChecked` / `dispatchCapabilityOnly` arm by arm, not
from the plan: `.call` runs `endpointCallCrossCoreDispatchChecked`, `.reply` runs
`endpointReplyCrossCoreDispatchChecked`, `.replyRecv` runs `replyRecvBody` (the
two-leg composition), `.receive` runs the per-core `endpointReceiveDualOnCore`,
the two notification arms run their bound / wait cross-core dispatches, and
`.tcbSuspend` runs `suspendThreadOnCore`.

Each keeps the class its single-core counterpart carries — a cross-core wrapper
re-routes *where* a transition lands, never *what authority* it demands — and
`enforcementBoundaryPerCore_crossCore_classes_match` is the check on that.

**Read `.policyGated` as a property of the arm, not of the named function.**
Two of these entries name an operation that performs no flow check itself:
`.receive` runs the *unchecked* `endpointReceiveDualOnCore` because its enclosing
arm has already rejected a denied `endpoint→receiver` flow with `.flowDenied`
before reaching it, and `replyRecvBody` likewise runs under the arm's
`securityFlowsTo` guard on `replier→prevCaller`.  That is the same convention the
canonical boundary uses (`cspaceDelete` names `cspaceDeleteSlot`, not a
`…Checked` wrapper): the entry names the operation reached, the class records how
authority is derived on the path that reaches it.  Stated here because
`.policyGated "endpointReceiveDualOnCore"` would otherwise read as a claim that
the function gates, which it does not. -/
def crossCoreEnforcementEntries : List EnforcementClass :=
  [ .policyGated "endpointCallCrossCoreDispatchChecked"
  , .policyGated "endpointReplyCrossCoreDispatchChecked"
  , .policyGated "replyRecvBody"
  , .policyGated "endpointReceiveDualOnCore"
  , .policyGated "notificationSignalBoundCrossCoreDispatchChecked"
  , .policyGated "notificationWaitCrossCoreDispatchChecked"
  , .capabilityOnly "suspendThreadOnCore" ]

/-- SM8.B.6: the SMP enforcement boundary — the canonical classification, the
two-phase-locking bracket the per-object lock discipline introduces, and the
seven live cross-core wrappers.

The canonical entries are **kept**, not replaced: the boot-pinned
`syscallDispatchInner` still reaches the single-core wrappers, so both surfaces
are live and both must be classified. -/
def enforcementBoundaryPerCore : List EnforcementClass :=
  enforcementBoundaryExtended ++ [.capabilityOnly "withLockSet"] ++ crossCoreEnforcementEntries

/-- SM8.B.6: the per-core boundary has 46 entries — the live canonical 38, the
2PL bracket, and the seven cross-core wrappers.  Re-anchored at the SM8.A cut and
again in the fourth review round; `enforcementBoundaryExtended_count` is the
authority for the base figure. -/
theorem enforcementBoundaryPerCore_count : enforcementBoundaryPerCore.length = 46 := by rfl

/-- SM8.B.7 (completeness, part 1): the per-core boundary **extends** the
canonical one — it is the canonical list followed by the 2PL bracket and the
seven live cross-core wrappers, so no existing classification was dropped or
reclassified in the lift.  Additive by construction: `List.IsPrefix` is the
statement that the canonical list survives unmodified as a prefix. -/
theorem enforcementBoundaryPerCore_extends_canonical :
    enforcementBoundaryPerCore
      = enforcementBoundary ++ ([.capabilityOnly "withLockSet"] ++ crossCoreEnforcementEntries) :=
  rfl

/-- SM8.B.7: and the canonical list is a genuine prefix, so nothing in it moved
position either — the form a reader can use without unfolding the append. -/
theorem enforcementBoundary_prefix_of_perCore :
    enforcementBoundary <+: enforcementBoundaryPerCore :=
  ⟨[.capabilityOnly "withLockSet"] ++ crossCoreEnforcementEntries, rfl⟩

/-- SM8.B.7 (completeness, part 2): every `SyscallId` still maps to an entry
present in the per-core boundary.

`enforcementBoundaryComplete` checks the same property of the canonical list;
this re-checks it against the extended one, so a future edit that *replaces*
rather than appends is caught.  Decided rather than argued, and with `decide`
rather than `native_decide` — the Lean runtime evaluator stays out of the
trusted computing base (AF4-A).

This is the **single-core** half of the audit: it re-checks the canonical
mapping against the extended list, so a future edit that *replaces* rather than
appends is caught.  The SMP half — that the wrappers the live cross-core
dispatch reaches are classified — is
`enforcementBoundaryPerCore_is_complete_crossCore` below.  Both are needed: the
boot-pinned `syscallDispatchInner` still reaches the single-core wrappers.

Decided rather than argued, and with `decide` rather than `native_decide` — the
Lean runtime evaluator stays out of the trusted computing base (AF4-A). -/
def enforcementBoundaryPerCoreComplete : Bool :=
  SyscallId.all.all (fun sid =>
    let name := syscallIdToEnforcementName sid
    enforcementBoundaryPerCore.any (fun ec =>
      match ec with
      | .policyGated n | .capabilityOnly n | .readOnly n => n == name))

theorem enforcementBoundaryPerCore_is_complete : enforcementBoundaryPerCoreComplete = true := by
  decide

/-- SM8.B.6: **the operation each syscall reaches under SMP.**

Differs from `syscallIdToEnforcementName` at exactly the seven arms SM6
re-routed; every other syscall reaches the same operation it did before SMP, so
it falls through to the canonical mapping rather than being restated (a second
full copy would be a second thing to keep in sync). -/
def syscallIdToEnforcementNamePerCore : SyscallId → String
  | .call                => "endpointCallCrossCoreDispatchChecked"
  | .reply               => "endpointReplyCrossCoreDispatchChecked"
  | .replyRecv           => "replyRecvBody"
  | .receive             => "endpointReceiveDualOnCore"
  | .notificationSignal  => "notificationSignalBoundCrossCoreDispatchChecked"
  | .notificationWait    => "notificationWaitCrossCoreDispatchChecked"
  | .tcbSuspend          => "suspendThreadOnCore"
  | sid                  => syscallIdToEnforcementName sid

/-- SM8.B.7 (completeness, part 2b — **the SMP half**): every `SyscallId` maps,
*through the per-core mapping*, to an entry present in the per-core boundary.

This is the theorem the fourth review round asked for.  Its predecessor audited
the canonical table, whose `.call` entry is the single-core `endpointCallChecked`
— so it could return `true` with no entry corresponding to the operation the
live SMP dispatch actually reaches.  This one is built from the live cross-core
wrapper names, so that hole is closed. -/
def enforcementBoundaryPerCoreCompleteCrossCore : Bool :=
  SyscallId.all.all (fun sid =>
    let name := syscallIdToEnforcementNamePerCore sid
    enforcementBoundaryPerCore.any (fun ec =>
      match ec with
      | .policyGated n | .capabilityOnly n | .readOnly n => n == name))

theorem enforcementBoundaryPerCore_is_complete_crossCore :
    enforcementBoundaryPerCoreCompleteCrossCore = true := by decide

/-- SM8.B.7: the seven re-routed arms are genuinely re-routed — the per-core
mapping differs from the canonical one at exactly those syscalls, and nowhere
else.  A syscall silently added to (or dropped from) the cross-core surface
moves this count. -/
theorem syscallIdToEnforcementNamePerCore_differs_at_seven :
    (SyscallId.all.filter (fun sid =>
      decide (syscallIdToEnforcementNamePerCore sid ≠ syscallIdToEnforcementName sid))).length
      = 7 := by decide

/-- SM8.B.7: **a cross-core wrapper carries the same enforcement class as the
single-core operation it replaced.**  Re-routing a transition to another core
changes where it lands, not what authority it demands, and this is where that
claim is checked rather than asserted: for each re-routed syscall, the class of
its per-core entry equals the class of its canonical one. -/
theorem enforcementBoundaryPerCore_crossCore_classes_match :
    ([SyscallId.call, .reply, .replyRecv, .receive, .notificationSignal,
      .notificationWait, .tcbSuspend].all (fun sid =>
        let canonical := enforcementBoundary.find? (fun ec =>
          match ec with
          | .policyGated n | .capabilityOnly n | .readOnly n =>
              n == syscallIdToEnforcementName sid)
        let perCore := enforcementBoundaryPerCore.find? (fun ec =>
          match ec with
          | .policyGated n | .capabilityOnly n | .readOnly n =>
              n == syscallIdToEnforcementNamePerCore sid)
        match canonical, perCore with
        | some (.policyGated _), some (.policyGated _) => true
        | some (.capabilityOnly _), some (.capabilityOnly _) => true
        | some (.readOnly _), some (.readOnly _) => true
        | _, _ => false)) = true := by decide

/-- SM8.B.7 (completeness, part 3): the entry SMP adds is genuinely new — the
canonical boundary does not already classify `withLockSet`, so the count really
does go up by one and the extension is not a silent duplicate. -/
theorem enforcementBoundaryPerCore_entry_is_new :
    enforcementBoundary.any (fun ec =>
      match ec with
      | .policyGated n | .capabilityOnly n | .readOnly n => n == "withLockSet") = false := by
  decide

-- ============================================================================
-- §2  SM8.B.8 / SM8.B.9 / SM8.B.10 — the accepted covert-channel inventory
-- ============================================================================

/-- SM8.B.8: how much a channel can carry, on the coarse scale the plan's
risk inventory uses. -/
inductive CovertChannelSeverity where
  | low
  | medium
  | high
  deriving Repr, DecidableEq

/-- SM8.B.8: an **accepted** covert channel — one the model does not close, is
not going to close before v1.0.0, and therefore has to name.

`modelVisible` is the field that keeps the inventory honest.  A channel whose
information flows through `ObservableState` is one the projection *carries*
(the scheduling state, CC-1, is the archetype); a channel with
`modelVisible := false` is one the projection provably excludes, so it exists
only because a real observer has instruments a kernel-level projection cannot
take away — a clock, a cache, a TLB.  Recording the distinction as data rather
than as prose is what lets `acceptedCovertChannel_modelVisible_count` state it
as a checked fact.

`perCoreInstance` records the SMP-specific part: a channel carried by per-core
state exists **once per core**, so its aggregate bandwidth scales with
`numCores`. -/
structure CovertChannel where
  /-- The plan's §3.5 inventory number (CC-`channelId`).  Carried as data so the
      inventory's numbering is `rfl`-checkable rather than a comment. -/
  channelId : Nat
  /-- Short identifier, unique within the inventory. -/
  name : String
  /-- What the channel carries. -/
  description : String
  /-- What bounds it today, and what would close it. -/
  mitigation : String
  /-- Coarse capacity class. -/
  severity : CovertChannelSeverity
  /-- Whether the information flows through `ObservableState` (`true`) or only
      through hardware the projection excludes (`false`). -/
  modelVisible : Bool
  /-- Whether SMP gives the channel one instance per core. -/
  perCoreInstance : Bool
  deriving Repr, DecidableEq

/-- CC-1 (V6-L): the domain-scheduling state passes through the projection
unfiltered.  Witnessed by `acceptedCovertChannel_scheduling` (two clearances see
the same value) and, per core, by `onCore_schedulingTransparency` — which is
stated against the **raw** scheduler reads, so it is evidence about the
channel's content rather than merely about two clearances agreeing.  Under SMP
each core carries its own `activeDomain` / `domainTimeRemaining` /
`domainScheduleIndex`, so the channel exists once per core. -/
def acceptedCovertChannel_scheduling_perCore : CovertChannel :=
  { channelId := 1
    name := "scheduling state"
    description :=
      "activeDomain, domainTimeRemaining and domainScheduleIndex are projected \
       unfiltered to every observer; under SMP each core carries its own."
    mitigation :=
      "Temporal partitioning: each domain gets a guaranteed quantum regardless \
       of other domains' behaviour. No capacity bound is claimed: only the \
       schedule-index component has a bounded alphabet \
       (schedulingChannelIndex_alphabet_bounded), and domainTimeRemaining is an \
       unrestricted Nat carried unfiltered \
       (schedulingChannel_not_bounded_by_scheduleLength)."
    severity := .low
    modelVisible := true
    perCoreInstance := true }

/-- CC-2 (V6-L): the machine timer.  Deliberately **excluded** from
`ObservableState`; `onCore_machineTimer` restates the exclusion per core.  It
stays in the inventory because the exclusion is a statement about the model — a
real observer reads `CNTVCT_EL0`. -/
def acceptedCovertChannel_machineTimer : CovertChannel :=
  { channelId := 2
    name := "machine timer"
    description :=
      "A monotonic counter an observer can read directly on hardware; excluded \
       from the projection (onCore_machineTimer) so no model-level flow exists."
    mitigation :=
      "Hardware partitioning (CCA/MPAM) or a virtualised per-partition counter; \
       deferred to WS-W."
    severity := .medium
    modelVisible := false
    perCoreInstance := true }

/-- CC-3 (V6-L): TCB metadata (priority, IPC state) of a thread the observer can
already see.  Model-visible by construction — the projection carries the TCB. -/
def acceptedCovertChannel_tcbMetadata : CovertChannel :=
  { channelId := 3
    name := "TCB metadata"
    description :=
      "Priority and IPC state of any thread the observer can observe; seL4 does \
       not treat thread priority as confidential."
    mitigation :=
      "Labelling discipline: do not place threads whose priority is confidential \
       in a domain that flows to the observer."
    severity := .low
    modelVisible := true
    perCoreInstance := false }

/-- CC-4 (V6-L): object-store metadata — which object ids exist, filtered by
label.  Model-visible: `projectObjectIndex` is part of the projection. -/
def acceptedCovertChannel_objectStoreMetadata : CovertChannel :=
  { channelId := 4
    name := "object store metadata"
    description :=
      "The label-filtered object index reveals the observable object population, \
       hence indirectly the system's allocation behaviour."
    mitigation :=
      "The filter itself: only ids whose label flows to the observer appear."
    severity := .low
    modelVisible := true
    perCoreInstance := false }

/-- SM8.B.8 (plan Definition 3.4.1): **CC-5 — lock-contention timing.**

When core `c` spins on a lock held by core `c'`, the spin duration measures
`c'`'s critical-section length, which may correlate with confidential data on
`c'`.

`modelVisible := false` is a proven fact, not an assertion:
`withLockSet_preserves_projection` says the 2PL bracket leaves the observer's
projection *identical*, with no hypothesis on the lock set — because
`projectKernelObject` erases the per-object `lock` field (SM8.B.4).  Without
that erasure the channel would also be a **state** channel: `RwLockState`
carries `writerHeld`, `readers` and `waiters`, all core identities, so an
observer that can see an object would read off which cores are operating on it —
the placement channel WS-SM SM5.B closed on `TCB.cpuAffinity`, re-opened through
another field.  What remains is timing, and timing only. -/
def acceptedCovertChannel_lockContention : CovertChannel :=
  { channelId := 5
    name := "lock-contention timing"
    description :=
      "A core spinning on a contended lock can measure the duration of another \
       core's critical section, leaking information about the holder. The model \
       carries no state flow (withLockSet_preserves_projection); the channel is \
       the spin time itself."
    mitigation :=
      "WS-W (CCA/MPAM partitioning) narrows it via partition-aware lock \
       scheduling. Closing it outright needs lock-free structures or per-domain \
       lock partitioning, both out of scope for v1.0.0."
    severity := .medium
    modelVisible := false
    perCoreInstance := true }

/-- SM8.B.8: **CC-6 — per-core TLB residency** (registered at the SM8.A cut).
`onCore_perCoreTlb` proves the SM7.C view outside the observable read set, so
there is no model-level flow; a real observer times its own accesses. -/
def acceptedCovertChannel_tlbResidency : CovertChannel :=
  { channelId := 6
    name := "per-core TLB residency"
    description :=
      "Whether a translation is cached on this core is measurable by timing an \
       access; the model excludes the view (onCore_perCoreTlb)."
    mitigation :=
      "Hardware partitioning (CCA/MPAM); the SM7.B shootdown protocol bounds \
       staleness but not observability. Deferred to WS-W."
    severity := .medium
    modelVisible := false
    perCoreInstance := true }

/-- SM8.B.8: **CC-7 — per-core instruction-cache residency** (registered at the
SM8.A cut).  The structural sibling of CC-6; `onCore_perCoreICache` is its
exclusion theorem. -/
def acceptedCovertChannel_icacheResidency : CovertChannel :=
  { channelId := 7
    name := "per-core instruction-cache residency"
    description :=
      "A resident instruction line is evidence of a past fetch, measurable by \
       timing; the model excludes the view (onCore_perCoreICache)."
    mitigation :=
      "Hardware partitioning (CCA/MPAM); the SM7.D maintenance broadcast bounds \
       staleness but not observability. Deferred to WS-W."
    severity := .medium
    modelVisible := false
    perCoreInstance := true }

/-- SM8.B.10: the accepted covert channels under SMP, in the plan's §3.5 order.
CC-1 … CC-4 are the pre-SMP inventory; CC-5 is SM8.B.8's lock-contention
channel; CC-6 and CC-7 were registered at the SM8.A cut when SM7.C and SM7.D
mounted the per-core TLB and instruction-cache views. -/
def acceptedCovertChannelsPerCore : List CovertChannel :=
  [ acceptedCovertChannel_scheduling_perCore
  , acceptedCovertChannel_machineTimer
  , acceptedCovertChannel_tcbMetadata
  , acceptedCovertChannel_objectStoreMetadata
  , acceptedCovertChannel_lockContention
  , acceptedCovertChannel_tlbResidency
  , acceptedCovertChannel_icacheResidency ]

/-- SM8.B.10: **seven** accepted covert channels under SMP.

The plan's sub-task line reads "= 5", written before CC-6 and CC-7 existed: the
SM8.A cut registered them when SM7.C mounted `SystemState.perCoreTlb` and SM7.D
mounted `SystemState.perCoreICache`, and the plan's §3.5 inventory lists all
seven.  Asserting 5 here would produce a *false* count, so the figure is
re-anchored against the inventory — the same correction the plan applies to its
own 32→35 constructor and 22→38 boundary figures. -/
theorem acceptedCovertChannel_perCoreCount : acceptedCovertChannelsPerCore.length = 7 := by rfl

/-- SM8.B.10: the inventory carries the plan's §3.5 numbering, in order and
without repetition — CC-1 … CC-7.  Distinctness of the entries follows, so the
count above counts channels rather than list cells, and a re-ordering or a
duplicated entry is a build failure. -/
theorem acceptedCovertChannel_perCore_ids :
    acceptedCovertChannelsPerCore.map CovertChannel.channelId = [1, 2, 3, 4, 5, 6, 7] := rfl

/-- SM8.B.10: exactly three of the seven are carried by the model
(`ObservableState`); the other four exist only through hardware the projection
excludes.  The split is what the `modelVisible` field exists to record, and
pinning it means a future channel cannot be filed on the wrong side by
accident. -/
theorem acceptedCovertChannel_modelVisible_count :
    (acceptedCovertChannelsPerCore.filter CovertChannel.modelVisible).length = 3 := rfl

/-- SM8.B.10: five of the seven have one instance **per core** under SMP, so
their aggregate capacity scales with `numCores`.  The two that do not are the
label-filtered metadata channels, which read shared state. -/
theorem acceptedCovertChannel_perCoreInstance_count :
    (acceptedCovertChannelsPerCore.filter CovertChannel.perCoreInstance).length = 5 := rfl

/-- SM8.B.9 (the mitigation note, as a checked fact rather than a comment): the
four channels deferred to WS-W hardware partitioning are exactly the four the
model does **not** carry — which is why no kernel-level change can close them,
and why the remaining three are bounded by kernel mechanisms instead (temporal
partitioning for CC-1, the label filter for CC-3 and CC-4).

Stated over the seven named constants rather than by quantifying over the list:
the point is that the classification is exhaustive, and enumerating it is what
makes a new entry impossible to add without deciding which side it falls on. -/
theorem acceptedCovertChannel_hardwareChannels_are_not_modelVisible :
    acceptedCovertChannel_machineTimer.modelVisible = false ∧
      acceptedCovertChannel_lockContention.modelVisible = false ∧
      acceptedCovertChannel_tlbResidency.modelVisible = false ∧
      acceptedCovertChannel_icacheResidency.modelVisible = false ∧
      acceptedCovertChannel_scheduling_perCore.modelVisible = true ∧
      acceptedCovertChannel_tcbMetadata.modelVisible = true ∧
      acceptedCovertChannel_objectStoreMetadata.modelVisible = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- SM8.B.10 (the SMP delta): CC-5, CC-6 and CC-7 are the three channels SMP
adds, and all three are per-core hardware channels.  The pre-SMP inventory
(CC-1 … CC-4) is unchanged — SM8 widens the inventory, it does not reclassify
what was already in it. -/
theorem acceptedCovertChannel_smp_additions :
    (acceptedCovertChannelsPerCore.filter (fun ch => decide (ch.channelId ≥ 5))).length = 3 ∧
      acceptedCovertChannel_lockContention.perCoreInstance = true ∧
      acceptedCovertChannel_tlbResidency.perCoreInstance = true ∧
      acceptedCovertChannel_icacheResidency.perCoreInstance = true :=
  ⟨rfl, rfl, rfl, rfl⟩

/-- SM8.B.8 (the CC-5 witness): the lock-contention channel is registered with
`modelVisible := false`, and `withLockSet_preserves_projection` is why.  Stated
here so the inventory entry and the theorem that justifies it cannot drift
apart: this fails if the entry is reclassified without the theorem changing. -/
theorem acceptedCovertChannel_lockContention_is_timing_only
    {α : Type} (ctx : LabelingContext) (observer : IfObserver)
    (S : SeLe4n.Kernel.Concurrency.LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (hInv : s.objects.invExt)
    (hActionInv : ∀ s', s'.objects.invExt → ((action s').1).objects.invExt)
    (hAction : ∀ s', s'.objects.invExt →
      projectState ctx observer (action s').1 = projectState ctx observer s') :
    acceptedCovertChannel_lockContention.modelVisible = false ∧
      projectState ctx observer (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1
        = projectState ctx observer s :=
  ⟨rfl, withLockSet_preserves_projection ctx observer S core action s hInv hActionInv hAction⟩

/-- SM8.B.8 (the CC-6 / CC-7 witnesses): both hardware-residency channels are
registered `modelVisible := false`, and the SM8.A exclusion theorems are why. -/
theorem acceptedCovertChannel_residency_excluded_from_view (ctx : LabelingContext)
    (L : SecurityLabel) (s : SystemState) (c : CoreId)
    (vTlb : Vector TlbState SeLe4n.Kernel.Concurrency.numCores)
    (vIcache : Vector ICacheState SeLe4n.Kernel.Concurrency.numCores) :
    acceptedCovertChannel_tlbResidency.modelVisible = false ∧
      acceptedCovertChannel_icacheResidency.modelVisible = false ∧
      ObservableState.onCore ctx c L { s with perCoreTlb := vTlb }
        = ObservableState.onCore ctx c L s ∧
      ObservableState.onCore ctx c L { s with perCoreICache := vIcache }
        = ObservableState.onCore ctx c L s :=
  ⟨rfl, rfl, onCore_perCoreTlb ctx L s c vTlb, onCore_perCoreICache ctx L s c vIcache⟩

/-- SM8.B.8 (the CC-1 witness): the scheduling channel is registered
`modelVisible := true`, and `onCore_schedulingTransparency` is why — the
observer reads core `c`'s raw scheduler slots. -/
theorem acceptedCovertChannel_scheduling_is_model_visible (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (s : SystemState) :
    acceptedCovertChannel_scheduling_perCore.modelVisible = true ∧
      (ObservableState.onCore ctx c L s).activeDomain = s.scheduler.activeDomainOnCore c :=
  ⟨rfl, (onCore_schedulingTransparency ctx c L s).1⟩

/-- SM8.B.8 (the CC-2 witness): the machine timer is registered
`modelVisible := false`, and `onCore_machineTimer` is why — advancing the
counter moves no per-core observer's view at all. -/
theorem acceptedCovertChannel_machineTimer_excluded_from_view (ctx : LabelingContext)
    (L : SecurityLabel) (s : SystemState) (c : CoreId) (t : Nat) :
    acceptedCovertChannel_machineTimer.modelVisible = false ∧
      ObservableState.onCore ctx c L { s with machine := { s.machine with timer := t } }
        = ObservableState.onCore ctx c L s :=
  ⟨rfl, onCore_machineTimer ctx L s c t⟩

/-- SM8.B.8 (the CC-3 witness): TCB metadata is registered `modelVisible := true`,
and this says **why in terms of the metadata itself** — for a thread the observer
can already see, the projected TCB carries the *same* `priority` and the *same*
`ipcState` as the real one.

The fifth review round rejected the previous form, which asserted only
`(onCore …).objects = projectObjects …`.  That is a component identity: it
never selects a TCB and never mentions either field, so erasing `priority` from
`projectKernelObject`'s `.tcb` arm would have left it — and every inventory
check built on it — green while invalidating the `modelVisible := true`
classification it exists to justify.  Both equations below are `rfl` *because*
those fields survive the projection; strip either one and this theorem stops
compiling.

Note what this still does **not** say: that every TCB is visible.  The filter is
real, which is what the `hObservable` premise carries — CC-3 is about the
metadata of threads the observer can already see. -/
theorem acceptedCovertChannel_tcbMetadata_is_model_visible (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (s : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hObservable : objectObservable ctx (IfObserver.ofLabel L) tid.toObjId = true)
    (hLookup : s.getTcb? tid = some tcb) :
    acceptedCovertChannel_tcbMetadata.modelVisible = true ∧
      ∃ projected : TCB,
        (ObservableState.onCore ctx c L s).objects tid.toObjId = some (.tcb projected)
        ∧ projected.priority = tcb.priority
        ∧ projected.ipcState = tcb.ipcState := by
  refine ⟨rfl, ?_⟩
  rw [onCore_objects ctx c L s]
  unfold projectObjects
  rw [if_pos hObservable, (SystemState.getTcb?_eq_some_iff s tid tcb).mp hLookup]
  exact ⟨_, rfl, rfl, rfl⟩

/-- SM8.B.8 (the CC-3 component identity): the observer's `objects` view *is* the
label-filtered object store.  Kept as its own statement — it is true and used —
but it is deliberately no longer the channel's witness, because it holds
independently of which TCB fields survive projection. -/
theorem onCore_objects_eq_projectObjects (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (s : SystemState) :
    (ObservableState.onCore ctx c L s).objects
      = projectObjects ctx (IfObserver.ofLabel L) s :=
  onCore_objects ctx c L s

/-- SM8.B.8 (the CC-4 witness): object-store metadata is registered
`modelVisible := true`, and `onCore_objectIndex` is why — the label-filtered
object index is a component of the observer's view, so the observable object
population is carried by the model rather than merely inferable from hardware. -/
theorem acceptedCovertChannel_objectStoreMetadata_is_model_visible (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (s : SystemState) :
    acceptedCovertChannel_objectStoreMetadata.modelVisible = true ∧
      (ObservableState.onCore ctx c L s).objectIndex
        = projectObjectIndex ctx (IfObserver.ofLabel L) s :=
  ⟨rfl, onCore_objectIndex ctx c L s⟩

-- ----------------------------------------------------------------------------
-- SM8.B.9 — what is actually bounded about CC-1, and what is not
-- ----------------------------------------------------------------------------
--
-- The fourth review round found this entry's mitigation citing
-- `schedulingCovertChannel_bounded_width` for a `log2(|domainSchedule|)`
-- bits-per-switch figure.  That theorem proves three definitional equalities
-- (the projections are the raw scheduler reads) and contains no cardinality,
-- frequency or capacity argument -- its own docstring's "bounded to exactly 4
-- observable values" counts *components*, not values.  The two theorems below
-- replace the unsupported figure with what is true: one component has a bounded
-- alphabet, and the others do not, so schedule length alone bounds nothing.

/-- SM8.B.9: **the one genuinely bounded component of CC-1.**  Under the
scheduler's own index-bounds invariant, the observed `domainScheduleIndex` on
any core is either reading an empty schedule (single-domain mode, one value) or
lies strictly below `|domainSchedule|`.

So the *index* component's alphabet has at most `max 1 |domainSchedule|`
elements, and that -- not the whole channel -- is what a
`log2(|domainSchedule|)` figure can describe. -/
theorem schedulingChannelIndex_alphabet_bounded (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState)
    (hBounds : domainScheduleIndexInBoundsOnCore s c) :
    s.scheduler.domainSchedule = [] ∨
      (ObservableState.onCore ctx c L s).domainScheduleIndex
        < (ObservableState.onCore ctx c L s).domainSchedule.length := by
  rcases hBounds with hEmpty | hLt
  · exact Or.inl hEmpty
  · exact Or.inr (by
      rw [(onCore_schedulingTransparency ctx c L s).2.2.2,
        (onCore_schedulingTransparency ctx c L s).2.2.1]
      exact hLt)

/-- SM8.B.9 (**the load-bearing negative**): schedule length does *not* bound
CC-1.  `domainTimeRemaining` is an unrestricted `Nat` carried through the
projection unfiltered, so for any two values -- however far apart, and with the
schedule and the index held fixed -- the observer distinguishes the two states.

This is why the entry's mitigation no longer claims a bits-per-switch figure:
bounding the channel would need a range hypothesis on the quantum and a
switch-frequency hypothesis, neither of which the model carries.  Temporal
partitioning is still the right mitigation; it is just not a proven capacity
bound. -/
theorem schedulingChannel_not_bounded_by_scheduleLength (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) (t₁ t₂ : Nat) (hNe : t₁ ≠ t₂) :
    (ObservableState.onCore ctx c L
        { s with scheduler := s.scheduler.setDomainTimeRemainingOnCore c t₁ }).domainTimeRemaining
      ≠ (ObservableState.onCore ctx c L
          { s with scheduler := s.scheduler.setDomainTimeRemainingOnCore c t₂ }).domainTimeRemaining := by
  rw [(onCore_schedulingTransparency ctx c L _).2.1,
    (onCore_schedulingTransparency ctx c L _).2.1]
  simpa using hNe

-- ----------------------------------------------------------------------------
-- The classification is exhaustive *and* evidence-bound
-- ----------------------------------------------------------------------------
--
-- The seven witnesses above are individually real, but on their own they leave
-- the same hole the fourth review round found in the count theorems: nothing
-- forces a *new* entry to have one, and nothing forces an existing entry's
-- `modelVisible` literal to match a projection theorem rather than merely
-- matching itself.  `CovertChannelId` closes that by making the inventory a
-- total function out of a finite enum: a new channel is a new constructor, and
-- a new constructor is a missing case in every table below.

/-- SM8.B.8: the inventory's index set.  An enum rather than a `Nat`, so the
tables below are exhaustive by pattern match. -/
inductive CovertChannelId where
  | schedulingState
  | machineTimer
  | tcbMetadata
  | objectStoreMetadata
  | lockContention
  | tlbResidency
  | icacheResidency
  deriving DecidableEq, Repr

def CovertChannelId.all : List CovertChannelId :=
  [.schedulingState, .machineTimer, .tcbMetadata, .objectStoreMetadata, .lockContention,
   .tlbResidency, .icacheResidency]

/-- SM8.B.8: the entry each id names. -/
def covertChannelEntry : CovertChannelId → CovertChannel
  | .schedulingState => acceptedCovertChannel_scheduling_perCore
  | .machineTimer => acceptedCovertChannel_machineTimer
  | .tcbMetadata => acceptedCovertChannel_tcbMetadata
  | .objectStoreMetadata => acceptedCovertChannel_objectStoreMetadata
  | .lockContention => acceptedCovertChannel_lockContention
  | .tlbResidency => acceptedCovertChannel_tlbResidency
  | .icacheResidency => acceptedCovertChannel_icacheResidency

/-- SM8.B.8: **the projection theorem that justifies each entry's
`modelVisible`**, compile-time-validated through `niName!`.

This is the table the fourth review round asked for.  Every id must name a
theorem, the macro rejects a name that does not resolve, and each named theorem
states the entry's `modelVisible` literal *conjoined with* the projection fact
that makes it true — so a reclassification without a matching change to the
projection breaks the witness, not just this string. -/
def covertChannelEvidence : CovertChannelId → String
  | .schedulingState => niName! acceptedCovertChannel_scheduling_is_model_visible
  | .machineTimer => niName! acceptedCovertChannel_machineTimer_excluded_from_view
  | .tcbMetadata => niName! acceptedCovertChannel_tcbMetadata_is_model_visible
  | .objectStoreMetadata => niName! acceptedCovertChannel_objectStoreMetadata_is_model_visible
  | .lockContention => niName! acceptedCovertChannel_lockContention_is_timing_only
  | .tlbResidency => niName! acceptedCovertChannel_residency_excluded_from_view
  | .icacheResidency => niName! acceptedCovertChannel_residency_excluded_from_view

/-- SM8.B.8: the id-indexed inventory **is** the list one, entry for entry and in
order.  Without this the enum would be a second inventory that could drift from
the first. -/
theorem covertChannelEntry_eq_inventory :
    CovertChannelId.all.map covertChannelEntry = acceptedCovertChannelsPerCore := rfl

/-- SM8.B.8: every id has evidence — no entry carries an empty citation.  Trivial
to read, load-bearing to have: with `covertChannelEvidence` total, adding a
channel without deciding what proves its classification is a compile error, and
this rules out discharging that obligation with `""`. -/
theorem covertChannelEvidence_nonempty :
    ∀ id : CovertChannelId, (covertChannelEvidence id).length > 0 := by
  intro id; cases id <;> decide

/-- SM8.B.8: the two residency channels share a witness (it proves both
exclusions at once) and every other channel has its own.  Pinned so a reader
knows the sharing is intentional rather than a copy-paste. -/
theorem covertChannelEvidence_shared_only_for_residency :
    (CovertChannelId.all.map covertChannelEvidence).eraseDups.length = 6 := by decide


-- ============================================================================
-- §3  SM8.B.11 — `endpointPolicyRestricted_perCore`
-- ============================================================================

/-- SM8.B.11: the per-core form of the V6-G endpoint-policy restriction — a
per-endpoint policy override may only *restrict* the global policy, and must do
so as seen from every core.

**The quantifier here is vacuous, deliberately and provably.**  `_c` is unused
because `endpointPolicyRestricted` mentions no state and no core: it is a
property of two policies.  This is the SM4.D `…_smp` idiom applied for uniformity
of naming, and `endpointPolicyRestricted_perCore_iff` is the *proof* that it is
notation rather than content — stated as an `iff` precisely so no reader has to
take the claim on trust.

The security content SMP actually adds is not here but in
`endpointFlowCheckAtCore` below: the gate as the kernel *resolves* it does depend
on the state and the core, and the theorem worth having is that its only such
dependence is through which thread is the subject. -/
def endpointPolicyRestricted_perCore (globalPolicy : DomainFlowPolicy)
    (epPolicy : EndpointFlowPolicy) : Prop :=
  ∀ _c : CoreId, endpointPolicyRestricted globalPolicy epPolicy

theorem endpointPolicyRestricted_perCore_iff (globalPolicy : DomainFlowPolicy)
    (epPolicy : EndpointFlowPolicy) :
    endpointPolicyRestricted_perCore globalPolicy epPolicy ↔
      endpointPolicyRestricted globalPolicy epPolicy :=
  ⟨fun h => h bootCoreId, fun h _ => h⟩

theorem endpointPolicyRestricted_perCore_at (globalPolicy : DomainFlowPolicy)
    (epPolicy : EndpointFlowPolicy) (c : CoreId)
    (h : endpointPolicyRestricted_perCore globalPolicy epPolicy) :
    endpointPolicyRestricted globalPolicy epPolicy := h c

/-- SM8.B.11: with no endpoint overrides the per-core restriction is trivially
satisfied, on every core (the per-core lift of
`endpointPolicyRestricted_no_overrides`). -/
theorem endpointPolicyRestricted_perCore_no_overrides (globalPolicy : DomainFlowPolicy) :
    endpointPolicyRestricted_perCore globalPolicy { endpointPolicy := fun _ => none } :=
  fun _ => endpointPolicyRestricted_no_overrides globalPolicy

/-- SM8.B.11: **the endpoint flow gate as the kernel resolves it in context** —
at state `st`, on core `c`, for the thread currently running there, sending to
`endpointId`.

Unlike `endpointFlowCheck`, this genuinely reads the system state and the core:
it has to, because the *subject* of a flow is whoever is running.  Introducing it
is what makes the state-independence claim below a theorem rather than a
tautology — a claim about `endpointFlowCheck` itself could only ever be `rfl`,
since that function takes neither a state nor a core. -/
def endpointFlowCheckAtCore (ctx : GenericLabelingContext) (epPolicy : EndpointFlowPolicy)
    (endpointId : SeLe4n.ObjId) (st : SystemState) (c : CoreId) : Bool :=
  match st.scheduler.currentOnCore c with
  | none => false
  | some tid =>
      endpointFlowCheck ctx epPolicy endpointId
        (ctx.threadDomainOf tid) (ctx.endpointDomainOf endpointId)

/-- SM8.B.11 (**the substantive SMP fact**): the resolved gate depends on the
state and the core **only** through which thread is the subject.

Two states and two cores that agree on the current thread give the same
decision — so the gate consults no other per-core coordinate: not the core's
active domain, not its run queue, not its register bank, not its identity.  This
would be *false* for a gate that (say) let a core's active domain widen what its
current thread may send to, which is exactly the sort of SMP-introduced
domain-confusion bug the theorem excludes. -/
theorem endpointFlowCheckAtCore_depends_only_on_subject (ctx : GenericLabelingContext)
    (epPolicy : EndpointFlowPolicy) (endpointId : SeLe4n.ObjId)
    (st₁ st₂ : SystemState) (c₁ c₂ : CoreId)
    (hSubject : st₁.scheduler.currentOnCore c₁ = st₂.scheduler.currentOnCore c₂) :
    endpointFlowCheckAtCore ctx epPolicy endpointId st₁ c₁
      = endpointFlowCheckAtCore ctx epPolicy endpointId st₂ c₂ := by
  unfold endpointFlowCheckAtCore
  rw [hSubject]

/-- SM8.B.11 (the SMP corollary, via SM8.B.2's confinement machinery): **a
transition running on other cores cannot flip core `c`'s flow gate.**

So an SMP kernel cannot be made to admit a denied flow by rescheduling: whatever
another core is doing, core `c`'s enforcement decision for its own current
thread is exactly what it was.  Note this consumes
`observableSlotsConfinedToCores` — the same write-set discipline the cross-core
non-interference results use — rather than re-deriving anything. -/
theorem endpointFlowCheckAtCore_stable_under_confined_transition
    (ctx : GenericLabelingContext) (epPolicy : EndpointFlowPolicy)
    (endpointId : SeLe4n.ObjId) {st st' : SystemState} {c : CoreId} {cs : List CoreId}
    (hne : c ∉ cs) (hRuns : observableSlotsConfinedToCores st st' cs) :
    endpointFlowCheckAtCore ctx epPolicy endpointId st' c
      = endpointFlowCheckAtCore ctx epPolicy endpointId st c :=
  endpointFlowCheckAtCore_depends_only_on_subject ctx epPolicy endpointId st' st c c
    (hRuns.agreeOn hne).current

/-- SM8.B.11 (non-vacuity of the *stability* claim): the resolved gate is not a
constant function — it really does move when the subject changes.  Without this,
`…_depends_only_on_subject` and `…_stable_under_confined_transition` would be
satisfied by a gate that always returned `false`.

The subject is a **non-sentinel** `ThreadId`: `ThreadId.isReserved` is
`val = 0`, so a state whose current thread is `⟨0⟩` violates
`currentThreadValidOnCore` and would make this a witness over an unreachable
state (PR #861 review).

What the review also asked for — a subject "backed by a real TCB" — is
deliberately *not* added, and the reason is the point of the theorem above:
`endpointFlowCheckAtCore` reads `currentOnCore` and the labeling context's
domain maps, and **never touches the object store**, so the presence or content
of a TCB cannot change its value.  Requiring one would suggest the gate consults
state it provably does not consult. -/
theorem endpointFlowCheckAtCore_is_not_constant :
    ∃ (ctx : GenericLabelingContext) (epPolicy : EndpointFlowPolicy)
      (endpointId : SeLe4n.ObjId) (st₁ st₂ : SystemState) (c : CoreId)
      (subject : SeLe4n.ThreadId), subject.isReserved = false ∧
      st₁.scheduler.currentOnCore c = some subject ∧
      endpointFlowCheckAtCore ctx epPolicy endpointId st₁ c
        ≠ endpointFlowCheckAtCore ctx epPolicy endpointId st₂ c := by
  refine ⟨{ policy := { canFlow := fun _ _ => true }
            objectDomainOf := fun _ => ⟨0⟩, threadDomainOf := fun _ => ⟨0⟩
            endpointDomainOf := fun _ => ⟨0⟩, serviceDomainOf := fun _ => ⟨0⟩ },
          { endpointPolicy := fun _ => none }, ⟨0⟩,
          { (default : SystemState) with scheduler :=
              (default : SystemState).scheduler.setCurrentOnCore bootCoreId (some ⟨1⟩) },
          (default : SystemState), bootCoreId, ⟨1⟩, by decide, ?_, ?_⟩
  · simp only [SchedulerState.setCurrentOnCore_currentOnCore_self]
  · simp only [endpointFlowCheckAtCore, SchedulerState.setCurrentOnCore_currentOnCore_self]
    decide

/-- SM8.B.11: under the per-core restriction, an endpoint flow admitted at any
core is admitted by the global policy — the per-core lift of
`endpointFlowCheck_restricted_subset`, which is the form SM8.C's cross-core
declassification audit consumes. -/
theorem endpointFlowCheck_restricted_subset_perCore (ctx : GenericLabelingContext)
    (epPolicy : EndpointFlowPolicy) (endpointId : SeLe4n.ObjId)
    (src dst : SecurityDomain) (c : CoreId)
    (hRestricted : endpointPolicyRestricted_perCore ctx.policy epPolicy)
    (hFlow : endpointFlowCheck ctx epPolicy endpointId src dst = true) :
    genericFlowCheck ctx src dst = true :=
  endpointFlowCheck_restricted_subset ctx epPolicy endpointId src dst
    (endpointPolicyRestricted_perCore_at ctx.policy epPolicy c hRestricted) hFlow

/-- SM8.B.11 (non-vacuity): the restriction hypothesis is **load-bearing**.  An
endpoint override that admits everything, over a global policy that admits
nothing, is a policy bypass: the endpoint check says `true` where the global
check says `false`.  So `endpointFlowCheck_restricted_subset_perCore` is not a
theorem about a vacuous premise. -/
theorem endpointPolicyRestricted_perCore_is_necessary :
    ∃ (ctx : GenericLabelingContext) (epPolicy : EndpointFlowPolicy)
      (endpointId : SeLe4n.ObjId) (src dst : SecurityDomain),
      endpointFlowCheck ctx epPolicy endpointId src dst = true ∧
        genericFlowCheck ctx src dst = false ∧
        ¬ endpointPolicyRestricted_perCore ctx.policy epPolicy := by
  refine ⟨{ policy := { canFlow := fun _ _ => false }
            objectDomainOf := fun _ => ⟨0⟩, threadDomainOf := fun _ => ⟨0⟩
            endpointDomainOf := fun _ => ⟨0⟩, serviceDomainOf := fun _ => ⟨0⟩ },
          { endpointPolicy := fun _ => some { canFlow := fun _ _ => true } },
          ⟨0⟩, ⟨0⟩, ⟨0⟩, rfl, rfl, ?_⟩
  intro hRestricted
  have := hRestricted bootCoreId ⟨0⟩ { canFlow := fun _ _ => true } rfl ⟨0⟩ ⟨0⟩ rfl
  exact absurd this (by decide)

-- ============================================================================
-- §4  SM8.B.12 — the bridge to the release-grade non-interference witnesses
-- ============================================================================
--
-- The release-grade NI statements are the whole-projection preservation
-- theorems over the live dispatch path: `dispatchCapabilityOnly_preserves_projection`
-- and `dispatchSyscallChecked_preserves_projection` (`Kernel/API.lean`, AK6-F /
-- AE1-G3).  They speak of `projectState`, i.e. the boot-core observer.
--
-- The bridge runs in both directions, and both are worth having:
--
--   * **up** — a release-grade witness plus boot-core confinement gives the
--     per-core statement on every core (`…_preserves_projectionOnCore`);
--   * **down** — the per-core statement *implies* the release-grade one
--     (instantiate at `bootCoreId`), so SM8.B strengthens the release surface
--     rather than running beside it.

/-- SM8.B.12 (up): the syscall-entry non-interference witness lifts to every
core, given that the entry's writes stay on the boot core.

`syscallEntry_preserves_projection` is the release-grade statement at the live
entry point: decode is pure, the register lookup is read-only, and the caller
supplies the dispatched operation's projection-preservation proof.  This lifts
it from the boot-core observer to all of them.

The confinement premise is not decoration.  The *live* SMP entry is
`syscallDispatchCrossCoreEntry`, whose cross-core arms genuinely write a remote
core's run queue, so a per-core statement cannot be free.

Where the premise comes from depends on which arm ran, and the split is worth
stating precisely rather than gesturing at:

* for a dispatch that stays on the executing core, §4 of
  `NonInterferencePerCore` derives boot-core confinement from the operation's
  own semantics — thirty-one of the thirty-five operations;
* for a dispatch that routes cross-core (`.call` → `endpointCallOnCore`,
  `.reply` → `endpointReplyOnCore`, `.notificationSignal` →
  `notificationSignalOnCore`, `.tcbSuspend` → the `descheduleThread` leg), the
  premise is **false in general** — those transitions really do write a remote
  core.  What holds instead is the set-of-cores statement, and
  `NonInterferenceCrossCore` proves it for each of them: the writes stay inside
  a write set computed from the pre-state.

  **Read that boundary precisely.**  Those write sets bound the *below-API
  transitions*, and the live dispatch is more than the transition: the `.call`
  arm is `endpointCallCrossCoreDispatch`, which additionally runs
  `applyCallDonation` (per-core silent) and `propagatePipChainCrossCore` (which
  re-buckets each boosted server's run queue on that server's **home** core, so
  it can write cores the call's own write set does not name).  A statement about
  the live arm has to be made against the union —
  `endpointCallLiveWriteSet` — and anything narrower would be false.  The chain
  leg is `pipChainWriteSet`, proved sound by fuel induction mirroring the walk's
  own recursion; note it is **not** recoverable from the pre-state, because the
  live walk starts at the resolved *receiver* at the *post-donation* state, and
  both the call and the donation move `blockingServer`.

(The two inner witnesses,
`dispatchCapabilityOnly_preserves_projection` and
`dispatchSyscallChecked_preserves_projection`, are reached through this one:
their hypotheses mention `dispatchCapabilityOnly` / `dispatchWithCapChecked`,
which are `private` to `API.lean`, so their per-core statements belong at the
public entry point.) -/
theorem syscallEntry_preserves_projectionOnCore (ctx : LabelingContext)
    (observer : IfObserver) (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat)
    (st st' : SystemState)
    (hOk : syscallEntry layout regCount st = .ok ((), st'))
    (hDispatchProj : ∀ decoded tid, dispatchSyscall decoded tid st = .ok ((), st') →
      projectState ctx observer st' = projectState ctx observer st)
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
    lowEquivalent_smp ctx observer st' st :=
  lowEquivalent_smp_of_projection_and_confinement ctx observer
    (syscallEntry_preserves_projection ctx observer layout regCount st st' hOk hDispatchProj)
    hConfined

/-- SM8.B.12 (up, the `NonInterferenceStep` form): a successful syscall entry
through a non-observable current thread yields a per-core non-interference
result, composing the WS-J1-D bridge with §3 of `NonInterferencePerCore`. -/
theorem syscallEntry_success_perCore_NI (ctx : LabelingContext) (observer : IfObserver)
    (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat) (st st' : SystemState)
    (hObjInv : st.objects.invExt) (hIdxComplete : objectIndexSetComplete st)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hOk : syscallEntry layout regCount st = .ok ((), st'))
    (hCurrentHigh : ∀ t, st.scheduler.currentOnCore bootCoreId = some t →
      threadObservable ctx observer t = false)
    (hDispatchProj : ∀ decoded tid, dispatchSyscall decoded tid st = .ok ((), st') →
      projectState ctx observer st' = projectState ctx observer st)
    (hConfined : observableSlotsConfinedToCore st st' bootCoreId) :
    lowEquivalent_smp ctx observer st' st :=
  nonInterference_perCore ctx observer st st' hObjInv hIdxComplete hObjSetInv
    (syscallEntry_success_yields_NI_step ctx observer layout regCount st st' hOk hCurrentHigh
      hDispatchProj)
    hConfined

/-- SM8.B.12 (up): a *failed* syscall entry changes nothing, so it is per-core
non-interfering with no premise at all — the fail-closed half of the bridge. -/
theorem syscallEntry_error_perCore_NI (ctx : LabelingContext) (observer : IfObserver)
    (layout : SeLe4n.SyscallRegisterLayout) (regCount : Nat) (st : SystemState)
    (e : KernelError) (_hErr : syscallEntry layout regCount st = .error e) :
    lowEquivalent_smp ctx observer st st :=
  lowEquivalent_smp_of_projection_and_confinement ctx observer rfl
    (observableSlotsConfinedToCore_refl st bootCoreId)

/-- SM8.B.12 (down): the per-core statement implies the release-grade one.

Instantiating at `bootCoreId` and using SM8.A's `onCore_bootCore` bridge (which
is `rfl`) recovers exactly `lowEquivalent`, the relation the release-grade
theorems are stated in.  So the SM8.B surface is a strengthening of the release
surface: anything the release gate checks, the per-core theorems already
imply. -/
theorem nonInterference_release_of_perCore (ctx : LabelingContext) (observer : IfObserver)
    (st st' : SystemState) (h : lowEquivalent_smp ctx observer st' st) :
    lowEquivalent ctx observer st' st :=
  lowEquivalent_smp_to_singleCore ctx observer st' st h

/-- SM8.B.12 (down, observer form): and therefore for the boot-core observer at
any clearance — the form the release-gate documentation quotes. -/
theorem nonInterference_release_of_perCore_observer (ctx : LabelingContext)
    (L : SecurityLabel) (st st' : SystemState)
    (h : lowEquivalent_smp ctx (IfObserver.ofLabel L) st' st) :
    lowEquivalentForObserver ctx (PerCoreObserver.onBootCore L) st' st :=
  h bootCoreId


end SeLe4n.Kernel
