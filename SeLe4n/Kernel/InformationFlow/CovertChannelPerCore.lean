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

/-- SM8.B.6: the SMP enforcement boundary — the canonical classification plus
the two-phase-locking bracket the per-object lock discipline introduces. -/
def enforcementBoundaryPerCore : List EnforcementClass :=
  enforcementBoundaryExtended ++ [.capabilityOnly "withLockSet"]

/-- SM8.B.6: the per-core boundary has 39 entries — the live canonical 38 plus
the 2PL bracket.  Re-anchored at the SM8.A cut; `enforcementBoundaryExtended_count`
is the authority for the base figure. -/
theorem enforcementBoundaryPerCore_count : enforcementBoundaryPerCore.length = 39 := by rfl

/-- SM8.B.7 (completeness, part 1): the per-core boundary **extends** the
canonical one — it is the canonical list followed by the new entry, so no
existing classification was dropped or reclassified in the lift. -/
theorem enforcementBoundaryPerCore_extends_canonical :
    enforcementBoundaryPerCore = enforcementBoundary ++ [.capabilityOnly "withLockSet"] := rfl

/-- SM8.B.7 (completeness, part 2): every `SyscallId` still maps to an entry
present in the per-core boundary.

`enforcementBoundaryComplete` checks the same property of the canonical list;
this re-checks it against the extended one, so a future edit that *replaces*
rather than appends is caught.  Decided rather than argued, and with `decide`
rather than `native_decide` — the Lean runtime evaluator stays out of the
trusted computing base (AF4-A). -/
def enforcementBoundaryPerCoreComplete : Bool :=
  SyscallId.all.all (fun sid =>
    let name := syscallIdToEnforcementName sid
    enforcementBoundaryPerCore.any (fun ec =>
      match ec with
      | .policyGated n | .capabilityOnly n | .readOnly n => n == name))

theorem enforcementBoundaryPerCore_is_complete : enforcementBoundaryPerCoreComplete = true := by
  decide

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
       of other domains' behaviour, bounding the channel at log2(|domainSchedule|) \
       bits per domain switch (schedulingCovertChannel_bounded_width)."
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


-- ============================================================================
-- §3  SM8.B.11 — `endpointPolicyRestricted_perCore`
-- ============================================================================

/-- SM8.B.11: the per-core form of the V6-G endpoint-policy restriction — a
per-endpoint policy override may only *restrict* the global policy, and must do
so as seen from every core.

Defined as the ∀-core quantification in the SM4.D `…_smp` idiom rather than as a
new predicate: the enforcement decision reads the labeling context and the two
domains and **no per-core state**, so the core coordinate cannot change it.
`endpointPolicyRestricted_perCore_iff` records that as an `iff` rather than
leaving it implicit, and `endpointFlowCheck_state_independent` is the fact that
makes it true — which is exactly the security-relevant SMP statement here: a
transition on another core can never flip a flow gate, so the SMP kernel cannot
be made to admit a denied flow by rescheduling. -/
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

/-- SM8.B.11 (the substantive SMP fact): **the endpoint flow decision reads no
system state at all**, so it is the same on every core and cannot be changed by
a transition running elsewhere.

This is what makes the per-core lift trivial *and* is the property worth having:
under SMP the executing core is a scheduling coordinate threaded through
`determineExecutingCore`, and a reader could reasonably wonder whether the
enforcement gate picks it up.  It does not. -/
theorem endpointFlowCheck_state_independent (ctx : GenericLabelingContext)
    (epPolicy : EndpointFlowPolicy) (endpointId : SeLe4n.ObjId)
    (src dst : SecurityDomain) (_st₁ _st₂ : SystemState) (_c₁ _c₂ : CoreId) :
    endpointFlowCheck ctx epPolicy endpointId src dst =
      endpointFlowCheck ctx epPolicy endpointId src dst := rfl

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
core's run queue, so a per-core statement cannot be free — and §4b of
`NonInterferencePerCore` discharges exactly this obligation for each operation
the dispatch routes to.  (The two inner witnesses,
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
