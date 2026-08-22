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
-- **WS-SM SM8.E.3 promoted that entry into the canonical list**, which is why
-- the per-core boundary below no longer appends it: it is the canonical
-- boundary followed by the live cross-core wrappers, and `withLockSet` reaches
-- it through the canonical prefix.  The promotion was deliberately deferred to
-- SM8.E so the canonical count moved exactly once — see
-- `enforcementBoundary_classifies_withLockSet` and
-- `enforcementBoundaryPerCore_classifies_withLockSet_once`, which are what
-- keep "promoted, not duplicated" a checked fact rather than a comment.
--
-- The plan's SM8.B.6 figure ("23 entries") was written against the `v0.31.2`
-- audited cut.  The live canonical boundary's size is **not restated here** —
-- read `enforcementBoundaryExtended_count`, and this list's own size
-- `enforcementBoundaryPerCore_count` — because a figure repeated in a comment
-- goes stale the first time the boundary grows without a comment edit, which is
-- what happened to this sentence (it read "38 entries" through the WS-SM SM8.C
-- expansion) and to `enforcementBoundary`'s own docstring before it.  The
-- per-core list is the canonical one (which now carries the 2PL bracket) plus
-- the cross-core wrappers; `enforcementBoundaryPerCore_is_complete_crossCore`
-- is what pins the relationship, rather than a pair of numbers a reader must
-- compare.

/-- SM8.B.6: **the operations the live SMP dispatch actually reaches**, for the
syscalls whose arm SM6 re-routed through a cross-core wrapper.

Read off `API.dispatchWithCapChecked` / `dispatchCapabilityOnly` arm by arm, not
from the plan: `.call` runs `endpointCallCrossCoreDispatchChecked`, `.reply` runs
`endpointReplyCrossCoreDispatchChecked`, `.replyRecv` runs `replyRecvBody` (the
two-leg composition), `.receive` runs the per-core `endpointReceiveDualWithCapsOnCore`,
the two notification arms run their bound / wait cross-core dispatches, and
`.tcbSuspend` runs `suspendThreadOnCore`.

Each keeps the class its single-core counterpart carries — a cross-core wrapper
re-routes *where* a transition lands, never *what authority* it demands — and
`enforcementBoundaryPerCore_crossCore_classes_match` is the check on that.

**Read `.policyGated` as a property of the arm, not of the named function.**
Two of these entries name an operation that performs no flow check itself:
`.receive` runs the *unchecked* `endpointReceiveDualWithCapsOnCore` because its enclosing
arm has already rejected a denied `endpoint→receiver` flow with `.flowDenied`
before reaching it, and `replyRecvBody` likewise runs under the arm's
`securityFlowsTo` guard on `replier→prevCaller`.  That is the same convention the
canonical boundary uses (`cspaceDelete` names `cspaceDeleteSlot`, not a
`…Checked` wrapper): the entry names the operation reached, the class records how
authority is derived on the path that reaches it.  Stated here because
`.policyGated "endpointReceiveDualWithCapsOnCore"` would otherwise read as a claim that
the function gates, which it does not. -/
def crossCoreEnforcementEntries : List EnforcementClass :=
  [ .policyGated "endpointCallCrossCoreDispatchChecked"
  , .policyGated "endpointReplyCrossCoreDispatchChecked"
  , .policyGated "replyRecvBody"
  -- PR #873 round 6: the `.receive` arm was routed off the bare per-core
  -- receive, which delivered a parked sender's message wholesale and installed
  -- none of the capabilities it was carrying — so a transfer happened or not
  -- depending on which side reached the endpoint first.  The live operation is
  -- now the WithCaps wrapper.
  , .policyGated "endpointReceiveDualWithCapsOnCore"
  , .policyGated "notificationSignalBoundCrossCoreDispatchChecked"
  , .policyGated "notificationWaitCrossCoreDispatchChecked"
  , .capabilityOnly "suspendThreadOnCore"
  -- PR #861 review round 10: the `.send` arm was still boot-pinned through
  -- `endpointSendDualWithCaps`; rerouted, so its live operation is now this one.
  , .policyGated "endpointSendCrossCoreDispatchChecked"
  -- Round 10, same finding on the resume side.
  , .capabilityOnly "resumeThreadOnCoreLive"
  -- PR #861 review round 12: the SM7.D/SM7.F architecture wrappers are live
  -- per-core arms too — each is what its `dispatchWithCap_…_delegates` theorem
  -- says the arm reaches, and each does strictly more than the canonical
  -- operation it replaced (initiator-atomic TLB drain, I-cache maintenance).
  -- Leaving them out let the per-core table report a cross-core surface of
  -- seven when the live one is twelve.
  , .capabilityOnly "vspaceMapPageCheckedWithShootdownFromStatePerCore"
  , .capabilityOnly "vspaceUnmapPageWithShootdownAndIcacheBroadcast"
  , .capabilityOnly "lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache"
  -- PR #861 review round 12: the priority-control arms were boot-pinned twice
  -- over — the run-queue re-bucket tested membership in the BOOT core's queue
  -- (a silent no-op for a thread queued anywhere else, so a demotion never took
  -- effect) and the preemption check read the boot core's current thread.
  , .capabilityOnly "setPriorityOnCore"
  , .capabilityOnly "setMCPriorityOnCore"
  -- PR #861 review round 37, and the first arm found by the *gate* rather than
  -- by a review round: `setThreadCpuAffinityOp` hardcoded `bootCoreId` as the
  -- executing core and then discarded the SGI the migration computed.  Inert
  -- live (the committed state does not depend on that argument, and the diff
  -- seam re-derives the poke keyed on the real core), but a value computed
  -- against the wrong core and thrown away is a defect waiting for a consumer.
  , .capabilityOnly "setThreadCpuAffinityOnCore" ]

/-- SM8.B.6: the SMP enforcement boundary — the canonical classification (which
since SM8.E.3 carries the two-phase-locking bracket the per-object lock
discipline introduces) and the fifteen live cross-core wrappers.

The canonical entries are **kept**, not replaced: the boot-pinned
`syscallEntry` (`Kernel/API.lean` — driven by the trace harness and every
single-core suite) still reaches the single-core wrappers, so both surfaces
are live and both must be classified. -/
def enforcementBoundaryPerCore : List EnforcementClass :=
  enforcementBoundaryExtended ++ crossCoreEnforcementEntries

/-- SM8.B.6: the per-core boundary has 58 entries — the live canonical 43 (39
plus the 2PL bracket SM8.E.3 promoted into it, plus WS-SM SM9.A.11's two
audit-trail entries, plus WS-SM SM9.C.8's data-carrying declassification) and
the fifteen cross-core wrappers.  Re-anchored at the
SM8.A cut, in the fourth review round, again in rounds 10 and 12 as the `.send`,
resume and architecture arms joined the cross-core surface, in round 37 as the
routing gate found `.tcbSetAffinity`, at SM9.A.11, and at SM9.C.8.
`enforcementBoundaryExtended_count` is the authority for the base figure and
this theorem for the total; the sentence above is worth what they are worth, and
round 38 caught it stale at 53 one commit after the theorem moved.

The SM8.E.3 promotion left the total **unchanged**, which is the point of
appending the bracket last in the canonical list; SM9.A.11 moves it, because the
two audit entries are genuinely new operations rather than a reclassification. -/
theorem enforcementBoundaryPerCore_count : enforcementBoundaryPerCore.length = 58 := by rfl

/-- SM8.B.7 (completeness, part 1): the per-core boundary **extends** the
canonical one — it is the canonical list followed by the fifteen live cross-core
wrappers, so no existing classification was dropped or reclassified in the lift.
Additive by construction: `List.IsPrefix` is the statement that the canonical
list survives unmodified as a prefix. -/
theorem enforcementBoundaryPerCore_extends_canonical :
    enforcementBoundaryPerCore = enforcementBoundary ++ crossCoreEnforcementEntries :=
  rfl

/-- SM8.B.7: and the canonical list is a genuine prefix, so nothing in it moved
position either — the form a reader can use without unfolding the append. -/
theorem enforcementBoundary_prefix_of_perCore :
    enforcementBoundary <+: enforcementBoundaryPerCore :=
  ⟨crossCoreEnforcementEntries, rfl⟩

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
boot-pinned `syscallEntry` still reaches the single-core wrappers.

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

Differs from `syscallIdToEnforcementName` at exactly the fifteen arms the SMP
work re-routed — seven from SM6, `.send` and `.tcbResume` from PR #861 review
round 10, the three SM7.D/SM7.F architecture wrappers, and the two
priority-control arms from round 12; every other syscall
reaches the same operation it did before SMP, so it falls through to the
canonical mapping rather than being restated (a second full copy would be a
second thing to keep in sync). -/
def syscallIdToEnforcementNamePerCore : SyscallId → String
  | .call                => "endpointCallCrossCoreDispatchChecked"
  | .reply               => "endpointReplyCrossCoreDispatchChecked"
  | .replyRecv           => "replyRecvBody"
  | .receive             => "endpointReceiveDualWithCapsOnCore"
  | .notificationSignal  => "notificationSignalBoundCrossCoreDispatchChecked"
  | .notificationWait    => "notificationWaitCrossCoreDispatchChecked"
  | .tcbSuspend          => "suspendThreadOnCore"
  | .send                => "endpointSendCrossCoreDispatchChecked"
  | .tcbResume           => "resumeThreadOnCoreLive"
  | .vspaceMap           => "vspaceMapPageCheckedWithShootdownFromStatePerCore"
  | .vspaceUnmap         => "vspaceUnmapPageWithShootdownAndIcacheBroadcast"
  | .lifecycleRetype     => "lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache"
  | .tcbSetPriority      => "setPriorityOnCore"
  | .tcbSetMCPriority    => "setMCPriorityOnCore"
  | .tcbSetAffinity      => "setThreadCpuAffinityOnCore"
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

/-- SM8.B.7: the fifteen re-routed arms are genuinely re-routed — the per-core
mapping differs from the canonical one at exactly those syscalls, and nowhere
else.  A syscall silently added to (or dropped from) the cross-core surface
moves this count.

Was seven until PR #861 review round 10 rerouted `.send` and `.tcbResume` off
their boot-pinned operations, and round 12 observed that the three SM7.D/SM7.F
architecture wrappers had been live per-core arms all along without appearing
here.  Round 37 added `.tcbSetAffinity`, found by the widened routing gate. -/
theorem syscallIdToEnforcementNamePerCore_differs_at_fifteen :
    (SyscallId.all.filter (fun sid =>
      decide (syscallIdToEnforcementNamePerCore sid ≠ syscallIdToEnforcementName sid))).length
      = 15 := by decide

/-- SM8.B.7: **a cross-core wrapper carries the same enforcement class as the
single-core operation it replaced.**  Re-routing a transition to another core
changes where it lands, not what authority it demands, and this is where that
claim is checked rather than asserted: for each re-routed syscall, the class of
its per-core entry equals the class of its canonical one.

**Quantified over the mapping-difference list, not a hand-written one**
(PR #861 review round 39).  The enumeration here listed fourteen syscalls and
went stale the moment round 37 made `.tcbSetAffinity` the fifteenth re-route —
the second time this list drifted from the mapping it is supposed to audit.
Computing it from the difference makes the checked set exactly the re-routed
set by construction, so a new re-route enters this theorem the moment the
mapping changes and the two inventories cannot part company again. -/
theorem enforcementBoundaryPerCore_crossCore_classes_match :
    ((SyscallId.all.filter (fun sid =>
        decide (syscallIdToEnforcementNamePerCore sid
          ≠ syscallIdToEnforcementName sid))).all (fun sid =>
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

/-- SM8.E.3 (completeness, part 3 — **the promoted entry**): the canonical
boundary now classifies the 2PL bracket, and classifies it capability-only.

Replaces `enforcementBoundaryPerCore_entry_is_new`, which asserted the opposite
(that the canonical list did *not* carry `withLockSet`) and was true only for as
long as the promotion was outstanding.  Retiring it rather than weakening it is
the point: the negative said "the extension is not a silent duplicate", and
after SM8.E.3 that property is carried by
`enforcementBoundaryPerCore_classifies_withLockSet_once` below, which is the
statement a duplicate would actually break.

The `.capabilityOnly` pattern is written into the check rather than tested
separately, so a promotion that filed the bracket policy-gated — asserting the
bracket consults a flow policy, which it does not — fails here. -/
theorem enforcementBoundary_classifies_withLockSet :
    enforcementBoundary.any (fun ec =>
      match ec with
      | .capabilityOnly n => n == "withLockSet"
      | _ => false) = true := by decide

/-- SM8.E.3 (completeness, part 3b — **promoted, not duplicated**): the bracket
is classified exactly **once** across the whole per-core boundary.

The load-bearing half of the promotion.  `enforcementBoundaryPerCore` used to
append the entry itself; had SM8.E.3 added it to the canonical list without
removing that append, the per-core list would carry it twice — two entries a
future edit could reclassify inconsistently, with no gate noticing.  Counting
occurrences is the check that a membership test cannot make. -/
theorem enforcementBoundaryPerCore_classifies_withLockSet_once :
    (enforcementBoundaryPerCore.filter (fun ec =>
      match ec with
      | .policyGated n | .capabilityOnly n | .readOnly n => n == "withLockSet")).length
      = 1 := by decide

/-- SM8.E.3 (completeness, part 3c): and the single occurrence lives in the
**canonical prefix**, not among the cross-core wrappers — so a consumer that
reads only `enforcementBoundary` (the boot-pinned single-core surface) sees the
bracket too.  Stated as a `¬`-conjunct rather than by position, because a later
append to `crossCoreEnforcementEntries` must not be able to satisfy it. -/
theorem crossCoreEnforcementEntries_omits_withLockSet :
    crossCoreEnforcementEntries.any (fun ec =>
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
       of other domains' behaviour. Capacity, per core and per observation: at \
       most log2(|domainSchedule| * (quantumBound + 1)) bits, where quantumBound \
       caps domainTimeRemaining — proven as an injection of the observation \
       alphabet into Fin (|domainSchedule| * (quantumBound + 1)) by \
       schedulingChannel_alphabet_bounded with \
       schedulingObservationCode_injective, and covering the active domain too \
       via schedulingChannel_full_observation_determined under \
       domainConsistentOnCore. The observation rate is the TIMER-TICK rate, not \
       the domain-switch rate: an ordinary tick decrements the observed \
       countdown, so consecutive observations differ between switches \
       (schedulingObservation_changes_on_domain_tick). Over an n-tick run the \
       whole trace is one of alphabet^n possibilities \
       (schedulingChannel_trace_capacity into boundedCodeTraces). The quantum \
       cap is a required hypothesis, not a formality: \
       schedulingChannel_not_bounded_by_scheduleLength proves that \
       |domainSchedule| alone bounds nothing, because domainTimeRemaining is an \
       unrestricted Nat carried unfiltered."
    severity := .medium
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

/-- WS-SM SM9.A / PR #870 round 7: **CC-8 — audit-trail occupancy.**

The declassification audit trail is bounded (`auditLogBounded`, the 16th
`proofLayerInvariantBundle` conjunct) and **fail-closed** at the bound: an
authorized downgrade against a full trail is refused with
`.auditLogCapacityExceeded` rather than left unrecorded
(`recordDeclassificationChecked_isSome_iff`).  Those two deliberate security
decisions make the trail's **fill level** an observable that every
policy-authorized declassifier reads through its own syscall outcome — and
everyone who moves the fill level transmits: other declassifiers by
appending, and the SM9.A monitor by draining
(`auditDrain_flips_declassify_outcome` in `AuditRead.lean` is the flip
witness — the same authorized request refused at the full trail succeeds
after a monitor's drain).

The channel is **functionally forced**, not an implementation slip.  The
impossibility triangle: removing it means an unbounded trail (rejected —
`auditLogBounded` is a mounted invariant), or dropping records instead of
refusing (rejected — an unrecorded authorized downgrade is the exact failure
`declassifyStoreOnCore_never_unaudited` excludes), or a trail nobody can
drain (the pre-SM9.A 256-entry cliff the phase exists to close).  Per-domain
capacity partitioning would shrink the declassifier-to-declassifier half but
cannot remove the monitor half — freeing capacity a subject can
consume-and-observe *is* transmitting to that subject — and per-domain
quotas are unbuildable over an unbounded domain space, the
`observerScopedGeneration_not_mountable` argument again.  Round 6 closed the
occupancy's *gratuitous* receiver surface (the audit reader, now
monitor-only); the capacity refusal is the irreducible one, so it is
registered and bounded rather than half-closed a third time.

`modelVisible := true` with a caveat the other `true` entries do not need:
the carrier is not `ObservableState` but the caller's **own syscall
outcome** (WS-RA's error frame) — still the honest side of the split, since
the model alone transmits and no hardware instrument is involved. -/
def acceptedCovertChannel_auditOccupancy : CovertChannel :=
  { channelId := 8
    name := "audit-trail occupancy"
    description :=
      "The bounded, fail-closed declassification audit trail refuses an \
       authorized downgrade at capacity (.auditLogCapacityExceeded), so its \
       fill level is observable to every policy-authorized declassifier \
       through its own syscall outcome; appends (other declassifiers) and \
       drains (the SM9.A monitor) both move it, so a monitor-controlled \
       drain changes lower-domain declassification results."
    mitigation :=
      "Functionally forced by bounded + fail-closed + drainable; every \
       removal route is rejected by design (unbounded trail; dropped \
       records; a permanent capacity cliff). Bounds: the receiver set is \
       the policy-authorized declassifiers — empty under the deny-all \
       default; one observation is one bit; the fill level ranges over \
       maxDeclassificationAuditEntries + 1 = 257 values \
       (auditOccupancy_alphabet_bounded), so one drain transmits at most \
       the freed count plus its timing (about 8 bits); a SUCCESSFUL probe \
       appends an attributed record to the very trail the monitor reads \
       (declassifyObjectFromCore_never_unaudited), and refused probes are \
       counted and attributed in SM9.B's refusal ledger — landed, which is \
       the channel's monitoring half. The drain-flip witness is \
       auditDrain_flips_declassify_outcome."
    severity := .low
    modelVisible := true
    perCoreInstance := false }

/-- SM8.B.10: the accepted covert channels, in the plan's §3.5 order.
CC-1 … CC-4 are the pre-SMP inventory; CC-5 is SM8.B.8's lock-contention
channel; CC-6 and CC-7 were registered at the SM8.A cut when SM7.C and SM7.D
mounted the per-core TLB and instruction-cache views; CC-8 was registered at
the SM9.A PR #870 round-7 cut, when the audit trail's capacity refusal was
recognised as the occupancy channel's irreducible receiver surface. -/
def acceptedCovertChannelsPerCore : List CovertChannel :=
  [ acceptedCovertChannel_scheduling_perCore
  , acceptedCovertChannel_machineTimer
  , acceptedCovertChannel_tcbMetadata
  , acceptedCovertChannel_objectStoreMetadata
  , acceptedCovertChannel_lockContention
  , acceptedCovertChannel_tlbResidency
  , acceptedCovertChannel_icacheResidency
  , acceptedCovertChannel_auditOccupancy ]

/-- SM8.B.10: **eight** accepted covert channels.

The plan's sub-task line reads "= 5", written before CC-6 and CC-7 existed: the
SM8.A cut registered them when SM7.C mounted `SystemState.perCoreTlb` and SM7.D
mounted `SystemState.perCoreICache`; CC-8 joined at the SM9.A PR #870 round-7
cut.  Asserting a stale figure here would produce a *false* count, so it is
re-anchored against the inventory — the same correction the plan applies to its
own 32→35 constructor and 22→38 boundary figures. -/
theorem acceptedCovertChannel_perCoreCount : acceptedCovertChannelsPerCore.length = 8 := by rfl

/-- SM8.B.10: the inventory carries the plan's §3.5 numbering, in order and
without repetition — CC-1 … CC-8.  Distinctness of the entries follows, so the
count above counts channels rather than list cells, and a re-ordering or a
duplicated entry is a build failure. -/
theorem acceptedCovertChannel_perCore_ids :
    acceptedCovertChannelsPerCore.map CovertChannel.channelId = [1, 2, 3, 4, 5, 6, 7, 8] := rfl

/-- SM8.B.10: exactly four of the eight are carried by the model; the other
four exist only through hardware the projection excludes.  Three of the four
model-carried channels flow through `ObservableState`; the fourth (CC-8) flows
through the caller's own syscall outcome — model-level either way, no
instrument required.  The split is what the `modelVisible` field exists to
record, and pinning it means a future channel cannot be filed on the wrong
side by accident. -/
theorem acceptedCovertChannel_modelVisible_count :
    (acceptedCovertChannelsPerCore.filter CovertChannel.modelVisible).length = 4 := rfl

/-- SM8.B.10: five of the eight have one instance **per core** under SMP, so
their aggregate capacity scales with `numCores`.  The three that do not — the
two label-filtered metadata channels and CC-8's shared trail — read shared
state. -/
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
      acceptedCovertChannel_objectStoreMetadata.modelVisible = true ∧
      acceptedCovertChannel_auditOccupancy.modelVisible = true :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- SM8.B.10 (the SMP delta): CC-5, CC-6 and CC-7 are the three channels SMP
adds, and all three are per-core hardware channels.  The pre-SMP inventory
(CC-1 … CC-4) is unchanged — SM8 widens the inventory, it does not reclassify
what was already in it.  (The filter's upper bound exists because CC-8 is
SM9.A's addition, not SMP's — a plain `≥ 5` would silently absorb it into the
SMP delta.) -/
theorem acceptedCovertChannel_smp_additions :
    (acceptedCovertChannelsPerCore.filter
      (fun ch => decide (ch.channelId ≥ 5) && decide (ch.channelId ≤ 7))).length = 3 ∧
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

/-- SM8.B.9: **the observation an SMP scheduling-channel receiver can make** on
core `c` — the two unfiltered per-core components the observer's view exposes,
paired.  `activeDomain` is omitted deliberately, but **not** because the
index-bounds invariant makes it redundant — that was the fifth round's claim and
it was wrong.  `domainScheduleIndexInBoundsOnCore` constrains the index alone;
the invariant that ties `activeDomainOnCore` to `domainSchedule[index]` is the
separate `domainConsistentOnCore` (SM5.G.2).
`schedulingChannel_full_observation_determined` is what licenses the omission,
and it takes that invariant as a hypothesis. -/
def schedulingObservationOnCore (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) : Nat × Nat :=
  ((ObservableState.onCore ctx c L s).domainScheduleIndex,
   (ObservableState.onCore ctx c L s).domainTimeRemaining)

/-- SM8.B.9: the observation, as a single natural number, relative to a bound
`quantumBound` on the countdown.  A positional encoding — index in the high
digit, countdown in the low one. -/
def schedulingObservationCode (quantumBound : Nat) (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState) : Nat :=
  (schedulingObservationOnCore ctx c L s).1 * (quantumBound + 1)
    + (schedulingObservationOnCore ctx c L s).2

/-- SM8.B.9: a positional encoding with a bounded low digit is injective.
Pure arithmetic, factored out so the channel theorem reads as a statement about
the channel rather than about `Nat` division. -/
private theorem positionalCode_injective {q i₁ t₁ i₂ t₂ : Nat}
    (h₁ : t₁ < q + 1) (h₂ : t₂ < q + 1)
    (h : i₁ * (q + 1) + t₁ = i₂ * (q + 1) + t₂) : i₁ = i₂ ∧ t₁ = t₂ := by
  rcases Nat.lt_trichotomy i₁ i₂ with hlt | heq | hgt
  · exfalso
    have step : (i₁ + 1) * (q + 1) ≤ i₂ * (q + 1) := Nat.mul_le_mul_right _ hlt
    have expand : (i₁ + 1) * (q + 1) = i₁ * (q + 1) + (q + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    omega
  · refine ⟨heq, ?_⟩
    subst heq
    omega
  · exfalso
    have step : (i₂ + 1) * (q + 1) ≤ i₁ * (q + 1) := Nat.mul_le_mul_right _ hgt
    have expand : (i₂ + 1) * (q + 1) = i₂ * (q + 1) + (q + 1) := by
      rw [Nat.add_mul, Nat.one_mul]
    omega

/-- SM8.B.9: the encoding **loses nothing** — two states the observer can tell
apart by their scheduling components get different codes, provided both
countdowns respect the bound.  Without this the cardinality bound below would
be a bound on an arbitrary function rather than on the channel. -/
theorem schedulingObservationCode_injective (quantumBound : Nat) (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (h₁ : (schedulingObservationOnCore ctx c L s₁).2 ≤ quantumBound)
    (h₂ : (schedulingObservationOnCore ctx c L s₂).2 ≤ quantumBound)
    (hCode : schedulingObservationCode quantumBound ctx c L s₁
      = schedulingObservationCode quantumBound ctx c L s₂) :
    schedulingObservationOnCore ctx c L s₁ = schedulingObservationOnCore ctx c L s₂ := by
  obtain ⟨hi, ht⟩ := positionalCode_injective (Nat.lt_succ_of_le h₁) (Nat.lt_succ_of_le h₂) hCode
  exact Prod.ext hi ht

/-- SM8.B.9 (**the CC-1 capacity bound**): under the scheduler's index-bounds
invariant and a bound `quantumBound` on the countdown, the scheduling channel's
observation alphabet on core `c` injects into
`Fin (|domainSchedule| × (quantumBound + 1))`.

So an observer learns **at most `log₂(|domainSchedule| × (quantumBound + 1))`
bits per observation**, and at **tick** frequency `F` at most that many times
`F` bits per second.  This is the figure the deployment guidance quotes.

The rate factor is the tick rate, not the domain-*switch* rate (round 42
corrected this docstring, which was the last site still quoting the lower
figure).  `domainTimeRemaining` is an observed component and an ordinary tick
decrements it, so a fresh observation is available every tick rather than every
switch — `schedulingObservation_changes_on_domain_tick` is that fact as a
theorem, and it is what takes the canonical 1 kHz deployment to ≤ 12 000
bits/second rather than the switch-paced figure this once quoted.

The two hypotheses are exactly what the fourth review round showed to be
necessary rather than decorative: `schedulingChannel_not_bounded_by_scheduleLength`
proves that `|domainSchedule|` **alone** bounds nothing, because
`domainTimeRemaining` is an unrestricted `Nat` carried unfiltered.  A deployment
that does not cap the countdown does not get this bound — which is a statement
about the deployment, not a hole in the theorem. -/
theorem schedulingChannel_alphabet_bounded (quantumBound : Nat) (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (s : SystemState)
    (hBounds : domainScheduleIndexInBoundsOnCore s c)
    (hNonEmpty : s.scheduler.domainSchedule ≠ [])
    (hQuantum : s.scheduler.domainTimeRemainingOnCore c ≤ quantumBound) :
    schedulingObservationCode quantumBound ctx c L s
      < s.scheduler.domainSchedule.length * (quantumBound + 1) := by
  have hIdx : s.scheduler.domainScheduleIndexOnCore c < s.scheduler.domainSchedule.length := by
    rcases hBounds with hEmpty | hLt
    · exact absurd hEmpty hNonEmpty
    · exact hLt
  have hTrans := onCore_schedulingTransparency ctx c L s
  simp only [schedulingObservationCode, schedulingObservationOnCore, hTrans.2.1]
  calc s.scheduler.domainScheduleIndexOnCore c * (quantumBound + 1)
          + s.scheduler.domainTimeRemainingOnCore c
      < s.scheduler.domainScheduleIndexOnCore c * (quantumBound + 1) + (quantumBound + 1) := by
        omega
    _ = (s.scheduler.domainScheduleIndexOnCore c + 1) * (quantumBound + 1) := by
        rw [Nat.add_mul, Nat.one_mul]
    _ ≤ s.scheduler.domainSchedule.length * (quantumBound + 1) :=
        Nat.mul_le_mul_right _ hIdx

/-- SM8.B.9: **the complete scheduling observation**, active domain included.

`schedulingObservationOnCore` deliberately carries only the index and the
countdown; this is the whole tuple, and `schedulingChannel_full_observation_determined`
below is what licenses bounding the channel by the smaller one. -/
def schedulingObservationFullOnCore (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel)
    (s : SystemState) : SeLe4n.DomainId × Nat × Nat :=
  ((ObservableState.onCore ctx c L s).activeDomain,
   (ObservableState.onCore ctx c L s).domainScheduleIndex,
   (ObservableState.onCore ctx c L s).domainTimeRemaining)

/-- SM8.B.9: **the active domain is a function of the schedule and the index** —
under `domainConsistentOnCore`, which is the invariant that actually ties them.

The fifth review round's form of the capacity bound claimed this held "under the
index-bounds invariant", and that was wrong: `domainScheduleIndexInBoundsOnCore`
constrains the index and says nothing about `activeDomainOnCore`.  The tie is a
*separate* invariant (`domainConsistentOnCore`, SM5.G.2), so without it two
states could share a schedule, an index and a countdown while exposing different
active domains — and the code below would map them together while the observer
told them apart. -/
theorem schedulingObservation_activeDomain_determined (ctx : LabelingContext) (c : CoreId)
    (L : SecurityLabel) (s : SystemState)
    (hCons : domainConsistentOnCore s c)
    (hBounds : domainScheduleIndexInBoundsOnCore s c)
    (hNonEmpty : s.scheduler.domainSchedule ≠ []) :
    ∃ entry : DomainScheduleEntry,
      s.scheduler.domainSchedule[(ObservableState.onCore ctx c L s).domainScheduleIndex]?
          = some entry
      ∧ (ObservableState.onCore ctx c L s).activeDomain = DomainScheduleEntry.domain entry := by
  have hTrans := onCore_schedulingTransparency ctx c L s
  have hIdx : s.scheduler.domainScheduleIndexOnCore c < s.scheduler.domainSchedule.length := by
    rcases hBounds with hEmpty | hLt
    · exact absurd hEmpty hNonEmpty
    · exact hLt
  obtain ⟨entry, hEntry⟩ :
      ∃ e, s.scheduler.domainSchedule[s.scheduler.domainScheduleIndexOnCore c]? = some e :=
    ⟨_, List.getElem?_eq_getElem hIdx⟩
  refine ⟨entry, ?_, ?_⟩
  · rw [hTrans.2.2.2]; exact hEntry
  · rw [hTrans.1]; exact hCons entry hEntry

/-- SM8.B.9 (**the capacity bound covers the whole channel**): two states the
code identifies have the *same complete observation* — active domain included.

This is what the alphabet bound needs in order to be a bound on the scheduling
channel rather than on two of its three components.  The schedule is a hypothesis
rather than a component of the code because it is quasi-static configuration: a
capacity figure is quoted for a fixed domain schedule, and a deployment that
rewrites its schedule at runtime is changing the channel, not transmitting
through it. -/
theorem schedulingChannel_full_observation_determined (quantumBound : Nat)
    (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (hSched : s₁.scheduler.domainSchedule = s₂.scheduler.domainSchedule)
    (hNonEmpty : s₁.scheduler.domainSchedule ≠ [])
    (hCons₁ : domainConsistentOnCore s₁ c) (hCons₂ : domainConsistentOnCore s₂ c)
    (hBounds₁ : domainScheduleIndexInBoundsOnCore s₁ c)
    (hBounds₂ : domainScheduleIndexInBoundsOnCore s₂ c)
    (hQ₁ : (schedulingObservationOnCore ctx c L s₁).2 ≤ quantumBound)
    (hQ₂ : (schedulingObservationOnCore ctx c L s₂).2 ≤ quantumBound)
    (hCode : schedulingObservationCode quantumBound ctx c L s₁
      = schedulingObservationCode quantumBound ctx c L s₂) :
    schedulingObservationFullOnCore ctx c L s₁ = schedulingObservationFullOnCore ctx c L s₂ := by
  have hPair := schedulingObservationCode_injective quantumBound ctx c L s₁ s₂ hQ₁ hQ₂ hCode
  have hIdx : (ObservableState.onCore ctx c L s₁).domainScheduleIndex
      = (ObservableState.onCore ctx c L s₂).domainScheduleIndex :=
    congrArg Prod.fst hPair
  have hRem : (ObservableState.onCore ctx c L s₁).domainTimeRemaining
      = (ObservableState.onCore ctx c L s₂).domainTimeRemaining :=
    congrArg Prod.snd hPair
  obtain ⟨e₁, hLook₁, hDom₁⟩ :=
    schedulingObservation_activeDomain_determined ctx c L s₁ hCons₁ hBounds₁ hNonEmpty
  obtain ⟨e₂, hLook₂, hDom₂⟩ :=
    schedulingObservation_activeDomain_determined ctx c L s₂ hCons₂ hBounds₂ (hSched ▸ hNonEmpty)
  have hSame : e₁ = e₂ := by
    have h₁ := hLook₁
    rw [hSched, hIdx] at h₁
    rw [h₁] at hLook₂
    exact Option.some.inj hLook₂
  simp only [schedulingObservationFullOnCore]
  refine Prod.ext ?_ (Prod.ext hIdx hRem)
  simp only []
  rw [hDom₁, hDom₂, hSame]

/-- SM8.B.9: **every premise the capacity bound needs, as one predicate.**

The ninth review round observed that the operator-facing guidance quoted
`log₂(N × (Q + 1)) × F` while naming only the countdown cap `Q` as a deployment
obligation — but `schedulingChannel_alphabet_bounded` also needs a *non-empty*
schedule and the index-bounds invariant, and the cross-state form additionally
needs `domainConsistentOnCore`.  A capacity figure whose hypotheses are spread
across three theorem signatures is a figure an operator will quote without them.

Bundled here so the conditions are one checkable object, cited by one name in the
advisory and the deployment guide.

**The empty schedule is genuinely excluded, not merely unhandled**:
`domainScheduleIndexInBoundsOnCore` degenerates to `True` when the schedule is
empty (its first disjunct), so single-domain mode places *no* bound on the
observed index — and the index is projected unfiltered.  This analysis therefore
gives no capacity bound in that configuration, exactly as it gives none without
a countdown cap. -/
def schedulingCapacityPreconditions (quantumBound : Nat) (s : SystemState) (c : CoreId) :
    Prop :=
  s.scheduler.domainSchedule ≠ []
  ∧ domainScheduleIndexInBoundsOnCore s c
  ∧ domainConsistentOnCore s c
  ∧ s.scheduler.domainTimeRemainingOnCore c ≤ quantumBound

/-- SM8.B.9: the capacity bound, stated against the bundled preconditions — the
form the operator documentation cites. -/
theorem schedulingChannel_alphabet_bounded_of_preconditions (quantumBound : Nat)
    (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : SystemState)
    (hPre : schedulingCapacityPreconditions quantumBound s c) :
    schedulingObservationCode quantumBound ctx c L s
      < s.scheduler.domainSchedule.length * (quantumBound + 1) :=
  schedulingChannel_alphabet_bounded quantumBound ctx c L s hPre.2.1 hPre.1 hPre.2.2.2

/-- SM8.B.9: **the cross-state premise the per-state bundle cannot carry.**

`schedulingChannel_full_observation_determined` compares two states, and needs
their schedules to be *the same list* — not merely the same length.  The schedule
is itself projected unfiltered, so a deployment that rewrites it between
observations has a second channel that fixing `N` does nothing about.

Nothing in the kernel writes this field: `SchedulerState` has a
`setDomainScheduleIndexOnCore` but **no** `setDomainSchedule`, and the only
assignments in the tree are the boot builder and the freeze copy (which is
`rfl`).  So the premise holds by construction today, and a Tier-3 negative anchor
keeps it that way; introducing a reconfiguration syscall would break that anchor
and must come with this bound restated. -/
def schedulingCapacityComparable (quantumBound : Nat) (s₁ s₂ : SystemState) (c : CoreId) :
    Prop :=
  schedulingCapacityPreconditions quantumBound s₁ c
  ∧ schedulingCapacityPreconditions quantumBound s₂ c
  ∧ s₁.scheduler.domainSchedule = s₂.scheduler.domainSchedule

/-- SM8.B.9: under the comparable-state preconditions, equal codes mean equal
complete observations — the whole-channel statement, with every hypothesis it
rests on named in one place. -/
theorem schedulingChannel_full_observation_determined_of_preconditions (quantumBound : Nat)
    (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s₁ s₂ : SystemState)
    (hPre : schedulingCapacityComparable quantumBound s₁ s₂ c)
    (hCode : schedulingObservationCode quantumBound ctx c L s₁
      = schedulingObservationCode quantumBound ctx c L s₂) :
    schedulingObservationFullOnCore ctx c L s₁ = schedulingObservationFullOnCore ctx c L s₂ := by
  obtain ⟨⟨hNE₁, hB₁, hC₁, hQ₁⟩, ⟨_, hB₂, hC₂, hQ₂⟩, hSched⟩ := hPre
  have hTrans₁ := onCore_schedulingTransparency ctx c L s₁
  have hTrans₂ := onCore_schedulingTransparency ctx c L s₂
  refine schedulingChannel_full_observation_determined quantumBound ctx c L s₁ s₂ hSched
    hNE₁ hC₁ hC₂ hB₁ hB₂ ?_ ?_ hCode
  · simpa [schedulingObservationOnCore, hTrans₁.2.1] using hQ₁
  · simpa [schedulingObservationOnCore, hTrans₂.2.1] using hQ₂

-- ============================================================================
-- SM8.B.9 — the CC-1 **observation-rate** bound (PR #861 review round 12)
-- ============================================================================
--
-- The alphabet bound above says how much ONE observation carries.  A bandwidth
-- figure needs the second factor, and the guidance had it wrong: it multiplied
-- by the domain-**switch** frequency.  The observable tuple carries
-- `domainTimeRemaining`, and that field is decremented on every ordinary timer
-- tick, so consecutive observations differ *between* switches too — the
-- observation rate is the **tick** rate, which on the canonical RPi5
-- configuration (`configDefaultTimeSlice = 1000`, a 1 ms tick) is three orders
-- of magnitude higher than the switch rate.
--
-- `schedulingObservation_changes_on_domain_tick` below is that fact as a
-- theorem, and the trace-capacity bound is stated per observation rather than
-- per switch so the two cannot drift apart again.

/-- SM8.B.9 (**the pacing fact**): an ordinary timer tick — one that does *not*
reach a domain boundary — **changes the observation**.

`decrementDomainTimeOnCore` is the tick's domain-countdown leg, and the countdown
is the second component of the observed tuple, so a tick with time left produces
an observation distinct from the previous one.  Consequently the observer is not
paced by domain switches: it can read a fresh value once per tick. -/
theorem schedulingObservation_changes_on_domain_tick (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (s : SystemState)
    (hPos : 0 < s.scheduler.domainTimeRemainingOnCore c) :
    schedulingObservationOnCore ctx c L (decrementDomainTimeOnCore s c)
      ≠ schedulingObservationOnCore ctx c L s := by
  intro hEq
  have hTransPre := onCore_schedulingTransparency ctx c L s
  have hTransPost := onCore_schedulingTransparency ctx c L (decrementDomainTimeOnCore s c)
  have hSnd : (schedulingObservationOnCore ctx c L (decrementDomainTimeOnCore s c)).2
      = (schedulingObservationOnCore ctx c L s).2 := by rw [hEq]
  rw [show (schedulingObservationOnCore ctx c L (decrementDomainTimeOnCore s c)).2
        = (decrementDomainTimeOnCore s c).scheduler.domainTimeRemainingOnCore c from
        hTransPost.2.1,
      show (schedulingObservationOnCore ctx c L s).2
        = s.scheduler.domainTimeRemainingOnCore c from hTransPre.2.1,
      decrementDomainTimeOnCore_decrements] at hSnd
  omega

/-- SM8.B.9: **every code trace of length `n` over an alphabet of size `a`**,
enumerated.  The observer's whole run of observations is one element of this
list, and the list's length is exactly `a ^ n` — which is the capacity statement
without a logarithm, and without Mathlib's cardinality machinery. -/
def boundedCodeTraces (alphabet : Nat) : Nat → List (List Nat)
  | 0 => [[]]
  | n + 1 =>
      (List.range alphabet).flatMap (fun x => (boundedCodeTraces alphabet n).map (x :: ·))

/-- SM8.B.9: the enumeration has exactly `alphabet ^ n` elements. -/
theorem boundedCodeTraces_length (alphabet : Nat) :
    ∀ n, (boundedCodeTraces alphabet n).length = alphabet ^ n
  | 0 => by simp [boundedCodeTraces]
  | n + 1 => by
      have hConst : ∀ l : List Nat,
          (List.map (fun _ => alphabet ^ n) l).sum = l.length * alphabet ^ n := by
        intro l
        induction l with
        | nil => simp
        | cons a t ih => simp [ih, Nat.succ_mul, Nat.add_comm]
      simp [boundedCodeTraces, List.length_flatMap, boundedCodeTraces_length alphabet n,
        hConst, Nat.pow_succ, Nat.mul_comm]

/-- SM8.B.9: and it contains **exactly** the length-`n` traces whose every entry
is below the alphabet size — so the count above is a count of the right set,
not of a superset that happens to be easy to enumerate. -/
theorem mem_boundedCodeTraces (alphabet : Nat) :
    ∀ (n : Nat) (l : List Nat),
      l ∈ boundedCodeTraces alphabet n ↔ (l.length = n ∧ ∀ x ∈ l, x < alphabet)
  | 0, l => by
      constructor
      · intro h
        simp only [boundedCodeTraces, List.mem_singleton] at h
        subst h; simp
      · rintro ⟨hLen, -⟩
        simp only [boundedCodeTraces, List.mem_singleton]
        exact List.eq_nil_of_length_eq_zero hLen
  | n + 1, l => by
      simp only [boundedCodeTraces, List.mem_flatMap, List.mem_map, List.mem_range]
      constructor
      · rintro ⟨x, hx, t, ht, rfl⟩
        obtain ⟨hLen, hAll⟩ := (mem_boundedCodeTraces alphabet n t).mp ht
        refine ⟨by simp [hLen], ?_⟩
        intro y hy
        rcases List.mem_cons.mp hy with rfl | hy'
        · exact hx
        · exact hAll y hy'
      · rintro ⟨hLen, hAll⟩
        cases l with
        | nil => simp at hLen
        | cons x t =>
          refine ⟨x, hAll x (by simp), t, ?_, rfl⟩
          refine (mem_boundedCodeTraces alphabet n t).mpr ⟨by simpa using hLen, ?_⟩
          intro y hy
          exact hAll y (List.mem_cons_of_mem _ hy)

/-- SM8.B.9: **the preconditions a whole run must satisfy** for the trace bound
to be a capacity claim — the per-state bundle at every state, and one schedule
across the run.

The second clause is the run-level form of `schedulingCapacityComparable`'s
schedule equality, and it is required for the same reason: the schedule is
projected unfiltered, so two same-length but different schedules are two
observer-distinguishable configurations that the index/countdown code cannot
tell apart.  Fixing `N` bounds the alphabet; it does not bound the schedule's
contents. -/
def schedulingCapacityRun (quantumBound : Nat) (run : List SystemState) (c : CoreId) : Prop :=
  (∀ s ∈ run, schedulingCapacityPreconditions quantumBound s c)
  ∧ (∀ s₁ ∈ run, ∀ s₂ ∈ run, s₁.scheduler.domainSchedule = s₂.scheduler.domainSchedule)

/-- SM8.B.9: a run of one state satisfies the run preconditions as soon as that
state satisfies the per-state bundle — schedule equality is reflexive, so the
single-observation case needs nothing extra. -/
theorem schedulingCapacityRun_singleton (quantumBound : Nat) (s : SystemState) (c : CoreId)
    (hPre : schedulingCapacityPreconditions quantumBound s c) :
    schedulingCapacityRun quantumBound [s] c := by
  refine ⟨?_, ?_⟩
  · intro x hx; rw [List.mem_singleton.mp hx]; exact hPre
  · intro a ha b hb
    rw [List.mem_singleton.mp ha, List.mem_singleton.mp hb]

/-- SM8.B.9: the sequence of codes an observer on `(c, L)` reads off a run. -/
def schedulingObservationTrace (quantumBound : Nat) (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (run : List SystemState) : List Nat :=
  run.map (schedulingObservationCode quantumBound ctx c L)

/-- SM8.B.9 (**the CC-1 bandwidth bound**): over a run of `n` observations —
one per **timer tick**, by the pacing fact above, not one per domain switch —
the observer's whole trace is a single element of `boundedCodeTraces alphabet n`,
a set of exactly `alphabet ^ n` elements, where
`alphabet = |domainSchedule| × (quantumBound + 1)`.

Equivalently: at most `log₂(alphabet)` bits per tick, and no more over the run
than that times the number of ticks.

**The run-level preconditions are `schedulingCapacityRun`, and the schedule
clause is load-bearing** (PR #861 review round 13).  An earlier cut quantified
only `schedulingCapacityPreconditions` pointwise while its docstring claimed the
states shared one schedule.  The membership conclusion was still true, but the
*capacity reading* it supports was not: the observer also sees `domainSchedule`
and the `activeDomain` it determines, so with two same-length but different
schedules in one run the code trace stops distinguishing what the observer
distinguishes, and `alphabet ^ n` counts fewer behaviours than exist.  The
premise is required here, and `schedulingChannel_trace_determines_observations`
below is what turns the count into a capacity claim: under it, the code trace
determines the *full* observation trace. -/
theorem schedulingChannel_trace_capacity (quantumBound : Nat) (ctx : LabelingContext)
    (c : CoreId) (L : SecurityLabel) (run : List SystemState) (alphabet : Nat)
    (hRun : schedulingCapacityRun quantumBound run c)
    (hAlphabet : ∀ s ∈ run, s.scheduler.domainSchedule.length * (quantumBound + 1) ≤ alphabet) :
    schedulingObservationTrace quantumBound ctx c L run
      ∈ boundedCodeTraces alphabet run.length := by
  refine (mem_boundedCodeTraces alphabet run.length _).mpr ⟨by simp [schedulingObservationTrace], ?_⟩
  intro x hx
  simp only [schedulingObservationTrace, List.mem_map] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  exact Nat.lt_of_lt_of_le
    (schedulingChannel_alphabet_bounded_of_preconditions quantumBound ctx c L s (hRun.1 s hs))
    (hAlphabet s hs)

/-- SM8.B.9 (**what makes the count a capacity bound**): under the run
preconditions, and with one schedule across *both* runs, equal code traces mean
equal **complete** observation traces — active domain included.

Without this the `alphabet ^ n` figure counts *codes*, not observer-distinguishable
behaviours.  With it, the observer's whole run of observations is a function of
an element of a set of exactly `alphabet ^ n`, which is the statement the
deployment guidance quotes.

Proved pointwise off `schedulingChannel_full_observation_determined_of_preconditions`
by induction on the two runs — the code trace being a `List.map`, equal traces
give equal heads and equal tails. -/
theorem schedulingChannel_trace_determines_observations (quantumBound : Nat)
    (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) :
    ∀ (run₁ run₂ : List SystemState),
      schedulingCapacityRun quantumBound run₁ c →
      schedulingCapacityRun quantumBound run₂ c →
      (∀ s₁ ∈ run₁, ∀ s₂ ∈ run₂,
        s₁.scheduler.domainSchedule = s₂.scheduler.domainSchedule) →
      schedulingObservationTrace quantumBound ctx c L run₁
        = schedulingObservationTrace quantumBound ctx c L run₂ →
      run₁.map (schedulingObservationFullOnCore ctx c L)
        = run₂.map (schedulingObservationFullOnCore ctx c L)
  | [], [], _, _, _, _ => rfl
  | [], _ :: _, _, _, _, hCode => by simp [schedulingObservationTrace] at hCode
  | _ :: _, [], _, _, _, hCode => by simp [schedulingObservationTrace] at hCode
  | s₁ :: t₁, s₂ :: t₂, hRun₁, hRun₂, hSched, hCode => by
      simp only [schedulingObservationTrace, List.map_cons, List.cons.injEq] at hCode
      obtain ⟨hHead, hTail⟩ := hCode
      have hFull : schedulingObservationFullOnCore ctx c L s₁
          = schedulingObservationFullOnCore ctx c L s₂ :=
        schedulingChannel_full_observation_determined_of_preconditions quantumBound ctx c L
          s₁ s₂ ⟨hRun₁.1 s₁ (by simp), hRun₂.1 s₂ (by simp),
                 hSched s₁ (by simp) s₂ (by simp)⟩ hHead
      have hRest := schedulingChannel_trace_determines_observations quantumBound ctx c L t₁ t₂
        ⟨fun s hs => hRun₁.1 s (List.mem_cons_of_mem _ hs),
         fun a ha b hb => hRun₁.2 a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
        ⟨fun s hs => hRun₂.1 s (List.mem_cons_of_mem _ hs),
         fun a ha b hb => hRun₂.2 a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb)⟩
        (fun a ha b hb => hSched a (List.mem_cons_of_mem _ ha) b (List.mem_cons_of_mem _ hb))
        hTail
      simp only [List.map_cons, hFull, hRest]

/-- SM8.B.9: the capacity really is exponential in the run length and nothing
smaller — a one-tick run over an eight-element alphabet admits eight traces, a
two-tick run sixty-four.  Stated so the `alphabet ^ n` is a computed fact rather
than a reading of the definition. -/
example : (boundedCodeTraces 8 1).length = 8 ∧ (boundedCodeTraces 8 2).length = 64 := by
  constructor <;> simp [boundedCodeTraces_length]

/-- SM8.B.9: the bound is **not vacuous** — with a two-entry schedule and a
countdown capped at 3 the alphabet has at most 8 elements, and a concrete state
lands inside it. -/
example : (2 : Nat) * (3 + 1) = 8 := by decide

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
  | auditOccupancy
  deriving DecidableEq, Repr

def CovertChannelId.all : List CovertChannelId :=
  [.schedulingState, .machineTimer, .tcbMetadata, .objectStoreMetadata, .lockContention,
   .tlbResidency, .icacheResidency, .auditOccupancy]

/-- SM8.B.8: **`all` really is all of them.**

The match-based tables below are exhaustive by construction — a new constructor
is a missing case and the module stops compiling.  `all` is not: it is a
hand-written list, and a constructor omitted from it would sail past
`covertChannelEntry_eq_inventory`, past both count theorems and past the
evidence-sharing check, because every one of those quantifies over `all` rather
than over the type (PR #861 review round 9).  The new channel would simply not
be audited.

`decide` closes that: adding a constructor without extending `all` now fails
*this* theorem, so the enumeration cannot fail open. -/
theorem CovertChannelId.mem_all (id : CovertChannelId) : id ∈ CovertChannelId.all := by
  cases id <;> decide

/-- SM8.B.8: and it lists each exactly once, so the counts below count channels
rather than repetitions. -/
theorem CovertChannelId.all_nodup : CovertChannelId.all.Nodup := by decide

/-- SM8.B.8: the entry each id names. -/
def covertChannelEntry : CovertChannelId → CovertChannel
  | .schedulingState => acceptedCovertChannel_scheduling_perCore
  | .machineTimer => acceptedCovertChannel_machineTimer
  | .tcbMetadata => acceptedCovertChannel_tcbMetadata
  | .objectStoreMetadata => acceptedCovertChannel_objectStoreMetadata
  | .lockContention => acceptedCovertChannel_lockContention
  | .tlbResidency => acceptedCovertChannel_tlbResidency
  | .icacheResidency => acceptedCovertChannel_icacheResidency
  | .auditOccupancy => acceptedCovertChannel_auditOccupancy

/-- SM8.B.8 (PR #861 review round 17): **the property each channel's evidence
must establish**, stated through `covertChannelEntry id` rather than through a
named constant.

`covertChannelEvidenceName` below is validated only in that its string resolves
to *some* declaration — so mapping `.machineTimer` at the scheduling witness
passed every check the module had.  This is the type that makes the mapping
itself checkable: because each arm reads `(covertChannelEntry id).modelVisible`
and `covertChannelEntry` reduces definitionally to the entry constant,
supplying the wrong channel's theorem is a **type error**, not a documentation
slip.  A `.machineTimer` arm demands `… .modelVisible = false`, and the
scheduling witness proves `= true` about a different entry.

Each arm is the conclusion of the theorem the corresponding
`covertChannelEvidenceName` arm names, so nothing new has to be proved —
`covertChannelEvidence` discharges them by citation. -/
def CovertChannelId.evidenceProp : CovertChannelId → Prop
  | .schedulingState =>
      ∀ (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : SystemState),
        (covertChannelEntry .schedulingState).modelVisible = true ∧
          (ObservableState.onCore ctx c L s).activeDomain = s.scheduler.activeDomainOnCore c
  | .machineTimer =>
      ∀ (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) (c : CoreId) (t : Nat),
        (covertChannelEntry .machineTimer).modelVisible = false ∧
          ObservableState.onCore ctx c L { s with machine := { s.machine with timer := t } }
            = ObservableState.onCore ctx c L s
  | .tcbMetadata =>
      ∀ (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : SystemState)
        (tid : SeLe4n.ThreadId) (tcb : TCB),
        objectObservable ctx (IfObserver.ofLabel L) tid.toObjId = true →
        s.getTcb? tid = some tcb →
        (covertChannelEntry .tcbMetadata).modelVisible = true ∧
          ∃ projected : TCB,
            (ObservableState.onCore ctx c L s).objects tid.toObjId = some (.tcb projected)
            ∧ projected.priority = tcb.priority
            ∧ projected.ipcState = tcb.ipcState
  | .objectStoreMetadata =>
      ∀ (ctx : LabelingContext) (c : CoreId) (L : SecurityLabel) (s : SystemState),
        (covertChannelEntry .objectStoreMetadata).modelVisible = true ∧
          (ObservableState.onCore ctx c L s).objectIndex
            = projectObjectIndex ctx (IfObserver.ofLabel L) s
  | .lockContention =>
      ∀ (ctx : LabelingContext) (observer : IfObserver)
        (S : SeLe4n.Kernel.Concurrency.LockSet) (core : CoreId)
        (action : SystemState → SystemState × Unit) (s : SystemState),
        s.objects.invExt →
        (∀ s', s'.objects.invExt → ((action s').1).objects.invExt) →
        (∀ s', s'.objects.invExt →
          projectState ctx observer (action s').1 = projectState ctx observer s') →
        (covertChannelEntry .lockContention).modelVisible = false ∧
          projectState ctx observer
              (SeLe4n.Kernel.Concurrency.withLockSet S core action s).1
            = projectState ctx observer s
  | .tlbResidency =>
      ∀ (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) (c : CoreId)
        (vTlb : Vector TlbState SeLe4n.Kernel.Concurrency.numCores),
        (covertChannelEntry .tlbResidency).modelVisible = false ∧
          ObservableState.onCore ctx c L { s with perCoreTlb := vTlb }
            = ObservableState.onCore ctx c L s
  | .icacheResidency =>
      ∀ (ctx : LabelingContext) (L : SecurityLabel) (s : SystemState) (c : CoreId)
        (vIcache : Vector ICacheState SeLe4n.Kernel.Concurrency.numCores),
        (covertChannelEntry .icacheResidency).modelVisible = false ∧
          ObservableState.onCore ctx c L { s with perCoreICache := vIcache }
            = ObservableState.onCore ctx c L s
  | .auditOccupancy =>
      ∀ (log : DeclassificationAuditLog) (e : DeclassificationEvent),
        (covertChannelEntry .auditOccupancy).modelVisible = true ∧
          ((recordDeclassificationChecked log e).isSome = true ↔
            log.length < maxDeclassificationAuditEntries)

/-- WS-SM SM9.A / PR #870 round 7 (the CC-8 witness): the entry's
`modelVisible := true` conjoined with the **capacity gate** that carries the
channel — the checked recorder succeeds exactly below the bound, so an
authorized caller's outcome is a function of the fill level.  The richer
witnesses — the drain-flip (`auditDrain_flips_declassify_outcome`) and the
occupancy alphabet (`auditOccupancy_alphabet_bounded`) — live in
`AuditRead.lean`, below this module's import reach the other way; the binding
theorem `acceptedCovertChannel_auditOccupancy_bounded` in
`DeclassificationPerCore.lean` ties this entry's literals to them. -/
theorem acceptedCovertChannel_auditOccupancy_capacity_gates :
    ∀ (log : DeclassificationAuditLog) (e : DeclassificationEvent),
      (covertChannelEntry .auditOccupancy).modelVisible = true ∧
        ((recordDeclassificationChecked log e).isSome = true ↔
          log.length < maxDeclassificationAuditEntries) :=
  fun log e => ⟨rfl, recordDeclassificationChecked_isSome_iff log e⟩

/-- SM8.B.8 (review round 17): **the evidence itself**, as a dependently-typed
total function — the load-bearing obligation the string table below only names.

Every channel must supply a proof of *its own* `evidenceProp`, so the id → proof
mapping is checked by the elaborator rather than by a reader comparing two
lists.  Adding a channel without deciding what proves its classification is now
a missing-arm error, and misattributing an existing proof is a type error.

The two residency channels legitimately share `…_residency_excluded_from_view`,
which proves both exclusions at once; here each takes the projection of that
theorem it needs, so the sharing is visible in the proof term rather than
asserted about a repeated string. -/
def covertChannelEvidence : (id : CovertChannelId) → id.evidenceProp
  | .schedulingState => fun ctx c L s =>
      acceptedCovertChannel_scheduling_is_model_visible ctx c L s
  | .machineTimer => fun ctx L s c t =>
      acceptedCovertChannel_machineTimer_excluded_from_view ctx L s c t
  | .tcbMetadata => fun ctx c L s tid tcb hObs hLookup =>
      acceptedCovertChannel_tcbMetadata_is_model_visible ctx c L s tid tcb hObs hLookup
  | .objectStoreMetadata => fun ctx c L s =>
      acceptedCovertChannel_objectStoreMetadata_is_model_visible ctx c L s
  | .lockContention => fun ctx observer S core action s hInv hActionInv hAction =>
      acceptedCovertChannel_lockContention_is_timing_only ctx observer S core action s
        hInv hActionInv hAction
  | .tlbResidency => fun ctx L s c vTlb =>
      let ⟨hTlb, _, hViewTlb, _⟩ :=
        acceptedCovertChannel_residency_excluded_from_view ctx L s c vTlb default
      ⟨hTlb, hViewTlb⟩
  | .icacheResidency => fun ctx L s c vIcache =>
      let ⟨_, hIcache, _, hViewIcache⟩ :=
        acceptedCovertChannel_residency_excluded_from_view ctx L s c default vIcache
      ⟨hIcache, hViewIcache⟩
  | .auditOccupancy => acceptedCovertChannel_auditOccupancy_capacity_gates

/-- SM8.B.8: **the projection theorem that justifies each entry's
`modelVisible`**, compile-time-validated through `niName!`.

This is the table the fourth review round asked for.  Every id must name a
theorem, the macro rejects a name that does not resolve, and each named theorem
states the entry's `modelVisible` literal *conjoined with* the projection fact
that makes it true — so a reclassification without a matching change to the
projection breaks the witness, not just this string.

Kept for the count theorems and the Tier-3 anchors, which need a comparable
value; `covertChannelEvidence` above is the obligation that actually binds. -/
def covertChannelEvidenceName : CovertChannelId → String
  | .schedulingState => niName! acceptedCovertChannel_scheduling_is_model_visible
  | .machineTimer => niName! acceptedCovertChannel_machineTimer_excluded_from_view
  | .tcbMetadata => niName! acceptedCovertChannel_tcbMetadata_is_model_visible
  | .objectStoreMetadata => niName! acceptedCovertChannel_objectStoreMetadata_is_model_visible
  | .lockContention => niName! acceptedCovertChannel_lockContention_is_timing_only
  | .tlbResidency => niName! acceptedCovertChannel_residency_excluded_from_view
  | .icacheResidency => niName! acceptedCovertChannel_residency_excluded_from_view
  | .auditOccupancy => niName! acceptedCovertChannel_auditOccupancy_capacity_gates

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
    ∀ id : CovertChannelId, (covertChannelEvidenceName id).length > 0 := by
  intro id; cases id <;> decide

/-- SM8.B.8: the two residency channels share a witness (it proves both
exclusions at once) and every other channel — CC-8 included since PR #870
round 7 — has its own.  Pinned so a reader knows the sharing is intentional
rather than a copy-paste. -/
theorem covertChannelEvidence_shared_only_for_residency :
    (CovertChannelId.all.map covertChannelEvidenceName).eraseDups.length = 7 := by decide


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
    (hDispatchProj : ∀ decoded tid stPost, dispatchSyscall decoded tid st = .ok ((), stPost) →
      projectState ctx observer stPost = projectState ctx observer st)
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
    (hDispatchProj : ∀ decoded tid stPost, dispatchSyscall decoded tid st = .ok ((), stPost) →
      projectState ctx observer stPost = projectState ctx observer st)
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
