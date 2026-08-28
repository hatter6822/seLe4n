# Security Advisory — seLe4n Kernel

## SA-1: Starvation Freedom Not Guaranteed (H-1)

**Severity**: HIGH (design-level — documentation only)
**Component**: Scheduler (`SeLe4n/Kernel/Scheduler/Operations/Core.lean`)
**Audit reference**: WS-X/X5-A, finding H-1

### Description

seLe4n implements a strict fixed-priority preemptive scheduler matching seL4's
classic scheduling model (`Core.lean`). Under this model, **starvation
freedom is NOT a kernel property** — a continuously runnable high-priority thread
will indefinitely preempt all lower-priority threads.

This is an intentional design decision inherited from seL4, where starvation
prevention is the responsibility of user-level scheduling policy, not the kernel.

### Impact

- Lower-priority threads may never execute if a higher-priority thread remains
  continuously runnable.
- Real-time deadline guarantees depend on correct user-level admission control.
- Denial-of-service is possible if a high-priority thread enters an infinite loop.

### Recommended Mitigations (User-Level)

1. **Priority ceiling protocol**: Assign ceiling priorities to shared resources
   to bound priority inversion and ensure eventual execution.
2. **Admission control**: Validate at system design time that all threads meet
   their scheduling requirements under worst-case execution times.
3. **Watchdog timers**: Use hardware or software watchdog timers to detect and
   recover from runaway high-priority threads.
4. **Domain scheduling**: Use seLe4n's domain scheduling to provide temporal
   partitioning — each domain gets guaranteed time quanta regardless of thread
   priorities within other domains.
5. **MCS scheduling extensions**: seL4's MCS (Mixed-Criticality Systems)
   scheduling extensions add sporadic server semantics with bandwidth
   enforcement. seLe4n has since modeled its own bandwidth-enforcement
   layer (WS-Z): the `SchedContext` subsystem
   (`SeLe4n/Kernel/SchedContext/`) with a CBS budget engine
   (`consumeBudget`, `scheduleReplenishment`, `admissionCheck`,
   `cbsUpdateDeadline`) and per-core CBS under SMP
   (`Scheduler/Operations/PerCoreCbs.lean`, SM5).

### seL4 Precedent

seL4 uses the same fixed-priority preemptive model (see seL4 Reference Manual
§6.2). The seL4 MCS extensions (Klein et al., 2018) add optional bandwidth
enforcement but are a separate scheduling policy layer above the base kernel.

### Formal Model Status

The scheduler's `schedule` function (`Core.lean`) selects the highest-priority
runnable thread via `chooseThread`. EDF deadline tie-breaking lives inside
the selection helpers (`betterCandidate` / `chooseBestInBucketEffective` in
`Scheduler/Operations/Selection.lean`) and changes the priority metric, not
the preemption semantics.

Liveness properties now exist but are **hypothesis-conditional**, so the
headline of this advisory stands: starvation freedom is not guaranteed
unconditionally. `no_starvation_under_smp` and
`thread_eventually_scheduled_onCore`
(`Scheduler/Operations/PerCoreWcrt.lean`) prove a runnable thread is
eventually scheduled within a closed bound, and the 8-module
`Scheduler/Liveness/` WCRT surface carries the bound — under externalized
deployment hypotheses (e.g. `eventuallyExits`,
`Liveness/BandExhaustion.lean`). The structural scheduler invariants
(`schedulerInvariantBundleFull`) remain unconditional.

---

## SA-2: Default Labeling Context Defeats Information Flow Enforcement (M-2)

> **See also**: [`docs/DEPLOYMENT_GUIDE.md`](DEPLOYMENT_GUIDE.md) Section 2.1
> for override instructions with a concrete code example.

**Severity**: MEDIUM (configuration-level)
**Component**: Information Flow (`SeLe4n/Kernel/InformationFlow/Policy.lean`)
**Audit reference**: WS-X/X5-H, finding M-2

### Description

The `defaultLabelingContext` (`Policy.lean`) assigns `publicLabel` (low
confidentiality, untrusted integrity) to ALL entities. Under this labeling,
`securityFlowsTo` is trivially `true` for all entity pairs, meaning **no
information flow is restricted**.

This is formally proven by `defaultLabelingContext_insecure` (`Policy.lean`)
and `defaultLabelingContext_all_threads_observable` (`Policy.lean`).

### Impact

Production deployments using the default labeling context receive zero
information-flow enforcement — any entity can communicate with any other entity.

### Required Mitigation

**Production deployments MUST override `defaultLabelingContext` with a
domain-specific labeling policy** that assigns appropriate security labels
to each entity based on the deployment's security requirements.

---

## SA-3: Scheduling Covert Channel (M-3)

**Severity**: MEDIUM (accepted by design)
**Component**: Information Flow (`SeLe4n/Kernel/InformationFlow/Projection.lean`)
**Audit reference**: WS-X/X5-C, finding M-3

### Description

Scheduling metadata (`activeDomain`, `domainSchedule`, `domainScheduleIndex`,
`domainTimeRemaining`) is unconditionally visible to all observers. This creates
a covert channel where a high-security domain can influence scheduling state
observable by a low-security domain.

This is formally witnessed by `acceptedCovertChannel_scheduling`
(`Projection.lean`).

### Bandwidth Analysis

- **Channel capacity**: ≤ log₂(N × (Q + 1)) × **tickFreq** bits/second, where
  N = |domainSchedule| and **Q is a deployment-supplied bound on
  `domainTimeRemaining`**
- **Upper bound**: for N ≤ 16, Q ≤ 255 each observation is ≤ 12 bits, and at
  the canonical RPi5 1 ms tick (F = 1000 Hz) that is ≤ **12 000 bits/second**
- **Realizable rate**: **not bounded by this analysis** — see below

**The rate factor is the tick rate, not the switch rate.**  This advisory
previously quoted ≤ 1200 bits/second at a ≤ 100 Hz *domain-switch* rate.  That
understates the channel by an order of magnitude on the canonical
configuration: `domainTimeRemaining` is one of the observed components and an
ordinary timer tick decrements it, so consecutive observations differ between
switches and the observer is paced by **ticks**
(`schedulingObservation_changes_on_domain_tick`, PR #861 review round 12).  The
run-length form is `schedulingChannel_trace_capacity`: over n observations the
observer's whole trace is one element of `boundedCodeTraces alphabet n`, a set
whose size is exactly `alphabet ^ n`.

**There is no "practical bandwidth" figure.**  Earlier revisions of this
advisory claimed "sub-bit-per-second under normal scheduling configurations" at
the *same* configurations the table now costs at thousands of bits/second —
two numbers orders of magnitude apart for one configuration, and the
smaller one had no derivation behind it (PR #861 review round 9).  It has been
removed rather than re-justified: deriving a realizable rate needs a model of how
much of the alphabet a sender can actually control and a receiver actually
resolve, and this kernel model has neither.  **Budget against the upper bound.**

**Operators must supply Q.**  This advisory previously quoted
≤ log₂(|domainSchedule|) × switchFreq, omitting the Q factor.  That figure is
**false as stated** and the kernel now proves it so:
`schedulingChannel_not_bounded_by_scheduleLength` shows that schedule length
alone bounds nothing, because `domainTimeRemaining` is projected unfiltered and
ranges over all of `Nat`.  A deployment that does not cap the domain countdown
has **no** capacity bound from this analysis.

**Every condition the bound rests on**, bundled as
`schedulingCapacityPreconditions` (per state) and `schedulingCapacityComparable`
(across two states) so they can be cited by name rather than reconstructed from
three theorem signatures:

| Condition | Who discharges it |
|-----------|-------------------|
| `domainSchedule` non-empty | **Deployment.** Single-domain mode (empty schedule) makes the index-bounds invariant vacuous, so the observed index is unbounded and this analysis yields no figure. |
| `domainTimeRemaining ≤ Q` | **Deployment.** No cap, no bound. |
| `domainScheduleIndexInBoundsOnCore` | Kernel — maintained by the domain transitions. |
| `domainConsistentOnCore` | Kernel — what makes `activeDomain` a function of the schedule and index rather than a fourth independent value. |
| `domainSchedule` unchanged between observations | Kernel **today**: no syscall mutates the schedule. The assignment sites are the boot builder, the freeze copy, and the test-only mutator `setDomainScheduleChecked` (`Model/State.lean`, exercised from test harnesses; no dispatch arm routes to it). A Tier-3 anchor pins the absence of a `setDomainSchedule` syscall surface. Adding a schedule-reconfiguration syscall would invalidate this figure — the schedule is projected unfiltered, so a mutable schedule is its own channel and fixing N bounds nothing about its contents. |

The corrected figure is proven rather than asserted:
`schedulingChannel_alphabet_bounded` injects the per-core observation alphabet
into `Fin (N × (Q + 1))`, `schedulingObservationCode_injective` is why that
injection loses nothing, and `schedulingChannel_full_observation_determined`
extends it to the third observable component (`activeDomain`) under
`domainConsistentOnCore`.  All three are in
`SeLe4n/Kernel/InformationFlow/CovertChannelPerCore.lean`.

Under SMP the channel exists **once per core** — each core carries its own
`activeDomain`, `domainTimeRemaining` and `domainScheduleIndex` — so a
deployment budgeting total leakage should multiply by the core count.

### Mitigation

Temporal partitioning via domain scheduling (already present) bounds the channel
bandwidth, **given a countdown cap Q**. This covert channel is accepted per seL4
design precedent (Murray et al., CCS 2013). Hardware-level isolation (partitioned
caches, separate timer domains) would further reduce bandwidth but is beyond the
kernel model's scope.

---

## SA-4: Non-BIBA Integrity Model (F-04)

**Severity**: HIGH (design-level — documentation only)
**Component**: Information Flow (`SeLe4n/Kernel/InformationFlow/Policy.lean`)
**Audit reference**: WS-AD/AD3, finding F-04

### Description

seLe4n's integrity model deliberately differs from standard BIBA. The
`integrityFlowsTo` function (`Policy.lean`) allows trusted-to-untrusted
flow (authority delegation) and denies untrusted-to-trusted flow (privilege
escalation). Standard BIBA reverses this: it denies write-down and allows
write-up.

This design is intentional for capability-based authority tracking — trusted
code delegates capabilities downward, and untrusted code cannot escalate
authority upward.

### Formal Witnesses

- `integrityFlowsTo_is_not_biba` (`Policy.lean`): Proves the model differs
  from BIBA at the `(trusted, untrusted)` case.
- `integrityFlowsTo_prevents_escalation` (`Policy.lean`): Proves
  untrusted-to-trusted escalation is denied.
- `bibaIntegrityFlowsTo` (`Policy.lean`): Reference BIBA implementation
  provided as a drop-in alternative.

### Recommended Mitigation

Commission an external threat-model review before deploying in high-assurance
environments. Verify that the authority-flow integrity model matches your
deployment's trust assumptions.

See [`docs/DEPLOYMENT_GUIDE.md`](DEPLOYMENT_GUIDE.md) Section 1.2 for detailed
analysis and the pre-deployment checklist.
