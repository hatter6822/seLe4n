# Security Advisory — seLe4n Kernel

## SA-1: Starvation Freedom Not Guaranteed (H-1)

**Severity**: HIGH (design-level — documentation only)
**Component**: Scheduler (`SeLe4n/Kernel/Scheduler/Operations/Core.lean`)
**Audit reference**: WS-X/X5-A, finding H-1

### Description

seLe4n implements a strict fixed-priority preemptive scheduler matching seL4's
classic scheduling model (`Core.lean:259–264`). Under this model, **starvation
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
   enforcement. These are not yet modeled in seLe4n but could be added as a
   future extension without breaking the formal model.

### seL4 Precedent

seL4 uses the same fixed-priority preemptive model (see seL4 Reference Manual
§6.2). The seL4 MCS extensions (Klein et al., 2018) add optional bandwidth
enforcement but are a separate scheduling policy layer above the base kernel.

### Formal Model Status

The scheduler's `schedule` function (`Core.lean:274`) selects the highest-priority
runnable thread via `chooseThread`. The EDF (Earliest Deadline First) variant
(`edfPriority`) provides deadline-aware selection but does not enforce starvation
freedom — it only changes the priority metric, not the preemption semantics.

No formal starvation freedom property is claimed or proven. All scheduler
invariants (`schedulerInvariantBundleFull`) concern structural correctness
(queue consistency, time-slice positivity, context matching), not liveness.

---

## SA-2: Default Labeling Context Defeats Information Flow Enforcement (M-2)

**Severity**: MEDIUM (configuration-level)
**Component**: Information Flow (`SeLe4n/Kernel/InformationFlow/Policy.lean`)
**Audit reference**: WS-X/X5-H, finding M-2

### Description

The `defaultLabelingContext` (`Policy.lean:214`) assigns `publicLabel` (low
confidentiality, untrusted integrity) to ALL entities. Under this labeling,
`securityFlowsTo` is trivially `true` for all entity pairs, meaning **no
information flow is restricted**.

This is formally proven by `defaultLabelingContext_insecure` (`Policy.lean:234`)
and `defaultLabelingContext_all_threads_observable` (`Policy.lean:244`).

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
(`Projection.lean:401`).

### Bandwidth Analysis

- **Channel capacity**: Bounded by domain schedule length × switch frequency
- **Practical bandwidth**: Sub-bit-per-second under normal scheduling
  configurations (domain switches at 1–100 Hz, 4 scalar values per observation)
- **Theoretical maximum**: ≤ log₂(|domainSchedule|) × switchFreq bits/second

### Mitigation

Temporal partitioning via domain scheduling (already present) bounds the channel
bandwidth. This covert channel is accepted per seL4 design precedent (Murray et
al., CCS 2013). Hardware-level isolation (partitioned caches, separate timer
domains) would further reduce bandwidth but is beyond the kernel model's scope.
