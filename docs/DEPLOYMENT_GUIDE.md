# seLe4n Production Deployment Guide

**Status**: Pre-release — requires external threat-model review before
high-assurance deployment.  **The kernel does not boot yet**: producing a
bootable image is SM10.1's work, so this guide describes the deployment model
the kernel is being built to satisfy, not a procedure you can run today.  See
[`CLAIM_EVIDENCE_INDEX.md`](CLAIM_EVIDENCE_INDEX.md) §8 for what is and is not
claimed.

---

## 1. Security Model Overview

seLe4n implements a formally verified microkernel with machine-checked
information flow enforcement. Before deploying in production, deployers must
understand the security model's scope, design decisions, and known limitations
documented in this guide.

### 1.1 Information Flow Enforcement

The kernel enforces non-interference (NI) across the following subsystems:

- **IPC** (endpoint send/receive, call/reply, notifications)
- **Scheduling** (thread selection, yield, timer tick, domain rotation)
- **Capability operations** (insert, delete, revoke, mint)
- **Lifecycle** (thread suspend/resume, object retype)
- **Decode/dispatch** (syscall argument decode, capability-gated dispatch)

The NI model uses 35 `NonInterferenceStep` constructors
(`SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean`) covering all
kernel-primitive transitions with per-step and trace-level NI proofs.

**What NI does NOT cover** (see Section 3):

- Service orchestration internals (lifecycle, restart policies, dependency
  resolution, heartbeat state)
- Cache and timing side channels (hardware-level; see F-17 in audit)

### 1.2 Integrity Model — Non-BIBA Authority Flow (F-04)

seLe4n uses a **non-standard BIBA integrity model** optimized for capability
authority delegation. This is a deliberate design decision, not a bug.

| Flow direction | seLe4n | Standard BIBA |
|----------------|--------|---------------|
| Trusted -> Untrusted (write-down / authority delegation) | **ALLOWED** | Denied |
| Untrusted -> Trusted (write-up / privilege escalation) | **DENIED** | Allowed |
| Same trust level | Allowed | Allowed |

**Rationale**: In a capability system, authority flows downward via delegation.
Trusted code grants capabilities to untrusted code (write-down). The reverse
(untrusted code escalating to trusted) is the actual security threat and is
blocked.

**Formal witnesses** (`SeLe4n/Kernel/InformationFlow/Policy.lean`):

| Theorem | Purpose |
|---------|---------|
| `integrityFlowsTo_is_not_biba` | Proves seLe4n differs from BIBA |
| `integrityFlowsTo_prevents_escalation` | Proves escalation is denied |
| `securityFlowsTo_prevents_label_escalation` | Combined 2D label proof |

A standard BIBA reference implementation (`bibaIntegrityFlowsTo`) is
provided for comparison and could serve as a drop-in replacement if a deployment
requires strict BIBA semantics.

**RECOMMENDATION**: Commission an external threat-model review of the non-BIBA
integrity direction before deploying in high-assurance environments. The
authority-flow model is correct for capability-based systems but may not match
all deployment threat models.

### 1.3 Known Covert Channels (F-06)

The domain scheduling metadata is unconditionally visible to all observers,
creating a bounded covert channel.

**Channel source**: 4 scheduling scalar values (`activeDomain`,
`domainSchedule`, `domainScheduleIndex`, `domainTimeRemaining`)

**Bandwidth analysis**:

| Metric | Value |
|--------|-------|
| Observable values per observation | 4 scalars |
| Channel capacity | &le; log&#8322;(N &times; (Q+1)) &times; tickFreq bps, N = \|domainSchedule\|, Q = your countdown cap |
| Upper bound (N&le;16, Q&le;255, F = 1000 Hz tick) | &le; 12 bits per observation, &le; 12&nbsp;000 bits/second |
| Realizable rate | **Not bounded by this analysis** — budget against the upper bound |
| Without a countdown cap, or with an empty schedule | **Unbounded** — see below |
| Instances | **One per core** under SMP |

**Formal witnesses** (`SeLe4n/Kernel/InformationFlow/Projection.lean`):

| Theorem | Where | Purpose |
|---------|-------|---------|
| `acceptedCovertChannel_scheduling` | `Projection.lean` | Witnesses channel existence |
| `schedulingCovertChannel_bounded_width` | `Projection.lean` | Confirms the channel is transparent (the projections are the raw scheduler reads) — **not** a capacity bound |
| `schedulingChannel_not_bounded_by_scheduleLength` | `CovertChannelPerCore.lean` | Why Q is required: `domainTimeRemaining` is an unrestricted `Nat`, so schedule length alone bounds nothing |
| `schedulingChannel_alphabet_bounded` | `CovertChannelPerCore.lean` | **The capacity bound**: the observation alphabet injects into `Fin (N × (Q+1))` |
| `schedulingObservationCode_injective` | `CovertChannelPerCore.lean` | Why that injection loses nothing |
| `schedulingChannel_full_observation_determined` | `CovertChannelPerCore.lean` | Extends the bound to `activeDomain`, under `domainConsistentOnCore` |
| `schedulingObservation_changes_on_domain_tick` | `CovertChannelPerCore.lean` | **Why the rate factor is the tick rate**: an ordinary tick decrements the observed countdown, so observations differ between domain switches |
| `schedulingChannel_trace_capacity` | `CovertChannelPerCore.lean` | The run-length bound: an n-observation trace is one of `alphabet ^ n` (`boundedCodeTraces`, whose length is exactly that) |

**Mitigation**: Temporal partitioning via domain scheduling (already present).
Each domain receives guaranteed time quanta.

**You must supply a non-empty schedule and a countdown cap Q.**  Both are
deployment obligations; the kernel discharges the other three conditions
(`domainScheduleIndexInBoundsOnCore`, `domainConsistentOnCore`, and an unchanged
`domainSchedule` — the model's one schedule mutator,
`setDomainScheduleChecked` in `Model/State.lean`, is exercised only from
test harnesses and no syscall routes to it).  The full list
is `schedulingCapacityPreconditions` / `schedulingCapacityComparable` in
`CovertChannelPerCore.lean`; `docs/SECURITY_ADVISORY.md` §SA-3 tabulates who
discharges each.  An empty schedule (single-domain mode) makes the index-bounds
invariant vacuous, so the observed index is unbounded and no figure applies.

**No "practical bandwidth" figure is offered.**  Earlier revisions claimed
sub-bit-per-second at the same rates this table costs at thousands of
bits/second; that claim had no derivation and has been removed rather than
re-justified.

**Budget against the tick rate, not the switch rate.**  An earlier revision of
this table multiplied the per-observation figure by the domain-*switch*
frequency.  `domainTimeRemaining` is one of the observed components and every
ordinary timer tick decrements it, so a receiver can read a fresh value once per
tick — three orders of magnitude more often on the canonical 1 ms
configuration.  `schedulingObservation_changes_on_domain_tick` is the proof.

**You must supply Q.**  The capacity figure above holds only for a deployment
that caps `domainTimeRemaining`; without such a cap this analysis gives **no**
bound, and `schedulingChannel_not_bounded_by_scheduleLength` is the proof of
that rather than a caveat about it.  An earlier revision of this guide quoted
&le; log&#8322;(\|domainSchedule\|) &times; switchFreq with no Q factor — that
figure was false as stated, and a revision after it swung the other way and
claimed no bound at all.  Both are superseded by the proven bound.

**seL4 precedent**: This covert channel matches seL4's accepted design
(Murray et al., "seL4: From General Purpose to a Proof of Information Flow
Enforcement", IEEE S&P 2013). Full elimination requires hardware-level temporal
isolation beyond the kernel model's scope.

---

## 2. Required Configuration

### 2.1 Security Labeling Override (F-07) -- MANDATORY

The `defaultLabelingContext` (`Policy.lean`) assigns `publicLabel` (low
confidentiality, untrusted integrity) to **ALL** entities. Under this labeling,
`securityFlowsTo` is trivially `true` for all entity pairs, meaning **no
information flow is restricted**.

**Formal proof of insecurity** (`SeLe4n/Kernel/InformationFlow/Policy.lean`):

| Theorem | Proves |
|---------|--------|
| `defaultLabelingContext_insecure` | All object pairs allow flow |
| `defaultLabelingContext_all_threads_observable` | All threads mutually observable |

**Production deployments MUST override `defaultLabelingContext`** with a
domain-specific labeling policy. Failure to do so negates all information-flow
enforcement guarantees.

#### Override Example: Two-Domain Labeling Policy

```lean
import SeLe4n.Kernel.InformationFlow.Policy

/-- Example: two-domain labeling policy.
    Domain A (trusted): objects 0-3, threads 0-3, endpoints 0-1
    Domain B (untrusted): all other entities -/
def productionLabelingContext : LabelingContext :=
  { objectLabelOf := fun oid =>
      if oid.toNat < 4 then SecurityLabel.kernelTrusted
      else SecurityLabel.publicLabel
    threadLabelOf := fun tid =>
      if tid.toNat < 4 then SecurityLabel.kernelTrusted
      else SecurityLabel.publicLabel
    endpointLabelOf := fun eid =>
      if eid.toNat < 2 then SecurityLabel.kernelTrusted
      else SecurityLabel.publicLabel
    serviceLabelOf := fun _ => SecurityLabel.kernelTrusted }
```

The `LabelingContext` structure (`Policy.lean`) carries four label
assignment functions (`objectLabelOf`, `threadLabelOf`, `endpointLabelOf`,
`serviceLabelOf`), an optional `memoryOwnership` for memory projection,
and three policy knobs: `endpointPolicy` and `declassificationPolicy`
(§2.3) and `auditMonitorClearance` — the audit-trail read/drain gate a
declassifying deployment must configure (§2.3).

See also: `docs/SECURITY_ADVISORY.md` SA-2.

### 2.2 Platform Binding

Hardware-specific configuration is required for production deployment:

- **MachineConfig**: CPU parameters, memory layout, timer configuration
- **MMIO regions**: BCM2712 addresses for Raspberry Pi 5 (see
  `SeLe4n/Platform/RPi5/Board.lean`)
- **PlatformBinding**: Typeclass instance providing boot, runtime, and
  interrupt contracts (see `SeLe4n/Platform/Contract.lean`)

The simulation platform (`SeLe4n/Platform/Sim/`) provides permissive contracts
for testing. Production deployments must use hardware-specific contracts (e.g.,
`SeLe4n/Platform/RPi5/Contract.lean` for Raspberry Pi 5).

### 2.3 Endpoint flow overrides and the declassification policy (WS-SM SM8.C)

Two `LabelingContext` fields govern flows the base lattice would otherwise
decide on its own.  **Both default to the safe value, so a deployment that
configures neither behaves exactly as it did before they existed.**

#### `endpointPolicy` — per-endpoint flow overrides

`LabelingContext.endpointPolicy` maps an endpoint's `ObjId` to an optional
`DomainFlowPolicy`.  The live IPC gates read it through `endpointFlowGate`,
which **conjoins** the override with the global lattice check:

```
endpointFlowGate ctx ep src dst  =  securityFlowsTo src dst  &&  override ep src dst
```

The conjunction is the security property, not an implementation detail.  It
means an override can only ever **narrow**:

* A *narrowing* override refuses traffic the lattice would have allowed — the
  intended use (an endpoint that only two of five permitted domains may use).
* A *widening* override — one that permits a pair the lattice denies — has **no
  effect**.  `endpointGateRestricted_always` proves the gate is restricted for
  every context with no well-formedness hypothesis, and
  `endpointGateRestricted_survives_widening_override` is the witness that a
  misconfigured, V6-G-violating policy still cannot open a flow.

So a misconfiguration here can cause a **denial of service** (traffic refused
that policy intended to allow); it cannot cause a **leak**.  Review overrides
for availability, not for isolation.

**Scope**: `endpointPolicy` governs flows *crossing an endpoint*.  It does not
reach the notification gates (a notification is not an endpoint) or the reply
leg of `replyRecv` (a thread-to-thread flow crossing no endpoint) — checked
facts, not conventions: `notificationSignalChecked_endpointPolicy_independent`,
`notificationWaitChecked_endpointPolicy_independent`,
`endpointReplyChecked_endpointPolicy_independent`.

#### `declassificationPolicy` — authorized downgrade paths

`LabelingContext.declassificationPolicy` names the domain pairs the
`.declassify` syscall may downgrade along.  **It defaults to deny-all**, so an
unconfigured deployment cannot declassify at all: every `.declassify` returns
`.declassificationDenied`.

Configure it only if your deployment has a *trusted downgrader* — a component
whose job is to release sanitized information across a boundary the lattice
forbids.  What the kernel does when it is configured:

1. Verifies the base lattice **denies** the flow (otherwise it is not a
   declassification, and the syscall returns `.flowDenied`).
2. Verifies `declassificationPolicy` **permits** the pair.
3. Appends one attributed entry to `SystemState.declassificationAuditLog`.

Neither security domain is a caller argument: the source is read off the thread
the executing core is running, the destination off the target object's own
labeling.  A caller cannot record a downgrade between two domains it has nothing
to do with.

**`.declassify` moves no data.**  Its entire state effect is the audit entry
(`authorizeDeclassificationOnCore_frame`).  It is a kernel-arbitrated,
kernel-recorded *authorization*, not a transfer; the transfer is whatever the
downgrader does next.

**Operational consequence — the trail is bounded and fail-closed.**  The audit
trail holds at most `maxDeclassificationAuditEntries` (256) entries.  At
capacity, `.declassify` **refuses the downgrade** with
`.auditLogCapacityExceeded` rather than dropping a record: an authorized
downgrade the kernel did not record is precisely the failure the audit exists to
prevent.  A deployment that declassifies routinely must therefore treat
`.auditLogCapacityExceeded` as an operational alert.

**The reader and drain exist (WS-SM SM9.A, v0.33.42+).**  Two live syscalls
close the 256-entry cliff: `.auditRead` (SyscallId 31) and `.auditDrain`
(SyscallId 32), implemented in `SeLe4n/Kernel/InformationFlow/AuditRead.lean`
behind a dedicated `CapTarget.auditTrail` capability. The clearance filter
(`auditLogVisibleTo`) is a function of the reader's clearance alone; a
**drain** additionally demands a complete view — the transition guard
(`auditDrainViewComplete`) refuses any drain whose clearance hides a
recorded source domain, because a partial-visibility drain would reveal
the positions of hidden entries. **Deployment-mandatory knob**: the live
`.auditRead`/`.auditDrain` arms consume the configured clearance only
through `validatedAuditMonitorClearance` (`AuditRead.lean`), which admits
it only when it dominates **all four** legacy security labels
(`legacySubjectLabels` — the kernel's entire subject/object label space)
and validates to `none` otherwise. A deployment that declassifies at all
must therefore configure `auditMonitorClearance` to dominate every legacy
label — a clearance covering merely the domains the policy lets
declassify is rejected whole, leaving **no monitor at all** (exactly the
unconfigured posture) — and run a monitor that drains the trail; an
unconfigured deployment has no audit reader and keeps the 256-per-boot
cliff as its conservative default.

**The declassification surface is wider than `.declassify` (SM9.B–SM9.D).**
`.declassifySignal` (SyscallId 33) is the data-carrying declassification — a
bound notification signal whose badge may cross a boundary the base lattice
denies, gated on both hops and recorded per authorized hop. Refused
downgrades are recorded too: the type-bounded refusal ledger
(`SystemState.declassificationRefusals`, SM9.B) lets a monitor distinguish
"no attempts" from "many attempts, all denied", read through `.auditRead`
sub-operations behind the same monitor gate. Causal provenance
(`DeclassificationTaint`, SM9.D) lets the monitor's laundering detector
follow content through ordinary IPC between two downgrades instead of
guessing from domains and timestamps.

---

## 3. NI Boundary Scope (F-05)

The kernel's non-interference guarantees have an explicitly documented boundary.

### 3.1 What Is Covered

The 35 `NonInterferenceStep` constructors in
`SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` cover all kernel
primitive transitions. Per-step NI proofs and trace-level composition theorems
ensure that information flows only through policy-authorized channels.

### 3.2 What Is NOT Covered

**Service orchestration internals** are explicitly outside the NI boundary.

The `serviceOrchestrationOutsideNiBoundary` theorem
(`Projection.lean`) formally proves that service orchestration state
(lifecycle policies, restart state, heartbeat, dependency resolution order)
is not captured by the NI projection model. Only the service registry layer
(presence and dependency edges) is observable.

**Implication for deployers**: If your deployment relies on service-layer
isolation, you must analyze service-layer information flows separately.
The kernel NI guarantees do not extend to service orchestration semantics.

**Additional exclusions**:

- **Cache/timing side channels** (F-17): Not modeled; requires hardware-level
  measurement and mitigation (partitioned caches, separate timer domains)
- **MMIO volatile non-determinism** (F-16): Bounded by `MmioSafe` hypothesis;
  deferred to hardware binding (H3)

---

## 4. Pre-Deployment Checklist

- [ ] **Custom LabelingContext configured** (F-07) -- override
  `defaultLabelingContext` with domain-specific labels; verify with
  `defaultLabelingContext_insecure` theorem as negative test
- [ ] **Integrity model reviewed** (F-04) -- assess whether the non-BIBA
  authority-flow model matches your deployment's threat model; consider
  external review for high-assurance environments
- [ ] **Covert channel bandwidth acceptable** (F-06) -- budget the
  scheduling covert channel against the proven upper bound in §1.3 (your
  N, Q and tick rate; &le;12,000 bits/second at the canonical bounds — no
  smaller "practical" figure is offered) and confirm it is within your
  security policy
- [ ] **Service-layer NI analyzed separately** (F-05) -- kernel NI does not
  cover service orchestration; conduct independent analysis if service
  isolation is required
- [ ] **Platform binding validated** -- use hardware-specific `PlatformBinding`
  instance (not simulation contracts) for target hardware
- [ ] **Endpoint overrides reviewed for availability** (SM8.C) -- a widening
  `endpointPolicy` override cannot leak (the gate conjoins), but a narrowing one
  can refuse traffic policy intended to allow; review §2.x
- [ ] **Declassification policy decided** (SM8.C/SM9) -- the default is deny-all
  and `.declassify` is refused outright; if a trusted downgrader is configured,
  treat `.auditLogCapacityExceeded` as an alert AND provision the read/drain
  path (§2.3): grant the monitor a `CapTarget.auditTrail` capability, configure
  `auditMonitorClearance` to dominate **all four** legacy security labels
  (`validatedAuditMonitorClearance` rejects anything less, leaving no monitor
  at all), and run a drain process -- an unconfigured deployment keeps the
  256-per-boot fail-closed cliff
- [ ] **Security advisory reviewed** -- read `docs/SECURITY_ADVISORY.md`
  (SA-1: starvation, SA-2: labeling, SA-3: covert channel)
- [ ] **Test suite passed** -- run `./scripts/test_full.sh` with production
  configuration

---

## 5. Cross-References

| Document | Content |
|----------|---------|
| [`docs/SECURITY_ADVISORY.md`](SECURITY_ADVISORY.md) | SA-1 (starvation), SA-2 (labeling override), SA-3 (covert channel) |
| [`docs/THREAT_MODEL.md`](THREAT_MODEL.md) | Trust boundaries, attack surface analysis |
| [`docs/spec/SELE4N_SPEC.md`](spec/SELE4N_SPEC.md) | Formal specification, NI boundary scope |
| [`docs/HARDWARE_BOUNDARY_CONTRACT_POLICY.md`](HARDWARE_BOUNDARY_CONTRACT_POLICY.md) | Hardware/software boundary contracts |
| `SeLe4n/Kernel/InformationFlow/Policy.lean` | Security label lattice, flow policies, labeling context |
| `SeLe4n/Kernel/InformationFlow/Projection.lean` | NI projection, covert channel analysis |

---

*Created as part of WS-AD Phase AD3 (v0.25.13). Addresses findings F-04
(HIGH), F-05 (HIGH), F-06 (HIGH), F-07 (MEDIUM) from the pre-release audit.*
