# Path to Real Hardware (Mobile-First)

## Why mobile-first

Mobile devices are an important practical target for high-assurance compartmentalization:

- they run heterogeneous, privilege-sensitive workloads,
- they are exposed to hostile networks and app ecosystems,
- and they require strong isolation with tight performance/power constraints.

A mobile-first strategy gives seLe4n a realistic deployment pressure profile early.

## Reality check: model-to-hardware is a multi-stage bridge

seLe4n today is a formal/executable model project, not a drop-in deployable kernel. A credible
hardware path requires staged convergence across semantics, tooling, architecture binding, and
system integration.

## Staged roadmap toward hardware relevance

### Stage H0: Semantic completeness in architecture-neutral model

- complete lifecycle/capability/IPC/scheduler interactions,
- harden invariant composition and error-path coverage,
- strengthen executable scenarios to represent realistic subsystem choreography.

### Stage H1: Architecture-binding interface plan

- identify architecture-dependent assumptions currently abstracted,
- define explicit interfaces for CPU mode transitions, interrupt surfaces, and memory mappings,
- keep architecture-neutral theorems reusable where possible.

### Stage H2: Boot and platform model alignment

- model assumptions required at early boot (object initialization, capability roots, thread startup),
- encode minimal platform contracts needed before user-space service graph starts.

### Stage H3: Mobile-oriented subsystem decomposition

- define trusted/less-trusted component boundaries for mobile use-cases,
- map expected services (UI, radio, storage, sensor brokering) to capability/IPC patterns,
- prioritize least-privilege capability distribution strategies.

### Stage H4: Performance and predictability envelope

- identify IPC and scheduling hot paths that matter on mobile SoCs,
- introduce scenario-driven performance hypotheses (without prematurely overfitting),
- track proof-friendly simplifications versus deployment realism trade-offs.

### Stage H5: Prototype integration path

- produce a small demonstrator topology that mirrors a realistic mobile security partition,
- connect formal model assumptions to implementation obligations,
- establish traceability from theorem claims to system-level tests.

## Mobile-first target outcomes (long horizon)

1. clear trust-boundary documentation for mobile service partitions,
2. lifecycle/capability semantics robust enough for dynamic service management,
3. explicit failure semantics for compromised/restarted services,
4. architecture-binding strategy that does not invalidate core proofs,
5. incremental evidence chain from model behavior to deployment constraints.

## Risks and mitigations

1. **Risk: overcommitting to hardware details too early**
   - mitigation: preserve architecture-neutral core while isolating binding interfaces.
2. **Risk: proof complexity explosion during architecture binding**
   - mitigation: keep theorem layering compositional and interface-driven.
3. **Risk: performance surprises on mobile IPC/scheduling paths**
   - mitigation: add scenario-guided profiling hypotheses early in H4 planning.
4. **Risk: docs drift between formal model and integration assumptions**
   - mitigation: treat roadmap and assumption docs as versioned artifacts with PR gating.

## What contributors can do now

- keep M4 work crisp and deterministic,
- document assumptions where lifecycle semantics intersect capability authority,
- add executable scenarios that resemble real compartment orchestration,
- and keep spec/development/testing/gitbook docs synchronized as the roadmap evolves.
