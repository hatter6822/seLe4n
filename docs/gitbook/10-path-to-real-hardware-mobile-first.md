# Path to Real Hardware (Raspberry Pi 5 First)

## Why this chapter changed

The project hardware direction is now explicitly **Raspberry Pi 5 first**.

Earlier documentation described a broad mobile-first direction. That remains useful context, but
execution planning now prioritizes a concrete first architecture target to reduce ambiguity and
improve milestone accountability.

## 1. Hardware reality check

seLe4n is currently a formal and executable model project, not a direct deployable kernel image.
The path to real hardware is staged and contract-driven:

1. architecture-neutral semantics and invariants,
2. explicit architecture-binding interfaces,
3. platform-specific binding of those interfaces,
4. traceable evidence from model behavior to platform assumptions.

## 2. Why Raspberry Pi 5 first

1. practical ARM64 platform for repeated experiments,
2. realistic enough interrupt/memory/boot profile for architecture-bound modeling,
3. broad tooling availability for incremental bring-up,
4. good tradeoff between accessibility and systems realism.

## 3. Stage model toward Raspberry Pi 5 relevance

### Stage H0 — Completed baseline hardening (M1–M5)

- scheduler/capability/IPC/lifecycle/service semantics and proof bundles,
- deterministic success/failure semantics and executable evidence,
- testing tiers and CI contracts.

### Stage H1 — Current execution (M6)

- extract architecture assumptions as explicit interfaces,
- define proof-carrying adapters from architecture-neutral semantics,
- harden boot/runtime boundary obligations as concrete contracts.

### Stage H2 — Raspberry Pi 5 contract instantiation (post-M6)

- instantiate M6 interfaces for Raspberry Pi 5 constraints,
- map platform assumptions to theorem obligations,
- keep core theorem surfaces reusable.

### Stage H3 — Minimal platform-oriented trust partition

- define first constrained deployment partition,
- map service graph boundaries to capability distribution constraints,
- validate expected failure semantics for restart/isolation paths.

### Stage H4 — Evidence convergence

- connect executable scenarios to platform-facing assumptions,
- extend symbol/fixture coverage to architecture-bound claims,
- package evidence for iterative integration decisions.

## 4. Raspberry Pi 5 target outcomes (long horizon)

1. explicit platform-assumption contract inventory,
2. architecture-binding interfaces that do not invalidate core proofs,
3. predictable failure semantics for boundary violations,
4. reusable traceability from theorem claims to validation artifacts,
5. incremental integration path from model-level confidence to platform-level confidence.

## 5. Risks and mitigations

1. **Premature platform lock-in**
   - mitigation: complete M6 contract surfaces before broad platform encoding.
2. **Proof complexity growth at binding boundary**
   - mitigation: maintain local-first theorem layering and narrow adapter contracts.
3. **Evidence mismatch between model and platform assumptions**
   - mitigation: enforce synchronized updates across traces, tests, and docs.
4. **Roadmap ambiguity**
   - mitigation: keep README/spec/GitBook synchronized on Raspberry Pi 5-first direction.

## 6. What contributors can do now

- align milestone PRs to M6 workstreams,
- document architecture assumptions explicitly,
- add executable evidence for boundary success/failure behavior,
- avoid implicit platform assumptions in architecture-neutral modules,
- keep handoff notes explicit for the Raspberry Pi 5 slice.
