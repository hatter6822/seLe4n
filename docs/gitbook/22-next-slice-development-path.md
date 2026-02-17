# Next Slice Development Path (Post-M7)

This chapter describes the expected development path after M7 audit remediation closes.

The immediate objective after M7 is to start a hardware-oriented slice with lower integration risk,
using Raspberry Pi 5 as the first concrete architecture target.

## 1. Why this path exists

M1–M6 built a proof-bearing semantic model and architecture boundary contracts.
M7 hardens repository operations so that expansion can happen with stronger safety rails.
The next slice should convert that readiness into controlled hardware-facing progress.

## 2. Next-slice mission

Build a first hardware-instantiation lane that demonstrates:

1. architecture assumptions can be concretely bound without weakening theorem discipline,
2. adapter boundaries support realistic platform interactions,
3. trace/test/proof evidence remains reproducible during platform-specific growth.

## 3. Proposed workstreams for the next slice

> Naming is provisional until ratified in `docs/SEL4_SPEC.md`.

### WS-N1 — Assumption-to-platform binding package

- map architecture assumptions to Raspberry Pi 5-facing implementation notes,
- define obligation tables (what is trusted, validated, or deferred),
- add explicit mismatch handling for unsupported hardware states.

### WS-N2 — Hardware adapter specialization and simulation-backed validation

- implement architecture-specialized adapter stubs behind stable interfaces,
- maintain deterministic fallback paths for CI/non-hardware environments,
- add simulation traces that approximate hardware interaction sequences.

### WS-N3 — Architecture-targeted test and replay tracks

- extend test tiers with architecture-focused traces,
- add replay bundles that validate deterministic behavior under specialized adapters,
- ensure failure-path diagnostics remain concise.

### WS-N4 — Security/information-flow pre-foundation

- introduce first noninterference-oriented modeling scope,
- align capability and scheduler assumptions with future information-flow statements,
- publish acceptance criteria for security-proof slice successors.

### WS-N5 — Developer operations for hardware-adjacent work

- standardize local vs CI execution profiles,
- publish contributor instructions for architecture-specific checks,
- tighten changelog discipline around platform-facing semantics.

## 4. Entry criteria from M7

The next slice should not start until these conditions are true:

1. M7 high-priority outcomes are fully closed,
2. CI baseline includes reliable quality gates and deterministic replay,
3. type-safety migration for core IDs/pointers is complete or explicitly risk-accepted,
4. test-only permissive contracts are isolated from runtime surfaces,
5. docs consistently represent M7 as complete and next-slice as active.

## 5. Target outcomes for the next slice

1. **N-O1:** first architecture binding package is reviewable and traceable.
2. **N-O2:** adapter specialization path is executable in non-hardware CI mode.
3. **N-O3:** architecture-focused trace suite is integrated into tiered testing.
4. **N-O4:** information-flow trajectory is concretely staged (not just conceptual).
5. **N-O5:** contributor UX for platform-facing changes remains predictable.

## 6. Risks and mitigations

1. **Overcoupling risk**
   - mitigation: keep adapter interfaces stable, isolate platform-specific modules.
2. **Evidence drift risk**
   - mitigation: require trace/test/doc updates in the same PR range.
3. **Security claim inflation risk**
   - mitigation: stage claims explicitly and tie each to concrete proof obligations.
4. **Hardware lock-in risk**
   - mitigation: maintain simulation-backed abstractions and portability notes.

## 7. Recommended kickoff package

When opening the first next-slice PR set, include:

1. updated spec status markers,
2. next-slice workstream board with owners,
3. architecture binding assumptions table,
4. minimal adapter specialization prototype,
5. CI/test evidence commands and expected outputs.

This keeps the transition from “remediation” to “expansion” measurable and low-risk.
