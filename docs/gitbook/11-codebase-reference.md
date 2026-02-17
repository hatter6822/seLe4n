# Codebase Reference (Deep Developer Map)

This chapter maps where semantics, proofs, and execution evidence live in the current repository.
It also highlights where M6 closeout artifacts, active audit-remediation work, and post-remediation Raspberry Pi 5 work should land.

## 1. Repository-level structure

- `SeLe4n.lean`
  - package export root.
- `Main.lean`
  - executable scenario trace harness used by smoke checks.
- `SeLe4n/`
  - model, transition, and theorem modules.
- `scripts/`
  - tiered test runners and support helpers.
- `tests/fixtures/`
  - expected trace fragments for regression checks.

## 2. Module inventory by responsibility

### Foundation layer

- `SeLe4n/Prelude.lean`
  - IDs/aliases and core monadic kernel execution shape.
- `SeLe4n/Machine.lean`
  - machine-level state helpers.
- `SeLe4n/Model/Object.lean`
  - object-level representations.
- `SeLe4n/Model/State.lean`
  - global system-state composition and update helpers.

### Kernel transition/invariant families

- `SeLe4n/Kernel/Scheduler/Operations.lean`
- `SeLe4n/Kernel/Scheduler/Invariant.lean`
- `SeLe4n/Kernel/Capability/Operations.lean`
- `SeLe4n/Kernel/Capability/Invariant.lean`
- `SeLe4n/Kernel/IPC/Invariant.lean`
- `SeLe4n/Kernel/Lifecycle/Operations.lean`
- `SeLe4n/Kernel/Lifecycle/Invariant.lean`
- `SeLe4n/Kernel/Service/Operations.lean`
- `SeLe4n/Kernel/Service/Invariant.lean`
- `SeLe4n/Kernel/API.lean`

### Evidence and automation

- `scripts/test_tier0_hygiene.sh`
- `scripts/test_tier1_build.sh`
- `scripts/test_tier2_trace.sh`
- `scripts/test_tier3_invariant_surface.sh`
- `scripts/test_tier4_nightly_candidates.sh`
- umbrella runners: `test_fast.sh`, `test_smoke.sh`, `test_full.sh`, `test_nightly.sh`

## 3. How M6 should map onto this codebase

### M6 boundary extraction (WS-M6-A) ✅ **completed**

Implemented touch points:

- `SeLe4n/Kernel/Architecture/Assumptions.lean`
- `SeLe4n/Kernel/API.lean`
- `SeLe4n.lean`

Outcome: architecture-facing assumptions are isolated into explicit, named interface surfaces (including first-class contract references) and exported for downstream adapter/proof work.

### M6 adapter semantics (WS-M6-B) ✅ **completed**

Implemented touch points:

- `SeLe4n/Kernel/Architecture/Adapter.lean`
- `SeLe4n/Kernel/API.lean`
- `SeLe4n.lean`

Outcome: explicit deterministic adapter entrypoints compile with bounded failure mapping for invalid/unsupported architecture-bound contexts, using runtime-contract decidability witnesses for executable branch selection.

### M6 proof integration (WS-M6-C) ✅ **completed**

Implemented touch points:

- `SeLe4n/Kernel/Architecture/Invariant.lean`,
- `SeLe4n/Kernel/API.lean`,
- `SeLe4n.lean`.

Outcome: adapter assumptions are connected to theorem-layer invariants through `proofLayerInvariantBundle`, with explicit local/composed preservation hooks for success and denied/unsupported failure paths.

### M6 evidence expansion (WS-M6-D)

Likely touch points:

- `Main.lean`,
- `tests/fixtures/main_trace_smoke.expected`,
- tier scripts where new symbol checks are needed.

Goal: executable/test evidence for both success and bounded failure behavior.

## 4. Post-M6 placement guidance for Raspberry Pi 5 direction

When M6 interfaces stabilize, Raspberry Pi 5-specific work should:

1. instantiate interface contracts rather than rewriting core modules,
2. avoid embedding platform details directly into architecture-neutral invariant bundles,
3. preserve import stability from `SeLe4n.lean` and interface discoverability from `Kernel/API.lean`.

## 5. High-signal contributor checklist

Before opening an architecture-boundary PR:

1. identify affected module family and invariant bundle,
2. ensure failure-path semantics are explicit,
3. update tests/fixtures/symbol anchors as needed,
4. synchronize docs (README/spec/DEVELOPMENT/GitBook),
5. include a short "what this unlocks for Raspberry Pi 5 path" note.
