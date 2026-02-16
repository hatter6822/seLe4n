# M6 Execution Plan and Workstreams

This chapter is the delivery playbook for the **current active slice (M6)**.

M6 goal: turn architecture-facing assumptions into explicit interfaces and proof-carrying contracts,
while preserving all established M1–M5 semantics/invariants/evidence obligations.

---

## 1. Slice-level target outcomes (definition of success)

M6 is considered complete only when all outcomes are met:

1. **Architecture-assumption interfaces are explicit**
   - architecture-bound assumptions are represented in named Lean-level interfaces,
   - assumptions are discoverable, reviewable, and test-addressable,
   - hidden architecture coupling in operational semantics is reduced.

2. **Proof-carrying adapter surfaces exist**
   - adapter predicates/theorems bridge architecture-neutral semantics to architecture-bound contexts,
   - theorem layering remains compositional (local first, composed second),
   - failure-path obligations remain explicit.

3. **Hardware-facing boundary contracts are hardened**
   - boot/runtime boundary assumptions are documented as contracts rather than narrative,
   - contract surfaces identify what is guaranteed by model code vs expected from platform adapters,
   - future hardware work can consume these contracts without rewriting core proof bundles.

4. **Evidence and CI continuity is preserved**
   - required Tier 0–3 gates remain green,
   - added surfaces get symbol/fixture coverage where appropriate,
   - roadmap claims in docs remain synchronized with code and tests.

---

## 2. M6 workstream breakdown

### WS-M6-A — Assumption inventory and boundary extraction ✅ **completed**

**Objective:** Enumerate architecture-facing assumptions currently implicit in model behavior and
lift them into explicit interface artifacts.

**Primary deliverables**
- assumption inventory surfaced in `SeLe4n/Kernel/Architecture/Assumptions.lean` (`ArchAssumption`, `assumptionInventory`),
- typed interface skeletons landed as `BootBoundaryContract`, `RuntimeBoundaryContract`, `InterruptBoundaryContract`, plus first-class `ContractRef` obligations,
- mapping from existing transitions/invariants captured by `assumptionTransitionMap` and `assumptionInvariantMap`.

**Exit signal**
- achieved: reviewers can point to a bounded list of assumptions and their interface location.

### WS-M6-B — Interface API and adapter semantics ✅ **completed**

**Objective:** Define interface APIs that maintain deterministic transition behavior and explicit
error branching.

**Primary deliverables**
- architecture-binding adapter API landed in `SeLe4n/Kernel/Architecture/Adapter.lean`,
- explicit error mapping for unsupported/invalid bound-context cases via `mapAdapterError`,
- deterministic state update semantics at the adapter boundary via `advanceTimerState` and `writeRegisterState`, with runtime contract decidability witnesses making branches executable.

**Exit signal**
- achieved: adapter entrypoints compile and preserve transition-level determinism expectations (`adapterAdvanceTimer_deterministic`).

### WS-M6-C — Proof-layer integration ✅ **completed**

**Objective:** Integrate adapter assumptions with existing theorem bundles (scheduler,
capability, IPC, lifecycle, service).

**Primary deliverables**
- local preservation theorems for boundary-facing operations are implemented in `SeLe4n/Kernel/Architecture/Invariant.lean`,
- composed preservation hooks from adapter contracts into bundle-level invariants are exposed through `proofLayerInvariantBundle`,
- explicit failure-path preservation statements exist for denied/unsupported adapter conditions (`adapterAdvanceTimer_error_invalidContext_preserves_proofLayerInvariantBundle`, `adapterAdvanceTimer_error_unsupportedBinding_preserves_proofLayerInvariantBundle`, `adapterWriteRegister_error_unsupportedBinding_preserves_proofLayerInvariantBundle`, `adapterReadMemory_error_unsupportedBinding_preserves_proofLayerInvariantBundle`).

**Exit signal**
- achieved: theorem surfaces are importable via `SeLe4n/Kernel/API.lean` and `SeLe4n.lean` without reworking M1–M5 invariant layout.

### WS-M6-D — Evidence, traces, and test anchors ✅ **completed**

**Objective:** Expand evidence so boundary assumptions and failure branches are executable and
regression-checked.

**Primary deliverables**
- `Main.lean` scenario growth where architecture-boundary success/failure behavior is externally visible (`adapterAdvanceTimer`, `adapterReadMemory`, `adapterWriteRegister` branches),
- fixture updates with semantic intent notes in `tests/scenarios/README.md` and stabilized evidence fragments in `tests/fixtures/main_trace_smoke.expected`,
- Tier 3 anchor updates in `scripts/test_tier3_invariant_surface.sh` for new theorem/invariant/API and trace claims.

**Exit signal**
- achieved: evidence demonstrates both expected success path and bounded failure semantics.

### WS-M6-E — Documentation and handoff packaging

**Objective:** Keep roadmap/spec/development/GitBook synchronized and prepare post-M6 execution
handoff.

**Primary deliverables**
- synchronized stage markers in root docs and GitBook,
- explicit list of post-M6 unlocks and deferrals,
- risk register updates tied to new boundary contracts.

**Exit signal**
- M6 claims are fully traceable from docs → code → proofs → tests.

---

## 3. Current-slice outcome matrix

| Outcome | Workstreams | Evidence command(s) | Completion signal |
|---|---|---|---|
| Explicit architecture assumptions | WS-M6-A, WS-M6-E | `lake build`, `./scripts/test_tier3_invariant_surface.sh` | Interfaces and symbols are discoverable and anchored |
| Adapter semantics and error handling | WS-M6-B | `./scripts/test_fast.sh`, `lake exe sele4n` | Deterministic success/failure behavior is executable |
| Proof compositionality across boundary | WS-M6-C ✅ completed | `lake build`, `./scripts/test_full.sh` | Local + composed theorems compile and remain layered |
| Regression-safe evidence growth | WS-M6-D ✅ completed | `./scripts/test_smoke.sh`, `./scripts/test_nightly.sh` | Fixture and nightly checks validate expected traces |
| Slice handoff coherence | WS-M6-E | docs review + CI-required set | Spec/README/DEVELOPMENT/GitBook all match |

---

## 4. Raspberry Pi 5 first-hardware direction

The first real-hardware architecture focus for seLe4n is **Raspberry Pi 5**. M6 does not attempt
full hardware enablement; it prepares the architecture-binding contracts needed for that path.

### Why Raspberry Pi 5 first

1. practical and accessible ARM64 platform for repeatable lab validation,
2. modern enough hardware profile for realistic interrupt/memory/boot assumptions,
3. strong community tooling ecosystem for incremental bring-up,
4. suitable for demonstrating constrained but meaningful trust-boundary deployments.

### What M6 must unlock specifically for Raspberry Pi 5

1. CPU/exception/interrupt boundary assumptions represented as interface contracts,
2. boot-time object and capability-root expectations captured as explicit prerequisites,
3. memory-mapping assumptions isolated from architecture-neutral invariants,
4. adapter hooks that permit later platform-specific refinement without proof reset.

---

## 5. Post-M6 immediate slice preview (M7 directional)

Planned immediate follow-on after M6 stabilization:

1. **Raspberry Pi 5 binding prototype track**
   - instantiate M6 interfaces for Raspberry Pi 5-specific constraints,
   - preserve architecture-neutral theorem reuse where possible.
2. **Platform-constraint evidence track**
   - extend executable scenarios and traces to reflect realistic boot/runtime assumptions.
3. **Trust-boundary validation track**
   - map service graph expectations onto a minimal realistic deployment partition.

These tracks should remain incremental and should not force bulk redesign of M1–M5 proof
surfaces.

---

## 6. Contributor checklist for M6 milestone-moving PRs

Include this in each milestone-moving PR description:

- M6 workstream(s) advanced (`WS-M6-*`):
- target outcome(s) advanced:
- theorem/invariant/API surfaces introduced or modified:
- evidence commands run:
- fixture changes and semantic rationale:
- deferred items and destination slice:
- what this unlocks next (especially for Raspberry Pi 5 path):
