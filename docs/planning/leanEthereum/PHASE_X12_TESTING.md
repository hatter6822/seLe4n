# Phase X12: Testing Infrastructure & Trace Harness

**Version**: v0.12.0
**Status**: PLANNED
**Sub-tasks**: 14 atomic units
**Dependencies**: X6 (State Transition), X11 (Rust ABI — for XVAL)
**Estimated Lean LoC**: ~500
**Files created**: 10+ new files

## 1. Objective

Build the four-tier validation pipeline mirroring seLe4n's testing
infrastructure. Create the executable trace harness, golden fixture framework,
scenario registry, and all validation scripts.

## 2. Sub-task Breakdown

### Group A: Trace Harness (X12-A1 through X12-A4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X12-A1 | **Create consensus trace harness.** Executable main: (1) generate genesis from test config with N validators, (2) apply test blocks with attestations, (3) print state transitions in pipe-delimited format: `[SCENARIO-ID] | SUBSYSTEM | action | result`. Mirror seLe4n's `MainTraceHarness.lean`. | `Testing/TraceHarness.lean` | ~70 | X6 |
| X12-A2 | **Create state builder for tests.** Helpers: `buildGenesisState : Nat → State`, `buildTestBlock : State → List Attestation → Block`, `buildTestAttestation : State → ValidatorIndex → AttestationData`, `applyBlocks : State → List Block → Except ConsensusError State`. Deterministic test key generation. | `Testing/StateBuilder.lean` | ~50 | X5, X4 |
| X12-A3 | **Create fixture comparison framework.** `compareOutput : String → String → Bool`. `loadFixture : String → IO String`. `assertFixtureMatch : String → String → IO Unit`. Support `--update-fixtures` flag for regeneration. | `Testing/Fixtures.lean` | ~25 | — |
| X12-A4 | **Create golden trace fixture.** Canonical test scenario: genesis (4 validators) → 5 blocks with attestations → justification at block 3 → finalization at block 5. Expected output captures every state transition. | `tests/fixtures/consensus_trace_smoke.expected` | ~40 | X12-A1 |

### Group B: Validation Scripts (X12-B1 through X12-B4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X12-B1 | **Create `scripts/test_tier0_hygiene.sh`.** Shellcheck on all scripts. YAML scenario registry validation. Traceability tag consistency (`LS-*` tags). Sorry/axiom grep. | `scripts/test_tier0_hygiene.sh` | ~30 | — |
| X12-B2 | **Create `scripts/test_tier1_build.sh`.** `lake build LeanEth`. `cargo build --release` (Rust crates). Module-level build verification for all Lean files. | `scripts/test_tier1_build.sh` | ~20 | — |
| X12-B3 | **Create `scripts/test_smoke.sh` (Tier 0+1+2).** Run tier 0 + tier 1. Then tier 2: execute trace harness, compare golden fixture. Run SSZ roundtrip suite. Run state transition suite. Run negative-state suite. | `scripts/test_smoke.sh` | ~35 | X12-B1, X12-B2 |
| X12-B4 | **Create `scripts/test_full.sh` (Tier 0-3).** Run smoke. Then tier 3: `#check` validation of anchor theorems (3SF-mini safety, finalization monotonicity, SSZ roundtrip, XMSS soundness). XVAL cross-validation. | `scripts/test_full.sh` | ~25 | X12-B3 |

### Group C: Negative & Scenario Tests (X12-C1 through X12-C4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X12-C1 | **Create negative-state test suite.** ≥ 15 error-path tests: invalid slot, wrong proposer, bad parent root, bad state root, future attestation, already-justified target, non-justifiable slot distance, slot regression, invalid signature, validator not found, history limit exceeded, duplicate block, empty validators. | `tests/NegativeStateSuite.lean` | ~60 | X6 |
| X12-C2 | **Create scenario registry.** `tests/fixtures/scenario_registry.yaml` — metadata for every test scenario: ID, description, subsystem, source function, expected outcome, tier. | `tests/fixtures/scenario_registry.yaml` | ~30 | — |
| X12-C3 | **Create determinism test suite.** Run state transition 3 times with same inputs, verify BEq equality of all intermediate states. ≥ 50 determinism assertions. | `tests/DeterminismSuite.lean` | ~30 | X6 |
| X12-C4 | **Integrate into build system.** Add all test executables to `lakefile.toml`. Ensure `lake build` builds library + all test suites. Create `leaneth` executable target for trace harness. | `lakefile.toml` | ~20 | All X12-* |

### Group D: Pre-commit Hook (X12-D1 through X12-D2)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X12-D1 | **Create pre-commit hook.** Detect staged `.lean` files. Build each modified module via `lake build <Module.Path>`. Check for `sorry` in staged content. Block commit if build fails or sorry found. | `scripts/pre-commit-lean-build.sh` | ~30 | — |
| X12-D2 | **Create CI configuration.** GitHub Actions workflow: tier 0+1 on every push, tier 2 on PR, tier 3 nightly. Rust CI: `cargo test`, `cargo clippy`. | `.github/workflows/ci.yml` | ~40 | All X12-* |

## 3. Exit Criteria

- [ ] Trace harness produces golden output matching fixture
- [ ] All four test tiers pass
- [ ] ≥ 15 negative-state tests
- [ ] ≥ 50 determinism assertions
- [ ] Scenario registry covers all test cases
- [ ] Pre-commit hook blocks sorry and build failures
- [ ] CI pipeline configured and passing
