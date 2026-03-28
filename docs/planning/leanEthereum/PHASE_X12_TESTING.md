# Phase X12: Testing Infrastructure & Trace Harness

**Version**: v0.12.0
**Status**: PLANNED
**Sub-tasks**: 26 atomic units
**Dependencies**: X6 (State Transition), X11 (Rust ABI — for XVAL)
**Estimated Lean LoC**: ~650
**Files created**: 14 new files

## 1. Objective

Build the four-tier validation pipeline mirroring seLe4n's testing
infrastructure. Create the executable trace harness, golden fixture framework,
scenario registry, and all validation scripts.

## 2. Source Layout

```
LeanEth/
├── Testing/
│   ├── TraceHarness.lean        Executable trace harness
│   ├── StateBuilder.lean        Test state construction helpers
│   ├── Fixtures.lean            Fixture comparison framework
│   ├── Scenarios.lean           Scenario definitions + registry
│   └── Determinism.lean         Determinism checking utilities
├── tests/
│   ├── SSZRoundtripSuite.lean   (from X1-H2)
│   ├── MerkleizationSuite.lean  (from X2-D5)
│   ├── CryptoSuite.lean         (from X3-A7/B8)
│   ├── ContainerSuite.lean      (from X5-E1)
│   ├── ForkChoiceSuite.lean     (from X8-D4)
│   ├── NetworkSuite.lean        (from X9-B8)
│   ├── NodeServiceSuite.lean    (from X10-F1)
│   ├── NegativeStateSuite.lean  Error-path tests
│   ├── DeterminismSuite.lean    State determinism tests
│   ├── IntegrationSuite.lean    End-to-end flow tests
│   ├── XvalSuite.lean           (from X11-F1)
│   └── fixtures/
│       ├── consensus_trace_smoke.expected
│       ├── scenario_registry.yaml
│       └── ssz_roundtrip.expected
├── scripts/
│   ├── test_tier0_hygiene.sh
│   ├── test_tier1_build.sh
│   ├── test_smoke.sh            (Tier 0+1+2)
│   ├── test_full.sh             (Tier 0-3)
│   └── pre-commit-lean-build.sh
└── .github/workflows/ci.yml
```

## 3. Sub-task Breakdown

### Group A: Trace Harness & State Builder (X12-A1 through X12-A5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X12-A1 | **Create state builder for tests.** `buildGenesisState : Nat → State` — deterministic genesis with N validators using test keys. `buildTestBlock : State → List Attestation → Block` — construct valid block for current slot. `buildTestAttestation : State → ValidatorIndex → AttestationData` — construct attestation for chain head. `applyBlocks : State → List Block → Except ConsensusError State` — sequential application. `deterministicKeyGen : Nat → KeyPair` — reproducible keys from seed. | `Testing/StateBuilder.lean` | ~50 | X5, X4, X6 |
| X12-A2 | **Create fixture comparison framework.** `compareOutput : String → String → Bool` — line-by-line comparison ignoring trailing whitespace. `loadFixture : String → IO String`. `assertFixtureMatch : String → String → IO Unit` — fail with diff on mismatch. `updateFixture : String → String → IO Unit`. Support `--update-fixtures` CLI flag for regeneration. `diffLines : String → String → List (Nat × String × String)` — produce human-readable diff of mismatched lines. | `Testing/Fixtures.lean` | ~30 | — |
| X12-A3 | **Create consensus trace harness — genesis and block production.** Executable main part 1: (1) generate genesis from test config with 4 validators, (2) print genesis state root and validator set. Output format: `[SCENARIO-ID] | SUBSYSTEM | action | result`. Mirror seLe4n's `MainTraceHarness.lean` pipe-delimited format. Include scenario header with timestamp and version. | `Testing/TraceHarness.lean` | ~35 | X12-A1 |
| X12-A4 | **Create consensus trace harness — state transitions and attestations.** Part 2: (3) apply 5 blocks with attestations from all validators, (4) print each state transition (slot, head root, justified checkpoint, finalized checkpoint), (5) verify justification at block 3, finalization at block 5. (6) Print summary: total transitions, final state root, final finalized slot. | `Testing/TraceHarness.lean` | ~40 | X12-A3, X6 |
| X12-A5 | **Create golden trace fixture.** Canonical test scenario output: genesis (4 validators) → 5 blocks → justification at slot 3 → finalization at slot 5. Expected output captures every state transition in pipe-delimited format. Record: genesis state root, each intermediate state root, each justified/finalized checkpoint, final summary. This fixture is the smoke test baseline. | `tests/fixtures/consensus_trace_smoke.expected` | ~40 | X12-A4 |

### Group B: Validation Scripts (X12-B1 through X12-B5)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X12-B1 | **Create Tier 0 hygiene script.** `scripts/test_tier0_hygiene.sh`: (1) Shellcheck on all `.sh` scripts. (2) YAML scenario registry validation (valid YAML, required fields present). (3) Sorry/axiom grep — reject any `sorry` in non-test `.lean` files, verify axiom count = 3. (4) Trailing whitespace check. (5) Import cycle detection via `lake env`. (6) Website link manifest check (if integrated with seLe4n). Return non-zero on any failure. | `scripts/test_tier0_hygiene.sh` | ~35 | — |
| X12-B2 | **Create Tier 1 build script.** `scripts/test_tier1_build.sh`: (1) `source ~/.elan/env && lake build LeanEth`. (2) `cargo build --release` (Rust crates, if present). (3) Module-level build: for each `.lean` file in `LeanEth/`, verify `lake build <Module.Path>` succeeds. (4) Report: total modules built, time per module, any failures. | `scripts/test_tier1_build.sh` | ~25 | — |
| X12-B3 | **Create Tier 2 smoke script.** `scripts/test_smoke.sh` (Tier 0+1+2): (1) Run tier 0 hygiene. (2) Run tier 1 build. (3) Execute trace harness → compare against golden fixture. (4) Run SSZ roundtrip suite. (5) Run state transition positive tests. (6) Run negative-state suite. (7) Summary: pass/fail counts, total time. | `scripts/test_smoke.sh` | ~35 | X12-B1, X12-B2 |
| X12-B4 | **Create Tier 3 full script.** `scripts/test_full.sh` (Tier 0-3): (1) Run smoke. (2) `#check` validation of anchor theorems: `threeSFSafety`, `finalizationMonotonicity`, `sszRoundtrip_all`, `xmssSoundness`. (3) XVAL cross-validation (Lean vs Rust). (4) Determinism suite. (5) Fork choice test suite. (6) Convergence test. (7) Summary with theorem inventory count. | `scripts/test_full.sh` | ~30 | X12-B3 |
| X12-B5 | **Create Tier 4 nightly script.** `scripts/test_nightly.sh` (optional, behind `NIGHTLY_ENABLE_EXPERIMENTAL=1`): (1) Run full. (2) Extended stress: 100-block chain with random attestation patterns. (3) Performance benchmarks: state transition throughput, SSZ encode/decode rate. (4) Memory profiling: peak allocation during 100-block chain. (5) Cross-platform: verify test vectors match on different architectures (if CI supports). | `scripts/test_nightly.sh` | ~25 | X12-B4 |

### Group C: Negative & Scenario Tests (X12-C1 through X12-C6)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X12-C1 | **Create negative-state test suite — slot and header errors.** (1) Invalid slot (regression). (2) Wrong proposer (index mismatch). (3) Bad parent root (doesn't match previous). (4) Bad state root (hash mismatch). (5) Slot ahead of chain. Each test: construct invalid input, apply transition, verify specific error variant returned. | `tests/NegativeStateSuite.lean` | ~30 | X6 |
| X12-C2 | **Create negative-state test suite — attestation errors.** (6) Future attestation (slot > current). (7) Already-justified target. (8) Non-justifiable slot distance (not ≤5, not perfect square, not pronic). (9) Source checkpoint mismatch. (10) Invalid XMSS signature. (11) Unknown validator index. Each: specific error variant verified. | `tests/NegativeStateSuite.lean` | ~30 | X6, X4 |
| X12-C3 | **Create negative-state test suite — structural errors.** (12) Duplicate block (same root). (13) Empty validator set. (14) History limit exceeded. (15) State root mismatch on genesis. (16) Finalized slot regression. (17) Block body root mismatch. Minimum 17 negative tests total. | `tests/NegativeStateSuite.lean` | ~25 | X6, X8 |
| X12-C4 | **Create scenario registry.** `tests/fixtures/scenario_registry.yaml`: metadata for every test scenario. Fields: `id`, `description`, `subsystem` (ssz/crypto/consensus/fork_choice/sync/bridge), `source_function`, `expected_outcome` (success/error variant), `tier` (0-4), `xval` (boolean). Cover all test suites. | `tests/fixtures/scenario_registry.yaml` | ~40 | — |
| X12-C5 | **Create determinism test suite.** Run state transition 3 times with identical inputs. `BEq` equality of all intermediate states. Cover: genesis, single block, 5-block chain, attestation processing, justification, finalization. ≥ 50 determinism assertions (state equality checks). Verify: `hashTreeRoot` identical across runs. | `tests/DeterminismSuite.lean` | ~35 | X6 |
| X12-C6 | **Create scenario definitions module.** Reusable test scenarios: `simpleChainScenario : Nat → Nat → TestScenario` (N validators, M blocks). `forkScenario : TestScenario` (two competing chains). `reorgScenario : TestScenario` (attestation-driven reorg). `justificationScenario : TestScenario` (3SF-mini justification). `finalizationScenario : TestScenario` (full finalization). Each returns `TestScenario` with inputs + expected outputs. | `Testing/Scenarios.lean` | ~40 | X12-A1 |

### Group D: Build Integration & CI (X12-D1 through X12-D4)

| ID | Description | Files | Est. Lines | Depends On |
|----|-------------|-------|-----------|------------|
| X12-D1 | **Create pre-commit hook.** `scripts/pre-commit-lean-build.sh`: (1) Detect staged `.lean` files. (2) For each: `lake build <Module.Path>`. (3) Grep staged content for `sorry` — block if found. (4) Verify no axiom additions without `AXIOM-CRYPTO-*` annotation. (5) Timing: report build time per module. Exit non-zero on any failure. Installation: `cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit`. | `scripts/pre-commit-lean-build.sh` | ~35 | — |
| X12-D2 | **Integrate test suites into build system.** Add to `lakefile.toml`: `[[lean_exe]] name = "leaneth" root = "Testing.TraceHarness"`. Add test library targets for each suite: `NegativeStateSuite`, `DeterminismSuite`, `XvalSuite`, etc. Verify `lake build` builds library + all test suites. `lake exe leaneth` runs trace harness. | `lakefile.toml` | ~25 | All X12-* |
| X12-D3 | **Create CI configuration — Lean.** GitHub Actions workflow `.github/workflows/ci.yml`: (1) On push to any branch: tier 0 + tier 1. (2) On PR to main: tier 0 + tier 1 + tier 2 (smoke). (3) Nightly: tier 0-3 (full). (4) Cache: `~/.elan/`, `lake-packages/`. (5) Matrix: Lean 4.28.0. (6) Artifact: test results as CI output. | `.github/workflows/ci.yml` | ~40 | X12-B1 through X12-B4 |
| X12-D4 | **Create CI configuration — Rust.** Add to CI workflow: (1) `cargo build --release`. (2) `cargo test`. (3) `cargo clippy -- -D warnings`. (4) `cargo fmt -- --check`. (5) XVAL: run Lean XVAL suite → run Rust XVAL suite → compare outputs. (6) Cache: `target/`, `~/.cargo/registry/`. | `.github/workflows/ci.yml` | ~25 | X11 |

## 4. Exit Criteria

- [ ] Trace harness produces golden output matching fixture
- [ ] All four test tiers pass (tier 4 optional behind flag)
- [ ] ≥ 17 negative-state tests covering all error paths
- [ ] ≥ 50 determinism assertions across 6+ scenarios
- [ ] Scenario registry covers all test cases with metadata
- [ ] 5 reusable test scenarios defined
- [ ] Pre-commit hook blocks sorry, axiom additions, and build failures
- [ ] CI pipeline configured: Lean + Rust, push + PR + nightly
- [ ] `lake exe leaneth` runs trace harness successfully
- [ ] All test suites integrated into `lakefile.toml`
