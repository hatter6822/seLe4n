# seLe4n Repository Audit

**Audit date:** 2026-02-17
**Scope:** Complete repository — architecture, code quality, testing, documentation, CI/CD, security
**Codebase version at audit time:** 0.8.0 (Lean 4.27.0, M6 complete / M7 active)

---

**Post-audit remediation note (M7 WS-A1/WS-A2):**
- WS-A1 is complete: Tier 3 is promoted into CI and nightly determinism + CI policy documentation are present (`.github/workflows/lean_action_ci.yml`, `.github/workflows/nightly_determinism.yml`, `docs/CI_POLICY.md`).
- WS-A2 is complete: IPC transition operations are split into `SeLe4n/Kernel/IPC/Operations.lean` and invariant/proof obligations remain in `SeLe4n/Kernel/IPC/Invariant.lean` behind a stable `SeLe4n/Kernel/API.lean` facade.
- Findings in this audit remain a historical snapshot at audit-time version 0.8.0; authoritative current status for historical remediation closure is tracked in `docs/M7_CLOSEOUT_PACKET.md` and `docs/gitbook/21-m7-current-slice-outcomes-and-workstreams.md`.

## Executive Summary

seLe4n is a Lean 4 formalization of core seL4 microkernel semantics. The repository
contains **4,466 lines** of Lean across **19 source files**, backed by **189 machine-checked
theorems**, a **4+1 tiered test framework** (805 lines of shell), and **~2,200 lines of
documentation** across root docs, a GitBook handbook, and inline docstrings.

**Overall assessment: the project is in excellent health.** Proof discipline is
industry-leading (99.3% complete, zero `sorry` in core modules), state management is
purely functional with atomic updates, error handling is comprehensive and typed, and
documentation is unusually thorough for a formal-methods project. The criticisms below
are constructive — they reflect areas where an already-strong project can sharpen
further as it enters the M7 hardware-binding phase.

---

## 1. Architecture

### 1.1 Module Graph

```
SeLe4n.lean (root re-exports)
├── Prelude.lean            type aliases + KernelM monad
├── Machine.lean            abstract register file / memory / timer
├── Model/
│   ├── Object.lean         KernelObject inductive (TCB, CNode, Endpoint)
│   └── State.lean          SystemState, storeObject, helpers, lifecycle metadata
└── Kernel/
    ├── API.lean            public re-export surface
    ├── Scheduler/
    │   ├── Invariant.lean  predicates: wellFormed, queueCurrentConsistent, runQueueUnique
    │   └── Operations.lean schedule, chooseThread, handleYield + 34 theorems
    ├── Capability/
    │   ├── Operations.lean lookup, insert, mint, delete, revoke
    │   └── Invariant.lean  slotUnique, lookupSound, attenuationRule + 50 theorems
    ├── IPC/
    │   └── Invariant.lean  endpointSend/Receive/Await + transport lemmas + 38 theorems
    ├── Lifecycle/
    │   ├── Operations.lean retype, revokeDeleteRetype composition
    │   └── Invariant.lean  identity, authority, stale-reference exclusion + 10 theorems
    ├── Service/
    │   ├── Operations.lean start, stop, restart + policy predicates
    │   └── Invariant.lean  service-lifecycle-capability bridge + 19 theorems
    └── Architecture/
        ├── Assumptions.lean Boot/Runtime/Interrupt boundary contracts
        ├── Adapter.lean     timer, register, memory adapters + 7 theorems
        └── Invariant.lean   adapter proof-hooks, composition anchor points
```

### 1.2 Strengths

- **Clean subsystem boundaries.** Each kernel subsystem follows a consistent
  Operations + Invariant split. Operations define executable transitions;
  invariant files define predicates and prove preservation. This separation
  makes auditing straightforward.
- **Acyclic dependency graph.** Imports flow strictly downward: Model -> Kernel
  subsystems -> Architecture. No circular dependencies.
- **Unified namespace management.** `SeLe4n.Kernel.*` for operations,
  `SeLe4n.Model.*` for data, `SeLe4n.Kernel.Architecture.*` for hardware
  boundary contracts.
- **Single public surface** via `API.lean` — consumers import one module.

### 1.3 Criticisms

- **IPC lacks an Operations/Invariant split.** `IPC/Invariant.lean` (805 lines)
  mixes both endpoint operations (`endpointSend`, `endpointReceive`,
  `endpointAwaitReceive`) and their invariant proofs in one file. Every other
  subsystem splits these. At 805 lines it is also the largest file in the
  codebase.
- **No module-level README or dependency diagram.** The architecture is
  discoverable by reading imports, but a visual dependency graph in the docs
  would reduce onboarding time. The GitBook architecture chapter references
  the layout but doesn't include a concrete graph.
- **API.lean is thin.** It re-exports everything but adds no abstraction layer,
  capability-check wrappers, or syscall-dispatch surface. This means callers
  (Main.lean) must know the full internal API — fine for a verification
  project, but limits the path to a realistic syscall dispatcher.

---

## 2. Code Quality

### 2.1 Quantitative Profile

| Metric | Value |
|--------|-------|
| Total lines of Lean | 4,466 |
| Source files | 19 |
| Theorems / lemmas | 189 |
| Definitions / structures / inductives | 156 |
| Proof completeness | 99.3% (3 `sorry` uses, all in Architecture assumption layer) |
| Largest file | `IPC/Invariant.lean` (805 lines) |
| Average theorem size | 5–15 lines |
| Longest proof | `cspaceRevoke_local_target_reduction` (~173 lines) |

### 2.2 Strengths

- **Zero proof debt in core modules.** No `sorry`, `axiom`, or `admit` outside
  of `Architecture/Assumptions.lean`, where boundary assumptions are
  explicitly documented and expected.
- **Naming is near-perfect.** 189 theorems follow a consistent
  `<operation>_preserves_<property>` convention. Types use PascalCase,
  functions use camelCase, and abbreviations are semantically meaningful
  (`ObjId`, `ThreadId`, `CPtr`).
- **Functional state management.** Every operation returns
  `Except KernelError (α × SystemState)`. No mutable references. State
  updates use `{ st with ... }` for clarity. Intermediate states are
  explicitly named (`st1`, `stRevoked`, `stDeleted`).
- **Typed error handling.** 10 distinct `KernelError` constructors (not
  strings). Operations document their error ordering. Failure-path
  preservation theorems prove invariants hold even on error. The Adapter
  layer maps domain-specific `AdapterErrorKind` to kernel errors through
  a single `mapAdapterError` function.
- **Decidability properly integrated.** `RuntimeBoundaryContract` bundles
  both propositions and their `Decidable` instances, allowing both
  proof-time reasoning and executable checking.
- **Clean Lean 4 idioms.** Proper `Monad` instance, correct `Decidable`
  typeclass usage, idiomatic tactic proofs (`cases`, `simp`, `induction`,
  `rcases`, `refine`), and no universe-level hacks.

### 2.3 Criticisms

- **Theorem docstrings are absent.** Operations have good `/--` docstrings
  explaining semantics and failure branches, but all 189 theorems lack any
  documentation. For a formal verification project, explaining *why* each
  theorem matters (not just *what* it proves) would significantly improve
  auditability by non-Lean readers.
- **Documentation density is inconsistent across modules.**
  `Service/Operations.lean` has numbered check-ordering docs;
  `Scheduler/Operations.lean` has sparse comments despite equal complexity.
- **Type aliasing via `abbrev` provides no compile-time safety.** `ObjId`,
  `ThreadId`, `Slot`, `Badge`, `CPtr` are all `abbrev ... := Nat`. A
  `ThreadId` can be silently used where an `ObjId` is expected. For a
  security-critical kernel model, newtype wrappers (`structure ThreadId where
  val : Nat`) would catch cross-domain confusion at compile time.
- **Endpoint transport lemmas are duplicated.** Three nearly identical
  `*_ok_as_storeObject` lemmas in `IPC/Invariant.lean` (lines 145–227, ~85
  lines) follow the same extraction pattern. A generic helper parameterized
  over the endpoint constructor would reduce duplication.
- **Preservation theorem family is repetitive.** In `Capability/Invariant.lean`
  (lines 392–455), five `*_preserves_capabilityInvariantBundle` theorems
  follow the same structure: destructure the bundle, apply per-component
  preservation, reassemble. A generic tactic or meta-program could generate
  these. The same pattern repeats in Service and Lifecycle modules.
- **Named hypothesis `_hTicks` is introduced but unused** in
  `Adapter.lean:29`. Minor, but a clean codebase should not have dead
  bindings.
- **Main.lean is deeply nested.** The main function chains 35 match
  expressions to 15+ levels of indentation. This is fine for a demo but
  would benefit from using `do`-notation with the `KernelM` monad or a
  structured test runner if the executable grows further.

---

## 3. Testing

### 3.1 Framework Overview

The project uses a **custom 4+1 tiered shell-based validation system** (805
lines of infrastructure in `scripts/`), which is well-suited for a theorem-
proving project where "coverage" means obligation fulfillment, not statement
percentage.

| Tier | Script | What It Validates | CI? |
|------|--------|-------------------|-----|
| 0 | `test_tier0_hygiene.sh` | No `axiom`/`sorry`/`TODO` in proof surface; optional `shellcheck` | Yes |
| 1 | `test_tier1_build.sh` | Full `lake build` compilation (17 modules, 189 theorems) | Yes |
| 2 | `test_tier2_trace.sh` | 34 semantic fixture expectations against executable output | Yes |
| 3 | `test_tier3_invariant_surface.sh` | 237 symbol anchor checks for theorem/bundle existence | No (local) |
| 4 | `test_tier4_nightly_candidates.sh` | Determinism diff (run twice, compare traces) | No (opt-in) |

**Entrypoints:** `test_fast.sh` (T0+T1), `test_smoke.sh` (T0+T1+T2),
`test_full.sh` (T0+T1+T2+T3), `test_nightly.sh` (all + T4 opt-in).

### 3.2 Strengths

- **Multi-layer defense.** Hygiene catches proof placeholders before they reach
  CI. Build closure catches type errors. Trace fixtures catch semantic
  regressions. Symbol anchors catch silent theorem renaming. Determinism
  checks catch non-deterministic trace drift.
- **Meaningful test scenarios, not smoke tests.** `Main.lean` exercises 35
  distinct kernel paths including 18+ explicit failure branches: adapter
  contract rejection, service policy denial, lifecycle authority mismatch,
  IPC state machine violations, capability revocation cascades.
- **Contract-based mocking.** `runtimeContractAcceptAll` and
  `runtimeContractDenyAll` in `Main.lean` provide first-class test doubles
  without mock libraries. Both success and failure paths are validated.
- **Fixture discipline.** `tests/fixtures/main_trace_smoke.expected` uses
  line-oriented, order-agnostic, semantic substring matching — resistant to
  formatting changes while catching behavioral drift.
- **Negative controls.** `audit_testing_framework.sh` deliberately injects
  an impossible expectation to verify that Tier 2 correctly detects
  mismatches. This validates the test framework itself.
- **CI artifact diagnostics.** On Tier 2 failure, GitHub Actions uploads
  `main_trace_smoke.actual.log` and `main_trace_smoke.missing.txt` for
  debugging without re-running locally.
- **Shared test library** (`test_lib.sh`, 183 lines) with color management,
  `--continue` mode, `run_check()` wrapper, and `finalize_report()` — avoids
  boilerplate in individual tier scripts.

### 3.3 Criticisms

- **Tier 3 and Tier 4 are not in CI.** Only Tiers 0–2 run in GitHub Actions.
  Tier 3's 237 symbol anchor checks are the strongest regression guard for
  proof surface integrity, yet they only run locally. A refactoring PR that
  renames a theorem will pass CI but fail Tier 3. At minimum, `test_full.sh`
  should be a CI job (even if slow) or Tier 3 should be promoted to the
  smoke gate.
- **No property-based or fuzz testing.** The 34 fixture expectations cover a
  fixed set of scenarios. Lean 4's `#eval` and metaprogramming could support
  randomized state generation to explore edge cases (e.g., deep CNode radix
  trees, large run queues, concurrent IPC senders).
- **Single-path scheduler testing.** The bootstrap state has only 2 threads
  with a static run queue. Priority inversion, preemption, starvation, and
  multi-domain scheduling are not exercised.
- **IPC scale is minimal.** One endpoint, 2 senders, 1 receiver. No tests
  for queue saturation, multiple competing endpoints, or sender/receiver
  interleaving.
- **CSpace radix depth is always 0.** All CNode objects use `radix := 0`
  (single-slot). Deep radix tree traversal is never tested.
- **Memory testing is trivial.** `adapterReadMemory` is tested with address 0
  only. No boundary addresses, alignment checks, or range validation.
- **Service dependency graph is shallow.** 5 services with at most 1
  dependency. Complex dependency chains, cyclic detection, and large-graph
  isolation policies are not exercised.
- **No Lean-native test framework.** Shell scripts cannot assert on
  proof-internal properties. A Lean-native test harness (using `#eval` or
  `IO.Process`) could validate kernel operations programmatically with
  richer assertions.
- **Fixture file is not version-controlled with semantic comments.** Each of
  the 34 lines in `main_trace_smoke.expected` should have a comment
  explaining which test scenario it anchors. Currently, mapping expectations
  to code requires cross-referencing with `Main.lean`.

---

## 4. Documentation

### 4.1 Inventory

| Document | Lines | Purpose |
|----------|-------|---------|
| `README.md` | 72 | Quick start, repository map, milestone status |
| `docs/spec/SELE4N_SPEC.md` | -- | Normative specification baseline, acceptance criteria |
| `docs/spec/SEL4_SPEC.md` | -- | Upstream seL4 microkernel reference |
| `docs/DEVELOPMENT.md` | 369 | Contributor workflow, proof engineering standards |
| `docs/TESTING_FRAMEWORK_PLAN.md` | 139 | Active testing baseline, tier signal map |
| `docs/audits/AUDIT_v0.9.0.md` | 764 | Comprehensive end-to-end quality audit snapshot |
| `docs/licensing_research/LICENSE_REVIEW.md` | 65 | MIT license adoption review |
| `docs/gitbook/` (26 chapters) | ~1,100 | Long-form handbook |
| `tests/scenarios/README.md` | 73 | Fixture maintenance workflow |

### 4.2 Strengths

- **Multiple entry points for different readers.** README for quick start,
  DEVELOPMENT.md for contributors, SELE4N_SPEC.md for normative baseline,
  GitBook for long-form orientation.
- **Excellent cross-document synchronization.** M6 completion status, M7
  active status, Raspberry Pi 5 hardware direction, and test script
  references are consistent across all documents checked.
- **Explicit change-control policies.** SELE4N_SPEC.md defines
  5 requirements for scope changes. DEVELOPMENT.md (lines 218–236) requires
  synchronized doc updates with any PR changing transitions or invariants.
- **Obligation-based quality model.** Historical audit narratives clearly articulate
  why statement-coverage percentages are inappropriate for a theorem-proving
  project and defines 6 obligation categories instead.
- **Milestone acceptance criteria are concrete.** Each completed milestone
  (M1–M6) has explicit acceptance criteria, workstream matrices, and
  completion evidence checklists.
- **GitBook SUMMARY.md has perfect 1:1 alignment** with the handbook README's
  navigation structure. All 26 referenced chapters exist.
- **No stale file references detected.** All cross-document paths, script
  references, and module names resolve correctly.

### 4.3 Criticisms

- **No architectural dependency diagram.** The GitBook architecture chapter
  describes the module layout textually, but a visual graph (even ASCII art)
  of the module dependency structure would help onboarding. The subsystem
  relationship (Scheduler -> Capability -> IPC -> Lifecycle -> Service ->
  Architecture) is implicit in import chains but never drawn.
- **Pre-filled checklist item inconsistency.** Both `DEVELOPMENT.md:266` and
  `SELE4N_SPEC.md` (formerly `SEL4_SPEC.md:317`) have one item marked `[x] Preservation theorem
  entrypoints compile.` while all other items remain `[ ]`. This is
  ambiguous: is it a template that contributors should leave checked, or
  was it accidentally committed?
- **GitBook chapters vary widely in depth.** `01-project-overview.md` (76
  lines) is well-developed; some later chapters read as stubs or pure
  cross-references. The handbook would benefit from a completeness pass.
- **No CONTRIBUTING.md at repository root.** DEVELOPMENT.md serves this
  purpose but lives in `docs/`, where GitHub will not automatically surface
  it to new contributors. A root CONTRIBUTING.md (even a one-liner pointing
  to DEVELOPMENT.md) would improve discoverability.
- **No CHANGELOG.** Milestone completions are documented in specs, but there
  is no single chronological record of what changed between versions.
  `lakefile.toml` showed version 0.8.0 at audit time, but there was no history of 0.1–0.7.
- **Inline code documentation gaps.** 189 theorems lack docstrings. The
  proof engineering standards require "explicit theorem statements" but not
  theorem-level documentation. For a project whose primary artifact is
  proofs, each theorem should explain its security/correctness significance.

---

## 5. Build, CI/CD, and Dependencies

### 5.1 Build System

- **`lakefile.toml`** — Clean 11-line config. Single library (`SeLe4n`) and
  executable (`sele4n`). Version 0.8.0 at audit time.
- **`lean-toolchain`** — Pinned to `leanprover/lean4:v4.27.0`. Good for
  reproducibility.
- **`lake-manifest.json`** — No external dependencies. Eliminates supply-chain
  risk entirely.
- **`.gitignore`** — Minimal and correct: `/.lake` (build cache) and
  `/tests/artifacts`.

### 5.2 CI Pipeline

**GitHub Actions** (`lean_action_ci.yml`, 46 lines):
- **Job 1: test-fast** (Tier 0 + Tier 1) — Every push/PR.
- **Job 2: test-smoke** (Tier 0 + Tier 1 + Tier 2) — Depends on test-fast.
  Uploads trace diagnostics on failure.
- **Trigger:** push, pull_request, workflow_dispatch.

### 5.3 Criticisms

- **No caching of Lake build artifacts.** Each CI run rebuilds from scratch.
  Adding `actions/cache` for `~/.elan` and `.lake` would significantly reduce
  CI time (Lean compilation is expensive).
- **No matrix testing.** Only `ubuntu-latest`. If M7 targets Raspberry Pi 5
  (ARM64), cross-platform CI should be added before hardware binding begins.
- **No branch protection rules documented.** The CI runs on all pushes but
  there's no documented expectation that PRs must pass CI before merge.
  Branch protection should require `test-smoke` to pass.
- **Tier 3 absent from CI** (repeated from Testing section). This is the most
  impactful CI gap.
- **No Lean toolchain version pinning in CI.** `setup_lean_env.sh` installs
  from `lean-toolchain`, which is correct, but there's no hash pinning of
  the `elan` installer itself. A compromised installer could inject code.
- **No dependency scanning or license checking in CI.** Currently moot (zero
  dependencies), but should be added before any `lake` dependency is
  introduced.

---

## 6. Security Posture

### 6.1 Strengths

- **Zero external dependencies.** No supply-chain attack surface.
- **No secrets in repository.** No `.env` files, API keys, or credentials.
- **`.gitignore` correctly excludes build artifacts.**
- **MIT license cleanly adopted** with documented review
  (`docs/licensing_research/LICENSE_REVIEW.md`).
- **Proof-level security properties.** `capabilityInvariantBundle` proves
  slot uniqueness, lookup soundness, and attenuation rules. These are
  compile-time-verified security invariants — stronger than any runtime
  check.
- **Authority separation in lifecycle operations.** The aliasing guard
  (`if authority = cleanup then .error .illegalState`) in
  `lifecycleRevokeDeleteRetype` prevents capability confusion attacks.
- **Typed errors prevent information leakage.** Error constructors carry no
  runtime data — only enum tags. No risk of leaking kernel state through
  error messages.

### 6.2 Criticisms

- **Type aliasing allows cross-domain confusion.** As noted in code quality:
  `ThreadId`, `ObjId`, `Slot`, `Badge`, and `CPtr` are all `Nat`. A thread
  ID could be passed as a capability pointer without type error. In a
  security-critical model, this is a meaningful risk that newtype wrapping
  would eliminate.
- **No formal information-flow analysis.** The project proves capability
  invariants but does not yet model or prove information-flow properties
  (noninterference, confidentiality). This is a known gap for M7+.
- **`runtimeContractAcceptAll` is dangerous if used outside tests.** The
  accept-all contract allows any timer advance, register write, or memory
  access. If accidentally used in a non-test context, it would bypass all
  hardware boundary checks. Consider adding a `[test_only]` annotation or
  moving it to a dedicated test module.
- **No CI security scanning.** No SAST, no secret scanning, no Dependabot
  (moot now, but should be enabled preemptively).

---

## 7. Recommendations for Future Development

### 7.1 High Priority (before M7)

1. **Promote Tier 3 to CI.** Add a `test-full` job to `lean_action_ci.yml`
   that runs the 237 symbol anchor checks. This is the single highest-value
   change to prevent silent proof-surface regressions.

2. **Add Lake build caching to CI.** Cache `~/.elan` and `.lake` directories.
   Lean compilation is expensive; this will cut CI time significantly.

3. **Split `IPC/Invariant.lean` into Operations + Invariant.** Follow the
   pattern of every other subsystem. This file at 805 lines mixes concerns
   and is the largest in the codebase.

4. **Introduce newtype wrappers for security-critical IDs.** Replace `abbrev
   ThreadId := Nat` with `structure ThreadId where val : Nat`. Do this for
   at least `ThreadId`, `ObjId`, `CPtr`, and `Slot`. This catches
   cross-domain confusion at compile time.

5. **Move `runtimeContractAcceptAll`/`DenyAll` out of Main.lean** into a
   dedicated `SeLe4n/Testing/Contracts.lean` or similar, to prevent
   accidental use in non-test code as the project grows.

### 7.2 Medium Priority (during M7)

6. **Add docstrings to all 189 theorems.** Each theorem should explain its
   security or correctness significance in 1–2 sentences. This is the
   biggest documentation gap.

7. **Add a CONTRIBUTING.md at repository root.** Even a 3-line file pointing
   to `docs/DEVELOPMENT.md` ensures GitHub surfaces contribution guidance.

8. **Add a CHANGELOG.md.** Track milestone completions and version bumps in
   one chronological document.

9. **Add cross-platform CI.** Before Raspberry Pi 5 binding, add an ARM64
   runner (even QEMU-based) to catch platform-specific issues early.

10. **Expand Tier 2 fixture coverage.** Add scenarios for: deep CNode radix
    trees, large run queues (10+ threads), multiple IPC endpoints, service
    dependency chains (5+ deep), and boundary memory addresses.

11. **Add a module dependency diagram** to the GitBook architecture chapter.
    ASCII art or a Mermaid diagram in the README would suffice.

### 7.3 Low Priority (post-M7)

12. **Explore Lean-native testing.** Use `#eval` or `IO.Process` for
    programmatic kernel-state assertions, complementing the shell fixture
    approach.

13. **Add property-based testing.** Generate random `SystemState` values and
    check invariant preservation across random operation sequences.

14. **Consolidate endpoint transport lemmas.** Parameterize the
    `*_ok_as_storeObject` pattern to reduce the ~85 lines of duplication in
    `IPC/Invariant.lean`.

15. **Extract a generic preservation tactic.** The 5 per-operation
    `*_preserves_capabilityInvariantBundle` theorems follow identical
    structure. A custom tactic or meta-program could generate these.

16. **Add information-flow properties.** Model noninterference and prove that
    capability boundaries enforce confidentiality — a natural next step for
    a seL4-inspired verification project.

17. **Add semantic comments to fixture file.** Annotate each line in
    `main_trace_smoke.expected` with the test scenario it anchors.

---

## 8. Summary Scorecard

| Dimension | Grade | Notes |
|-----------|-------|-------|
| **Architecture** | A | Clean subsystem boundaries; acyclic imports; consistent Operations/Invariant split (except IPC) |
| **Code Quality** | A+ | 189 theorems, 99.3% complete; exemplary naming; functional state management |
| **Type Safety** | A- | Excellent decidability integration; marked down for `Nat` aliasing |
| **Testing** | A- | Multi-tier validation with real semantic assertions; marked down for CI gaps and scale coverage |
| **Documentation** | A- | Unusually thorough for formal methods; marked down for missing theorem docs and diagram |
| **CI/CD** | B+ | Functional pipeline with artifact diagnostics; no caching, no Tier 3, single platform |
| **Security** | A | Zero dependencies; typed errors; proof-level invariants; aliasing guard |
| **Proof Discipline** | A+ | Zero `sorry` in core; systematic preservation bundles; clean tactic proofs |
| **Overall** | **A** | **Production-quality formal verification framework. Ready for M7 with targeted improvements.** |

---

*This audit was conducted against the repository at commit HEAD on branch
`claude/repository-audit-H9DJn`. It covers all 19 Lean source files, 12 test
scripts, 1 CI workflow, 8 documentation files, and 26 GitBook chapters.*
