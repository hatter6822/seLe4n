# Comprehensive Repository Audit — seLe4n

**Date:** 2026-02-17
**Version audited:** 0.9.0 (post-M7 closeout)
**Lean toolchain:** v4.27.0
**Auditor:** Automated deep review

---

## 1. Executive Summary

seLe4n is a Lean 4 formalization of core seL4 microkernel semantics. It provides
executable, machine-checked transition models for scheduling, capability management,
IPC, lifecycle management, service orchestration, and hardware-boundary contracts.
The project has completed milestones M1–M7 and is entering a hardware-oriented
execution phase targeting the Raspberry Pi 5.

**Overall assessment:** The repository demonstrates strong formal-methods discipline
with clean architecture, exhaustive type safety, and zero unresolved proof
obligations in production code. The primary areas for improvement are in testing
depth (particularly property-based and negative testing), scalability of the state
model, and a few architectural patterns that will need revision before real hardware
integration.

---

## 2. Architecture

### 2.1 Strengths

- **Clean layered dependency DAG.** The dependency flow is strictly
  `Prelude → Machine → Model → Kernel subsystems → Architecture → API → Main`,
  with no circular imports. This prevents proof cycles and keeps compilation
  incremental.

- **Operations/Invariant separation.** Every kernel subsystem (Scheduler,
  Capability, IPC, Lifecycle, Service, Architecture) is split into
  `Operations.lean` for executable semantics and `Invariant.lean` for
  preservation theorems. This is a textbook approach for formal development.

- **Explicit error model.** `KernelError` (`Model/State.lean:6-17`) enumerates
  ten distinct failure modes. Every transition function returns
  `Except KernelError`, making failure explicit rather than silent.

- **Monad design.** `KernelM` (`Prelude.lean:112`) is a clean state/error monad
  `σ → Except ε (α × σ)` with a proper `Monad` instance. State threading is
  pure and deterministic — no side effects.

- **Wrapper types for domain IDs.** `ObjId`, `ThreadId`, `CPtr`, `Slot`
  (`Prelude.lean:4-97`) are dedicated `structure` types rather than raw `Nat`
  aliases. This prevents cross-domain confusion at the type level.

### 2.2 Criticisms

- **Function-encoded maps do not scale.** `SystemState.objects` is typed as
  `ObjId → Option KernelObject` (`Model/State.lean:40`), which is a total
  function. This works for a formal model but makes enumeration, serialization,
  and finiteness reasoning difficult. As the project moves toward hardware
  execution, switching to `Std.HashMap` or `Lean.RBMap` for finite maps should
  be considered.

- **`DomainId`, `Priority`, `Irq`, `Badge`, `ASID`, `VAddr`, `PAddr` remain
  raw `abbrev := Nat`.** Unlike `ObjId`/`ThreadId`/`CPtr`/`Slot`, these six
  identifiers (`Prelude.lean:48-109`) are plain `Nat` aliases. They receive no
  type-level distinction. A `Priority` can be silently used where a `DomainId`
  is expected, which defeats the purpose of the wrapper-type upgrade in WS-A3.

- **VSpace is a placeholder.** The model has `vspaceRoot : ObjId` in `TCB`
  (`Model/Object.lean:72`) but no `VSpace` kernel object type, no page-table
  model, and no memory isolation semantics. This is acknowledged as deferred but
  represents the single largest gap between the model and real seL4.

- **Memory is `PAddr → UInt8`.** The `Memory` type (`Machine.lean:12`) is a
  total function from physical addresses to bytes. This is adequate for abstract
  modeling but will need bounded representations and page-level access control
  for hardware integration.

- **No notification objects.** seL4 distinguishes endpoints from notifications.
  The current model only has `Endpoint` (`Model/Object.lean:83-87`). Adding
  notifications will be necessary for complete IPC coverage.

- **CNode slots are list-encoded.** `CNode.slots` is `List (Slot × Capability)`
  (`Model/Object.lean:92`). Lookup is O(n). For formal modeling this is fine,
  but the radix-tree semantics of real seL4 CNodes are not captured — `guard`
  and `radix` fields exist but are never used in address resolution logic.

### 2.3 Recommendations

1. Upgrade the remaining six `abbrev` type aliases to wrapper `structure` types,
   mirroring the `ObjId`/`ThreadId` pattern.
2. Introduce a finite-map abstraction (even if backed by `List` initially) with
   explicit `keys`/`values`/`size` operations to prepare for hardware transition.
3. Plan a VSpace/page-table milestone as a prerequisite for Raspberry Pi 5 work.
4. Model CNode guard/radix address resolution to close the gap with seL4 CSpace
   semantics.

---

## 3. Code Quality

### 3.1 Strengths

- **Zero `sorry` and zero `axiom` in production code.** Verified by grep scan
  across all 19 source files in `SeLe4n/`. Every theorem is fully proved.

- **Consistent naming conventions.** Functions follow `<subsystem><Action>`
  (e.g., `cspaceLookupSlot`, `endpointSend`, `serviceStart`). Theorems follow
  `<transition>_preserves_<invariant>`. This is systematic and discoverable.

- **Exhaustive pattern matching.** All `match` expressions cover every
  constructor of the matched type. No wildcard catch-alls hide missing cases
  in transition logic.

- **Pure functional style.** No mutable state, no `unsafe`, no `IO` in kernel
  modules. Side effects are confined to `Main.lean`.

- **Well-factored helper lemmas.** Shared helpers like
  `storeObject_preserves_objectTypeMetadataConsistent` (`Model/State.lean:332-345`)
  and `endpoint_store_preserves_schedulerInvariantBundle`
  (`IPC/Invariant.lean:656-689`) are reused across multiple proofs, reducing
  duplication.

### 3.2 Criticisms

- **`Main.lean` has deeply nested match chains.** The `main` function
  (`Main.lean:132-405`) is a single 273-line `do` block with match expressions
  nested 6+ levels deep. This is difficult to read and maintain. Many of these
  branches are independent scenarios that could be extracted into named functions.

- **`bootstrapState` uses cascading `if/else` for object maps.**
  `Main.lean:24-66` initializes the object store with a chain of `if oid = X`
  conditions. This is fragile and hard to extend. A list-based initializer
  converted to a function would be clearer.

- **Error paths in `Main.lean` only print — they don't assert.** When an
  operation hits an error branch, the code prints a message but the test still
  "passes." There is no programmatic verification that the *correct* error was
  produced.

- **`capAttenuates` is a `Prop`, not a `Bool`.** The attenuation predicate
  (`Capability/Operations.lean:14-15`) is not computationally decidable without
  additional work. The code works around this with `rightsSubset` (a `Bool`
  function) for runtime checks, but there is no formal bridge theorem proving
  `rightsSubset = true → capAttenuates`. The `rightsSubset_sound` theorem
  (`Capability/Operations.lean:76-83`) only goes one direction.

- **`ServicePolicy` is `ServiceId → Bool`.** This function type
  (`Service/Operations.lean`) is maximally abstract but carries no structure.
  There is no way to inspect, compose, or reason about policies beyond
  pointwise evaluation.

### 3.3 Recommendations

1. Refactor `Main.lean` by extracting each scenario into a named function
   (e.g., `demoScheduler`, `demoCapability`, `demoIPC`, etc.) and composing
   them in `main`.
2. Replace cascading `if/else` object initialization with a list-based builder:
   ```lean
   def mkObjects (entries : List (ObjId × KernelObject)) : ObjId → Option KernelObject :=
     fun oid => (entries.find? (·.1 == oid)).map (·.2)
   ```
3. Add assertion functions to `Main.lean` that verify expected error variants,
   not just print them.
4. Prove the completeness direction of `rightsSubset` → `capAttenuates` to
   close the specification-implementation gap.
5. Consider a `ServicePolicy` structure with named fields (e.g., `canStart`,
   `canStop`) for composability.

---

## 4. Testing

### 4.1 Strengths

- **Five-tier test system.** Tiers 0–4 cover hygiene, build, trace fixtures,
  invariant surface anchoring, and nightly determinism. Each tier has a clear
  script and documented purpose.

- **56 fixture expectations.** `tests/fixtures/main_trace_smoke.expected`
  contains 56 tagged test scenarios with scenario IDs and risk classes,
  providing regression coverage for all major kernel paths.

- **Stochastic testing.** `tests/TraceSequenceProbe.lean` runs pseudo-random
  IPC operation sequences (250+ steps × multiple seeds) to explore the endpoint
  state machine.

- **Invariant surface verification.** Tier 3 (`test_tier3_invariant_surface.sh`)
  grep-verifies that 180+ theorem/definition/structure names exist in the
  codebase, catching silent renames or deletions.

- **Test-fixture isolation.** `RuntimeContractFixtures.lean` is confined to
  `SeLe4n/Testing/` and Tier 0 hygiene (`test_tier0_hygiene.sh:19-23`) enforces
  that production modules never import it.

### 4.2 Criticisms

- **No unit tests for individual operations.** All testing is done through
  end-to-end trace execution (`Main.lean`) or surface-level grep checks. There
  are no isolated unit tests that exercise a single function with controlled
  inputs and verify specific outputs. For example, there are no tests that call
  `cspaceRevoke` with a known CNode state and verify the exact resulting slot
  list.

- **Trace matching is order-agnostic and fragment-based.**
  `test_tier2_trace.sh` checks whether *any* output line contains a given
  substring. This means:
  - Tests pass if a matching string appears in an unexpected context.
  - Tests cannot verify that a specific sequence of outputs occurs in order.
  - Two different failures could produce the same matching substring.

- **No negative/adversarial tests.** The test suite verifies that invariants
  *hold*. It never constructs states that deliberately violate invariants and
  verifies that the system correctly detects the violation. This is important
  for confirming that the invariant checks are not vacuously true.

- **Single bootstrap state.** All trace tests operate on one fixed 5-object,
  6-service state (`bootstrapState`). This limits coverage to one point in the
  state space. There is no parameterized or generative testing.

- **`TraceSequenceProbe` only tests IPC.** The stochastic probe
  (`tests/TraceSequenceProbe.lean`) exercises only three operations
  (`send`, `awaitReceive`, `receive`) on a single endpoint. Scheduler,
  capability, lifecycle, and service operations are not covered by randomized
  testing.

- **No concurrency or interleaving tests.** All tests execute operations
  sequentially. There are no tests that explore interleavings of operations from
  multiple threads or services.

- **No performance or resource-exhaustion tests.** No tests exercise large state
  spaces, deep recursion, or resource limits.

- **Error branch verification is informal.** When `Main.lean` hits an error
  branch, it prints the error but does not programmatically check that the
  error is the expected variant. The fixture file checks substring matches,
  which could match the wrong error.

### 4.3 Recommendations

1. **Add property-based testing.** Extend `TraceSequenceProbe` (or create new
   probes) to cover all subsystems, not just IPC. Generate random `SystemState`
   values and verify that transitions preserve invariants.
2. **Add negative tests.** Construct deliberately malformed states (e.g.,
   duplicate slots in a CNode, circular service dependencies) and verify that
   operations return the correct `KernelError` variant.
3. **Add structured trace assertions.** Replace fragment matching in Tier 2 with
   structured output (e.g., JSON or tagged lines) and exact-match verification.
4. **Parameterize bootstrap state.** Create a state-builder DSL or use Lean's
   `Gen` monad (if available) to generate diverse initial states.
5. **Expand stochastic coverage.** Add probes for Scheduler (random thread
   insertions/removals), Capability (random mint/revoke/delete sequences), and
   Service (random start/stop/restart with varying policies).

---

## 5. Documentation

### 5.1 Strengths

- **Exceptional breadth.** 40+ markdown documents covering specification,
  development workflow, testing tiers, CI policy, hardware boundary policy,
  audit remediation, and a 23-chapter GitBook handbook.

- **Every public API has a `/--` docstring.** Functions, structures, and
  type definitions in the Lean source include inline documentation.

- **Clear contributor onboarding.** `CONTRIBUTING.md` provides a 5-minute path
  through essential documents. `README.md` offers a structured "start here"
  section.

- **Detailed changelog.** `CHANGELOG.md` (173 lines) tracks version history
  with workstream references.

- **Policy documents are actionable.** `CI_POLICY.md`, `TESTING_FRAMEWORK_PLAN.md`,
  and `HARDWARE_BOUNDARY_CONTRACT_POLICY.md` include checklists, required
  commands, and enforcement mechanisms — not just aspirational text.

### 5.2 Criticisms

- **Documentation-to-code ratio is very high.** The repository has ~4,250 lines
  of Lean source code and an estimated 10,000+ lines of markdown documentation.
  While thorough, this creates a maintenance burden: every code change must be
  cross-checked against multiple documents. There is no automated link or
  reference validation.

- **Proof strategy documentation is thin.** Invariant files
  (e.g., `Capability/Invariant.lean` at 765 lines, `IPC/Invariant.lean` at
  730 lines) contain complex proofs but minimal comments explaining *why* a
  particular proof strategy was chosen. A reader familiar with Lean tactics can
  follow the proofs, but the intent and key insights are not documented.

- **GitBook chapters have significant overlap with root docs.** Content in
  `docs/gitbook/07-testing-and-ci.md` largely duplicates
  `docs/TESTING_FRAMEWORK_PLAN.md` and `docs/CI_POLICY.md`. Similarly,
  `docs/gitbook/06-development-workflow.md` overlaps with `docs/DEVELOPMENT.md`.
  This creates a risk of drift.

- **No API reference generation.** Lean 4 supports `doc-gen4` for auto-generating
  browsable API documentation from `/--` docstrings. This project does not use
  it.

- **`tests/scenarios/README.md` exists but scenarios directory is otherwise
  empty.** The README references a scenario framework that has not been
  populated.

### 5.3 Recommendations

1. Add a `doc-gen4` step to CI for auto-generated API reference.
2. Consolidate GitBook chapters and root docs by having GitBook chapters
   `include` or reference root docs rather than duplicating content.
3. Add proof-strategy comments to invariant files explaining key lemma
   decomposition choices.
4. Add a CI check that validates internal markdown cross-references.
5. Populate or remove the empty `tests/scenarios/` directory.

---

## 6. Security

### 6.1 Strengths

- **Zero hardcoded secrets.** Grep scan for secrets patterns returned no matches
  in source code. GitHub Actions workflows use `secrets.GITHUB_TOKEN` properly.

- **Automated security scanning.** The `platform_security_baseline.yml` workflow
  runs Gitleaks (secret scanning), Trivy (dependency vulnerabilities), and
  CodeQL (workflow analysis) on every PR and weekly.

- **Test-fixture isolation is enforced.** Tier 0 hygiene verifies that
  `SeLe4n/Kernel/` never imports `SeLe4n/Testing/RuntimeContractFixtures`,
  preventing permissive test contracts from leaking into production modules.

- **Capability attenuation is formally proven.** The type system and theorem
  proofs guarantee that derived capabilities cannot gain rights beyond their
  parent — a core seL4 security property.

- **No `unsafe` code.** Grep scan confirmed zero uses of `unsafe` in the
  codebase.

- **Minimal dependency surface.** Zero external Lean package dependencies.
  The only supply-chain exposure is the Lean toolchain itself.

### 6.2 Criticisms

- **`.gitignore` is minimal.** Only `/.lake` and `/tests/artifacts` are excluded.
  Common editor artifacts (`.vscode/`, `.idea/`, `*.swp`) and OS files
  (`.DS_Store`, `Thumbs.db`) are not excluded, creating a minor risk of
  accidental commits.

- **`setup_lean_env.sh` pipes curl to sh.** Line 107-108 downloads and executes
  `elan-init.sh` via `curl | sh`. This is standard for Lean toolchain
  installation but bypasses integrity verification (no checksum or signature
  check).

- **Information-flow properties are deferred.** The `INFORMATION_FLOW_ROADMAP.md`
  documents a 5-milestone plan (IF-M1..IF-M5) for noninterference and
  confidentiality proofs, but no code exists for this yet. Until these proofs
  are complete, the model cannot claim end-to-end information-flow security.

- **No explicit threat model document.** While individual security properties
  are proven (capability attenuation, authority monotonicity), there is no
  document that articulates the threat model, trust boundaries, and security
  goals of the formal model as a whole.

### 6.3 Recommendations

1. Expand `.gitignore` with standard editor and OS artifact patterns.
2. Add checksum verification to `setup_lean_env.sh` for the Elan installer.
3. Create a `THREAT_MODEL.md` document articulating trust boundaries and
   security goals.
4. Prioritize the IF-M1 milestone to begin information-flow formalization.

---

## 7. Build and CI/CD

### 7.1 Strengths

- **Three-workflow CI pipeline.** `lean_action_ci.yml` (tiered testing),
  `nightly_determinism.yml` (Tier 4 replay), and `platform_security_baseline.yml`
  (ARM64 + security scans) provide comprehensive automated validation.

- **Progressive gating.** CI jobs are chained: `test-fast` → `test-smoke` →
  `test-full`, preventing expensive runs when basic checks fail.

- **Aggressive caching.** Lean toolchain (`~/.elan`), Lake packages
  (`.lake/packages`), and build artifacts (`.lake/build`) are cached with
  composite keys derived from `lean-toolchain`, `lake-manifest.json`,
  `lakefile.toml`, and `setup_lean_env.sh`.

- **ARM64 platform signal.** The `architecture-arm64-fast` job validates
  compilation on `ubuntu-24.04-arm`, important for Raspberry Pi 5 targeting.

- **Nightly artifact preservation.** Tier 4 nightly runs upload trace artifacts
  and determinism diffs for post-run analysis.

### 7.2 Criticisms

- **No branch protection enforcement in repository settings is verified by CI.**
  `CI_POLICY.md` documents required branch protection rules, but there is no
  automated check that these settings are actually configured on the repository.

- **CodeQL analysis is non-blocking.** `platform_security_baseline.yml:80` sets
  `continue-on-error: true` for CodeQL. This means CodeQL failures are silently
  ignored.

- **No Lean version upgrade automation.** The toolchain is pinned at `v4.27.0`
  via `lean-toolchain`. There is no Dependabot or equivalent configuration to
  track Lean releases and propose updates.

- **Cache invalidation granularity.** The cache key includes `setup_lean_env.sh`,
  which means any edit to the setup script (even a comment change) invalidates
  the entire Lean toolchain cache. This is overly conservative.

- **No test timing or flake tracking.** CI does not record test execution times
  or track flaky test history. As the test suite grows, this will become
  important for maintaining CI reliability.

### 7.3 Recommendations

1. Make CodeQL analysis blocking, or add explicit justification for
   `continue-on-error`.
2. Add Dependabot or Renovate configuration for Lean toolchain tracking.
3. Refine cache keys to use a hash of only the installer URL/version rather
   than the entire setup script.
4. Add test timing output to CI artifacts for performance trend tracking.
5. Consider a GitHub Actions workflow that verifies branch protection settings
   via the GitHub API.

---

## 8. Specific File-Level Observations

| File | Lines | Observation |
|------|-------|-------------|
| `Prelude.lean` | 131 | Clean. Six `abbrev` types should be upgraded to `structure`. |
| `Machine.lean` | 50 | Minimal and correct. `Memory := PAddr → UInt8` needs bounded alternative for hardware. |
| `Model/Object.lean` | 168 | Well-structured. `CNode.slots` list encoding hides radix-tree semantics. |
| `Model/State.lean` | 376 | Largest model file. Good theorem coverage for helper operations. |
| `Scheduler/Operations.lean` | ~60 | Clean. Minimal complexity. |
| `Capability/Operations.lean` | 139 | Solid. `capAttenuates` Prop/Bool gap noted above. |
| `Capability/Invariant.lean` | ~765 | Extensive proofs. Needs proof-strategy comments. |
| `IPC/Operations.lean` | 62 | Clean state-machine implementation. |
| `IPC/Invariant.lean` | ~730 | Complex proofs. Good helper factoring via `endpoint_store_preserves_*`. |
| `Lifecycle/Operations.lean` | ~100 | Good error ordering documentation. |
| `Service/Operations.lean` | ~100 | Policy abstraction is maximally generic. |
| `Architecture/Assumptions.lean` | 120 | Excellent inventory design with completeness proof. |
| `Architecture/Adapter.lean` | ~80 | Clean adapter pattern with error mapping. |
| `Main.lean` | 405 | Needs refactoring. Deeply nested, no assertions, single bootstrap state. |

---

## 9. Summary of Recommendations by Priority

### High Priority (before hardware milestone)

1. **Model VSpace/page-tables.** This is the critical gap for Raspberry Pi 5.
2. **Add property-based testing across all subsystems.** The current test suite
   covers one fixed state. Generative testing is essential for confidence.
3. **Refactor `Main.lean`.** Extract named scenario functions and add
   programmatic assertions.
4. **Upgrade remaining `abbrev` types to `structure` wrappers.** Completes the
   WS-A3 type-safety initiative.

### Medium Priority (next 1–2 milestones)

5. **Add negative/adversarial tests.** Verify that malformed states produce
   correct errors.
6. **Model CNode guard/radix address resolution.** Closes a semantic gap with
   real seL4.
7. **Add notification objects.** Required for complete IPC modeling.
8. **Begin information-flow proofs (IF-M1).** Deferred security properties
   represent the largest residual risk.
9. **Integrate `doc-gen4` for API reference generation.**
10. **Create `THREAT_MODEL.md`.** Articulates what the formal model guarantees.

### Low Priority (ongoing maintenance)

11. Expand `.gitignore` with editor/OS patterns.
12. Add checksum verification to `setup_lean_env.sh`.
13. Consolidate duplicated GitBook/root documentation.
14. Make CodeQL blocking or justify non-blocking status.
15. Add Dependabot/Renovate for toolchain tracking.
16. Populate or remove empty `tests/scenarios/` directory.
17. Add CI test timing and flake tracking.

---

## 10. Conclusion

seLe4n is a well-engineered formal verification project that demonstrates strong
discipline in proof development, architecture, and documentation. The codebase has
zero unresolved proof obligations, clean module boundaries, and a mature CI pipeline
with security scanning.

The main risks for the next phase are:

- **The model is abstract.** Function-encoded maps, unresolved VSpace, and
  list-encoded CNode slots will all need revision for hardware execution.
- **Testing is broad but shallow.** One fixed state, fragment-based trace
  matching, and no negative tests leave gaps in confidence.
- **Documentation volume creates maintenance burden.** The high doc-to-code
  ratio requires disciplined co-evolution.

These are tractable problems for a project at this maturity level, and the
existing architecture provides a solid foundation for addressing them.
