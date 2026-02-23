# Comprehensive Project Audit — seLe4n v0.11.6

**Date:** 2026-02-23
**Scope:** End-to-end codebase audit covering foundations, kernel subsystems,
proof integrity, test infrastructure, information-flow model, documentation
accuracy, and architectural coherence.

**Methodology:** Direct source code examination of all 33 `.lean` files, all 19
scripts, test fixtures, build configuration, and cross-referencing documentation
claims against actual code artifacts. No reliance on documentation self-reporting.

---

## Executive Summary

seLe4n is a well-structured Lean 4 formalization of core seL4 microkernel
semantics with **zero `sorry`/`axiom` usage** in the proof surface, a clean
Operations/Invariant separation across all subsystems, and comprehensive
executable test suites. The project demonstrates disciplined formal methods
engineering.

However, this audit identifies **18 material findings** and **12 advisory
observations** across type safety, proof coverage gaps, invariant quality,
architecture proof boundaries, information-flow model limitations, and test
infrastructure weaknesses that should be addressed to strengthen assurance
claims.

---

## 1. Proof Integrity (PASS)

**Result:** Clean. No `sorry`, `axiom`, `Axiom`, `native_decide`, or `decide!`
found anywhere in the `.lean` source tree.

All 33 Lean files were scanned. Every theorem is machine-checked by the Lean 4
kernel. This is the single most important property of the project and it holds.

---

## 2. Foundations (Prelude, Machine, Model)

### 2.1 Typed Identifiers — Well Done

`SeLe4n/Prelude.lean` defines typed wrappers (`ThreadId`, `ObjId`, `CPtr`,
`Slot`, `DomainId`, `Priority`, etc.) as distinct `structure` types wrapping
`Nat`. Cross-type conversions are explicit (`ThreadId.toObjId`). This eliminates
an entire class of bugs where IDs from different domains could be silently
confused.

### 2.2 FINDING [F-HIGH-01]: `RegName`/`RegValue` Are Type Aliases, Not Wrappers

**File:** `SeLe4n/Machine.lean:6-9`
**Severity:** High

```lean
abbrev RegName := Nat
abbrev RegValue := Nat
```

These are `abbrev` (transparent aliases), meaning a `RegName` is
indistinguishable from any `Nat` at the type level. A raw `Nat` can be passed
where `RegName` is expected with zero compiler protection. This directly
contradicts the typed-identifier discipline used everywhere else in Prelude.

**Recommendation:** Convert to `structure RegName where val : Nat` and
`structure RegValue where val : Nat` with explicit conversion helpers, matching
the pattern used for all other identifiers.

### 2.3 FINDING [F-MED-01]: Monad Has No `MonadError`/`MonadState` Instances

**File:** `SeLe4n/Prelude.lean:259-276`
**Severity:** Medium

`KernelM` is defined as:
```lean
abbrev KernelM (σ ε α : Type) := σ → Except ε (α × σ)
```

Only a bare `Monad` instance is provided. There is no `MonadError` or
`MonadState` instance, forcing all call sites to manually pattern-match on
`Except` and thread state. This leads to deeply nested match cascades throughout
Operations files (e.g., `IPC/Operations.lean` has 3-4 levels of nested matching
in `notificationWait`).

**Recommendation:** Add `MonadError` and `MonadState` instances (or use `do`
notation with `ExceptT (StateT σ Id)`). This would reduce boilerplate and make
transition functions more readable without changing semantics.

### 2.4 Memory Model Is Intentionally Abstract

`Memory := PAddr → UInt8` allows unbounded addresses with no bounds checking.
This is acceptable for an abstract model but should be documented as a
simplification that would need refinement for hardware-targeted verification.

---

## 3. Kernel Subsystems

### 3.1 Scheduler (`Kernel/Scheduler/`)

**Strengths:**
- Three clean invariant components: `queueCurrentConsistent`,
  `runQueueUnique`, `currentThreadValid`
- All operations (`chooseThread`, `schedule`, `handleYield`) have complete
  preservation proofs for the full `kernelInvariant` bundle
- `chooseThread` is proven read-only (`chooseThread_preserves_state`)
- Priority-based selection is deterministic (first-in-order tie-breaking)

**FINDING [F-MED-02]: `schedulerWellFormed` Is a Degenerate Alias**

**File:** `SeLe4n/Kernel/Scheduler/Invariant.lean:39`
**Severity:** Medium

```lean
abbrev schedulerWellFormed (s : SchedulerState) : Prop :=
  queueCurrentConsistent s
```

`schedulerWellFormed` is an alias for just `queueCurrentConsistent`, not the
full bundle. The comment says "intentionally identical" but this is misleading
— the name suggests it should encompass all well-formedness conditions
(`queueCurrentConsistent ∧ runQueueUnique ∧ currentThreadValid`). The real
bundle is `kernelInvariant` which is itself aliased as
`schedulerInvariantBundle`.

This creates a confusing naming hierarchy:
```
schedulerWellFormed = queueCurrentConsistent (SUBSET)
kernelInvariant = queueCurrentConsistent ∧ runQueueUnique ∧ currentThreadValid
schedulerInvariantBundle = kernelInvariant (ALIAS)
```

**Recommendation:** Either rename `schedulerWellFormed` to
`schedulerQueueConsistent` to avoid confusion, or expand it to match
`kernelInvariant`. Having three names for two different things (where one
name is misleading) is a maintenance trap.

### 3.2 Capability Operations (`Kernel/Capability/`)

**Strengths:**
- Clean CSpace lookup, insert, delete, revoke, and mint operations
- `cspaceLookupSlot_ok_iff_lookupSlotCap` establishes bidirectional
  correspondence between monadic lookup and pure lookup
- `mintDerivedCap` enforces rights attenuation with `rightsSubset_sound`
  providing the soundness proof
- Revoke is correctly scoped to local CNode (documented as intentional)

**Observation:** `cspaceLookupSlot` has a subtle asymmetry — on failure it
distinguishes "CNode exists but slot is empty" (→ `invalidCapability`) from
"no CNode at all" (→ `objectNotFound`). This is good API design.

### FINDING [F-HIGH-03]: Capability Invariants Are Tautologically True

**File:** `SeLe4n/Kernel/Capability/Invariant.lean:456-477`
**Severity:** High

Two of the four `capabilityInvariantBundle` components are trivially true
by construction and provide no meaningful assurance:

**`cspaceSlotUnique`**: Claims "lookup is deterministic for each slot address."
The proof works because `cspaceLookupSlot` is read-only (doesn't modify
state), so two lookups of the same address trivially return the same result.
This is a property of pure functions in general, not a meaningful uniqueness
guarantee.

**`cspaceLookupSound`**: Claims "successful lookup corresponds to concrete
content." The proof simply unpacks `cspaceLookupSlot`'s return value. Since
lookup doesn't modify state (st' = st is immediate), and it returns what's
in the slot, this is tautological.

Both invariants are "preserved" by every operation trivially — they hold for
any `SystemState` whatsoever. They inflate the capability invariant bundle
without providing security evidence.

**Recommendation:** Either remove these tautological components from the
bundle, or redefine them to capture meaningful properties (e.g., slot
uniqueness across different CNode paths that resolve to the same backing
slot).

### 3.3 IPC Operations (`Kernel/IPC/`)

**Strengths:**
- Endpoint state machine is explicit: idle → send/receive transitions are
  fully deterministic with all invalid transitions returning specific errors
- `notificationWait` correctly handles duplicate-wait prevention (F-12)
- Badge accumulation uses bitwise OR — matches real seL4 semantics
- Invariant file (~890 lines) has substantial preservation proofs

### FINDING [F-HIGH-04]: `uniqueWaiters` Not Composed Into Global IPC Invariant

**File:** `SeLe4n/Kernel/IPC/Invariant.lean:839-888`
**Severity:** High

The F-12 double-wait prevention (`uniqueWaiters`) is proven preserved by
`notificationWait`, but it is **NOT included** in the global `ipcInvariant`
bundle (lines 252-259). The bundle only contains `endpointInvariant` and
`notificationInvariant` (which is `notificationQueueWellFormed` alone).

This means:
- The composed bundles (M3, M3.5, M4-A) do not transitively verify
  double-wait prevention
- A state that violates waiter uniqueness would satisfy the global
  invariant bundle
- The F-12 proof exists but has no compositional force

**Recommendation:** Add `uniqueWaiters` to `notificationInvariant` or
`ipcInvariant` so preservation proofs compose through the bundle hierarchy.

### FINDING [F-MED-07]: `endpointObjectValid` Is Redundant

**File:** `SeLe4n/Kernel/IPC/Invariant.lean:232-239`
**Severity:** Medium

`endpointObjectValid` is provably implied by `endpointQueueWellFormed`
(theorem `endpointObjectValid_of_queueWellFormed`), yet both are included
in `endpointInvariant`. This redundancy inflates the invariant surface
without adding assurance.

**Recommendation:** Simplify `endpointInvariant` to just
`endpointQueueWellFormed`, or redefine `endpointObjectValid` to capture
an independent property.

**FINDING [F-MED-03]: `storeTcbIpcState` Silently Succeeds on Missing TCB**

**File:** `SeLe4n/Kernel/IPC/Operations.lean:24-30`
**Severity:** Medium

```lean
def storeTcbIpcState (st : SystemState) (tid : SeLe4n.ThreadId)
    (ipcState : ThreadIpcState) : Except KernelError SystemState :=
  match lookupTcb st tid with
  | none => .ok st    -- ← Silent success, no state change
  | some tcb => ...
```

When the target thread doesn't exist (or isn't a TCB), this function returns
`.ok st` — success with unchanged state. This means `notificationSignal` and
`notificationWait` can "succeed" in updating IPC state even when the thread
doesn't exist. The operations appear to succeed but silently skip the TCB
state update.

In real seL4, attempting to modify a non-existent thread's state would be an
error. This silent-success pattern could mask bugs in test scenarios where
a thread ID is misconfigured.

**Recommendation:** Return `.error .objectNotFound` when the TCB doesn't exist,
or at minimum document this as an intentional design choice with rationale.

### 3.4 Lifecycle Operations (`Kernel/Lifecycle/`)

**Strengths:**
- `lifecycleRetypeObject` enforces a 5-step deterministic check chain:
  object existence → metadata consistency → authority lookup → authority
  verification → atomic update
- `lifecycleRevokeDeleteRetype` composes revoke/delete/retype with explicit
  partial-failure semantics and an anti-aliasing guard
- Extensive decomposition theorems
  (`lifecycleRevokeDeleteRetype_ok_implies_staged_steps`)

### FINDING [F-MED-08]: Lifecycle Invariant Bundle Contains Redundant Components

**File:** `SeLe4n/Kernel/Lifecycle/Invariant.lean:40-101`
**Severity:** Medium

`lifecycleIdentityNoTypeAliasConflict` is proven derivable from
`lifecycleIdentityTypeExact` (theorem at line 103). Similarly,
`lifecycleCapabilityRefObjectTargetTypeAligned` is proven derivable from
identity exactness. Yet both are included in the bundle alongside the
properties that imply them.

This creates a misleading count of "independent" invariant components.
Preservation proofs for the bundle are weaker than they appear because
the redundant components add no additional verification obligation.

### FINDING [F-MED-09]: No Cross-Subsystem Composition Proof

**File:** `SeLe4n/Kernel/Capability/Invariant.lean:573-608`
**Severity:** Medium

The M3/M3.5/M4-A composed bundles are defined as conjunctions of subsystem
bundles, and individual operations are proven to preserve them. However:

1. No theorem proves that **arbitrary sequences** of operations from
   different subsystems preserve the composed bundle
2. No interference analysis proves that IPC operations cannot corrupt
   lifecycle state or vice versa
3. The storeObject_preserves_lifecycleMetadataConsistent lemma (used by
   lifecycle preservation) is taken as given without inline verification

The proof of `lifecycleRetypeObject_preserves_lifecycleInvariantBundle`
abstracts entirely through metadata consistency without verifying that
the retype preconditions (authority, type match) actually protect
invariants.

**Recommendation:** Add an explicit composition theorem or interference
analysis document.

---

## 4. Service Orchestration (`Kernel/Service/`)

**Strengths:**
- Clean start/stop/restart state machine with explicit policy gates
- Cycle detection via bounded BFS (`serviceHasPathTo`) is well-designed
- Self-dependency and idempotent re-registration are handled correctly
- `serviceRestart` has documented partial-failure semantics (F-11)

**FINDING [F-LOW-01]: BFS Fuel Bound Is Ad Hoc**

**File:** `SeLe4n/Kernel/Service/Operations.lean:96-97`
**Severity:** Low

```lean
def serviceBfsFuel (st : SystemState) : Nat :=
  st.objectIndex.length + 256
```

The `+ 256` magic constant is described as accounting for "service IDs that may
not have corresponding kernel objects." This is a reasonable heuristic but:

1. There is no proof that this fuel bound is sufficient for all reachable
   service graphs
2. If fuel is exhausted, `serviceHasPathTo` returns `false` (no path found),
   which means a cycle could go undetected, allowing cycle creation
3. The fuel should be tied to the number of *service entries*, not object index
   length

**Recommendation:** Use `(st.objectIndex.length + serviceCount st)` as the
fuel, or prove that the current bound is sufficient given the finite service
graph.

---

## 5. Architecture Layer (`Kernel/Architecture/`)

**Strengths:**
- Clean separation of assumptions from implementation via
  `ArchAssumption` enumeration and `RuntimeBoundaryContract` structure
- Adapter operations are gated by contract predicates with `Decidable`
  instances
- `assumptionInventoryComplete_holds` theorem proves the inventory
  enumeration is exhaustive
- VSpace operations have proper invariant proofs (ASID preservation,
  no-overlap, lookup correctness)

### FINDING [F-HIGH-05]: Architecture Layer Exports Proof Obligations Rather Than Closing Them

**File:** `SeLe4n/Kernel/Architecture/Invariant.lean:44-60`,
`SeLe4n/Kernel/Architecture/Assumptions.lean`
**Severity:** High

The architecture layer's five extracted assumptions (`deterministicTimerProgress`,
`deterministicRegisterContext`, `memoryAccessSafety`, `bootObjectTyping`,
`irqRoutingTotality`) are all **external preconditions**, not properties proven
by the kernel. The `RuntimeBoundaryContract` structure contains only
`Decidable` witnesses — no proof that the contract predicates are correct.

More critically, `AdapterProofHooks` (Invariant.lean:44-60) requires the
**caller** to provide preservation proofs for each adapter operation:

```lean
structure AdapterProofHooks (contract : RuntimeBoundaryContract) where
  preserveAdvanceTimer :
    ∀ ticks st,
      proofLayerInvariantBundle st →
      contract.timerMonotonic st (advanceTimerState ticks st) →
      ticks ≠ 0 →
      proofLayerInvariantBundle (advanceTimerState ticks st)
```

The kernel's claim is not "adapters preserve invariants" but rather
"**if you can prove adapters preserve invariants**, then the kernel is
sound." This is a conditional guarantee, not a self-contained one.

**Impact:** The theorem "if you assume X, the kernel is safe" is well
articulated. The dual "the kernel ensures X holds" is almost nowhere
proved. This fundamentally limits the assurance level.

**Recommendation:** Document this as an explicit architectural decision
(the kernel is a **verified component** that composes with platform
proofs, not a standalone safety proof). Alternatively, provide concrete
`AdapterProofHooks` instances for at least one reference platform.

### FINDING [F-MED-10]: `vspaceAsidRootsUnique` Required But Never Established

**File:** `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean`
**Severity:** Medium

The four VSpace round-trip theorems (TPI-001) — `vspaceLookup_after_map`,
`vspaceLookup_map_other`, `vspaceLookup_after_unmap`,
`vspaceLookup_unmap_other` — all assume `vspaceInvariantBundle st`, which
includes `vspaceAsidRootsUnique st` (no two VSpace roots share an ASID).

This property is **never proved** to hold after initialization or after
any VSpace operation. It is an assumed precondition. If two roots somehow
share an ASID (e.g., through misconfigured boot state), `resolveAsidRoot`
could return the wrong root and all VSpace correctness breaks down.

**Recommendation:** Prove that `vspaceMapPage` and `vspaceUnmapPage`
preserve `vspaceAsidRootsUnique`, or add initialization lemmas showing
it holds at boot.

### FINDING [F-MED-11]: Service Policy Surface Depends on Unproven Hypothesis

**File:** `SeLe4n/Kernel/Service/Invariant.lean:138-150`
**Severity:** Medium

`servicePolicySurfaceInvariant_of_lifecycleInvariant` bridges service
policy to lifecycle invariants but requires a free hypothesis
`hBackingObjects`:

```
∀ sid svc, lookupService st sid = some svc →
    ∃ obj, st.objects svc.identity.backingObject = some obj
```

This hypothesis — "every registered service has a backing object in the
object store" — is **never proved** in the codebase. No theorem states
that booting preserves it, nor that service operations maintain it.

If a service's backing object is deleted or never initialized, the
policy surface becomes vacuously satisfied but unsound.

**Recommendation:** Add `hBackingObjects` as a component of the service
invariant bundle, or prove it as a consequence of initialization.

---

## 6. Information Flow Model

### 6.1 Policy Layer — Correct but Minimal

**File:** `SeLe4n/Kernel/InformationFlow/Policy.lean`

The security lattice is a 2×2 product:
- Confidentiality: `{low, high}`
- Integrity: `{untrusted, trusted}`

With proven reflexivity and transitivity for both dimensions and the combined
`securityFlowsTo` relation. This is mathematically correct.

**However:** A two-point lattice is the minimum viable security lattice. Real
seL4 uses per-domain labels. The current model can only distinguish "public vs.
secret" and "trusted vs. untrusted" — it cannot express multi-level security
(MLS) with more than two levels, or mandatory access control (MAC) policies
with per-component labels.

### 6.2 Projection Layer — Correct

**File:** `SeLe4n/Kernel/InformationFlow/Projection.lean`

State projection is well-designed:
- `projectState` filters objects, runnable queue, current thread, and
  services through observability gates
- `lowEquivalent` is defined as equality of projections (standard
  definition)
- Proven to be an equivalence relation (refl, symm, trans)

### 6.3 FINDING [F-HIGH-02]: Non-Interference Proofs Have Structural Limitations

**File:** `SeLe4n/Kernel/InformationFlow/Invariant.lean`
**Severity:** High

The non-interference theorems have a significant structural pattern that
limits their assurance value:

**All theorems require the same operation to succeed on BOTH states.**

For example, `endpointSend_preserves_lowEquivalent` requires:
```lean
(hStep₁ : endpointSend endpointId sender s₁ = .ok ((), s₁'))
(hStep₂ : endpointSend endpointId sender s₂ = .ok ((), s₂'))
```

This means the theorem only applies when the operation succeeds on both
low-equivalent states. It does NOT cover the case where:
- The operation succeeds on `s₁` but fails on `s₂` (or vice versa)
- The success/failure outcome itself leaks information about the
  high-domain state

In real non-interference (e.g., the seL4 infoflow proof), you need to show
that if `s₁ ≈_L s₂`, then for any operation:
1. Both succeed with low-equivalent results, OR
2. Both fail, OR
3. The low-observable effect is the same regardless

The current theorems only cover case (1). An operation that succeeds on one
state and fails on another because of high-domain differences would violate
non-interference, and this isn't captured.

**Recommendation:** Either:
(a) Prove that for low-equivalent states, operations always have the same
    success/failure outcome (the "step consistency" lemma), or
(b) Extend the theorems to cover the mixed success/failure case, or
(c) Document this as a known limitation with a tracking issue.

### 6.4 FINDING [F-MED-04]: Enforcement Boundary Is Incomplete

**File:** `SeLe4n/Kernel/InformationFlow/Enforcement.lean`
**Severity:** Medium

Only 3 operations have policy-checked variants:
- `endpointSendChecked`
- `cspaceMintChecked`
- `serviceRestartChecked`

The enforcement module explicitly documents that other operations
(notification, vspace, lifecycle) rely on "capability-based authority alone."
But this argument is incomplete:

1. `notificationSignal` takes a `badge` parameter that merges into pending
   state via bitwise OR. A high-domain caller could encode information in
   badge bits that a low-domain waiter then reads.
2. `lifecycleRetypeObject` changes the type of an object that may be
   referenced by capabilities held in other domains.

The module's argument that "the capability itself encodes the authority grant"
conflates authorization with information flow. Having permission to perform an
operation doesn't mean the operation can't create an information channel.

**Recommendation:** Analyze each unchecked operation for covert channels, not
just authorization. At minimum, document which operations were analyzed and
which weren't.

### 6.5 Observation: `defaultLabelingContext` Labels Everything Public

`Policy.lean:61-67` defines a default labeling where every entity is
`publicLabel`. This means the information flow model is trivially permissive
unless a test or caller provides a non-default context. The tests do provide
custom contexts, which is good.

---

## 7. Test Infrastructure

### 7.1 Executable Test Suites — Good Coverage

The project has three executable test suites:

| Suite | Focus | Assertions |
|-------|-------|------------|
| `NegativeStateSuite` | Error paths, state machine violations | ~30 checks |
| `InformationFlowSuite` | Projection, enforcement, low-equivalence | ~25 checks |
| `TraceSequenceProbe` | Random IPC sequence fuzzing | 250 steps |

**Strengths:**
- `NegativeStateSuite` checks specific error codes, not just "did it fail"
- `InformationFlowSuite` was upgraded to test distinct-state low-equivalence
  (not just reflexive tautology)
- `TraceSequenceProbe` uses pseudo-random operation selection with invariant
  checking at every step
- `InvariantChecks.lean` provides reusable runtime invariant checkers that
  mirror the formal invariant definitions

### 7.2 FINDING [F-MED-05]: Runtime Invariant Checks Don't Cover All Formal Invariants

**File:** `SeLe4n/Testing/InvariantChecks.lean`
**Severity:** Medium

The runtime invariant checker (`stateInvariantChecksFor`) checks:
- Scheduler queue/current consistency
- Run queue uniqueness
- Current thread validity
- Runnable threads resolve to ready TCBs
- Endpoint queue/state well-formedness
- Notification queue/state well-formedness

**Missing from runtime checks:**
- `cspaceSlotUnique` — capability slot uniqueness
- `cspaceLookupSound` — lookup soundness
- `lifecycleMetadataConsistent` — metadata/object consistency
- `lifecycleStaleReferenceExclusionInvariant`
- Any information-flow invariants

The formal proof surface covers these, but the runtime tests cannot
detect violations in them. If a test constructs a state that violates
capability invariants, the runtime checker won't catch it.

**Recommendation:** Add runtime checks for capability and lifecycle
invariants, at least for the `NegativeStateSuite` which constructs
complex states.

### 7.3 FINDING [F-MED-06]: `TraceSequenceProbe` Only Exercises IPC

**File:** `tests/TraceSequenceProbe.lean`
**Severity:** Medium

The random probe only generates three operations:
```lean
inductive ProbeOp where
  | send
  | awaitReceive
  | receive
```

This means the fuzzer never exercises:
- Capability operations (mint, delete, revoke)
- Lifecycle operations (retype)
- Scheduler operations (schedule, yield)
- Notification operations
- VSpace operations
- Service operations

A state-machine fuzzer that only tests 3 out of ~20 operations has
limited bug-finding power.

**Recommendation:** Extend the probe to cover at minimum scheduler
operations, notification wait/signal, and capability mint/delete.

### 7.4 `MainTraceHarness` Is Fixture-Locked

The main trace harness output is compared against a golden fixture
(`tests/fixtures/main_trace_smoke.expected`). This is a good regression
guard but it means the trace harness is effectively a fixed script, not
a generative test. Changing any output text requires updating the fixture.

### 7.5 FINDING [F-MED-12]: Trace Fixture Validation Uses Substring Matching

**File:** `scripts/test_tier2_trace.sh:75`
**Severity:** Medium

The trace fixture comparison uses `grep -Fq` (fixed-string substring match):

```bash
if grep -Fq "${expected_fragment}" "${TRACE_OUTPUT}"; then
```

This means a fixture line like `"adapter timer success path value: 2"` would
match against output containing `"adapter timer success path value: 256"` or
`"adapter timer success path value: 2 (extra text)"`. The check verifies that
the expected substring appears *somewhere* in the output but does not verify:
- That the line matches exactly (no extra content)
- That each fixture line maps to a distinct output line (no double-counting)
- That the output doesn't contain unexpected *additional* lines

For a formal verification project where the trace output serves as a semantic
regression oracle, substring matching provides weaker guarantees than exact
line-for-line comparison.

**Recommendation:** Replace `grep -Fq` with an exact comparison strategy:
either full `diff` against the expected fixture, or line-by-line exact
matching with `==` (accounting for ordering). At minimum, add a post-match
assertion that `wc -l` of the output matches `wc -l` of the fixture.

### 7.6 FINDING [F-MED-13]: Tier 3 Invariant Surface Checks Are Definition-Presence Tests

**File:** `scripts/test_tier3_invariant_surface.sh`
**Severity:** Medium

Tier 3 runs 378 `run_check` invocations, but every single one is a `rg -n`
call checking that a definition, theorem, structure, or comment anchor
*exists* in a specific file. For example:

```bash
run_check "INVARIANT" rg -n '^theorem schedule_preserves_schedulerInvariantBundle' \
  SeLe4n/Kernel/Scheduler/Operations.lean
```

This verifies that the definition line exists — it does NOT verify:
- That the theorem actually type-checks (Tier 1 `lake build` covers this)
- That the theorem has the expected statement (signature could change)
- That the theorem is used or composed anywhere
- That the invariant it preserves is non-trivial

Since Tier 1 already builds the project (ensuring all theorems type-check),
the incremental value of Tier 3 is limited to detecting *accidental deletion*
of definitions. The 378 checks create a surface impression of deep validation
while functioning as an anchor-presence linter.

This is not a defect — anchor-presence checking has value for preventing
regressions during refactoring. But the tier's name ("invariant surface")
and position in the test hierarchy (above trace testing and negative suites)
overstates its assurance contribution.

**Recommendation:** Rename the tier to "Anchor Presence" or "Regression
Anchors" to set appropriate expectations. Alternatively, augment a subset
of checks with signature matching (e.g., verify that key theorems preserve
the expected invariant bundle, not just that a definition starting with the
name exists).

### 7.7 `test_lib.sh` Implicit Cascading Exit

**File:** `scripts/test_lib.sh:122-124`

The `run_check` function calls `finalize_report` when `CONTINUE_MODE=0` and
a check fails. `finalize_report` calls `exit 1` at line 134. This means
`run_check` has a hidden `exit` in its failure path — callers that expect
to run cleanup after `run_check` will be bypassed. This is acceptable given
the `set -euo pipefail` context, but it means the `trap` cleanup handlers
are the only reliable cleanup mechanism, which they are correctly used for
in `test_tier2_trace.sh`.

---

## 8. Build System and Scripts

### 8.1 Build Configuration

`lakefile.toml` is clean and minimal:
- Version 0.11.6, Lean 4.27.0
- One library (`SeLe4n`), one main executable, three test executables
- No external dependencies (pure Lean 4, no Mathlib)

The lack of Mathlib dependency is notable — all proofs use only Lean 4's
built-in tactics. This is admirable for self-containedness but means the
project cannot leverage Mathlib's extensive tactic and lemma library.

### 8.2 Tiered Test Scripts

The tier system is well-organized:
- Tier 0: Hygiene (file checks, naming conventions)
- Tier 1: Build succeeds
- Tier 2: Trace + negative state
- Tier 3: Invariant surface + doc anchors
- Tier 4: Nightly experimental

### 8.3 CI Workflows Present

Four GitHub Actions workflows exist in `.github/workflows/`:
- `lean_action_ci.yml` — PR/push CI (docs, fast, smoke, full jobs)
- `nightly_determinism.yml` — Daily nightly Tier 4 + flake probing
- `platform_security_baseline.yml` — Security baseline checks
- `lean_toolchain_update_proposal.yml` — Automated toolchain proposals

The CI pipeline properly caches `.elan`, `.lake/packages`, and
`.lake/build` for performance.

---

## 9. Documentation Accuracy

### 9.1 CLAUDE.md — Accurate

The project instructions file accurately describes:
- Build commands (confirmed: `lake build` succeeds)
- Source layout (verified: all paths exist)
- File size estimates (confirmed within reasonable bounds)
- Key conventions (verified: Operations/Invariant split maintained)

### 9.2 README.md — Mostly Accurate

- Version badge says 0.11.6 ✓ (matches `lakefile.toml`)
- Lean version badge says v4.27.0 ✓ (matches `lean-toolchain`)
- Codebase map is accurate ✓
- Workstream status claims match code evidence ✓

### 9.3 API.lean Is Just Imports

`SeLe4n/Kernel/API.lean` is described in docs as the "Public kernel interface"
but it's actually just a file of 21 `import` statements with no definitions,
no re-exports, and no public API surface. It serves as an import aggregator,
not an API module.

---

## 10. Cross-Cutting Concerns

### 10.1 Determinism — Excellent

Every transition function returns `Except KernelError (α × SystemState)`.
There are no `IO` operations in the kernel, no `unsafe`, no `partial` (except
`runProbeLoop` in test code which is appropriately marked). The entire model
is purely functional and deterministic.

### 10.2 Error Handling — Comprehensive

The `KernelError` enum has 24 variants covering all failure modes. Each
operation returns specific error codes with documented ordering. The negative
test suite verifies specific error codes, not just failure.

### 10.3 State Modeling — Sound With Known Simplifications

Objects are modeled as `ObjId → Option KernelObject` (total function with
finite support tracked by `objectIndex`). This is sound for abstract
verification but differs from seL4's actual implementation (finite object
tables with explicit allocation).

Known simplifications that are acceptable for the current abstraction level:
- Flat VSpace mappings (vs. multi-level page tables)
- Single waiting receiver on endpoints
- No explicit thread states beyond IPC
- No fault handling

---

## Finding Summary

| ID | Severity | Area | Summary |
|----|----------|------|---------|
| F-HIGH-01 | High | Machine.lean | `RegName`/`RegValue` are transparent type aliases, not typed wrappers |
| F-HIGH-02 | High | InformationFlow | Non-interference proofs only cover both-succeed case |
| F-HIGH-03 | High | Capability | `cspaceSlotUnique` and `cspaceLookupSound` are tautologically true |
| F-HIGH-04 | High | IPC | `uniqueWaiters` (F-12) not composed into global IPC invariant bundle |
| F-HIGH-05 | High | Architecture | Proof obligations exported to platform via `AdapterProofHooks`, not closed by kernel |
| F-MED-01 | Medium | Prelude.lean | No `MonadError`/`MonadState` instances for `KernelM` |
| F-MED-02 | Medium | Scheduler | `schedulerWellFormed` is a misleading alias for a subset of invariants |
| F-MED-03 | Medium | IPC | `storeTcbIpcState` silently succeeds on missing/non-TCB objects |
| F-MED-04 | Medium | InfoFlow | Enforcement boundary doesn't analyze covert channels |
| F-MED-05 | Medium | Testing | Runtime invariant checks miss capability/lifecycle invariants |
| F-MED-06 | Medium | Testing | `TraceSequenceProbe` only fuzzes 3 of ~20 operations |
| F-MED-07 | Medium | IPC | `endpointObjectValid` is fully redundant with `endpointQueueWellFormed` |
| F-MED-08 | Medium | Lifecycle | Lifecycle invariant bundle contains redundant derivable components |
| F-MED-09 | Medium | Composition | No cross-subsystem interference analysis or composition proof |
| F-MED-10 | Medium | VSpace | `vspaceAsidRootsUnique` required for correctness but never established |
| F-MED-11 | Medium | Service | Service policy surface depends on unproven `hBackingObjects` hypothesis |
| F-MED-12 | Medium | Testing | Trace fixture comparison uses substring matching, not exact comparison |
| F-MED-13 | Medium | Testing | Tier 3 invariant surface checks are definition-presence tests only |
| F-LOW-01 | Low | Service | BFS fuel bound is ad hoc with no sufficiency proof |

---

## Recommendations (Prioritized)

### Immediate (before next release)

1. **Compose `uniqueWaiters` into global IPC invariant** — the F-12
   double-wait prevention proof exists but has no compositional force.
   Add it to `ipcInvariant` or `notificationInvariant`.

2. **Add step-consistency lemmas for non-interference** — prove that
   low-equivalent states produce the same success/failure outcome for each
   operation, closing the gap in the information-flow proofs.

3. **Replace tautological capability invariants** — either remove
   `cspaceSlotUnique`/`cspaceLookupSound` from the bundle or redefine
   them to capture meaningful properties (e.g., cross-path slot
   resolution uniqueness).

4. **Wrap `RegName`/`RegValue` as structures** — straightforward change
   that completes the typed-identifier discipline.

### Short-term (next workstream)

5. **Remove redundant invariant components** — `endpointObjectValid` is
   implied by `endpointQueueWellFormed`; lifecycle non-aliasing is
   derivable from exactness. Simplify bundles to independent components.

6. **Add cross-subsystem composition proof** — prove that arbitrary
   interleaving of operations from different subsystems preserves the
   M4-A composed bundle, or document the interference analysis.

7. **Expand `TraceSequenceProbe`** to cover scheduler, notification, and
   capability operations.

8. **Add runtime invariant checks** for capability and lifecycle
   invariants.

9. **Document `storeTcbIpcState` silent-success** — either change to
   error or add explicit rationale.

10. **Upgrade trace fixture comparison** — replace `grep -Fq` substring
    matching in `test_tier2_trace.sh` with exact line-level comparison
    or full `diff` to prevent silent regressions.

### Medium-term

11. **Analyze covert channels** in notification badge accumulation and
    lifecycle retype, documenting the analysis results.

12. **Add `MonadError`/`MonadState`** instances to reduce boilerplate in
    transition functions.

13. **Rename `schedulerWellFormed`** to eliminate naming confusion.

14. **Prove BFS fuel sufficiency** or use a structurally-decreasing
    termination argument.

15. **Rename Tier 3** from "invariant surface" to "anchor presence" or
    augment selected checks with signature matching.

---

## Conclusion

seLe4n demonstrates strong formal methods discipline: zero proof gaps, clean
architecture, deterministic semantics, and comprehensive error handling. The
typed-identifier system, Operations/Invariant split, and multi-tier test
infrastructure are well-executed.

The most significant areas for improvement are:
1. **Invariant quality**: Several invariant components are tautologically
   true (capability) or redundant (IPC, lifecycle), inflating the apparent
   proof surface without adding assurance. The F-12 double-wait prevention
   proof is not composed into the global bundle.
2. **Information-flow completeness**: Non-interference proofs need
   step-consistency lemmas and the enforcement boundary needs covert
   channel analysis.
3. **Compositional safety**: No theorem proves that interleaved operations
   from different subsystems preserve the composed M4-A invariant bundle.
4. **Test coverage**: The fuzzer should be expanded beyond IPC to exercise
   the full operation surface.
5. **Test fidelity**: The trace fixture comparison uses substring matching
   rather than exact comparison, and the Tier 3 invariant surface tier
   verifies definition presence rather than semantic correctness, overstating
   the assurance provided by the 378 anchor checks.

The project's foundations are solid and the identified issues are addressable
without architectural changes.
