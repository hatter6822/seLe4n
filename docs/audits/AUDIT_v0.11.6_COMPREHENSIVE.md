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

However, this audit identifies **7 material findings** and **12 advisory
observations** across type safety, proof coverage gaps, information-flow model
limitations, and test infrastructure weaknesses that should be addressed to
strengthen assurance claims.

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

### 3.3 IPC Operations (`Kernel/IPC/`)

**Strengths:**
- Endpoint state machine is explicit: idle → send/receive transitions are
  fully deterministic with all invalid transitions returning specific errors
- `notificationWait` correctly handles duplicate-wait prevention (F-12)
- Badge accumulation uses bitwise OR — matches real seL4 semantics
- Invariant file (~890 lines) has substantial preservation proofs

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

**No material findings.** This is one of the cleanest subsystems.

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

**Observation:** The architecture layer is a well-designed abstraction boundary.
The `AdapterProofHooks` structure in the Invariant file creates a formal
contract between architecture-specific implementations and the proof layer.

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

### 8.3 Observation: No CI Workflow in Repository

The README references CI badges for `lean_action_ci.yml` and
`platform_security_baseline.yml`, but `.github/workflows/` is not
present in the repository file listing. This could mean the workflows
are in the remote but not in the local checkout, or they may not exist.

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
| F-MED-01 | Medium | Prelude.lean | No `MonadError`/`MonadState` instances for `KernelM` |
| F-MED-02 | Medium | Scheduler | `schedulerWellFormed` is a misleading alias for a subset of invariants |
| F-MED-03 | Medium | IPC | `storeTcbIpcState` silently succeeds on missing/non-TCB objects |
| F-MED-04 | Medium | InfoFlow | Enforcement boundary doesn't analyze covert channels |
| F-MED-05 | Medium | Testing | Runtime invariant checks miss capability/lifecycle invariants |
| F-MED-06 | Medium | Testing | `TraceSequenceProbe` only fuzzes 3 of ~20 operations |
| F-LOW-01 | Low | Service | BFS fuel bound is ad hoc with no sufficiency proof |

---

## Recommendations (Prioritized)

### Immediate (before next release)

1. **Wrap `RegName`/`RegValue` as structures** — straightforward change that
   completes the typed-identifier discipline.

2. **Add step-consistency lemmas for non-interference** — prove that
   low-equivalent states produce the same success/failure outcome for each
   operation, closing the gap in the information-flow proofs.

3. **Document `storeTcbIpcState` silent-success behavior** — either change
   to error or add explicit rationale.

### Short-term (next workstream)

4. **Expand `TraceSequenceProbe`** to cover scheduler, notification, and
   capability operations.

5. **Add runtime invariant checks** for capability slot uniqueness, lookup
   soundness, and lifecycle metadata consistency.

6. **Rename `schedulerWellFormed`** to eliminate the naming confusion.

### Medium-term

7. **Analyze covert channels** in notification badge accumulation and
   lifecycle retype, documenting the analysis results.

8. **Add `MonadError`/`MonadState`** instances to reduce boilerplate in
   transition functions.

9. **Prove BFS fuel sufficiency** or use a structurally-decreasing
   termination argument.

---

## Conclusion

seLe4n demonstrates strong formal methods discipline: zero proof gaps, clean
architecture, deterministic semantics, and comprehensive error handling. The
typed-identifier system, Operations/Invariant split, and multi-tier test
infrastructure are well-executed.

The most significant areas for improvement are:
1. The information-flow non-interference proofs need step-consistency lemmas
   to close the mixed success/failure gap
2. The enforcement boundary analysis should be extended to cover covert
   channels, not just authorization
3. The test fuzzer should be expanded beyond IPC to exercise the full
   operation surface

The project's foundations are solid and the identified issues are addressable
without architectural changes.
