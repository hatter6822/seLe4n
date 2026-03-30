# WS-Y Workstream Plan — Final Audit Remediation (v0.22.22)

**Created**: 2026-03-30
**Baseline version**: 0.22.22
**Baseline audit**:
- `docs/audits/AUDIT_COMPREHENSIVE_v0.22.22_FULL_KERNEL_RUST.md` (0 CRIT, 0 HIGH, 2 MED, 8 LOW, 6 INFO)
**Prior portfolios**: WS-B through WS-X (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Executive Summary

A comprehensive full-kernel audit of seLe4n v0.22.22 was conducted on 2026-03-30,
covering all 102 Lean kernel modules (73,626 lines), 26 Rust ABI files (4,675
lines), and 15 test suites (~8,776 lines). The audit found **zero CVE-worthy
vulnerabilities**, zero `sorry`/`axiom`/`native_decide` in production code, and
complete invariant preservation coverage across all kernel subsystems.

After validating every finding against the actual codebase, we identified **14
unique actionable findings** (2 MEDIUM, 8 LOW, 4 INFORMATIONAL) requiring code,
proof, or documentation changes, plus **2 findings that are correctly documented
design decisions** requiring no action.

The codebase is in exceptional shape. The findings are quality improvements, not
security vulnerabilities. This workstream addresses all actionable items in **3
compact phases** (Y1–Y3) with **20 atomic sub-tasks**.

### Finding Validation Summary

| Severity | Raw Findings | Erroneous/No-Action | Actionable |
|----------|-------------|---------------------|------------|
| Critical | 0 | 0 | 0 |
| High | 0 | 0 | 0 |
| Medium | 2 | 0 | 2 |
| Low | 8 | 0 | 8 |
| Informational | 6 | 2 (INFO-02, INFO-05) | 4 |
| **Total** | **16** | **2** | **14** |

### Phase Overview

| Phase | Name | Sub-tasks | Priority | Gate | Status |
|-------|------|-----------|----------|------|--------|
| Y1 | Frozen State & Foundation Fixes | 7 | HIGH | `lake build` clean, freeze proofs compile, `test_smoke.sh` green | **COMPLETE** (v0.22.23) |
| Y2 | Platform, Data Structures & Proof Hardening | 7 | MEDIUM | Module builds pass, `test_smoke.sh` green | **COMPLETE** (v0.22.24, Y2-D+ v0.22.25) |
| Y3 | Test Infrastructure & Documentation | 6 | LOW | All test suites pass, `test_fast.sh` green, docs consistent | PLANNED |

**Dependencies**: Y1 is the critical path — MED-01 (frozen time-slice transfer)
touches frozen state structures, freeze proofs, and frozen operations. Y2 is
independent of Y1 and can proceed in parallel. Y3 depends on Y1-C for sub-task
Y3-F only (frozen ops test updates need the corrected field). All other Y3
sub-tasks are independent and can begin immediately.

### Audit Count Corrections

During finding validation, one count discrepancy was identified:
- **MED-02** (NegativeStateSuite.lean): Audit claimed 31 `.build` calls;
  actual count is **38**. Total across all 3 suites is **62** (not 55).
  The finding severity and recommendation are unaffected.

---

## 2. Non-Actionable Findings

The following findings were verified against the codebase and confirmed as
intentional design decisions that are already properly documented. **No code
changes required.**

### NA-1: INFO-02 — Non-standard BIBA integrity direction (by-design)

**Audit claim**: "Non-standard BIBA integrity direction (reversed) — thoroughly
documented, by-design" at `Policy.lean:75-79`.

**Verification**: The reversed BIBA direction is a deliberate design choice with
extensive documentation, witness theorems (`integrityFlowsTo_is_not_biba`), and
explicit `_insecure` markers. The information flow subsystem was audited in
WS-X Phase X3 where `integrityFlowsTo_prevents_escalation` was proven. This is
a sound architectural decision, not a finding requiring remediation.

### NA-2: INFO-05 — MMIO volatile register modeling gap (documented tech debt)

**Audit claim**: "Volatile device register modeling gap — honestly documented
with `MmioSafe` hypothesis guards" in `MmioAdapter.lean`.

**Verification**: The MMIO formalization gap was addressed in WS-X Phase X1
(X1-B: `MmioReadOutcome` inductive encoding) with `MmioSafe` hypothesis guards
on every MMIO operation. The gap is a genuine limitation of modeling volatile
hardware in a pure-functional framework, honestly documented with defensive
guards. Further closure requires hardware-specific testing, not model changes.

---

## 3. Phase Y1 — Frozen State & Foundation Fixes

**Priority**: HIGH
**Gate**: `lake build` clean, freeze proofs compile, `test_smoke.sh` green
**Findings addressed**: MED-01, LOW-01, LOW-02, LOW-03

This phase resolves the highest-impact findings: the frozen time-slice data loss
(MED-01), the public `AccessRightSet.mk` constructor (LOW-01), the O(n²) BFS
visited-set (LOW-02), and the fragile tuple projections (LOW-03). These are all
in the foundation/model layer and share no file dependencies with each other,
so sub-tasks within this phase can be parallelized.

### Y1-A: Transfer `configDefaultTimeSlice` to `FrozenSchedulerState` (MED-01)

**Finding**: `freezeScheduler` (`FrozenState.lean:315-323`) copies all
`SchedulerState` fields to `FrozenSchedulerState` except
`configDefaultTimeSlice`. The configured time-slice value is silently lost
during the builder→frozen transition. Frozen-phase operations (`frozenTimerTick`)
fall back to a hardcoded constant (`frozenDefaultTimeSlice := 5`) instead of
the platform-configured value.

**Root cause**: When `configDefaultTimeSlice` was added to `SchedulerState` in
V5-L, the corresponding `FrozenSchedulerState` structure and `freezeScheduler`
function were not updated.

**Fix**:
1. Add `configDefaultTimeSlice : Nat` field to `FrozenSchedulerState`
   (`FrozenState.lean:211`).
2. Transfer the value in `freezeScheduler`: add
   `configDefaultTimeSlice := sched.configDefaultTimeSlice` (`FrozenState.lean:323`).

**Files**: `SeLe4n/Model/FrozenState.lean`
**Scope**: ~4 lines changed (structure + function)

### Y1-B: Add `freeze_preserves_configDefaultTimeSlice` proof (MED-01 cont.)

**Finding**: The freeze correctness proofs (`FrozenState.lean:394-404`) include
preservation theorems for `current`, `activeDomain`, and `domainSchedule` but
not for `configDefaultTimeSlice`.

**Fix**: Add a preservation theorem proving the value round-trips through freeze:
```
theorem freeze_preserves_configDefaultTimeSlice (st : SystemState) :
    (freeze st).scheduler.configDefaultTimeSlice =
    st.scheduler.configDefaultTimeSlice
```

**Depends on**: Y1-A (field must exist before proof can reference it)
**Files**: `SeLe4n/Model/FrozenState.lean`
**Scope**: ~4 lines (theorem statement + proof by `rfl`)

### Y1-C: Update `frozenTimerTick` to use frozen config field (MED-01 cont.)

**Finding**: `frozenTimerTick` (`FrozenOps/Operations.lean:168`) uses a
hardcoded `frozenDefaultTimeSlice` constant (= 5) instead of the frozen
scheduler's `configDefaultTimeSlice` field.

**Fix**:
1. Update `frozenTimerTick` to read `fst.scheduler.configDefaultTimeSlice`
   instead of `frozenDefaultTimeSlice`.
2. Deprecate `frozenDefaultTimeSlice` constant with a documentation comment
   noting the field-based approach.
3. Update `FrozenOps/Commutativity.lean` if any commutativity proofs reference
   the constant.

**Depends on**: Y1-A (field must exist in `FrozenSchedulerState`)
**Files**: `SeLe4n/Kernel/FrozenOps/Operations.lean`,
`SeLe4n/Kernel/FrozenOps/Commutativity.lean` (if affected)
**Scope**: ~6 lines changed

### Y1-D: Make `AccessRightSet` constructor private (LOW-01)

**Finding**: `AccessRightSet.mk` raw constructor (`Model/Object/Types.lean:70`)
is public, allowing construction of values with `bits ≥ 32` that bypass the
`valid` predicate (`bits < 2^5`). The safe constructors `ofNat` (masked) and
`mk_checked` (proof-carrying) exist but are not enforced.

**Verification**: Grep confirmed **zero external uses** of `AccessRightSet.mk`
or raw `⟨n⟩` constructor syntax outside the definition file. All 205+ external
uses go through `ofList`, `empty`, `singleton`, or other safe constructors.

**Fix**: Change `structure AccessRightSet where` to use `private` on the `mk`
constructor. In Lean 4 this is achieved by defining the structure within a
`private` block or by adding a `private` annotation. If Lean 4.28.0 does not
support `private` structure constructors directly, an alternative is to add
a module-level comment documenting the invariant and add an `opaque` smart
constructor wrapper.

**Verification step**: `lake build SeLe4n.Model.Object.Types` must succeed
with zero breakage in downstream modules.

**Files**: `SeLe4n/Model/Object/Types.lean`
**Scope**: ~3 lines changed

### Y1-E: Optimize `descendantsOf` visited-set to HashSet (LOW-02)

**Finding**: `descendantsOf` BFS (`Object/Structures.lean:975-985`) uses
`List.Mem` (`c ∉ acc`) for visited-set checks, yielding O(n) per-check and
O(n²) total traversal cost. `CdtNodeId` already has `Hashable` and
`LawfulHashable` instances (WS-J1-F), and `Std.Data.HashSet` is already in
scope via `Prelude.lean` imports.

**Fix**:
1. Change the `go` helper's `acc` parameter from `List CdtNodeId` to use a
   `Std.Data.HashSet CdtNodeId` for the visited set, plus a separate
   `List CdtNodeId` for the result accumulator.
2. Replace `c ∉ acc` with `!visited.contains c`.
3. Update the 5 callers (2 in `Capability/Operations.lean`, 2 in
   `Capability/Invariant/Preservation.lean`, 1 in test comments).

**Proof impact**: ~23 supporting theorems (`descendantsOf_go_acc_subset`, etc.
at `Structures.lean:1958-2162`) will need updating from list-containment to
set-membership. The BFS correctness argument is structurally unchanged —
only the membership representation changes.

**Files**: `SeLe4n/Model/Object/Structures.lean`,
`SeLe4n/Kernel/Capability/Operations.lean`,
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean`
**Scope**: ~40–60 lines changed across definition + proofs

### Y1-F: Extract named accessors for `allTablesInvExtK` (LOW-03)

**Finding**: `allTablesInvExtK` decomposition in `Builder.lean` uses deeply
nested tuple projections (up to `.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1` — 14 levels
deep). Any field addition or reordering silently breaks all projection indices.

**Current state**: The codebase already provides named extraction theorems
(`allTablesInvExtK_services`, `allTablesInvExtK_objectTypes`, etc.) at
`Builder.lean:40-60` as a mitigation. The fragility concern is real but already
partially addressed through these named accessors.

**Fix**:
1. Verify that **all** call sites use the named extraction theorems rather than
   raw tuple projections.
2. If any raw projections exist outside `Builder.lean`, replace them with the
   named accessors.
3. Add a documentation comment on `allTablesInvExtK` warning against direct
   tuple projection and directing users to the named accessors.

**Files**: `SeLe4n/Model/Builder.lean` (primary), grep for raw `.2.2.2` usage
**Scope**: ~5–10 lines (documentation + any raw projection replacements)

### Y1-G: Verify and document `allTablesInvExtK` accessor completeness (LOW-03 cont.)

**Finding**: The named accessors must cover every conjunct of `allTablesInvExtK`
for the mitigation to be complete. If any table's `invExtK` is missing a named
accessor, callers would be forced to use raw projections.

**Fix**:
1. Enumerate all tables contributing to `allTablesInvExtK`.
2. Verify a named extraction theorem exists for each.
3. Add any missing named accessors.
4. Add a completeness comment listing all accessors.

**Depends on**: Y1-F
**Files**: `SeLe4n/Model/Builder.lean`
**Scope**: ~5–15 lines (any missing accessors + documentation)

---

## 4. Phase Y2 — Platform, Data Structures & Proof Hardening

**Priority**: MEDIUM
**Gate**: Module builds pass, `test_smoke.sh` green
**Findings addressed**: LOW-04, LOW-05, LOW-06, INFO-01, INFO-03, INFO-04, INFO-06

This phase addresses scheduler robustness (LOW-04), platform dead branching
(LOW-05), data structure fuel-exhaustion semantics (LOW-06), and four
informational proof/documentation gaps. All sub-tasks are independent of Phase
Y1 and independent of each other (different subsystems, no shared files).

### Y2-A: Document `switchDomain` fallback as unreachable (LOW-04)

**Finding**: `switchDomain` (`Operations/Core.lean:419`) has a fallback
`| none => .ok ((), st)` for `schedule[nextIdx]?` when `nextIdx` was computed
via modular arithmetic (`(idx + 1) % schedule.length`). The modular arithmetic
guarantees `0 ≤ nextIdx < schedule.length`, making the `none` branch
unreachable for non-empty schedules. However, the silent return of unchanged
state could mask corruption.

**Verification**: The `domainScheduleEntriesPositive` predicate (added in WS-X
X2-A as 9th conjunct of `schedulerInvariantBundleFull`) ensures schedule entries
are valid. Combined with the modular index computation, the `none` branch is
provably unreachable when the scheduler invariant holds.

**Fix**:
1. Add a documentation comment on the `| none =>` branch explaining why it is
   unreachable (modular arithmetic guarantee + `schedulerInvariantBundleFull`).
2. Add a `switchDomain_index_in_bounds` lemma proving
   `schedule[(idx + 1) % schedule.length]? = some _` when `schedule ≠ []`.
   This would formalize the argument without changing runtime behavior.

**Design decision**: We do NOT change the fallback to `panic!` or error — the
current behavior (return unchanged state) is the correct defensive choice for
a kernel. The fix is documentation + optional proof, not behavioral change.

**Files**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean`
**Scope**: ~8–12 lines (comment + optional lemma)

### Y2-B: Simplify `registerContextStableCheck` dead branching (LOW-05)

**Finding**: `registerContextStableCheck` (`RPi5/RuntimeContract.lean:86-96`)
has identical branches in `if oldTid == tid then regsMatchNewTcb else
regsMatchNewTcb`. Both the `then` and `else` branches return the same value.
The comments describe different semantic intentions (same-thread vs. context
switch) but the code is identical.

**Fix**:
1. Remove the `if oldTid == tid then ... else ...` conditional.
2. Return `regsMatchNewTcb` directly after the `some oldTid` match.
3. Add a comment explaining that register-context stability is checked
   uniformly regardless of whether a context switch occurred, because the
   `contextSwitchState` operation (X1-C) guarantees registers always match
   the current TCB's saved context.

**Files**: `SeLe4n/Platform/RPi5/RuntimeContract.lean`
**Scope**: ~6 lines changed (remove conditional + update comment)

### Y2-C: Document `insertLoop`/`backshiftLoop` fuel-exhaustion semantics (LOW-06)

**Finding**: `insertLoop` (`RobinHood/Core.lean:126`) returns `(slots, false)`
on fuel exhaustion, and `backshiftLoop` (`Core.lean:247`) returns `slots`
unchanged. Both silently abandon the operation without explicit error signaling.

**Verification**: The Robin Hood invariant suite proves that fuel exhaustion
cannot occur under the load-factor bound. Specifically:
- `insertLoop` is called with `fuel = capacity`, and the probe sequence is
  bounded by capacity when the load factor is below 1.0.
- `backshiftLoop` is called with `fuel = capacity`, and backshift terminates
  at the first empty slot (guaranteed to exist when load < 1.0).
- The `invExtK` bundle (WS-N) closes all precondition gaps.

**Fix**:
1. Add documentation comments on both fuel-exhaustion branches explaining:
   - Why fuel exhaustion cannot occur under the maintained invariants.
   - The `invExtK` preconditions that guarantee sufficient fuel.
   - The `false` return flag in `insertLoop` as the only signal of
     incomplete insertion.
2. Optionally, add `insertLoop_fuel_sufficient` and
   `backshiftLoop_fuel_sufficient` lemmas proving that the fuel parameter
   exceeds the maximum probe/backshift distance under `invExtK`.

**Design decision**: We do NOT change the fuel-exhaustion behavior. Returning
unchanged state is the correct defensive fallback for a kernel data structure.
The load-factor bound is the correct prevention mechanism.

**Files**: `SeLe4n/Kernel/RobinHood/Core.lean`
**Scope**: ~10–15 lines (documentation comments + optional lemmas)

### Y2-D: Replace `VSpaceRoot.beq_converse_limitation` placeholder (INFO-01)

**Finding**: `beq_converse_limitation` (`Object/Structures.lean:398-401`) uses
`True := trivial` as a documented limitation marker. The comment states that
VSpaceRoot equality is not used in any proof obligation and the converse proof
is deferred until `RHTable.LawfulBEq` is established.

**Verification**: The `LawfulBEq` instance for `RHTable` was established in
WS-V Phase V7 (`LawfulBEq` explicit API-level requirement for RHTable, 18-file
ripple). This means the prerequisite for the converse proof may now be
available.

**Fix**:
1. Check whether `RHTable.LawfulBEq` is now available for `VSpaceRoot`.
2. If available: replace `True := trivial` with the actual converse proof
   (`VSpaceRoot.BEq` reflects equality via the underlying `RHTable` fields).
3. If not yet available (the `VSpaceRoot.BEq` instance may use custom logic):
   document why the limitation persists and update the comment with current
   status.

**Files**: `SeLe4n/Model/Object/Structures.lean`
**Scope**: ~5–10 lines

### Y2-E: Unify remaining 5 enforcement wrappers into bridge (INFO-03)

**Finding**: `enforcementBridge_to_NonInterferenceStep` (`Soundness.lean:663-668`)
covers 6 of 11 checked wrappers. The remaining 5 (`endpointCallChecked`,
`endpointReplyChecked`, `endpointReplyRecvChecked`, `cspaceMintChecked`,
`notificationWaitChecked`) have individual soundness proofs via compound NI
constructors but are not unified into the bridge theorem.

**Fix**:
1. Extend `enforcementBridge_to_NonInterferenceStep` with 5 additional
   disjuncts covering the remaining checked wrappers.
2. Each new disjunct maps the wrapper's `securityFlowsTo` check to the
   corresponding compound NI constructor (`endpointCallHigh`,
   `endpointReplyRecvHigh`, `cspaceMint`, `notificationWait`,
   `syscallDispatchHigh`).
3. Update the coverage comment from "6 of 11" to "11 of 11".

**Proof strategy**: Each new case follows the same pattern as the existing 6:
unfold the checked wrapper, extract the `securityFlowsTo` hypothesis from the
`if` guard, and apply the corresponding NI constructor.

**Files**: `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean`
**Scope**: ~30–50 lines (5 new proof cases + updated documentation)

### Y2-F: Add VSpaceBackend integration status marker (INFO-04)

**Finding**: `VSpaceBackend.lean` is a 140-line forward declaration for the H3
ARMv8 backend. It defines a `VSpaceBackend` typeclass but is not yet
instantiated or imported by the kernel.

**Verification**: This is tracked tech debt for the Raspberry Pi 5 hardware
binding milestone. The module is correctly isolated and has no impact on the
current kernel.

**Fix**:
1. Add a module-level status comment at the top of `VSpaceBackend.lean`:
   `-- STATUS: H3 forward declaration — not yet integrated into kernel dispatch.`
   `-- MILESTONE: Raspberry Pi 5 hardware binding (post-v1.0).`
2. Add `VSpaceBackend` to the forward-declaration inventory in
   `docs/DEVELOPMENT.md` (if not already present).

**Files**: `SeLe4n/Kernel/Architecture/VSpaceBackend.lean`, `docs/DEVELOPMENT.md`
**Scope**: ~4 lines

### Y2-G: Document `collectQueueMembers` fuel sufficiency gap (INFO-06)

**Finding**: `collectQueueMembers` fuel sufficiency
(`CrossSubsystem.lean:80-85`) is not formally connected to
`tcbQueueChainAcyclic`. The existing theorem
`collectQueueMembers_fuel_sufficiency_documented` only covers the `none` start
case. The operational connection relies on an informal argument about acyclicity
guaranteeing unique visits.

**Verification**: The comment at `CrossSubsystem.lean:75-85` already documents
this gap thoroughly, explaining why a formal proof requires non-trivial
infrastructure (connecting `QueueNextPath` inductive to `queueNext` field
traversal).

**Fix**:
1. Verify the existing documentation is current and accurate.
2. Add a `-- TPI-DOC: fuel-sufficiency formal connection deferred` annotation
   for tracking.
3. Optionally, add a `collectQueueMembers_fuel_bound` lemma proving the
   weaker property that the result list length is bounded by `fuel`, which
   holds trivially by structural recursion and supports the informal argument.

**Files**: `SeLe4n/Kernel/CrossSubsystem.lean`
**Scope**: ~5–10 lines (annotation + optional lemma)

---

## 5. Phase Y3 — Test Infrastructure & Documentation

**Priority**: LOW
**Gate**: All test suites pass, `test_fast.sh` green, docs consistent
**Findings addressed**: MED-02, LOW-07, LOW-08

This phase addresses test infrastructure quality: migrating unchecked state
builders (MED-02), replacing a duplicate probe operation (LOW-07), and
documenting the threadState sync design (LOW-08). These changes are confined
to test files and do not affect production Lean code or proofs.

### Y3-A: Migrate `InformationFlowSuite.lean` to `.buildChecked` (MED-02, part 1)

**Finding**: 15 calls to `.build` (unchecked) in `InformationFlowSuite.lean`
bypass all 8 structural validation checks. Zero calls to `.buildChecked` exist
in this file.

**Verification**: Both `.build` and `.buildChecked` have identical type
signatures (`BootstrapBuilder → SystemState`). Migration is a mechanical
find-replace with no signature changes required. All test functions are already
in `IO` context, and `.buildChecked` is a pure function (panics on validation
failure rather than returning `Except`).

**Fix**:
1. Replace all 15 `.build` calls with `.buildChecked`.
2. Run the test suite to verify no tests panic (which would indicate the test
   was relying on a structurally invalid state).
3. For any test that panics: the test was using a malformed state. Decide
   whether to fix the state (if the malformation was unintentional) or keep
   `.build` with an explicit comment (if the malformation is deliberately
   testing error paths).

**Files**: `tests/InformationFlowSuite.lean`
**Scope**: 15 line changes (mechanical replacement)

### Y3-B: Migrate `NegativeStateSuite.lean` to `.buildChecked` (MED-02, part 2)

**Finding**: 38 calls to `.build` (unchecked) vs. 3 calls to `.buildChecked`
in `NegativeStateSuite.lean`. The audit claimed 31; actual count is 38.

**Important nuance**: `NegativeStateSuite` deliberately constructs invalid
states to test error paths. Many `.build` calls may intentionally violate
invariants. Each call requires individual review to determine:
- **Migrate to `.buildChecked`**: state should be structurally valid (the test
  is checking kernel error handling, not builder validation).
- **Keep `.build` with comment**: state is deliberately malformed (the test
  needs a specific invariant violation that `.buildChecked` would reject).

**Fix**:
1. Review each of the 38 `.build` calls individually.
2. For each call, determine if the constructed state would pass
   `.buildValidated`'s 8 checks.
3. Migrate valid states to `.buildChecked`.
4. For intentionally invalid states, add a per-call comment:
   `-- Uses .build intentionally: [reason for invariant violation]`
5. Run the full negative-state test suite after migration.

**Files**: `tests/NegativeStateSuite.lean`
**Scope**: 38 calls reviewed; estimate ~20 migrations + ~18 annotated retentions

### Y3-C: Migrate `OperationChainSuite.lean` to `.buildChecked` (MED-02, part 3)

**Finding**: 9 calls to `.build` (unchecked) vs. 23 calls to `.buildChecked`
in `OperationChainSuite.lean`. This suite already has a strong checked-to-
unchecked ratio (2.5:1).

**Fix**:
1. Review each of the 9 `.build` calls.
2. Migrate all valid states to `.buildChecked`.
3. Annotate any intentional retentions.
4. Run the operation-chain test suite after migration.

**Files**: `tests/OperationChainSuite.lean`
**Scope**: 9 calls reviewed; estimate ~7 migrations + ~2 annotated retentions

### Y3-D: Replace duplicate `awaitReceive` probe operation (LOW-07)

**Finding**: `awaitReceive` and `receive` in `TraceSequenceProbe.lean:180-189`
are functionally identical — both call `endpointReceiveDual` with the same
arguments. The only difference is in `classifyError` tag. The probe claims 7
distinct operations but exercises only 6.

**Fix**:
1. Replace the `awaitReceive` variant with a semantically distinct operation.
   **Recommended replacement**: `endpointCall` (synchronous call with reply),
   which exercises the reply-based IPC pattern not currently covered by any
   probe operation.
2. Update the `ProbeOp` inductive to rename `awaitReceive` to `call` (or
   similar).
3. Implement the `call` case in the probe dispatch using
   `SeLe4n.Kernel.endpointCallDual`.
4. Update the `classifyError` cases for the new operation.
5. Update any documentation referencing probe operation count.

**Alternative**: If `endpointCallDual` requires setup that the probe's
randomized state cannot guarantee (e.g., a reply capability), a simpler
alternative is `cspaceCopy` (capability copy), which tests a different
subsystem entirely.

**Files**: `tests/TraceSequenceProbe.lean`
**Scope**: ~15–20 lines changed

### Y3-E: Document `assertStateInvariantsFor` threadState sync design (LOW-08)

**Finding**: `assertStateInvariantsFor` (`InvariantChecks.lean:98-101`) calls
`syncThreadStates` before checking invariants, meaning it validates inference
self-consistency rather than detecting operational drift between `threadState`
fields and runtime queue membership.

**Verification**: The design comment at lines 94-101 already documents this
behavior as intentional: "The check is intentionally a design-consistency
assertion, not a divergence detector." The documentation is thorough and
accurate.

**Fix**:
1. Verify the existing V8-G7 documentation comment is current.
2. Add a brief annotation to the `assertStateInvariantsFor` docstring:
   `-- NOTE: Validates inference self-consistency (idempotency of syncThreadStates),`
   `-- not operational drift. See V8-G7 design note.`
3. Optionally, add a companion function `assertStateInvariantsWithoutSync` that
   checks invariants WITHOUT calling `syncThreadStates` first, enabling drift
   detection when needed.

**Files**: `SeLe4n/Testing/InvariantChecks.lean`
**Scope**: ~5–10 lines (documentation + optional companion function)

### Y3-F: Update test fixture and documentation for MED-01 changes (cross-phase)

**Finding**: The frozen time-slice fix (Y1-A/B/C) may affect test expectations
in `FrozenOpsSuite.lean` and `TwoPhaseArchSuite.lean` where `frozenTimerTick`
tests expect the hardcoded value 5.

**Depends on**: Y1-C (frozen ops changes must land first)
**Fix**:
1. Update `FrozenOpsSuite.lean` test `fo006_timerTickIdle` if it checks the
   reset time-slice value.
2. Update `TwoPhaseArchSuite.lean` comments at lines 269-272 that reference
   "frozenDefaultTimeSlice (5)" to reference the configurable field.
3. Verify `main_trace_smoke.expected` fixture is unaffected (frozen ops are
   not part of the main trace).
4. Update `CHANGELOG.md` with the MED-01 fix entry.

**Files**: `tests/FrozenOpsSuite.lean`, `tests/TwoPhaseArchSuite.lean`,
`CHANGELOG.md`
**Scope**: ~10 lines changed

---

## 6. Dependency Graph

```
Y1-A ──► Y1-B (proof needs field)
  │
  └────► Y1-C (ops needs field) ──► Y3-F (test update)

Y1-D (independent)
Y1-E (independent)
Y1-F ──► Y1-G (completeness check)

Y2-A through Y2-G (all independent of Y1 and each other)

Y3-A, Y3-B, Y3-C (independent of each other, depend on Y1-A for frozen state)
Y3-D (independent)
Y3-E (independent)
Y3-F (depends on Y1-C)
```

**Parallelism opportunities**:
- Y1-D, Y1-E, Y1-F can execute in parallel with Y1-A/B/C
- All Y2 sub-tasks can execute in parallel with all Y1 sub-tasks
- Y3-A/B/C/D/E can begin before Y1 completes (only Y3-F requires Y1-C)

---

## 7. Scope Summary

| Phase | Sub-tasks | Estimated Lines Changed | Files Touched |
|-------|-----------|------------------------|---------------|
| Y1 | 7 | ~70–100 | 6 Lean files |
| Y2 | 7 | ~70–110 | 7 Lean files + 1 doc |
| Y3 | 6 | ~90–120 | 6 test/doc files |
| **Total** | **20** | **~230–330** | **~17 files** |

### Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Y1-E proof ripple (descendantsOf HashSet) | Medium | Medium | 23 theorems need updating; BFS correctness unchanged. Break into sub-PRs if needed. |
| Y2-E bridge extension (5 NI cases) | Low | Low | Each case follows established pattern; individual proofs already exist. |
| Y3-B negative test review | Low | Medium | Manual review of 38 calls; some may intentionally need `.build`. Budget time for judgment calls. |
| Y1-D AccessRightSet privacy | Low | Low | Zero external `.mk` uses confirmed. Risk is Lean 4 syntax limitation. |

---

## 8. Validation Plan

### Per-Phase Gates

| Phase | Required Validation | Command |
|-------|-------------------|---------|
| Y1 | All modified modules build | `source ~/.elan/env && lake build SeLe4n.Model.FrozenState && lake build SeLe4n.Kernel.FrozenOps.Operations && lake build SeLe4n.Model.Object.Types && lake build SeLe4n.Model.Object.Structures && lake build SeLe4n.Model.Builder` |
| Y1 | Smoke tests pass | `./scripts/test_smoke.sh` |
| Y2 | All modified modules build | `source ~/.elan/env && lake build SeLe4n.Kernel.Scheduler.Operations.Core && lake build SeLe4n.Platform.RPi5.RuntimeContract && lake build SeLe4n.Kernel.RobinHood.Core && lake build SeLe4n.Kernel.InformationFlow.Enforcement.Soundness` |
| Y2 | Smoke tests pass | `./scripts/test_smoke.sh` |
| Y3 | All test suites pass | `./scripts/test_full.sh` |
| Y3 | Documentation consistent | Manual review of `CHANGELOG.md`, `docs/DEVELOPMENT.md` |

### Final Gate (all phases)

```bash
./scripts/test_full.sh          # Tier 0-3: full invariant surface
grep -r "sorry" SeLe4n/ --include="*.lean" | grep -v "-- " | wc -l  # Must be 0
grep -r "axiom" SeLe4n/ --include="*.lean" | grep -v "-- " | wc -l  # Must be 0
```

---

## 9. File Impact Matrix

| File | Sub-tasks | Change Type |
|------|-----------|-------------|
| `SeLe4n/Model/FrozenState.lean` | Y1-A, Y1-B | Structure + function + proof |
| `SeLe4n/Kernel/FrozenOps/Operations.lean` | Y1-C | Runtime logic |
| `SeLe4n/Model/Object/Types.lean` | Y1-D | Access control |
| `SeLe4n/Model/Object/Structures.lean` | Y1-E, Y2-D | Algorithm + proof |
| `SeLe4n/Model/Builder.lean` | Y1-F, Y1-G | Documentation + completeness |
| `SeLe4n/Kernel/Capability/Operations.lean` | Y1-E | Caller update |
| `SeLe4n/Kernel/Capability/Invariant/Preservation.lean` | Y1-E | Proof update |
| `SeLe4n/Kernel/Scheduler/Operations/Core.lean` | Y2-A | Documentation + optional proof |
| `SeLe4n/Platform/RPi5/RuntimeContract.lean` | Y2-B | Simplification |
| `SeLe4n/Kernel/RobinHood/Core.lean` | Y2-C | Documentation |
| `SeLe4n/Kernel/InformationFlow/Enforcement/Soundness.lean` | Y2-E | Proof extension |
| `SeLe4n/Kernel/Architecture/VSpaceBackend.lean` | Y2-F | Documentation |
| `SeLe4n/Kernel/CrossSubsystem.lean` | Y2-G | Documentation + optional proof |
| `tests/InformationFlowSuite.lean` | Y3-A | Builder migration |
| `tests/NegativeStateSuite.lean` | Y3-B | Builder migration + annotation |
| `tests/OperationChainSuite.lean` | Y3-C | Builder migration |
| `tests/TraceSequenceProbe.lean` | Y3-D | Operation replacement |
| `SeLe4n/Testing/InvariantChecks.lean` | Y3-E | Documentation |
| `tests/FrozenOpsSuite.lean` | Y3-F | Test update |
| `tests/TwoPhaseArchSuite.lean` | Y3-F | Comment update |
| `CHANGELOG.md` | Y3-F | Entry addition |

---

*Plan created by Claude (Opus 4.6) on 2026-03-30*
*Baseline: `docs/audits/AUDIT_COMPREHENSIVE_v0.22.22_FULL_KERNEL_RUST.md`*
*All 16 findings validated against source code; 14 actionable, 2 non-actionable*
