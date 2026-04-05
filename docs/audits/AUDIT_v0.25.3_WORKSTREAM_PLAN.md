# WS-AC Workstream Plan — Comprehensive Audit Remediation (v0.25.3)

**Created**: 2026-04-05
**Baseline version**: 0.25.3
**Baseline audit**: `docs/audits/AUDIT_v0.25.3_COMPREHENSIVE.md`
**Prior portfolios**: WS-B through WS-AB (all COMPLETE — see `docs/WORKSTREAM_HISTORY.md`)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Executive Summary

A comprehensive security and correctness audit of seLe4n v0.25.3 was conducted
on 2026-04-05, covering all Lean modules (~94K lines), Rust ABI crates (~31
files), and CI/test infrastructure. The audit found **zero Critical**, **3 High**,
**9 Medium**, **14 Low**, and **20+ Info** findings. Zero `sorry`, zero `axiom`,
and zero `unsafe` Rust beyond the single ARM64 `svc #0` instruction.

### 1.1 Audit Verification Results

Every finding was independently verified against the codebase before inclusion
in this plan. The verification discovered:

- **16 discrepancies** in the audit's severity summary table (section 14) versus
  the detailed body text (sections 1–12). The table contains phantom findings
  (S-07, I-06), wrong descriptions (S-04–S-06, I-04–I-05, C-01–C-02, A-02–A-03,
  IF-01, IF-02), and a severity escalation (I-02: Medium→High). **This plan uses
  the detailed body text as the authoritative source**, not the corrupted table.
- **A-01** (`vspaceMapPage` accessibility): **Reclassified as INFO** — the `def`
  visibility is intentional for proof decomposition; production paths correctly
  use `*WithFlush` variants; thorough documentation exists.
- **X-05** (field-disjointness): **Reclassified as LOW** — field-disjointness
  facts ARE machine-checked via `decide` theorems; only the architectural
  rationale is prose.
- **All other findings**: Confirmed as accurate with correct line numbers and
  behavioral descriptions.

### 1.2 Verified Finding Counts

| Severity | Body Text Count | After Verification | Actionable |
|----------|----------------|--------------------|------------|
| Critical | 0 | 0 | 0 |
| High | 3 | 3 | 3 |
| Medium | 9 | 9 (A-01→Info, I-02 stays Medium) | 9 |
| Low | 14 | 14 (X-05→Low, I-02→Medium) | 9 |
| Info | 20+ | 22+ | 0 (monitoring only) |

### 1.3 Actionable HIGH Findings

1. **S-01** — `hasSufficientBudget` fails open on missing SchedContext (defense-
   in-depth violation; single-line fix with proof update)
2. **I-01** — `notificationSignal` pending-message overwrite lacks formal
   invariant (structural argument exists but unproven; needs invariant theorem)
3. **C-01** — `cspaceMint` does not record CDT edges (documented design; needs
   API deprecation or removal of untracked path)

### 1.4 Plan Structure

This plan organizes all actionable findings into **6 phases** (AC1–AC6) with
**42 atomic sub-tasks**, explicit dependencies, gate conditions, and scope
estimates. Phases are ordered by security impact and dependency chain:

| Phase | Focus | Sub-tasks | Gate |
|-------|-------|-----------|------|
| AC1 | High-severity fixes | 9 | `lake build` + `test_smoke.sh` |
| AC2 | Scheduler & SchedContext hardening | 7 | `lake build` + `test_smoke.sh` |
| AC3 | IPC atomicity & invariant strengthening | 6 | `lake build` + `test_smoke.sh` |
| AC4 | Architecture & platform tightening | 5 | `lake build` + `test_smoke.sh` |
| AC5 | Cross-cutting & infrastructure | 8 | `lake build` + `test_full.sh` |
| AC6 | Documentation, testing & closure | 7 | `test_full.sh` + doc sync |

**Estimated scope**: ~620–1,035 total lines of changes (Lean code, proofs,
tests, documentation, and scripts). See section 11 for detailed breakdown.

---

## 2. Consolidated Finding Registry

### 2.1 HIGH Findings (3)

| ID | Subsystem | Description | Verified |
|----|-----------|-------------|----------|
| S-01 | Scheduler | `hasSufficientBudget` returns `true` when bound thread's SchedContext not found — fails open instead of fail-closed | YES — Selection.lean:289 returns `true` on `| _ =>` match arm |
| I-01 | IPC | `notificationSignal` overwrites waiter `pendingMessage` without formal `pendingMessage = none` invariant for waiting threads | YES — Endpoint.lean:334 unconditionally overwrites; `waitingThreadsPendingMessageNone` invariant exists in Defs.lean:267 but is not proven preserved by `notificationSignal` |
| C-01 | Capability | `cspaceMint` does not record CDT edges — minted capabilities are irrevocable via CDT walk; `cspaceMintWithCdt` exists as tracked alternative | YES — Operations.lean:541–551 (untracked); Operations.lean:785–794 (tracked); API.lean:66 documents the distinction |

### 2.2 MEDIUM Findings (9 — after A-01 reclassification, I-02 retained as Medium)

| ID | Subsystem | Description | Verified |
|----|-----------|-------------|----------|
| S-02 | Scheduler | `timeoutBlockedThreads` uses `st.objects.fold` — O(n) scan of full object store on budget exhaustion | YES — Core.lean:489 folds over all objects |
| S-03 | Scheduler | `blockingChain` fuel-based termination silently truncates on cycle rather than erroring | YES — BlockingGraph.lean:58–68; returns `[]` at fuel 0 |
| F-01 | Foundation | All identifier types (`ObjId`, `ThreadId`, etc.) wrap unbounded `Nat`; constructors bypass `isWord64` bounds | YES — Prelude.lean:30–42; `ofNat` performs no validation |
| F-02 | Foundation | `AccessRightSet.mk` raw constructor accessible despite `INTERNAL` convention; `⟨999⟩` bypasses 5-bit `valid` predicate | YES — Types.lean:76; `INTERNAL` comment is not enforced |
| F-03 | Foundation | `storeObject` always returns `.ok` with no capacity check; enforcement deferred to `retypeFromUntyped` | YES — State.lean:457–482 returns `.ok` unconditionally |
| IF-01 | InfoFlow | Enforcement boundary (11 policy-gated ops) is manual enumeration; no mechanical completeness witness across all `SyscallId` variants | YES — Wrappers.lean:186–225 is a `List EnforcementClass` runtime value, not a compile-time exhaustiveness proof |
| API-01 | API | `resolveExtraCaps` silently drops capabilities that fail to resolve; receiver cannot distinguish dropped caps from never-sent | YES — API.lean:411–417 uses `| .error _ => acc`; seL4-compatible behavior |
| SC-01 | SchedContext | CBS budget exhaustion triggers full object store scan via `timeoutBlockedThreads` (cross-ref S-02) | YES — duplicate root cause with S-02; shared remediation |
| I-02 | IPC | `donateSchedContext` performs 3 sequential `storeObject` calls; partial state on intermediate failure (I-03 subsumed) | YES — Endpoint.lean:170–194; callers discard error states but pattern is fragile |

### 2.3 LOW Findings — Actionable Subset (9)

| ID | Subsystem | Description | Verified |
|----|-----------|-------------|----------|
| S-04 | Scheduler | `defaultTimeSlice` hardcoded to 5; `configDefaultTimeSlice` field available but unused | YES — Core.lean:344 vs State.lean:102 |
| S-05 | Scheduler | `switchDomain` reads scheduler state from `st` but returns `stSaved` — fragile dual-state pattern | YES — Core.lean:740 reads `st`; line 753 returns `stSaved` |
| S-06 | Scheduler | RunQueue `insert`/`remove`/`rotateToBack` are O(n) on `flat` list | YES — RunQueue.lean; documented but not optimized |
| F-04 | Foundation | `KernelError` has 44 variants — catch-all `| _ =>` risk in matches | YES — State.lean:20–65; no catch-alls found but risk exists for future code |
| I-04 | IPC | `Badge.bor` uses unbounded Lean `Nat` for intermediate bitwise OR; `ofNatMasked` applies 64-bit mask on result | YES — Prelude.lean:489; intermediate is unbounded; result is masked |
| A-04 | VSpace | `physicalAddressBound` defaults to 2^52 (ARM64 LPA max); RPi5 BCM2712 uses 44-bit PA; gap in [2^44, 2^52) | YES — VSpace.lean:53 default; Board.lean:122 RPi5 config; platform-aware variant exists |
| X-05 | Cross-cutting | CrossSubsystem field-disjointness: facts are machine-checked via `decide` but architectural rationale is prose | PARTIALLY — `fieldsDisjoint` theorems use `by decide` (CrossSubsystem.lean:413–472); prose argument is supplementary |
| X-08 | Cross-cutting | GitBook-canonical doc drift risk; automated sync exists but hash comparison absent | YES — `test_docs_sync.sh` exists; manifest-driven; no content-hash check |
| T-03 | Testing | No dedicated test suites for `RegisterDecode.lean`/`SyscallArgDecode.lean`; coverage dispersed in NegativeStateSuite | PARTIALLY — tests exist in NegativeStateSuite.lean:1857–2230 but are not standalone |

### 2.4 Findings Excluded from Remediation

The following findings require no code changes (Info-level, positive findings,
already-mitigated, or reclassified):

| ID | Reason for Exclusion |
|----|---------------------|
| A-01 | **Reclassified INFO**: `vspaceMapPage` visibility is intentional for proof decomposition; `*WithFlush` variants enforce safety; thoroughly documented |
| F-05 | **Info**: `Memory` total type is documented with migration path via `RuntimeBoundaryContract` |
| F-06 | **Info**: `MachineConfig.wellFormed` as `Bool` is minor; only used at boot |
| F-07 | **Info**: Nat-based ID aliasing mitigated by pattern-match discipline and typed IDs |
| I-03 | **Subsumed by I-02**: Same atomicity pattern; shared remediation via I-02 documentation |
| I-05 | **Info**: Per-notification duplicate check is correct by design (exclusive `ipcState`) |
| IF-02 | **Info**: `LabelingContext` as TCB is documented; no code change needed |
| A-02 | **Info (positive)**: W^X enforcement correctly modeled |
| A-03 | **Info**: Full TLB flush is correct for single-core; optimization deferred to multi-core |
| SC-02 | **Info**: `processReplenishmentsDue` 3-way check is defensive and well-documented |
| SC-03 | **Info (positive)**: `setPriorityOp` MCP validation with non-escalation proof present |
| API-02 | **Info**: `syscallRequiredRight` synchronization enforced by conformance tests |
| API-03 | **Info**: `dispatchCapabilityOnly` control flow is unusual but correct |
| T-01, T-02 | **Info**: Runtime checks appropriate for test suites; strict bash mode is positive |
| R-01–R-05 | **Info (positive)**: Rust ABI is well-engineered; no changes needed |
| X-01 | **Info (revised)**: Fuel-bounded recursion IS tested at scale in NegativeStateSuite; formal connection deferred (TPI-DOC) |
| X-02–X-04, X-06, X-07 | **Info (positive)**: Confirmed strong properties; no action needed |
| S-07, I-06, etc. | **Phantom findings**: Exist only in corrupted severity table; no corresponding body text |

### 2.5 Audit Table Errata

The severity summary table in section 14 of the audit document contains **16
discrepancies** relative to the detailed findings in sections 1–12. These are
catalogued here for traceability:

| Table Row | Table Description | Actual Body Finding | Discrepancy Type |
|-----------|-------------------|---------------------|-----------------|
| I-02 | Severity "High" | Body text: "Medium" (line 167) | Severity escalation |
| S-03 | "fuel default may undercount" | Body: "fuel-based termination, not structural" | Description drift |
| S-04 | "`switchDomain` wrapping arithmetic unchecked" | Body: "`defaultTimeSlice` hardcoded despite configurable field" | Wrong finding |
| S-05 | "RunQueue duplicate insert behavior undocumented" | Body: "`switchDomain` reads from `st` but saves to `stSaved`" | Wrong finding |
| S-06 | "`inferThreadState` is best-effort heuristic" | Body: "RunQueue `flat` list operations are O(n)" | Wrong finding |
| S-07 | "EDF tie-breaking determinism relies on fold order" | Body: S-07 = "Positive findings" header | Phantom finding |
| I-04 | "Dual-queue `sendToEndpoint` head-insert bias" | Body: "Notification badge OR uses unbounded Nat" | Wrong finding |
| I-05 | "`callEndpoint` has 5-step state threading" | Body: "`notificationWait` duplicate check is per-notification" | Wrong finding |
| I-06 | "SchedContext donation wrappers have shallow proofs" | Body: I-06 = "Positive findings" header | Phantom finding |
| C-01 | "`resolveCapAddress` guard shift unchecked" + Low | Body: "`cspaceMint` no CDT edges" + High | Wrong finding + wrong severity |
| C-02 | "`rightsSubset` manual 5-field check" + Low | Body: "bidirectionally proven" (positive) | Positive→negative |
| A-02 | "TLB flush model abstract" | Body: "W^X enforcement correctly modeled" (positive) | Positive→negative |
| A-03 | "W^X enforcement at map time only" | Body: "TLB flush always full" | Wrong finding |
| IF-01 | "`securityFlowsTo` reflexivity/transitivity not proven" | Body: "enforcement boundary completeness not mechanically verified" | Wrong finding |
| IF-02 | "11 policy-gated wrappers with sufficiency proofs" + Info | Body: "`securityFlowsTo` is pure function check" + Low | Wrong finding + wrong severity |
| SC-01 | "`consumeBudget` underflow saturation at zero" | Body: "CBS budget exhaustion triggers full object store scan (same as S-02)" | Wrong finding |

**Recommendation**: A corrected severity table should be appended to the audit
document as an addendum after this workstream completes.

---

## 3. Phase AC1 — High-Severity Fixes

**Goal**: Resolve all 3 HIGH findings with minimal blast radius.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh` pass.
**Dependencies**: None (first phase).

### AC1-A: Change `hasSufficientBudget` to fail-closed (S-01)

**Finding**: `hasSufficientBudget` (Selection.lean:289) returns `true` when a
bound thread's SchedContext is not found in the object store. Under the
`schedContextStoreConsistent` invariant this path is unreachable, but fail-open
violates defense-in-depth.

**Change**:
1. In `SeLe4n/Kernel/Scheduler/Operations/Selection.lean:289`, change
   `| _ => true` to `| _ => false`.
2. Add a one-line comment: "Fail-closed: missing SchedContext → insufficient
   budget (defense-in-depth; unreachable under schedContextStoreConsistent)."

**Proof impact**: The `hasSufficientBudget` result feeds into `isBetterCandidate`
and `chooseBestInBucket`. Any preservation theorem that assumes
`hasSufficientBudget = true` for a candidate thread is unaffected because the
`schedContextStoreConsistent` invariant guarantees the `| _ =>` arm is never
taken. Verify by building `SeLe4n.Kernel.Scheduler.Operations.Selection` and
`SeLe4n.Kernel.Scheduler.Operations.Preservation`.

**Files modified**: `Selection.lean` (1 line).
**Estimated effort**: Minimal — single-line semantic change + proof verification.
**Build verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Selection`
and `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation`.

### AC1-B: Formalize `notificationWaiterPendingMessageNone` preservation (I-01)

**Finding**: `notificationSignal` (Endpoint.lean:334) unconditionally overwrites
a waiter's `pendingMessage`. The safety depends on `waitingThreadsPendingMessageNone`
(Defs.lean:267–290), which states threads blocked on receive or notification
have `pendingMessage = none`. However, the preservation of this invariant by
`notificationSignal` itself is not formally proven.

**Change**:
1. In `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean`, add a new
   theorem `notificationSignal_preserves_waitingThreadsPendingMessageNone` that
   proves the invariant is maintained after `notificationSignal` executes.
2. The proof structure:
   - **Pre-condition**: `waitingThreadsPendingMessageNone st` holds.
   - **Case 1** (no waiters — badge OR path): No thread's `pendingMessage` is
     modified; the badge OR updates the notification object only. Invariant
     trivially preserved.
   - **Case 2** (waiter exists — wake path): The woken thread transitions from
     `blockedOnNotification` to `ready` with `pendingMessage := some badgeMsg`.
     Since it is no longer in a blocking state, the `waitingThreadsPendingMessageNone`
     predicate no longer applies to it. All other threads are unchanged.
3. Wire the new theorem into the existing `notificationSignal_preserves_*`
   theorem family in `NotificationPreservation.lean`.

**Files modified**: `NotificationPreservation.lean` (~40–80 lines).
**Build verification**: `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`.

### AC1-C: Formalize `notificationSignal` pending-message precondition (I-01 supplement)

**Finding**: The argument that waiting threads have `pendingMessage = none` at
the point `notificationSignal` reads them relies on entry-path analysis (the
only way to enter `blockedOnNotification` is via `notificationWait`, which sets
`pendingMessage := none`). This should be an explicit precondition lemma.

**Change**:
1. In `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation.lean`, add a lemma
   `notificationWait_sets_pendingMessage_none` proving that after
   `notificationWait` succeeds, the thread's `pendingMessage` field is `none`.
2. This lemma supports AC1-B by establishing the base case of the invariant.

**Files modified**: `NotificationPreservation.lean` (~20–40 lines).
**Build verification**: `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`.

### AC1-D: Address `cspaceMint` CDT-tracking gap (C-01)

**Finding**: `cspaceMint` (Operations.lean:541–551) creates capabilities without
CDT edge recording. `cspaceMintWithCdt` (Operations.lean:785–794) is the
tracked alternative. The `syscallEntry` dispatch wires through the checked
path, but the untracked `cspaceMint` remains in the public API.

**Change** (option analysis — choose one):

**Option 1 (Conservative — Document and gate)**: Add a prominent doc-comment to
`cspaceMint` warning that it produces irrevocable capabilities. Add an
`@[deprecated]` attribute (if supported by current Lean 4.28.0) directing
callers to `cspaceMintWithCdt`. No semantic change.

**Option 2 (Moderate — Rename to signal intent)**: Rename `cspaceMint` to
`cspaceMintUntracked` to make the lack of CDT tracking visible at every call
site. Update all internal callers (primarily `cspaceMintWithCdt` which
delegates to it). Add a `@[inline]` to preserve codegen.

**Option 3 (Aggressive — Unify)**: Make `cspaceMint` always record CDT edges
by inlining the CDT logic. Remove `cspaceMintWithCdt` as a separate function.
This eliminates the gap but changes `cspaceMint` semantics and requires updating
all callers and proofs that depend on `cspaceMint` NOT modifying the CDT.

**Recommended**: Option 2. It makes the design decision visible without breaking
existing proofs. Option 3 has the highest blast radius and should be deferred
to a dedicated CDT workstream.

**Files modified**: `Operations.lean` (~10 lines rename), `API.lean` (~5 lines),
`Wrappers.lean` (~5 lines), any callers of `cspaceMint`.
**Build verification**: `lake build SeLe4n.Kernel.Capability.Operations` and
`lake build SeLe4n.Kernel.API`.

### AC1-E: Update preservation proofs for fail-closed `hasSufficientBudget` (S-01 proof chain)

**Finding**: After AC1-A changes the fallback from `true` to `false`, any
theorem that pattern-matches on `hasSufficientBudget` output needs verification.
The key theorems are in `Preservation.lean` (2170 lines).

**Change**:
1. Build `SeLe4n.Kernel.Scheduler.Operations.Preservation` after AC1-A.
2. If any theorem breaks, the fix is straightforward: the `| _ =>` arm now
   returns `false` instead of `true`, but the `schedContextStoreConsistent`
   invariant ensures the arm is unreachable, so proofs should not break.
3. If a proof previously relied on the `true` fallback (defensive assumption),
   refactor it to use the invariant instead.

**Files modified**: `Preservation.lean` (0–50 lines, likely 0).
**Build verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation`.

### AC1-F: Verify cross-subsystem impact of S-01 change

**Change**:
1. Build `SeLe4n.Kernel.Scheduler.Liveness.WCRT` — the WCRT theorem depends on
   budget sufficiency predicates.
2. Build `SeLe4n.Kernel.PriorityInheritance.Preservation` — PIP frame lemmas
   reference scheduler state.
3. Build `SeLe4n.Kernel.CrossSubsystem` — cross-subsystem invariant composition.

**Files modified**: None expected (verification only).
**Build verification**: `lake build SeLe4n.Kernel.Scheduler.Liveness.WCRT` and
`lake build SeLe4n.Kernel.PriorityInheritance.Preservation` and
`lake build SeLe4n.Kernel.CrossSubsystem`.

### AC1-G: Add negative test for fail-closed `hasSufficientBudget` (S-01 test)

**Change**:
1. In `tests/NegativeStateSuite.lean`, add a test case that constructs a
   `SystemState` with a thread bound to a non-existent `SchedContextId` and
   verifies that `hasSufficientBudget` returns `false`.
2. This directly regression-tests the S-01 fix.

**Files modified**: `tests/NegativeStateSuite.lean` (~15–20 lines).
**Build verification**: `lake build tests.NegativeStateSuite` + `lake exe test_negative_state`.

### AC1-H: Add negative test for `cspaceMintUntracked` CDT absence (C-01 test)

**Change**:
1. In `tests/NegativeStateSuite.lean` (or `tests/OperationChainSuite.lean`),
   add a test that calls `cspaceMintUntracked` (post-rename) and verifies the
   CDT has no new edges, then calls `cspaceMintWithCdt` and verifies the CDT
   does have a new edge.
2. This documents and regression-tests the intended CDT behavior difference.

**Files modified**: Test suite (~20–30 lines).
**Build verification**: Build + run the relevant test executable.

### AC1-I: Smoke test gate

**Change**: Run `./scripts/test_smoke.sh` to validate all Tier 0–2 checks pass
after Phase AC1 changes.

**Phase AC1 total**: 9 sub-tasks, ~120–230 lines of changes.

---

## 4. Phase AC2 — Scheduler & SchedContext Hardening

**Goal**: Address S-02/SC-01 performance concern, S-03 fuel documentation,
S-04 configurable time slice, S-05 dual-state documentation, S-06 RunQueue
complexity documentation.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh` pass.
**Dependencies**: AC1 complete (S-01 change affects scheduler module).

### AC2-A: Document `timeoutBlockedThreads` O(n) cost and add index TODO (S-02/SC-01)

**Finding**: `timeoutBlockedThreads` (Core.lean:487–502) folds over the entire
object store to find threads bound to an exhausted SchedContext. With 64K
objects on RPi5, this is a worst-case latency spike.

**Change**:
1. Add a structured documentation comment to `timeoutBlockedThreads` in
   `Core.lean` quantifying the O(n) cost and noting it occurs only at budget
   exhaustion events (not per-tick).
2. Add a `-- TODO(WS-AD/perf): Replace with per-SchedContext bound-thread index`
   comment marking this as a known performance optimization target for the
   hardware benchmarking phase.
3. Document in `DEVELOPMENT.md` under "Known Performance Characteristics" that
   budget exhaustion timeout is O(n) in object count.

**Rationale for deferral**: The O(n) scan is correct and infrequent. Introducing
a secondary index (e.g., `HashMap SchedContextId (List ThreadId)`) requires
maintaining consistency across all bind/unbind/delete paths — a non-trivial
change better suited to a dedicated performance workstream with hardware
profiling data to validate the improvement.

**Files modified**: `Core.lean` (~5 lines comment), `docs/DEVELOPMENT.md` (~5 lines).
**Build verification**: No Lean changes; doc-only.

### AC2-B: Document `blockingChain` fuel-truncation behavior (S-03)

**Finding**: `blockingChain` (BlockingGraph.lean:58–68) uses fuel-based
termination. A cyclic blocking graph would cause silent truncation. The
`blockingAcyclic` invariant prevents this.

**Change**:
1. Add a structured comment to `blockingChain` documenting:
   - The fuel default (`objectIndex.length`) and its justification.
   - The behavior on fuel exhaustion (returns `[]` — silent truncation).
   - The invariant dependency (`blockingAcyclic` from CrossSubsystem ensures
     no cycles; therefore fuel is always sufficient).
   - The consequence if the invariant is violated: PIP propagation stops early,
     threads retain stale priority boosts.
2. Add a `#check` or `example` that exercises `blockingChain` with fuel = 0
   to document the truncation behavior in the proof record.

**Files modified**: `BlockingGraph.lean` (~10–15 lines comment).
**Build verification**: `lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.BlockingGraph`.

### AC2-C: Migrate `timerTick`/`timerTickBudget` to `configDefaultTimeSlice` (S-04)

**Finding**: `defaultTimeSlice` (Core.lean:344) is hardcoded to 5. The
configurable `configDefaultTimeSlice` (State.lean:102) exists but is unused.

**Change**:
1. In `Core.lean`, replace all uses of `defaultTimeSlice` with
   `st.scheduler.configDefaultTimeSlice` in `timerTick` and `timerTickBudget`.
2. Remove the standalone `def defaultTimeSlice : Nat := 5` constant (or keep
   it as a default value initializer for `configDefaultTimeSlice`).
3. Update preservation theorems in `Preservation.lean` that reference
   `defaultTimeSlice`. The proofs should be structurally identical since both
   values default to 5; the change is from a global constant to a state field.
4. Update `Liveness/TimerTick.lean` if any budget monotonicity theorem references
   the hardcoded value.

**Proof impact**: Medium. The theorems need to reference `st.scheduler.configDefaultTimeSlice`
instead of `defaultTimeSlice`. Since the default is 5, `native_decide` proofs
may need restructuring to reference the state field.

**Files modified**: `Core.lean` (~10 lines), `Preservation.lean` (~20–60 lines),
possibly `Liveness/TimerTick.lean` (~10–20 lines).
**Build verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Core` and
`lake build SeLe4n.Kernel.Scheduler.Operations.Preservation` and
`lake build SeLe4n.Kernel.Scheduler.Liveness.TimerTick`.

### AC2-D: Document `switchDomain` dual-state rationale (S-05)

**Finding**: `switchDomain` (Core.lean:719–753) reads scheduler state from `st`
but returns a state based on `stSaved` (after context save). The split is
correct because `saveOutgoingContext` only modifies `objects`, not `scheduler`,
but the pattern is fragile.

**Change**:
1. Add a structured invariant comment at the `switchDomain` function documenting:
   - Why reads come from `st`: scheduler fields are identical between `st` and
     `stSaved` because `saveOutgoingContext` only touches `objects`.
   - Why the result uses `stSaved`: the returned state must include the saved
     register context.
   - The implicit assumption: `saveOutgoingContext` does not modify `scheduler`.
2. Add a `theorem saveOutgoingContext_scheduler_eq` in `Preservation.lean` (if
   not already present) proving `(saveOutgoingContext st).scheduler = st.scheduler`.
   This mechanizes the implicit assumption.

**Files modified**: `Core.lean` (~8 lines comment), possibly `Preservation.lean`
(~15 lines theorem).
**Build verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`.

### AC2-E: Document RunQueue flat-list complexity (S-06)

**Finding**: RunQueue uses a `flat : List ThreadId` backing store. `insert`,
`remove`, and `rotateToBack` are all O(n) on this list.

**Change**:
1. Add a complexity section to the `RunQueue` structure docstring in
   `RunQueue.lean` documenting:
   - O(1): `contains` (via `RHSet` membership), `head?` (via bucket lookup)
   - O(n): `insert` (flat append), `remove` (flat filter), `rotateToBack` (flat erase+append)
   - Acceptable for n < 256 threads (RPi5 target)
   - Future optimization: replace `flat` with a doubly-linked list or array
     for O(1) operations when hardware profiling indicates it matters.

**Files modified**: `RunQueue.lean` (~10 lines comment).
**Build verification**: None (doc-only).

### AC2-F: Add `KernelError` catch-all lint documentation (F-04)

**Finding**: `KernelError` has 44 variants. Lean's exhaustiveness checker
prevents missing arms, but `| _ =>` catch-all patterns can mask specific errors.

**Change**:
1. Add a comment at the `KernelError` inductive definition (State.lean:20)
   warning against catch-all patterns: "Prefer explicit match arms over
   `| _ =>` to ensure new variants trigger compilation warnings at all handlers."
2. Add a coding convention entry in `docs/DEVELOPMENT.md` prohibiting `| _ =>`
   on `KernelError` in production code.

**Files modified**: `State.lean` (~3 lines comment), `docs/DEVELOPMENT.md` (~5 lines).
**Build verification**: None (doc-only).

### AC2-G: Phase AC2 smoke test gate

**Change**: Run `./scripts/test_smoke.sh`.

**Phase AC2 total**: 7 sub-tasks, ~100–200 lines of changes.

---

## 5. Phase AC3 — IPC Atomicity & Invariant Strengthening

**Goal**: Address I-02 atomicity documentation, I-04 badge bounds, API-01
silent-drop documentation, and strengthen the IPC proof surface.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh` pass.
**Dependencies**: AC1 complete (I-01 invariant work is prerequisite context).

### AC3-A: Document `donateSchedContext` atomicity contract (I-02)

**Finding**: `donateSchedContext` (Endpoint.lean:170–194) performs three
sequential `storeObject` calls. If step 1 succeeds but step 2 fails, the
returned error state has a SchedContext pointing to the server with no TCB
update. Callers discard error states, but the pattern is fragile.

**Change**:
1. Add a structured atomicity comment to `donateSchedContext` documenting:
   - The three mutation steps and their order.
   - The intermediate state after each step (which fields are modified).
   - The contract: **callers MUST discard the state on `.error`**; the
     intermediate state after partial failure is semantically inconsistent.
   - The justification: in a single-core microkernel with no preemption during
     kernel transitions, atomicity is guaranteed by the execution model. On
     hardware, kernel transitions run with interrupts disabled, so no concurrent
     observer can see intermediate states.
2. Apply identical documentation to `returnDonatedSchedContext` (Endpoint.lean:
   208–238), which has the same 3-step pattern (I-03, subsumed).

**Files modified**: `Endpoint.lean` (~20 lines comments across both functions).
**Build verification**: No Lean changes; doc-only.

### AC3-B: Add `donateSchedContext` intermediate-state lemma (I-02 proof)

**Finding**: While documentation addresses the operational concern, a formal
proof strengthens the argument.

**Change**:
1. In `SeLe4n/Kernel/IPC/Operations/SchedulerLemmas.lean`, add a lemma
   `donateSchedContext_error_preserves_scheduler` proving that if
   `donateSchedContext` returns `.error`, the scheduler fields of the returned
   state are unchanged from input.
2. This supports the argument that callers who discard error states lose no
   scheduler consistency.

**Files modified**: `SchedulerLemmas.lean` (~30–50 lines).
**Build verification**: `lake build SeLe4n.Kernel.IPC.Operations.SchedulerLemmas`.

### AC3-C: Document `Badge.bor` unbounded-Nat intermediary (I-04)

**Finding**: `Badge.bor` (Prelude.lean:489) computes `a.val ||| b.val` on
unbounded Lean `Nat`, then masks via `ofNatMasked`. The intermediate OR result
is unbounded. On ARM64 hardware, notification words are 64-bit.

**Change**:
1. Add a structured comment to `Badge.bor` noting:
   - The intermediate `|||` result is unbounded Lean `Nat`.
   - `ofNatMasked` (Prelude.lean:485) applies `% machineWordMax` (2^64).
   - The formal theorem `bor_valid` (Prelude.lean:498) proves the result is
     within `machineWordMax`.
   - For hardware deployment: the platform binding layer must ensure all `Badge`
     values entering the model are already within 64-bit range, making the
     intermediate unboundedness a no-op.
2. No code change needed — the existing implementation is correct.

**Files modified**: `Prelude.lean` (~5 lines comment).
**Build verification**: None (doc-only).

### AC3-D: Document `resolveExtraCaps` silent-drop behavior (API-01)

**Finding**: `resolveExtraCaps` (API.lean:408–417) silently drops capabilities
that fail to resolve. This is seL4-compatible behavior but the receiver cannot
distinguish dropped caps from never-sent.

**Change**:
1. Expand the existing documentation comment at `resolveExtraCaps` to note:
   - The resolved capability count in the response `MessageInfo` reflects the
     actual number resolved, not the number attempted.
   - Callers should compare `response.extraCaps` with the expected count to
     detect drops.
   - This matches seL4 `lookupExtraCaps` semantics (audit confirmation X5-I).
2. Add a test in `tests/OperationChainSuite.lean` that verifies the count
   behavior: send 3 caps where 1 is invalid, verify receiver sees 2.

**Files modified**: `API.lean` (~5 lines comment), `tests/OperationChainSuite.lean`
(~20 lines test).
**Build verification**: `lake build SeLe4n.Kernel.API` + build/run test suite.

### AC3-E: Prove `storeObject_preserves_objectCount_bound` (F-03 supplement)

**Finding**: `storeObject` (State.lean:457–482) always returns `.ok` with no
capacity check. The preservation theorem `storeObject_preserves_objectIndexBounded`
exists (State.lean:488–495) proving the invariant is maintained. However, a
debug-mode assertion for hardware targets would provide additional safety.

**Change**:
1. Add a `def storeObjectChecked` variant in `State.lean` that checks
   `objectIndex.length < maxObjects` before delegating to `storeObject`,
   returning `KernelError.objectStoreCapacityExceeded` on violation.
2. Add a theorem `storeObjectChecked_capacity_safe` proving that successful
   `storeObjectChecked` results always satisfy the capacity bound.
3. The existing `storeObject` remains for proof-layer use where the invariant
   is already established.

**Files modified**: `State.lean` (~25–35 lines).
**Build verification**: `lake build SeLe4n.Model.State`.

### AC3-F: Phase AC3 smoke test gate

**Change**: Run `./scripts/test_smoke.sh`.

**Phase AC3 total**: 6 sub-tasks, ~110–170 lines of changes.

---

## 6. Phase AC4 — Architecture & Platform Tightening

**Goal**: Address A-04 physical address bound gap, F-01/F-02 identifier and
access-right constructor safety, and IF-01 enforcement boundary completeness.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh` pass.
**Dependencies**: AC1–AC3 complete.

### AC4-A: Parameterize `physicalAddressBound` via platform config (A-04)

**Finding**: `physicalAddressBound` (VSpace.lean:53) defaults to 2^52 (ARM64
LPA max). RPi5 BCM2712 uses 44-bit PA. The gap [2^44, 2^52) accepts addresses
invalid on RPi5. A platform-aware variant `physicalAddressBoundForConfig`
(VSpace.lean:58–59) already exists.

**Change**:
1. Verify that all production entry points (`syscallEntry` → `vspaceMapPageCheckedWithFlushFromState`)
   use the state-aware variant that reads `physicalAddressWidth` from
   `SystemState.machine`. This is believed to already be the case (API.lean
   wires through `vspaceMapPageCheckedWithFlushFromState`).
2. Add a comment to `physicalAddressBound` marking it as "proof-layer default
   only — production code must use `physicalAddressBoundForConfig` or
   `vspaceMapPageCheckedWithFlushFromState`."
3. Add a test that constructs a simulated RPi5 `MachineConfig` with
   `physicalAddressWidth := 44` and verifies that `vspaceMapPageCheckedWithFlushFromState`
   rejects an address at 2^44 (one beyond the 44-bit range).

**Files modified**: `VSpace.lean` (~5 lines comment), test suite (~15–20 lines).
**Build verification**: `lake build SeLe4n.Kernel.Architecture.VSpace`.

### AC4-B: Add `AccessRightSet` constructor-safety documentation (F-02)

**Finding**: `AccessRightSet.mk` (Types.lean:76) is structurally accessible.
The `INTERNAL` comment warns against direct use, but Lean 4 cannot enforce
private constructors.

**Change**:
1. Add a module-level comment at the top of the `AccessRightSet` section
   documenting:
   - `mk` is TCB-internal only.
   - All external construction must use `ofNat` (auto-masks), `mk_checked`
     (proof-carrying), `ofList`, `singleton`, or `empty`.
   - The `valid` predicate (`bits < 32`) is the canonical safety condition.
   - `subset` uses bitwise AND which masks high bits naturally, making invalid
     `AccessRightSet` values harmless for rights-checking operations.
2. Add a `theorem AccessRightSet.subset_masks_invalid` proving that for any
   `a b : AccessRightSet`, `a.subset b` produces a correct result regardless of
   whether `a.valid` or `b.valid` holds. This mechanizes the argument that
   invalid sets are safe operationally.

**Files modified**: `Types.lean` (~10 lines comment + ~15 lines theorem).
**Build verification**: `lake build SeLe4n.Model.Object.Types`.

### AC4-C: Document identifier `Nat` unboundedness and ABI validation (F-01)

**Finding**: All identifier types wrap unbounded `Nat`. `isWord64`/
`isWord64Bounded` predicates exist but constructors are unchecked.

**Change**:
1. Add a "Typed Identifier Safety Model" comment block at the top of
   `Prelude.lean` (after the existing identifier definitions) documenting:
   - Identifiers are unbounded `Nat` by design for proof ergonomics.
   - The ABI boundary (Rust crate + `RegisterDecode.lean` + `SyscallArgDecode.lean`)
     validates all incoming values before constructing identifiers.
   - Internal kernel operations are trusted to produce valid identifiers
     because they derive new IDs from existing (validated) ones.
   - For hardware deployment: the `isWord64` predicates must be enforced at
     every ABI entry point.
2. No code change — the existing design is sound for the model; this documents
   the trust boundary for hardware deployment.

**Files modified**: `Prelude.lean` (~15 lines comment).
**Build verification**: None (doc-only).

### AC4-D: Add enforcement boundary completeness witness (IF-01)

**Finding**: The enforcement boundary (Wrappers.lean:186–225) lists 30
classified operations across 4 categories, but the classification is a manual
`List EnforcementClass` — no compile-time check ensures every `SyscallId` is
accounted for.

**Change**:
1. In `SeLe4n/Kernel/InformationFlow/Enforcement/Wrappers.lean`, add a
   `def enforcementBoundaryComplete : Bool` function that:
   - Iterates over all 25 `SyscallId` variants (using the existing `SyscallId.all`
     list from Types.lean).
   - Checks that each variant appears in exactly one classification category.
   - Returns `true` iff the mapping is exhaustive and injective.
2. Add a theorem `enforcementBoundary_is_complete :
   enforcementBoundaryComplete = true := by native_decide`.
3. This creates a compile-time breakage whenever a new `SyscallId` is added
   without updating the enforcement boundary.

**Files modified**: `Wrappers.lean` (~30–50 lines).
**Build verification**: `lake build SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers`.

### AC4-E: Phase AC4 smoke test gate

**Change**: Run `./scripts/test_smoke.sh`.

**Phase AC4 total**: 5 sub-tasks, ~90–150 lines of changes.

---

## 7. Phase AC5 — Cross-Cutting & Infrastructure

**Goal**: Address X-05 field-disjointness prose gap, X-08 GitBook drift risk,
and add targeted infrastructure improvements.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_full.sh` pass.
**Dependencies**: AC1–AC4 complete (theorem changes may interact).

### AC5-A: Strengthen CrossSubsystem field-disjointness prose with theorem coverage (X-05)

**Finding**: The field-disjointness facts are machine-checked via `decide`
(CrossSubsystem.lean:413–472), but the architectural rationale explaining *why*
disjoint fields imply composable invariants is prose.

**Change**:
1. Add a structured comment block at CrossSubsystem.lean:230 that explicitly
   maps each invariant predicate to the `StateField` values it touches, with
   cross-references to the corresponding `fieldsDisjoint` theorems.
2. Add a `theorem allCrossSubsystemPredicates_pairwise_disjoint` that composes
   all individual `fieldsDisjoint` theorems into a single top-level statement
   covering all 8 predicates. This turns the "informal composition" argument
   into a single machine-checked theorem.

**Files modified**: `CrossSubsystem.lean` (~30–50 lines).
**Build verification**: `lake build SeLe4n.Kernel.CrossSubsystem`.

### AC5-B: Add GitBook content-hash drift check (X-08)

**Finding**: GitBook chapters mirror canonical `docs/` files. The existing
`test_docs_sync.sh` checks link integrity and navigation generation, but does
not verify that GitBook chapter *content* matches canonical sources.

**Change**:
1. In `scripts/test_docs_sync.sh`, add a new check that computes SHA-256 hashes
   of key canonical sections and compares them against corresponding GitBook
   chapter headers.
2. The check should compare structural headings (H1/H2 headers) between
   canonical and GitBook files — not byte-for-byte content (since GitBook adds
   navigation and formatting).
3. If headers diverge, emit a warning (not a hard failure) with the differing
   files listed.

**Files modified**: `scripts/test_docs_sync.sh` (~20–30 lines).
**Build verification**: `./scripts/test_docs_sync.sh`.

### AC5-C: Add `saveOutgoingContext_scheduler_eq` theorem (S-05 supplement)

**Finding**: The `switchDomain` dual-state pattern depends on `saveOutgoingContext`
not modifying the `scheduler` field. This should be mechanized.

**Change**:
1. In `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean`, add:
   ```lean
   theorem saveOutgoingContext_scheduler_eq (st : SystemState) :
       (saveOutgoingContext st).scheduler = st.scheduler
   ```
2. The proof should be a simple `simp [saveOutgoingContext]` since the function
   only modifies `objects` (register file save into the TCB).
3. Reference this theorem from the `switchDomain` documentation comment added
   in AC2-D.

**Files modified**: `Preservation.lean` (~10–15 lines).
**Build verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation`.

### AC5-D: Audit all `KernelError` match sites for catch-all patterns (F-04)

**Finding**: With 44 error variants, `| _ =>` catch-all patterns are a
correctness risk. No catch-alls were found during verification, but this should
be systematically confirmed.

**Change**:
1. Run a codebase-wide search for `| _ =>` in files that import `KernelError`
   or pattern-match on `.error`.
2. For each match found, classify as:
   - **Safe**: The catch-all is on a different type (not `KernelError`).
   - **Intentional**: The catch-all handles all errors uniformly (e.g., `fold`
     accumulators that discard error details).
   - **Risky**: The catch-all on `KernelError` could mask a specific variant.
3. Document results. If any "Risky" patterns are found, replace with explicit
   arms.

**Files modified**: Varies (0–20 lines per site, likely 0 based on verification).
**Build verification**: `lake build` for any modified files.

### AC5-E: Add `AccessRightSet.subset_masks_invalid` theorem (F-02 proof)

**Finding**: From AC4-B, the `subset` function uses bitwise AND, which naturally
masks high bits. This should be proven to close the `mk` bypass concern.

**Change**:
1. In `SeLe4n/Model/Object/Types.lean`, add:
   ```lean
   theorem AccessRightSet.subset_masks :
       ∀ (a b : AccessRightSet), (a.subset b).bits < 32 :=
   ```
   This proves that `subset` always produces a valid `AccessRightSet` regardless
   of input validity.
2. The proof relies on `Nat.land_lt_two_pow` or equivalent bitwise arithmetic
   lemma.

**Files modified**: `Types.lean` (~15–25 lines).
**Build verification**: `lake build SeLe4n.Model.Object.Types`.

### AC5-F: Add `storeObjectChecked` usage recommendation to coding conventions (F-03)

**Change**:
1. After AC3-E creates `storeObjectChecked`, add a coding convention entry in
   `docs/DEVELOPMENT.md` recommending:
   - Use `storeObjectChecked` in new code paths that are not covered by the
     `retypeFromUntyped` capacity gate.
   - Use `storeObject` only in proof-layer code where `objectIndexBounded` is
     an established precondition.

**Files modified**: `docs/DEVELOPMENT.md` (~8 lines).
**Build verification**: None (doc-only).

### AC5-G: Verify `enforcementBoundaryComplete` theorem compiles (IF-01 verify)

**Change**: After AC4-D adds the completeness witness, verify it compiles
cleanly and add it to the CI surface:
1. Ensure `lake build SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers`
   succeeds.
2. Verify that adding a hypothetical 26th `SyscallId` would break the theorem
   (by temporarily adding one in a scratch branch and confirming the build fails).
   Remove the hypothetical variant immediately.

**Files modified**: None (verification only).
**Build verification**: `lake build SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers`.

### AC5-H: Phase AC5 full test gate

**Change**: Run `./scripts/test_full.sh` (Tier 0–3) to validate all invariant
surface anchors still pass after the cumulative changes from AC1–AC5.

**Phase AC5 total**: 8 sub-tasks, ~120–200 lines of changes.

---

## 8. Phase AC6 — Documentation, Testing & Closure

**Goal**: Dedicated test suites for decode modules, documentation sync, audit
addendum, workstream history update, and final validation.
**Gate**: `./scripts/test_full.sh` pass + documentation sync check.
**Dependencies**: AC1–AC5 complete.

### AC6-A: Create dedicated `DecodingSuite.lean` test file (T-03)

**Finding**: `RegisterDecode.lean` and `SyscallArgDecode.lean` have coverage
dispersed across `NegativeStateSuite.lean` (lines 1857–2230) and
`OperationChainSuite.lean` (lines 516–607), but no standalone test suite.

**Change**:
1. Create `tests/DecodingSuite.lean` with test cases extracted and organized by
   decode function:
   - `decodeSyscallId`: valid range (0–24), boundary (25 = invalid), large values.
   - `decodeMsgInfo`: valid MessageInfo encoding/decoding round-trip, overflow.
   - `decodeCapPtr`: valid/invalid capability pointers.
   - `decodeSyscallArgs`: per-syscall typed argument decode for all 25 syscalls.
   - `validateRegBound`: register index bounds checking.
2. Add `DecodingSuite` to `lakefile.lean` as a test executable target.
3. Add `lake exe test_decoding` to `scripts/test_smoke.sh` (Tier 2).

**Files modified**: New `tests/DecodingSuite.lean` (~100–150 lines), `lakefile.lean`
(~5 lines), `scripts/test_smoke.sh` (~2 lines).
**Build verification**: `lake build tests.DecodingSuite` + `lake exe test_decoding`.

### AC6-B: Update `docs/DEVELOPMENT.md` with audit-driven coding conventions

**Change**: Consolidate all documentation additions from AC2–AC5 into a new
"Audit-Driven Coding Conventions" section in `DEVELOPMENT.md`:
1. `KernelError` match hygiene (no catch-all patterns).
2. `storeObject` vs `storeObjectChecked` usage.
3. Identifier `Nat` unboundedness and ABI boundary validation.
4. `AccessRightSet` constructor safety.
5. Multi-step mutation atomicity contract.

**Files modified**: `docs/DEVELOPMENT.md` (~30–40 lines).
**Build verification**: None (doc-only).

### AC6-C: Update `docs/WORKSTREAM_HISTORY.md` with WS-AC entry

**Change**:
1. Add a WS-AC entry to `docs/WORKSTREAM_HISTORY.md` recording:
   - Workstream ID: WS-AC
   - Title: Comprehensive Audit Remediation (v0.25.3)
   - Status: IN PROGRESS (update to COMPLETE when all phases are done)
   - Phase count: 6 (AC1–AC6)
   - Sub-task count: 42
   - Findings addressed: 3 HIGH, 8 MEDIUM, 10 LOW
   - Findings excluded: 22+ Info/positive/phantom

**Files modified**: `docs/WORKSTREAM_HISTORY.md` (~15 lines).
**Build verification**: None (doc-only).

### AC6-D: Append corrected severity table addendum to audit document

**Change**:
1. Append a "Section 16: Severity Table Addendum (Corrected)" to
   `docs/audits/AUDIT_v0.25.3_COMPREHENSIVE.md` containing:
   - A corrected severity table matching the detailed body text.
   - A note explaining the 16 discrepancies found during verification.
   - Cross-reference to this workstream plan.

**Files modified**: `docs/audits/AUDIT_v0.25.3_COMPREHENSIVE.md` (~40 lines appended).
**Build verification**: None (doc-only).

### AC6-E: Regenerate `docs/codebase_map.json` if Lean sources changed

**Change**:
1. If any new Lean files were created (e.g., `tests/DecodingSuite.lean`) or
   existing files renamed (e.g., `cspaceMintUntracked`), regenerate the codebase
   map: `python3 scripts/generate_codebase_map.py`.
2. Verify the map is consistent: `python3 scripts/generate_codebase_map.py --check`.

**Files modified**: `docs/codebase_map.json` (auto-generated).
**Build verification**: `python3 scripts/generate_codebase_map.py --check`.

### AC6-F: Full test suite validation

**Change**: Run `./scripts/test_full.sh` (Tier 0–3). This is the comprehensive
validation gate for the entire workstream:
- Tier 0: Hygiene (no sorry/axiom, website links, shellcheck)
- Tier 1: Build (lake build, Rust cargo build)
- Tier 2: Trace + negative state + new decoding suite
- Tier 3: Invariant surface anchors

### AC6-G: Workstream closure

**Change**:
1. Update WS-AC status in `docs/WORKSTREAM_HISTORY.md` to COMPLETE.
2. Update version number if appropriate.
3. Final commit with workstream summary.

**Phase AC6 total**: 7 sub-tasks, ~200–300 lines of changes.

---

## 9. Dependency Graph

```
AC1 (High fixes) ─────────────────────────────────────┐
  AC1-A (S-01 fail-closed) ──► AC1-E (proof chain) ──►│
  AC1-B (I-01 invariant)  ──► AC1-C (I-01 precond) ──►│
  AC1-D (C-01 rename)     ──► AC1-H (C-01 test) ─────►│── AC1-I gate
  AC1-A ──────────────────────► AC1-G (S-01 test) ────►│
                                                        │
AC2 (Scheduler harden) ◄───────────────────────────────┘
  AC2-A (S-02 doc)     ─┐
  AC2-B (S-03 doc)     ─┤
  AC2-C (S-04 migrate) ─┼─► AC2-G gate
  AC2-D (S-05 doc)     ─┤
  AC2-E (S-06 doc)     ─┤
  AC2-F (F-04 doc)     ─┘
                          │
AC3 (IPC strengthen) ◄───┘
  AC3-A (I-02 doc)     ─┐
  AC3-B (I-02 proof)   ─┤
  AC3-C (I-04 doc)     ─┼─► AC3-F gate
  AC3-D (API-01 doc)   ─┤
  AC3-E (F-03 checked) ─┘
                          │
AC4 (Arch tighten) ◄─────┘
  AC4-A (A-04 param)   ─┐
  AC4-B (F-02 safety)  ─┤
  AC4-C (F-01 doc)     ─┼─► AC4-E gate
  AC4-D (IF-01 witness)─┘
                          │
AC5 (Cross-cutting) ◄────┘
  AC5-A (X-05 theorem) ─┐
  AC5-B (X-08 hash)    ─┤
  AC5-C (S-05 theorem) ─┤
  AC5-D (F-04 audit)   ─┼─► AC5-H gate (test_full.sh)
  AC5-E (F-02 proof)   ─┤
  AC5-F (F-03 doc)     ─┤
  AC5-G (IF-01 verify) ─┘
                          │
AC6 (Doc & closure) ◄────┘
  AC6-A (T-03 suite)   ─┐
  AC6-B (conventions)   ─┤
  AC6-C (WS history)   ─┼─► AC6-F gate (test_full.sh) ──► AC6-G closure
  AC6-D (audit addendum)┤
  AC6-E (codebase map)  ─┘
```

### Parallelism Opportunities

Within each phase, tasks without data dependencies can execute in parallel:

| Phase | Parallel Groups |
|-------|----------------|
| AC1 | {AC1-A, AC1-B, AC1-C, AC1-D} can start in parallel; {AC1-E, AC1-F} after AC1-A; {AC1-G, AC1-H} after their parents |
| AC2 | {AC2-A, AC2-B, AC2-D, AC2-E, AC2-F} are independent; AC2-C is the only proof-impacting change |
| AC3 | {AC3-A, AC3-C, AC3-D} are doc-only and parallel; {AC3-B, AC3-E} are proof work |
| AC4 | {AC4-A, AC4-B, AC4-C} are independent; AC4-D depends on Types.lean stability |
| AC5 | {AC5-A, AC5-B, AC5-D, AC5-F} are independent; {AC5-C, AC5-E, AC5-G} need prior phases |
| AC6 | {AC6-A, AC6-B, AC6-C, AC6-D} are independent |

---

## 10. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| AC1-A breaks preservation proofs | Low | Medium | `schedContextStoreConsistent` ensures unreachable arm; proofs should not depend on `true` fallback |
| AC2-C (`configDefaultTimeSlice`) breaks Liveness theorems | Medium | Medium | Proofs reference a constant `5`; need to generalize to state field. May require non-trivial proof refactoring |
| AC4-D (`enforcementBoundaryComplete`) doesn't compile via `native_decide` | Low | Low | The `SyscallId` list is small (25 variants); `native_decide` is reliable for bounded enumeration |
| AC1-D rename (`cspaceMintUntracked`) misses a caller | Low | Low | Global grep + build verification catches all callers |
| New `DecodingSuite.lean` test failures reveal latent bugs | Medium | Low-Medium | Test failures are valuable — they would indicate actual decode issues worth fixing |
| AC3-E `storeObjectChecked` changes caller behavior | None | None | The checked variant is additive; existing `storeObject` is unchanged |

---

## 11. Scope Estimates Summary

| Phase | Sub-tasks | Lean Lines | Doc Lines | Test Lines | Proof Lines |
|-------|-----------|-----------|-----------|------------|-------------|
| AC1 | 9 | 1–10 | 10–20 | 35–50 | 60–150 |
| AC2 | 7 | 30–80 | 30–40 | 0 | 20–60 |
| AC3 | 6 | 25–35 | 25–35 | 20 | 30–50 |
| AC4 | 5 | 0–5 | 20–30 | 15–20 | 45–75 |
| AC5 | 8 | 0 | 8–15 | 0 | 55–90 |
| AC6 | 7 | 5 | 85–95 | 100–150 | 0 |
| **Total** | **42** | **61–135** | **178–235** | **170–240** | **210–425** |

**Grand total**: ~620–1,035 lines of changes across all categories.

---

## 12. Success Criteria

The workstream is COMPLETE when all of the following hold:

1. **Zero `sorry`/`axiom`** in production proof surface (maintained).
2. **All 3 HIGH findings** resolved:
   - S-01: `hasSufficientBudget` returns `false` on missing SchedContext.
   - I-01: `waitingThreadsPendingMessageNone` preservation proven for
     `notificationSignal`.
   - C-01: `cspaceMint` renamed to `cspaceMintUntracked` (or equivalent).
3. **All 9 MEDIUM findings** addressed (code fix, proof, or documented deferral).
4. **9 selected LOW findings** addressed (documentation, proofs, or tests).
5. **`test_full.sh`** passes (Tier 0–3).
6. **Documentation synchronized**: DEVELOPMENT.md, WORKSTREAM_HISTORY.md,
   codebase_map.json, audit addendum.
7. **Audit severity table corrected** via addendum.
8. **No regressions**: all existing test suites pass unchanged.

---

## 13. Finding-to-Task Traceability Matrix

| Finding ID | Severity | Primary Task | Supporting Tasks | Status |
|-----------|----------|-------------|-----------------|--------|
| S-01 | HIGH | AC1-A | AC1-E, AC1-F, AC1-G | Pending |
| I-01 | HIGH | AC1-B | AC1-C | Pending |
| C-01 | HIGH | AC1-D | AC1-H | Pending |
| S-02 | MEDIUM | AC2-A | — | Pending |
| SC-01 | MEDIUM | AC2-A | — (shared with S-02) | Pending |
| S-03 | MEDIUM | AC2-B | — | Pending |
| F-01 | MEDIUM | AC4-C | — | Pending |
| F-02 | MEDIUM | AC4-B | AC5-E | Pending |
| F-03 | MEDIUM | AC3-E | AC5-F | Pending |
| IF-01 | MEDIUM | AC4-D | AC5-G | Pending |
| API-01 | MEDIUM | AC3-D | — | Pending |
| S-04 | LOW | AC2-C | — | Pending |
| S-05 | LOW | AC2-D | AC5-C | Pending |
| S-06 | LOW | AC2-E | — | Pending |
| F-04 | LOW | AC2-F | AC5-D | Pending |
| I-02 | MEDIUM | AC3-A | AC3-B | Pending |
| I-04 | LOW | AC3-C | — | Pending |
| A-04 | LOW | AC4-A | — | Pending |
| X-05 | LOW | AC5-A | — | Pending |
| X-08 | LOW | AC5-B | — | Pending |
| T-03 | LOW | AC6-A | — | Pending |

**Coverage**: 21 findings (3 HIGH + 9 MEDIUM + 9 LOW) → 42 sub-tasks. All
actionable findings have at least one primary task. No finding is left
unaddressed.

---

*Plan created 2026-04-05. Author: Claude (Opus 4.6). Methodology: independent
verification of every audit finding against source code, followed by phased
remediation planning with dependency analysis and proof-impact assessment.*
