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
| Medium | 9 | 9 (A-01 reclassified to Info; net +0 because I-02 confirmed Medium) | 9 |
| Low | 14 | 14 (X-05 reclassified from Medium to Low; net +0) | 9 |
| Info | 20+ | 22+ (A-01 added; phantom findings excluded) | 0 (monitoring only) |

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

## 3. Phase AC1 — High-Severity Fixes ✓ COMPLETE

**Goal**: Resolve all 3 HIGH findings with minimal blast radius.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh` pass.
**Dependencies**: None (first phase).
**Status**: COMPLETE (v0.25.4). All 9 sub-tasks delivered. Zero sorry/axiom.

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

### AC1-B: Wire existing `waitingThreadsPendingMessageNone` preservation into NotificationPreservation (I-01)

**Finding**: `notificationSignal` (Endpoint.lean:334) unconditionally overwrites
a waiter's `pendingMessage`. The safety depends on `waitingThreadsPendingMessageNone`
(Defs.lean:284–290), which states threads blocked on receive or notification
have `pendingMessage = none`.

**Key discovery during verification**: The preservation theorems **already exist**
in `Structural.lean`:
- Line 7110–7149: `notificationSignal_preserves_waitingThreadsPendingMessageNone`
- Line 7248–7287: `notificationWait_preserves_waitingThreadsPendingMessageNone`

These are fully proven using helper lemmas:
- `storeTcbIpcStateAndMessage_preserves_waitingThreadsPendingMessageNone` (Structural.lean:7050–7088)
- `storeObject_nonTcb_preserves_waitingThreadsPendingMessageNone` (Structural.lean:6982–7000)
- `ensureRunnable_preserves_waitingThreadsPendingMessageNone` (Structural.lean:6969–6975)
- `notificationWake_pendingMessage_was_none` (Structural.lean:7098–7106)

The file `NotificationPreservation.lean` (lines 1352–1358) contains a
forward-reference comment to these theorems but does not import or re-export them.

**Implementation** (refactored from original re-export plan):

Rather than thin re-exports, the circular import dependency was broken by
extracting primitive helper lemmas into a new `WaitingThreadHelpers.lean`:

1. Created `Invariant/WaitingThreadHelpers.lean` with 7 primitive helpers
   extracted from Structural.lean (removeRunnable, ensureRunnable,
   storeObject_nonTcb, storeTcbIpcState, storeTcbIpcStateAndMessage,
   storeTcbQueueLinks, storeTcbPendingMessage — all `_preserves_waitingThreadsPendingMessageNone`).
2. Added `import WaitingThreadHelpers` to both NotificationPreservation.lean
   and Structural.lean.
3. Moved the 3 operation-level theorems (`notificationSignal_preserves_*`,
   `notificationWait_preserves_*`, `notificationWake_pendingMessage_was_none`)
   from Structural.lean into NotificationPreservation.lean with full
   machine-checked proofs (replacing comment cross-references).
4. Deleted ~330 lines from Structural.lean (moved code).

**Files modified**: `WaitingThreadHelpers.lean` (new, ~250 lines),
`NotificationPreservation.lean` (~140 lines replacing comment block),
`Structural.lean` (~330 lines deleted, 1 import added).
**Build verification**: All 3 modules + full `lake build` (232 jobs) pass.

### AC1-C: Wire `notificationWait` preservation into NotificationPreservation (I-01 supplement)

**Finding**: Same discovery — `notificationWait_preserves_waitingThreadsPendingMessageNone`
already exists in Structural.lean. Addressed jointly with AC1-B via the
WaitingThreadHelpers extraction (see AC1-B above).

**Files modified**: Same as AC1-B (joint implementation).
**Build verification**: `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`.

### AC1-D: Address `cspaceMint` CDT-tracking gap (C-01)

**Finding**: `cspaceMint` (Operations.lean:541–551) creates capabilities without
CDT edge recording. `cspaceMintWithCdt` (Operations.lean:785–794) is the
tracked alternative. The `syscallEntry` dispatch wires through the checked
path, but the untracked `cspaceMint` remains in the public API.

**Blast radius analysis**: Verification found **78 occurrences** of `cspaceMint`
across **18 files**:
- 8 direct function call sites (tests, API dispatch, CDT wrapper, checked wrapper)
- 27+ theorem parameters and `unfold cspaceMint` in proofs (Authority, Preservation,
  Non-Interference invariants across 6 proof files)
- 10+ pattern-match sites in composition theorems (KernelOperation inductive)
- 15+ API/documentation/comment references
- 7 model/type system references (SyscallId, FrozenOps)

**Decision**: **Option 1 (Conservative)** — renaming (Option 2) would touch 78
sites across 18 files with high proof breakage risk. Option 1 achieves the same
safety signal with near-zero blast radius.

**Change** (4 sub-steps):

**AC1-D.1**: Add a `@[deprecated "Use cspaceMintWithCdt for CDT-tracked derivation"]`
attribute to `cspaceMint` in Operations.lean:541. Lean 4.28.0 supports this
attribute (verified: no existing `@[deprecated]` usage in codebase — this is
the first).

**AC1-D.2**: Add a prominent doc-comment block above `cspaceMint` (Operations.lean:
535–540) documenting:
- This function creates **CDT-untracked** capabilities.
- It is the internal base operation composed within `cspaceMintWithCdt`.
- Direct use should be limited to: (a) internal composition within
  `cspaceMintWithCdt`, (b) proof decomposition, (c) tests.

**AC1-D.3** (SUPERSEDED): `@[deprecated]` was evaluated but rejected — 14
suppression annotations across 8 proof files outweighed the signal value.
Doc-comment serves the same purpose with zero blast radius.

**AC1-D.4** (IMPLEMENTED): Production dispatch wired through `cspaceMintWithCdt`.
Change path: `dispatchWithCap` → `cspaceMintWithCdt`, `cspaceMintChecked` →
`cspaceMintWithCdt`. NI proof updated with CDT-pipeline preservation
(`cdt_only_preserves_projection'`, `ensureCdtNodeForSlot_preserves_projection'`).
Enforcement soundness and dispatch delegation theorems updated. Minted
capabilities are now revocable via `cspaceRevoke`.

**Files modified**: `Operations.lean` (doc-comment), `API.lean` (dispatch +
delegation theorem), `Wrappers.lean` (checked wrapper + equivalence theorems),
`InformationFlow/Invariant/Operations.lean` (NI proof + early CDT helpers).
**Build verification**: All 4 modules build, 232 jobs, zero sorry/axiom.

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

### AC1-H: Add negative test for `cspaceMint` CDT absence (C-01 test)

**Change**:
1. In `tests/NegativeStateSuite.lean` (or `tests/OperationChainSuite.lean`),
   add a test that calls `cspaceMint` (deprecated but functional) and verifies
   the CDT has no new edges, then calls `cspaceMintWithCdt` on the same state
   and verifies the CDT does have a new edge.
2. This documents and regression-tests the intended CDT behavior difference,
   making the deprecation's rationale concrete.

**Files modified**: Test suite (~20–30 lines).
**Build verification**: Build + run the relevant test executable.

### AC1-I: Smoke test gate

**Change**: Run `./scripts/test_smoke.sh` to validate all Tier 0–2 checks pass
after Phase AC1 changes.

**Phase AC1 total**: 9 sub-tasks, ~120–230 lines of changes.

---

## 4. Phase AC2 — Scheduler & SchedContext Hardening ✓ COMPLETE

**Goal**: Address S-02/SC-01 performance concern, S-03 fuel documentation,
S-04 configurable time slice, S-05 dual-state documentation, S-06 RunQueue
complexity documentation.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh` pass.
**Dependencies**: AC1 complete (S-01 change affects scheduler module).
**Status**: COMPLETE (v0.25.6). All 7 sub-tasks delivered. Zero sorry/axiom.

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

**Blast radius analysis**: `defaultTimeSlice` appears in **~30 locations**:
- `Core.lean`: 2 function bodies (timerTick line 376, timerTickBudget line 527)
  and 4 comments
- `Preservation.lean`: **~22 occurrences** across proof bodies — `simp [defaultTimeSlice]`
  is used extensively in timerTick and timerTickBudget preservation proofs
  (lines 652, 1027, 1049, 1051, 1054, 1067, 1072, 1252, 1264, 1268, 1269,
  1547, 1824, 2541, 2572, 2575, 2591, 2723, 3013, 3357)
- `Liveness/TraceModel.lean`: 1 occurrence — `maxBudgetInBand` (line 249)
  uses `defaultTimeSlice` as fallback budget for unbound threads
- `InformationFlow/Invariant/Operations.lean`: 1 occurrence — `tcbReset`
  (line 2003) uses `defaultTimeSlice`
- `Model/Object/Types.lean`: 1 comment reference (line 419)

**Risk assessment**: The `simp [defaultTimeSlice]` calls in Preservation.lean
work because `defaultTimeSlice` unfolds to a concrete `Nat` literal (`5`),
which `simp` can then use for arithmetic simplification. Replacing with
`st.scheduler.configDefaultTimeSlice` (a state field) means `simp` can no
longer unfold to a concrete value — **every such proof site will break** unless
restructured to use a hypothesis `h : st.scheduler.configDefaultTimeSlice = 5`
or a `configDefaultTimeSlice > 0` precondition.

**Decision**: This task has **HIGH proof blast radius** (~22 proof sites). It
must be executed incrementally with careful build verification at each step.

**Change** (7 sub-steps):

**AC2-C.1**: In `Core.lean`, retain `defaultTimeSlice` as the **default value
initializer** for `configDefaultTimeSlice`:
```lean
def defaultTimeSlice : Nat := 5  -- retained as default initializer
```
This preserves backward compatibility for all proof sites that `simp [defaultTimeSlice]`.

**AC2-C.2**: In `Core.lean`, modify `timerTick` (line 376) to read the time
slice from the state field:
```lean
let tcb' := { tcb with timeSlice := st.scheduler.configDefaultTimeSlice }
```
Verify: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`.

**AC2-C.3**: In `Core.lean`, modify `timerTickBudget` (line 527) similarly.
Verify: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`.

**AC2-C.4**: In `Preservation.lean`, add a section-level hypothesis:
```lean
variable (hTimeSlice : st.scheduler.configDefaultTimeSlice = defaultTimeSlice)
```
This allows existing `simp [defaultTimeSlice]` calls to continue working by
rewriting through `hTimeSlice`. Apply to all timerTick preservation theorems.
Build incrementally — start with `timerTick_preserves_schedulerInvariantBundle`
(line ~1027) and verify before proceeding to others.

**AC2-C.5**: Update the ~22 proof sites in `Preservation.lean` that reference
`defaultTimeSlice` in their proof bodies. The 10 affected theorems are:

**HIGH difficulty** (contain `simp [defaultTimeSlice]` — 4 calls total):
- `timerTick_preserves_timeSlicePositive` (line 1029, **private**) — 2 simp calls
- `timerTick_preserves_currentTimeSlicePositive` (line 1226, **private**) — 2 simp calls

**MODERATE difficulty** (intermediate state constructions only):
- `timerTick_preserves_schedulerInvariantBundle` (line 623, public)
- `timerTick_preserves_runnableThreadsAreTCBs` (line 1520, public)
- `timerTick_preserves_domainTimeRemainingPositive` (line 1800, public)
- `timerTick_preserves_edfCurrentHasEarliestDeadline` (line 2501, private)
- `timerTick_preserves_contextMatchesCurrent` (line 2699, private)
- `timerTick_preserves_schedulerPriorityMatch` (line 2981, private)
- `timerTick_preserves_schedulerInvariantBundleFull` (line 3125, public)
- `consumeBudget_respects_unbound_invariant` (line ~3345, public)

**Migration strategy per site**:
- If the proof uses `simp [defaultTimeSlice]` for arithmetic (e.g., proving
  `5 > 0`), replace with `simp [← hTimeSlice, defaultTimeSlice]` or add an
  explicit `have : st.scheduler.configDefaultTimeSlice > 0 := by rw [hTimeSlice]; decide`.
- If the proof uses `defaultTimeSlice` in a term construction (e.g., `{ tcb with
  timeSlice := defaultTimeSlice }`), replace with `st.scheduler.configDefaultTimeSlice`.

**Recommended order**: Start with the 2 HIGH-difficulty private theorems (they
are internal and can be refactored freely). Then migrate the 8 moderate-difficulty
theorems in dependency order (bottom-up: private helpers first, then public
composites). Build after each group of 2–3 related theorems to catch errors early.

**AC2-C.6**: Update `Liveness/TraceModel.lean:249` — `maxBudgetInBand` uses
`defaultTimeSlice` as a fallback for unbound threads. Change to pass the
configurable value or add a comment explaining why the hardcoded default is
appropriate here (unbound threads always use the system default).
Verify: `lake build SeLe4n.Kernel.Scheduler.Liveness.TraceModel`.

**AC2-C.7**: Update `InformationFlow/Invariant/Operations.lean:2003` —
`tcbReset` uses `defaultTimeSlice`. Change to pass the configurable value from
the state parameter.
Verify: `lake build SeLe4n.Kernel.InformationFlow.Invariant.Operations`.

**Files modified**: `Core.lean` (~10 lines), `Preservation.lean` (~40–80 lines
across 22 proof sites), `TraceModel.lean` (~5 lines), `Operations.lean` (~5 lines).
**Build verification**: Incremental — verify each module after its changes.

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
   - Cross-reference to AC5-C which adds the formal theorem mechanizing this.

**Files modified**: `Core.lean` (~8 lines comment).
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

## 5. Phase AC3 — IPC Atomicity & Invariant Strengthening ✓ COMPLETE

**Goal**: Address I-02 atomicity documentation, I-04 badge bounds, API-01
silent-drop documentation, and strengthen the IPC proof surface.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh` pass.
**Dependencies**: AC1 complete (I-01 invariant work is prerequisite context).
**Status**: COMPLETE (v0.25.7). All 6 sub-tasks delivered. Zero sorry/axiom.

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
proof strengthens the argument. The function (Endpoint.lean:170–194) performs:
1. `storeObject clientScId.toObjId (.schedContext sc')` — update SchedContext
2. Lookup server TCB
3. `storeObject serverTid.toObjId (.tcb serverTcb')` — update server TCB

**Change** (3 sub-steps):

**AC3-B.1**: Add a lemma proving scheduler preservation on error:
```lean
theorem donateSchedContext_error_preserves_scheduler
    (st : SystemState) (clientScId : SeLe4n.SchedContextId)
    (serverTid : SeLe4n.ThreadId) (e : KernelError)
    (hErr : donateSchedContext clientScId serverTid st = .error e) :
    -- The returned error state's scheduler is identical to input
    -- (actually, .error returns no state — this is trivially true)
    True
```
**Correction**: In the `KernelM` monad, `.error e` returns no state at all —
`Except.error` carries only the error value. So the concern about "partial
state" is actually a non-issue in the pure model: if any step fails, the
caller gets `.error` with **no state**, not a partial state. The intermediate
state from step 1 is discarded by the monad's bind operation.

**AC3-B.2**: Instead, add a lemma proving that success implies all three steps
succeeded (strengthening the postcondition):
```lean
theorem donateSchedContext_ok_implies_all_stores_succeeded
    (st st' : SystemState) (clientScId : SeLe4n.SchedContextId)
    (serverTid : SeLe4n.ThreadId)
    (hOk : donateSchedContext clientScId serverTid st = .ok ((), st')) :
    ∃ sc' serverTcb', ...  -- all intermediate lookups succeeded
```

**AC3-B.3**: Verify build: `lake build SeLe4n.Kernel.IPC.Operations.SchedulerLemmas`.

**Important note**: The AC3-A documentation should be updated to reflect that
`.error` in `KernelM` carries **no state** — the "partial state" concern from
the audit is a misunderstanding of the `Except` monad semantics. The actual
risk is only relevant if someone extracts the intermediate state from a
`do`-block at a point between step 1 and step 2, which doesn't happen because
the entire function is a single `do`-expression.

**Files modified**: `SchedulerLemmas.lean` (~25–40 lines).
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

### AC3-E: Add `storeObjectChecked` with capacity enforcement (F-03 supplement)

**Finding**: `storeObject` (State.lean:457–482) always returns `.ok` with no
capacity check. The existing theorem `storeObject_preserves_objectIndexBounded`
(State.lean:488–495) proves the invariant holds but doesn't enforce it at
runtime. The capacity model uses:
- `objectIndex : List SeLe4n.ObjId` (State.lean:237)
- `maxObjects : Nat := 65536` (State.lean:398)
- `objectIndexBounded st ↔ st.objectIndex.length ≤ maxObjects` (State.lean:403–404)

**Change** (4 sub-steps):

**AC3-E.1**: Add the checked variant after `storeObject` (insert at ~State.lean:496):
```lean
def storeObjectChecked (id : SeLe4n.ObjId) (obj : KernelObject) : Kernel Unit :=
  fun st =>
    if st.objectIndex.length ≥ maxObjects && !st.objectIndexSet.contains id then
      .error .objectStoreCapacityExceeded
    else
      storeObject id obj st
```
Note: the `!st.objectIndexSet.contains id` check avoids false rejection when
updating an existing object (which doesn't grow `objectIndex`).

**AC3-E.2**: Add a postcondition theorem:
```lean
theorem storeObjectChecked_preserves_objectIndexBounded
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hBound : objectIndexBounded st)
    (hStore : storeObjectChecked id obj st = .ok ((), st')) :
    objectIndexBounded st'
```

**AC3-E.3**: Add a delegation theorem proving that `storeObjectChecked` and
`storeObject` produce identical results when the capacity bound holds:
```lean
theorem storeObjectChecked_eq_storeObject
    (st : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hBound : objectIndexBounded st) :
    storeObjectChecked id obj st = storeObject id obj st
```
This ensures that migrating callers from `storeObject` to `storeObjectChecked`
is semantically transparent under the invariant.

**AC3-E.4**: Verify build: `lake build SeLe4n.Model.State`.

**Files modified**: `State.lean` (~35–50 lines).
**Build verification**: `lake build SeLe4n.Model.State`.

### AC3-F: Phase AC3 smoke test gate

**Change**: Run `./scripts/test_smoke.sh`.

**Phase AC3 total**: 6 sub-tasks, ~110–170 lines of changes.

---

## 6. Phase AC4 — Architecture & Platform Tightening ✓ COMPLETE

**Goal**: Address A-04 physical address bound gap, F-01/F-02 identifier and
access-right constructor safety, and IF-01 enforcement boundary completeness.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_smoke.sh` pass.
**Dependencies**: AC1–AC3 complete.
**Status**: COMPLETE (v0.25.8). All 5 sub-tasks delivered. Zero sorry/axiom.

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
The existing `INTERNAL` comment (Types.lean:72–75) warns against direct use,
but Lean 4 cannot enforce private constructors. Safe alternatives exist:
`ofNat` (masked), `mk_checked` (proof-carrying), `ofList`, `singleton`, `empty`.

**Change** (2 sub-steps):

**AC4-B.1**: Expand the existing `INTERNAL` comment into a structured safety
model documentation block covering:
- `mk` is TCB-internal only — no enforcement possible in Lean 4.
- Safe constructors and when to use each: `ofNat` for user input (auto-masks to
  5 bits), `mk_checked` for proof contexts (carries `bits < 32` witness),
  `ofList`/`singleton`/`empty` for compile-time-known sets.
- Operational safety argument: `subset` (line 160) uses `&&&` (bitwise AND)
  which naturally bounds the result. `mem` (line 155) uses `testBit` which is
  safe for any `Nat`. Neither operation produces incorrect results for invalid
  sets — they just test more bits than the 5 defined rights.
- Cross-reference to AC5-E which adds formal proofs mechanizing this argument.

**AC4-B.2**: Add a brief comment at `inter` (line 167) and `union` (line 164)
noting that these return raw `⟨bits⟩` without masking, so they can propagate
invalid high bits. Callers should use `ofNat` on the result if validity is
required downstream.

**Files modified**: `Types.lean` (~15 lines comment).
**Build verification**: None (doc-only; formal proofs deferred to AC5-E).

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
classified operations across 4 categories (11 policy-gated, 16 capability-only,
3 read-only), but the classification is a manual `List EnforcementClass` — no
compile-time check ensures every `SyscallId` is accounted for.

**Key structural details discovered during verification**:
- `EnforcementClass` (Wrappers.lean:171–175) is an inductive with 3 variants,
  each carrying a `String` field (not a `SyscallId` — uses string names).
- `SyscallId` (Types.lean:883–909) has 25 variants with `DecidableEq` derived.
- **`SyscallId.all` does NOT exist** — must be created.
- `SyscallId.count : Nat := 25` exists, and `toNat`/`ofNat?` provide
  bidirectional conversion.
- Existing completeness pattern (Soundness.lean:314–330) uses definitional
  equality (`rfl`) for structural assertions.

**Change** (5 sub-steps):

**AC4-D.1**: In `SeLe4n/Model/Object/Types.lean`, add `SyscallId.all`:
```lean
def SyscallId.all : List SyscallId :=
  [.send, .receive, .call, .reply, .cspaceMint, .cspaceCopy, .cspaceMove,
   .cspaceDelete, .lifecycleRetype, .vspaceMap, .vspaceUnmap,
   .serviceRegister, .serviceRevoke, .serviceQuery,
   .notificationSignal, .notificationWait, .replyRecv,
   .schedContextConfigure, .schedContextBind, .schedContextUnbind,
   .tcbSuspend, .tcbResume, .tcbSetPriority, .tcbSetMCPriority, .tcbSetIPCBuffer]
```
Add a completeness theorem: `theorem SyscallId.all_length : all.length = count := by rfl`.
Verify: `lake build SeLe4n.Model.Object.Types`.

**AC4-D.2**: In `Wrappers.lean`, add a mapping function from `SyscallId` to
its enforcement classification string name:
```lean
def syscallIdToEnforcementName : SyscallId → String
  | .send => "endpointSendDualChecked"
  | .receive => "endpointReceiveDualChecked"
  | .call => "endpointCallChecked"
  -- ... (all 25 variants)
```
This bridges the `SyscallId` type to the string-based `EnforcementClass` list.

**AC4-D.3**: Add the completeness check function:
```lean
def enforcementBoundaryComplete : Bool :=
  SyscallId.all.all (fun sid =>
    let name := syscallIdToEnforcementName sid
    enforcementBoundary.any (fun ec =>
      match ec with
      | .policyGated n | .capabilityOnly n | .readOnly n => n == name))
```

**AC4-D.4**: Add the compile-time completeness theorem:
```lean
theorem enforcementBoundary_is_complete :
    enforcementBoundaryComplete = true := by native_decide
```
This will fail at compile time if any `SyscallId` variant is missing from the
enforcement boundary, or if the `syscallIdToEnforcementName` mapping is out of
sync with the `enforcementBoundary` list.

**AC4-D.5**: Verify: `lake build SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers`.

**Files modified**: `Types.lean` (~10 lines), `Wrappers.lean` (~40–55 lines).
**Build verification**: `lake build SeLe4n.Model.Object.Types` and
`lake build SeLe4n.Kernel.InformationFlow.Enforcement.Wrappers`.

### AC4-E: Phase AC4 smoke test gate

**Change**: Run `./scripts/test_smoke.sh`.

**Phase AC4 total**: 5 sub-tasks, ~90–150 lines of changes.

---

## 7. Phase AC5 — Cross-Cutting & Infrastructure ✓ COMPLETE

**Goal**: Address X-05 field-disjointness prose gap, X-08 GitBook drift risk,
and add targeted infrastructure improvements.
**Gate**: `source ~/.elan/env && lake build` + `./scripts/test_full.sh` pass.
**Dependencies**: AC1–AC4 complete (theorem changes may interact).
**Status**: COMPLETE (v0.25.9). All 8 sub-tasks delivered. Zero sorry/axiom.

### AC5-A: Strengthen CrossSubsystem field-disjointness theorem coverage (X-05)

**Finding**: The field-disjointness facts are partially machine-checked via
`decide` (CrossSubsystem.lean:413–472). Verification found:

**Current state** (10 theorems for 8 predicates):
- 6 **disjoint** pairs proven (all return `true` via `by decide`):
  `regDepConsistent ⊥ staleEndpoint`, `regDepConsistent ⊥ staleNotification`,
  `serviceGraph ⊥ staleEndpoint`, `serviceGraph ⊥ staleNotification`,
  `regDepConsistent ⊥ regEndpointValid`, `serviceGraph ⊥ regEndpointValid`
- 4 **shared** pairs proven (all return `false` via `by decide`):
  `staleEndpoint ∩ staleNotification`, `regEndpointValid ∩ staleEndpoint`,
  `regEndpointValid ∩ staleNotification`, `regDepConsistent ∩ serviceGraph`

**Gap**: For 8 predicates, C(8,2) = 28 pairs. Only 10 are covered.
The missing 18 pairs involve the 3 SchedContext predicates
(`schedContextStoreConsistent`, `schedContextNotDualBound`,
`schedContextRunQueueConsistent`) which were added later and don't have
field-set declarations or pairwise theorems yet.

**`StateField` enum** (CrossSubsystem.lean:358–363): 15 variants including
`machine`, `objects`, `objectIndex`, `scheduler`, `services`, `lifecycle`,
`asidTable`, `interfaceRegistry`, `serviceRegistry`, `cdt`, `tlb`, etc.

**Change** (4 sub-steps):

**AC5-A.1**: Add field-set declarations for the 3 SchedContext predicates:
```lean
def schedContextStoreConsistent_fields : List StateField := [.objects]
def schedContextNotDualBound_fields : List StateField := [.objects]
def schedContextRunQueueConsistent_fields : List StateField := [.objects, .scheduler]
```
These must accurately reflect which `StateField` values each predicate reads.
Verify by inspecting each predicate's definition (CrossSubsystem.lean:174–206).

**AC5-A.2**: Add the pairwise disjointness (or overlap) theorems for all pairs
involving the 3 new field-sets. For each pair, the theorem is:
```lean
theorem <pred1>_disjoint_<pred2> :
    fieldsDisjoint <pred1>_fields <pred2>_fields = true := by decide
-- OR
theorem <pred1>_shares_<pred2> :
    fieldsDisjoint <pred1>_fields <pred2>_fields = false := by decide
```
Since the SchedContext predicates all touch `objects`, pairs among them will
likely be **shared** (not disjoint). Pairs with predicates that only touch
`services`/`serviceRegistry` will be disjoint.

**AC5-A.3**: Add the structured comment block mapping each of the 8 predicates
to its field-set, organized as a table:
```
-- Predicate                         Fields Touched
-- registryEndpointValid             [objects, services]
-- registryDependencyConsistent      [services, serviceRegistry]
-- noStaleEndpointQueueReferences    [objects]
-- noStaleNotificationWaitReferences [objects]
-- serviceGraphInvariant             [services, serviceRegistry]
-- schedContextStoreConsistent       [objects]
-- schedContextNotDualBound          [objects]
-- schedContextRunQueueConsistent    [objects, scheduler]
```

**AC5-A.4**: Add a summary theorem that asserts the total count of disjoint
pairs and shared pairs:
```lean
theorem crossSubsystem_disjoint_pair_count :
    (<list of all disjoint pair bools>).countP id = <N> := by native_decide
```
This provides a single compile-time check that the full pairwise analysis is
complete.

**Files modified**: `CrossSubsystem.lean` (~50–70 lines).
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

### AC5-E: Add `AccessRightSet` operational safety theorems (F-02 proof)

**Finding**: `AccessRightSet.subset` (Types.lean:160–161) is defined as:
```lean
@[inline] def subset (a b : AccessRightSet) : Bool := a.bits &&& b.bits == a.bits
```
The `valid` predicate is `s.bits < maxBits` where `maxBits = 2^5 = 32`
(Types.lean:84, 89). The `mk` constructor bypass concern is that `⟨999⟩`
violates `valid` but `subset` still produces correct results because bitwise
AND masks high bits.

**Correction**: `subset` returns a `Bool`, not an `AccessRightSet` — it tests
whether `a ⊆ b`. The actual masking happens in `ofNat`, `inter` (line 167:
`⟨a.bits &&& b.bits⟩`), and `union` (line 164: `⟨a.bits ||| b.bits⟩`).

**Change** (3 sub-steps):

**AC5-E.1**: Add a theorem proving `inter` preserves validity when at least
one operand is valid:
```lean
theorem AccessRightSet.inter_valid_left (a b : AccessRightSet)
    (ha : a.valid) : (a.inter b).valid := by
  unfold valid inter maxBits at *
  exact Nat.lt_of_le_of_lt (Nat.land_le_left a.bits b.bits) ha
```

**AC5-E.2**: Add a theorem proving `subset` is sound regardless of `valid`:
```lean
theorem AccessRightSet.subset_correct (a b : AccessRightSet) :
    a.subset b = true ↔ ∀ i, i < 5 → (a.bits.testBit i = true → b.bits.testBit i = true)
```
This shows that `subset` correctly tests bit-level inclusion even for invalid
sets, because bitwise AND is well-defined on all `Nat` values.

**AC5-E.3**: Add a theorem proving `mem` is safe for invalid sets:
```lean
theorem AccessRightSet.mem_bounded (s : AccessRightSet) (r : AccessRight) :
    s.mem r = true → r.val < 5
```
This proves that membership checks cannot return `true` for out-of-range
rights, even if `s.bits` is invalid.

**Files modified**: `Types.lean` (~25–40 lines).
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

**Finding**: `RegisterDecode.lean` exports 5 Layer-1 decode functions;
`SyscallArgDecode.lean` exports ~20 Layer-2 per-syscall decode functions.
Coverage exists in `NegativeStateSuite.lean` (lines 1857–2230, tests J1-NEG-01
through J1-NEG-17) and `OperationChainSuite.lean` (lines 516–607, chains 10–11),
but is dispersed and not independently runnable.

**Test infrastructure details**:
- Test helpers: `SeLe4n.Testing.Helpers` provides `expectError`, `expectOk`,
  `expectOkState`, `runKernelState`
- State construction: `BootstrapBuilder.empty |>.withObject ... |>.buildChecked`
- Lakefile pattern: `[[lean_exe]] name = "suite_name" root = "tests.Module"`
- Invocation pattern: `run_check "TRACE" lake exe suite_name` in tier scripts

**Change** (6 sub-steps):

**AC6-A.1**: Create `tests/DecodingSuite.lean` skeleton (~30 lines):
```lean
import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallArgDecode
import SeLe4n.Testing.Helpers

namespace SeLe4n.Testing.DecodingSuite

-- Layer 1: RegisterDecode tests
def runRegisterDecodeTests : IO Unit := do ...

-- Layer 2: SyscallArgDecode tests
def runSyscallArgDecodeTests : IO Unit := do ...

def main : IO Unit := do
  IO.println "=== DecodingSuite ==="
  runRegisterDecodeTests
  runSyscallArgDecodeTests
  IO.println "=== DecodingSuite PASSED ==="
end SeLe4n.Testing.DecodingSuite
```

**AC6-A.2**: Add Layer-1 tests in `runRegisterDecodeTests` (~40 lines):
- `decodeSyscallId`: valid (0 → `.send`, 12 → `.serviceRegister`, 24 →
  `.tcbSetIPCBuffer`), invalid (25, 2^64), boundary (24/25 edge)
- `decodeMsgInfo`: valid round-trip (encode then decode), overflow (length > 120,
  extraCaps > 7), boundary (length = 120)
- `decodeCapPtr`: valid (small values), large value (2^63)
- `validateRegBound`: valid (0, 31), invalid (32, 2^64)
- `decodeSyscallArgs`: integration test with a fully populated register file

**AC6-A.3**: Add Layer-2 tests in `runSyscallArgDecodeTests` (~60 lines):
Organize by syscall family:
- **CSpace** (4 functions): `decodeCSpaceMintArgs`, `decodeCSpaceCopyArgs`,
  `decodeCSpaceMoveArgs`, `decodeCSpaceDeleteArgs` — test valid decode, missing
  register, zero values
- **VSpace** (2 functions): `decodeVSpaceMapArgs` (with permission validation),
  `decodeVSpaceUnmapArgs`
- **Notification** (3 functions): `decodeNotificationSignalArgs`,
  `decodeNotificationWaitArgs` (unit), `decodeReplyRecvArgs`
- **SchedContext** (3 functions): `decodeSchedContextConfigureArgs`,
  `decodeSchedContextBindArgs`, `decodeSchedContextUnbindArgs` (unit)
- **TCB** (5 functions): `decodeSetPriorityArgs`, `decodeSetMCPriorityArgs`,
  `decodeSetIPCBufferArgs`, `decodeSuspendArgs` (unit), `decodeResumeArgs` (unit)
- **Service** (2 functions): `decodeServiceRegisterArgs`, `decodeServiceRevokeArgs`
- **Lifecycle** (1 function): `decodeLifecycleRetypeArgs`

**AC6-A.4**: Add to `lakefile.toml`:
```toml
[[lean_exe]]
name = "decoding_suite"
root = "tests.DecodingSuite"
```

**AC6-A.5**: Add to `scripts/test_tier2_negative.sh` (or `test_smoke.sh` Tier 2
section):
```bash
run_check "TRACE" lake exe decoding_suite
```

**AC6-A.6**: Verify: `lake build tests.DecodingSuite` + `lake exe decoding_suite`.

**Files modified**: New `tests/DecodingSuite.lean` (~130–160 lines),
`lakefile.toml` (~3 lines), test script (~1 line).
**Build verification**: `lake build tests.DecodingSuite` + `lake exe decoding_suite`.

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
   - Findings addressed: 3 HIGH, 9 MEDIUM, 9 LOW
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
  AC1-D (C-01 deprecate)  ──► AC1-H (C-01 test) ─────►│── AC1-I gate
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

| Phase | Parallel Groups | Critical Path |
|-------|----------------|---------------|
| AC1 | {AC1-A, AC1-B, AC1-C, AC1-D} can start in parallel; {AC1-E, AC1-F} after AC1-A; {AC1-G, AC1-H} after their parents | AC1-A → AC1-E → AC1-F (scheduler proof chain) |
| AC2 | {AC2-A, AC2-B, AC2-D, AC2-E, AC2-F} are independent doc-only tasks; **AC2-C is the critical path** (7 sub-steps, 22 proof sites) — execute last within phase | AC2-C.1 → AC2-C.2 → AC2-C.4 → AC2-C.5 (incremental proof migration) |
| AC3 | {AC3-A, AC3-C, AC3-D} are doc-only and parallel; {AC3-B, AC3-E} are proof work and can run in parallel with each other | AC3-E (storeObjectChecked) is independent of all others |
| AC4 | {AC4-A, AC4-B, AC4-C} are independent; **AC4-D must run after AC4-D.1** (SyscallId.all in Types.lean) | AC4-D.1 (Types.lean) → AC4-D.2–D.4 (Wrappers.lean) |
| AC5 | {AC5-A, AC5-B, AC5-D, AC5-F} are independent; {AC5-C, AC5-E, AC5-G} depend on prior phases | AC5-A (50–70 lines in CrossSubsystem) is the largest task |
| AC6 | {AC6-A, AC6-B, AC6-C, AC6-D} are independent; AC6-E after all code changes | AC6-A (DecodingSuite, 130–160 lines) is the largest task |

---

## 10. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| AC1-A breaks preservation proofs | Low | Medium | `schedContextStoreConsistent` ensures unreachable arm; proofs should not depend on `true` fallback |
| AC2-C (`configDefaultTimeSlice`) breaks ~22 proof sites in Preservation.lean | **High** | **Medium** | Retain `defaultTimeSlice` as initializer; add `hTimeSlice` hypothesis; migrate incrementally with per-group build verification. **Highest-risk task in the workstream** |
| AC2-C breaks Liveness/TraceModel theorems | Medium | Medium | `maxBudgetInBand` uses `defaultTimeSlice` for unbound threads — may need special handling since unbound threads genuinely use the system default, not a per-state value |
| AC4-D `SyscallId.all` list falls out of sync with SyscallId inductive | Low | Low | `all_length` theorem (`= count := by rfl`) will catch any mismatch at compile time |
| AC4-D `syscallIdToEnforcementName` mapping has wrong string | Low | Medium | `native_decide` theorem fails at compile time if any mapping is wrong — caught before merge |
| AC1-D `@[deprecated]` attribute causes unexpected build warnings | Low | Low | Lean 4.28.0 `@[deprecated]` emits warnings not errors; suppress at 2 legitimate internal call sites |
| AC5-A SchedContext predicate field-set declarations are wrong | Medium | Low | Field-sets must be manually verified against predicate definitions; `by decide` will catch if wrong (disjointness claim on shared fields would fail) |
| AC5-E `Nat.land_le_left` or `Nat.testBit` lemmas not available in Lean 4.28.0 | Medium | Low | Fall back to `omega` or `decide` for small-domain proofs; bitwise arithmetic lemmas have been in Lean 4 since ~4.5.0 |
| New `DecodingSuite.lean` test failures reveal latent bugs | Medium | Low-Medium | Test failures are valuable — they would indicate actual decode issues worth fixing |
| AC3-E `storeObjectChecked` changes caller behavior | None | None | The checked variant is additive; existing `storeObject` is unchanged |

---

## 11. Scope Estimates Summary

| Phase | Sub-tasks | Lean Lines | Doc Lines | Test Lines | Proof Lines |
|-------|-----------|-----------|-----------|------------|-------------|
| AC1 | 9 | 1–15 | 15–25 | 35–50 | 25–40 |
| AC2 | 7 | 10–20 | 30–45 | 0 | 40–80 |
| AC3 | 6 | 15–25 | 25–35 | 20 | 25–40 |
| AC4 | 5 | 10–15 | 15–25 | 15–20 | 40–55 |
| AC5 | 8 | 0 | 8–15 | 0 | 75–130 |
| AC6 | 7 | 5 | 85–95 | 130–160 | 0 |
| **Total** | **42** | **41–80** | **178–240** | **200–250** | **205–345** |

**Grand total**: ~625–915 lines of changes across all categories.

**Key changes from initial estimate**: AC1-B/C reduced (proofs already exist —
wiring only). AC2-C increased (22 proof sites in Preservation.lean). AC4-D
increased (need `SyscallId.all` + string-to-SyscallId bridge). AC5-A increased
(18 missing pairwise theorems). AC5-E restructured (corrected `subset` vs
`inter` semantics).

---

## 12. Success Criteria

The workstream is COMPLETE when all of the following hold:

1. **Zero `sorry`/`axiom`** in production proof surface (maintained).
2. **All 3 HIGH findings** resolved:
   - S-01: `hasSufficientBudget` returns `false` on missing SchedContext.
   - I-01: `waitingThreadsPendingMessageNone` preservation wired from
     Structural.lean into NotificationPreservation.lean.
   - C-01: `cspaceMint` marked `@[deprecated]` with prominent safety documentation.
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
| S-01 | HIGH | AC1-A | AC1-E, AC1-F, AC1-G | ✓ Complete |
| I-01 | HIGH | AC1-B | AC1-C | ✓ Complete |
| C-01 | HIGH | AC1-D | AC1-H | ✓ Complete |
| S-02 | MEDIUM | AC2-A | — | ✓ Complete |
| SC-01 | MEDIUM | AC2-A | — (shared with S-02) | ✓ Complete |
| S-03 | MEDIUM | AC2-B | — | ✓ Complete |
| F-01 | MEDIUM | AC4-C | — | ✓ Complete |
| F-02 | MEDIUM | AC4-B | AC5-E | ✓ Complete |
| F-03 | MEDIUM | AC3-E | AC5-F | ✓ Complete |
| IF-01 | MEDIUM | AC4-D | AC5-G | ✓ Complete |
| API-01 | MEDIUM | AC3-D | — | ✓ Complete |
| S-04 | LOW | AC2-C | — | ✓ Complete |
| S-05 | LOW | AC2-D | AC5-C | ✓ Complete |
| S-06 | LOW | AC2-E | — | ✓ Complete |
| F-04 | LOW | AC2-F | AC5-D | ✓ Complete |
| I-02 | MEDIUM | AC3-A | AC3-B | ✓ Complete |
| I-04 | LOW | AC3-C | — | ✓ Complete |
| A-04 | LOW | AC4-A | — | ✓ Complete |
| X-05 | LOW | AC5-A | — | ✓ Complete |
| X-08 | LOW | AC5-B | — | ✓ Complete |
| T-03 | LOW | AC6-A | — | Pending |

**Coverage**: 21 findings (3 HIGH + 9 MEDIUM + 9 LOW) → 42 sub-tasks. All
actionable findings have at least one primary task. No finding is left
unaddressed.

---

*Plan created 2026-04-05. Author: Claude (Opus 4.6). Methodology: independent
verification of every audit finding against source code, followed by phased
remediation planning with dependency analysis and proof-impact assessment.*
