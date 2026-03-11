# WS-I Workstream Plan — Post-Audit Improvement Portfolio (v0.14.9)

**Created**: 2026-03-11
**Baseline audit**: `docs/audits/AUDIT_CODEBASE_v0.13.6.md` (zero critical issues)
**Prior portfolios**: WS-F (v0.12.2, 33/33 closed), WS-H (v0.12.15, H1–H16 closed)
**Constraint**: Zero `sorry`/`axiom` in production proof surface

---

## 1. Planning Objective

The comprehensive v0.14.9 codebase audit confirmed zero critical vulnerabilities,
zero sorry/axiom in the production proof surface, and all tests passing across
Tiers 0–4. However, the audit identified **18 non-blocking improvement
recommendations** spanning five categories:

- **Testing infrastructure** (8 items): Inter-transition invariant assertions,
  mandatory determinism validation, multi-operation chain tests, scenario ID
  traceability, semantic proof validation, scheduler stress tests, declassification
  tests, fixture infrastructure improvements
- **Documentation** (3 items): RegName/RegValue design decision, readers' guide
  for IF architecture, test fixture update process documentation
- **Proof completeness** (2 items): CDT decomposition lemmas for 4 CSpace NI
  proofs, VSpace memory projection domain ownership model
- **Code quality** (2 items): HashMap.fold migration for detachCNodeSlots,
  metrics regeneration automation
- **Test coverage expansion** (3 items): VSpace multi-ASID sharing tests, IPC
  interleaved send tests, lifecycle transaction chain tests

This plan organizes all 18 recommendations into **5 workstreams (WS-I1 through
WS-I5)** across **3 execution phases**, prioritized by risk reduction impact.

None of these items are blocking. The codebase is production-ready. This
portfolio strengthens an already-sound foundation.

---

## 2. Planning Principles

1. **Risk-reduction ordering**: Address items that catch the most bugs first
   (inter-transition checks, mandatory determinism).
2. **Proof-first**: Any new test infrastructure or invariant assertion must not
   introduce sorry or weaken the proof surface.
3. **Coherent slices**: Each workstream is independently deliverable and testable.
4. **Minimal disruption**: Improvements integrate with existing infrastructure
   patterns (run_check, stateInvariantChecksFor, fixture format).
5. **Deterministic semantics**: All new tests produce deterministic, reproducible
   output.
6. **Foundation-first**: Infrastructure improvements (WS-I1) precede coverage
   expansion (WS-I3, WS-I4) to avoid building on unstable ground.
7. **Documentation-with-code**: Documentation updates paired with implementation
   in the same workstream when relevant.

---

## 3. Recommendation-to-Workstream Matrix

| # | Recommendation | Severity | Category | Workstream |
|---|----------------|----------|----------|------------|
| R-01 | Add inter-transition invariant assertions in MainTraceHarness | HIGH | Testing | WS-I1 |
| R-02 | Move determinism check from Tier 4 to Tier 2 (mandatory) | HIGH | Testing | WS-I1 |
| R-03 | Add scenario IDs for fixture traceability | HIGH | Testing | WS-I1 |
| R-04 | Replace L-08 regex with semantic proof validation | MEDIUM | Testing | WS-I2 |
| R-05 | Extend Tier 3 with property correctness checks | MEDIUM | Testing | WS-I2 |
| R-06 | Add multi-operation chain tests | MEDIUM | Testing | WS-I3 |
| R-07 | Add scheduler stress tests (high thread counts) | MEDIUM | Testing | WS-I3 |
| R-08 | Add information-flow declassification tests | MEDIUM | Testing | WS-I3 |
| R-09 | Add VSpace multi-ASID sharing tests | LOW | Testing | WS-I4 |
| R-10 | Add IPC interleaved send tests | LOW | Testing | WS-I4 |
| R-11 | Add lifecycle transaction chain tests | LOW | Testing | WS-I4 |
| R-12 | Document RegName/RegValue design decision | LOW | Documentation | WS-I5 |
| R-13 | Add readers' guide for 3-layer IF architecture | LOW | Documentation | WS-I5 |
| R-14 | Document test fixture update process | LOW | Documentation | WS-I5 |
| R-15 | CDT decomposition lemmas for CSpace NI proofs | MEDIUM | Proof | WS-I2 |
| R-16 | VSpace memory projection domain ownership model | MEDIUM | Proof | WS-I2 |
| R-17 | HashMap.fold migration for detachCNodeSlots | LOW | Code quality | WS-I5 |
| R-18 | Metrics regeneration automation | LOW | Code quality | WS-I5 |

---

## 4. Phase Overview

### Phase 1: Critical Infrastructure (WS-I1)

**Focus**: Eliminate the highest-risk testing gaps immediately.
**Blocking**: None (independent of all other phases).
**Estimated effort**: 6–8 hours.

| Workstream | Deliverables | Risk Addressed |
|------------|-------------|----------------|
| WS-I1 | Inter-transition assertions, mandatory determinism, scenario IDs | State corruption undetected; non-determinism not caught early; fixture non-traceability |

### Phase 2: Proof & Validation Depth (WS-I2)

**Focus**: Strengthen proof completeness and validation sophistication.
**Blocking**: None (independent of Phase 1, but recommended after).
**Estimated effort**: 10–14 hours.

| Workstream | Deliverables | Risk Addressed |
|------------|-------------|----------------|
| WS-I2 | Semantic L-08, Tier 3 property checks, CDT lemmas, VSpace projection | Trivial proofs undetected; existence-only Tier 3; NI proof deferrals |

### Phase 3: Coverage Expansion & Polish (WS-I3, WS-I4, WS-I5)

**Focus**: Broaden test coverage and documentation completeness.
**Blocking**: WS-I1 recommended complete before WS-I3/I4 (chain tests benefit
from inter-transition assertions).
**Estimated effort**: 14–18 hours.

| Workstream | Deliverables | Risk Addressed |
|------------|-------------|----------------|
| WS-I3 | Chain tests, scheduler stress, declassification | Compositional bugs; high-concurrency regressions; covert channels |
| WS-I4 | VSpace multi-ASID, IPC interleaving, lifecycle chains | Cross-ASID coherency; queue contention; cascading revoke |
| WS-I5 | Design docs, fixture guide, HashMap.fold, metrics automation | Documentation gaps; developer guidance |

### Dependency Graph

```
Phase 1: WS-I1 (Critical Infrastructure)
           │
           ▼
Phase 2: WS-I2 (Proof & Validation Depth)    [parallel-safe with Phase 1]
           │
           ▼
Phase 3: WS-I3 ──┐
         WS-I4 ──┤ [parallel with each other; after WS-I1 recommended]
         WS-I5 ──┘ [fully independent]
```

---

## 5. Workstream Definitions

### WS-I1: Critical Testing Infrastructure

**Objective**: Eliminate the three highest-risk testing gaps — state corruption
going undetected between transitions, non-determinism not caught until nightly,
and fixture expectations being untraceable to source code.

**Priority**: HIGH — Phase 1
**Estimated effort**: 6–8 hours
**Dependencies**: None
**Recommendations addressed**: R-01, R-02, R-03

#### Part A: Inter-Transition Invariant Assertions (R-01)

**Problem**: `MainTraceHarness.lean` runs 13 test functions (lines 1208–1220)
calling 120+ kernel transitions, but only validates invariants at entry (line
1196). State corruption bugs (CDT orphaned nodes, ASID table mismatches, IPC
queue pointer corruption) that do not alter console output pass silently.

**Deliverables**:

1. Add `assertStateInvariants` calls after each major transition group within
   every test function in `MainTraceHarness.lean`. Place assertions after every
   3–5 state-modifying operations, not after every single call (to avoid
   excessive runtime overhead).

2. The assertion calls should use the existing
   `assertStateInvariantsFor label objectIds st` API from
   `SeLe4n/Testing/InvariantChecks.lean` (line 337).

3. Each assertion should carry a descriptive label indicating the transition
   group that just completed, e.g.:
   ```lean
   assertStateInvariants "post-timer+register+memory" stMem
   assertStateInvariants "post-vspace-map-unmap" stUnmapped
   assertStateInvariants "post-cspace-mint-copy-revoke" stRevoked
   ```

4. Add corresponding fixture expectations for the invariant check output. The
   assertions do not print on success (they only throw on failure), so no
   fixture lines are needed for passing assertions. However, the trace output
   should include a summary count at the end:
   ```lean
   IO.println s!"inter-transition invariant checks: {checkCount} passed"
   ```

**Files modified**:
- `SeLe4n/Testing/MainTraceHarness.lean` — add assertions within each of the
  13 `run*Trace` functions
- `tests/fixtures/main_trace_smoke.expected` — add summary count expectation

**Proof maintenance**: None required. `assertStateInvariantsFor` is a runtime
check function (IO monad), not part of the proof surface.

**Exit evidence**:
- `test_smoke.sh` passes with inter-transition assertions active
- Manual introduction of a deliberate CDT orphan (temporary, reverted) triggers
  assertion failure at the correct transition boundary

#### Part B: Mandatory Determinism Validation (R-02)

**Problem**: Determinism validation exists only in Tier 4
(`test_tier4_nightly_candidates.sh`, lines 31–33), gated behind
`NIGHTLY_ENABLE_EXPERIMENTAL=1`. Non-determinism bugs (e.g., HashMap iteration
order leaking into scheduler selection) are caught only 12+ hours after merge.

**Deliverables**:

1. Create `scripts/test_tier2_determinism.sh` containing the determinism check
   logic extracted from Tier 4:
   ```bash
   DETERMINISM_DIR="$(mktemp -d)"
   trap 'rm -rf "${DETERMINISM_DIR}"' EXIT

   run_check "TRACE" bash -lc "lake exe sele4n > '${DETERMINISM_DIR}/run1.trace'"
   run_check "TRACE" bash -lc "lake exe sele4n > '${DETERMINISM_DIR}/run2.trace'"
   run_check "TRACE" bash -lc "diff -q '${DETERMINISM_DIR}/run1.trace' \
       '${DETERMINISM_DIR}/run2.trace' || \
       { echo 'Non-determinism detected: trace output differs between runs' >&2; exit 1; }"
   ```

2. Integrate into `scripts/test_smoke.sh` between the trace fixture check and
   the negative state suite:
   ```bash
   run_check "META" "${SCRIPT_DIR}/test_tier2_trace.sh" "${sub_args[@]}"
   run_check "META" "${SCRIPT_DIR}/test_tier2_determinism.sh" "${sub_args[@]}"  # NEW
   run_check "META" "${SCRIPT_DIR}/test_tier2_negative.sh" "${sub_args[@]}"
   ```

3. Keep the Tier 4 determinism check in place (it runs the full nightly seed
   probe, which is a superset). Update its comment to note that basic
   determinism is now mandatory in Tier 2.

**Files modified**:
- `scripts/test_tier2_determinism.sh` — new file (~25 lines)
- `scripts/test_smoke.sh` — add one `run_check` line
- `scripts/test_tier4_nightly_candidates.sh` — update comment only

**Proof maintenance**: None. Shell scripts only.

**Exit evidence**:
- `test_smoke.sh` runs determinism check on every invocation
- Deliberate introduction of `IO.rand` in a trace function (temporary,
  reverted) causes determinism check to fail

#### Part C: Scenario ID Traceability (R-03)

**Problem**: The 121-line fixture `tests/fixtures/main_trace_smoke.expected`
contains expected substrings with no mapping to the source function or line
that produced them. Coverage analysis is impossible without manual code
inspection.

**Deliverables**:

1. Add scenario ID prefixes to all `IO.println` calls in `MainTraceHarness.lean`
   using a consistent format: `[WSID-NNN]` where WSID identifies the test
   function and NNN is a sequential number within that function.

   Prefix mapping:
   ```
   CAT-  → runCapabilityAndArchitectureTrace
   SST-  → runServiceAndStressTrace
   LEP-  → runLifecycleAndEndpointTrace
   CIC-  → runCapabilityIpcTrace
   IMT-  → runIpcMessageTransferTrace
   IMB-  → runIpcMessageBoundsTrace
   DDT-  → runDequeueOnDispatchTrace
   ICS-  → runInlineContextSwitchTrace
   BME-  → runBoundedMessageExtendedTrace
   STD-  → runSchedulerTimingDomainTrace
   UMT-  → runUntypedMemoryTrace
   SGT-  → runSyscallGateTrace
   RCF-  → runRuntimeContractFixtureTrace
   ```

   Example transformation:
   ```lean
   -- Before:
   IO.println s!"vspace map success: {mapped}"
   -- After:
   IO.println s!"[CAT-003] vspace map success: {mapped}"
   ```

2. Update `tests/fixtures/main_trace_smoke.expected` to include scenario IDs
   in the pipe-delimited format already supported by `test_tier2_trace.sh`
   (lines 61–67):
   ```
   CAT-003 | Architecture | vspace map success: true
   ```

3. Create `tests/fixtures/scenario_registry.yaml` mapping each scenario ID
   to its source location:
   ```yaml
   scenarios:
     CAT-001:
       source: SeLe4n/Testing/MainTraceHarness.lean
       function: runCapabilityAndArchitectureTrace
       line_range: "160-165"
       subsystem: Architecture
       description: "Timer monotonicity validation"
     CAT-002:
       source: SeLe4n/Testing/MainTraceHarness.lean
       function: runCapabilityAndArchitectureTrace
       line_range: "166-172"
       subsystem: Architecture
       description: "Register context stability check"
   ```

4. Add a Tier 0 hygiene check validating that every scenario ID in the fixture
   appears in the registry and vice versa:
   ```bash
   run_check "HYGIENE" python3 "${SCRIPT_DIR}/scenario_catalog.py" validate-registry
   ```

**Files modified**:
- `SeLe4n/Testing/MainTraceHarness.lean` — add scenario ID prefixes to all
  IO.println calls
- `tests/fixtures/main_trace_smoke.expected` — update all expectations with
  scenario IDs and pipe-delimited format
- `tests/fixtures/scenario_registry.yaml` — new file
- `scripts/scenario_catalog.py` — add `validate-registry` subcommand
- `scripts/test_tier0_hygiene.sh` — add registry validation check

**Proof maintenance**: None. IO.println changes do not affect the proof surface.

**Exit evidence**:
- Every fixture line has a scenario ID
- `scenario_catalog.py validate-registry` passes
- A developer can answer "Is VSpace mapping tested?" by grepping the registry
  for `subsystem: VSpace`

---

### WS-I2: Proof & Validation Depth

**Objective**: Strengthen proof validation beyond regex-based spot-checks and
existence-only Tier 3 anchors; discharge tracked NI proof deferrals where CDT
lemmas and VSpace domain ownership models enable completion.

**Priority**: MEDIUM — Phase 2
**Estimated effort**: 10–14 hours
**Dependencies**: None (parallel-safe with WS-I1, but recommended after)
**Recommendations addressed**: R-04, R-05, R-15, R-16

#### Part A: Semantic L-08 Proof Validation (R-04)

**Problem**: The L-08 check (`test_tier0_hygiene.sh`, lines 63–68) uses regex
`theorem.*preserves.*:=\s*(by\s+)?rfl\s*$` to detect trivial proofs. This only
catches single-line `rfl` proofs. Multi-line trivial proofs (e.g., `by simp;
rfl`) and incomplete proofs (e.g., `by sorry` on non-first line) are missed.

**Deliverables**:

1. Create `scripts/check_proof_depth.py` that uses Lean's `--print-info` or
   `lake env lean --run` to extract proof term structure from the 7 invariant
   files. The script should:
   - Parse each file for `theorem.*preserves` declarations
   - Extract the proof body (everything after `:= by` until the next
     declaration or `end`)
   - Flag proofs where the body consists only of: `rfl`, `trivial`, `simp`,
     or any single tactic with no case analysis, induction, or substantive
     rewriting
   - Flag proofs containing `sorry` on any line (not just the first)

2. Integrate into Tier 0 hygiene as a replacement for the regex-based check:
   ```bash
   if command -v python3 >/dev/null 2>&1; then
     run_check "HYGIENE" python3 "${SCRIPT_DIR}/check_proof_depth.py" \
       "${THEOREM_CHECK_TARGETS[@]}"
   else
     # Fallback to regex for environments without Python
     # [existing regex check]
   fi
   ```

3. The script should output structured results:
   ```
   L-08 PASS: SeLe4n/Kernel/Scheduler/Invariant.lean (14 theorems, 0 trivial)
   L-08 PASS: SeLe4n/Kernel/IPC/Invariant.lean (23 theorems, 0 trivial)
   ```

**Files modified**:
- `scripts/check_proof_depth.py` — new file (~80 lines)
- `scripts/test_tier0_hygiene.sh` — replace regex block (lines 63–68) with
  Python call, keeping regex as fallback

**Proof maintenance**: None. This is a test infrastructure script.

**Exit evidence**:
- `check_proof_depth.py` correctly flags a deliberately inserted trivial
  multi-line proof (temporary, reverted)
- Existing regex check retained as fallback

#### Part B: Tier 3 Property Correctness Checks (R-05)

**Problem**: Tier 3 (`test_tier3_invariant_surface.sh`) verifies that
definitions and theorems **exist** at expected locations via ripgrep patterns
but does not verify they are **correct**. A broken function (e.g.,
`def vspaceMapPage := .error .mappingConflict`) or a theorem with `sorry`
body would pass Tier 3.

**Deliverables**:

1. Add a set of `#check` commands executed via `lake env lean` that verify
   critical theorem type signatures match expected invariant shapes. These do
   not re-prove theorems; they verify the theorem has the expected type.

   Example checks:
   ```bash
   # Verify scheduler preservation theorem has correct type
   run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean <<EOF
   import SeLe4n.Kernel.Scheduler.Operations
   #check @SeLe4n.Kernel.schedule_preserves_schedulerInvariantBundle
   EOF'

   # Verify VSpace map preservation exists and is not sorry
   run_check "INVARIANT" bash -lc 'source ~/.elan/env && lake env lean <<EOF
   import SeLe4n.Kernel.Architecture.VSpaceInvariant
   #check @SeLe4n.Kernel.Architecture.vspaceMapPage_success_preserves_vspaceInvariantBundle
   EOF'
   ```

2. Add at least 10 such checks covering critical preservation theorems across
   all 7 invariant subsystems:
   - Scheduler: `schedule_preserves_schedulerInvariantBundle`
   - Capability: `cspaceMint_preserves_capabilityInvariantBundle`
   - IPC: `endpointSendDual_preserves_ipcInvariantBundle`
   - Lifecycle: `lifecycleRetypeObject_preserves_lifecycleInvariantBundle`
   - Service: `serviceStart_preserves_serviceInvariantBundle`
   - VSpace: `vspaceMapPage_success_preserves_vspaceInvariantBundle`
   - InformationFlow: `step_preserves_projection`

3. These checks are Lean type-level; if a theorem is defined with `sorry`, the
   `#check` will still succeed (Lean accepts sorry-backed theorems). To catch
   sorry in theorem bodies specifically, combine with the L-08 enhancement
   from Part A.

**Files modified**:
- `scripts/test_tier3_invariant_surface.sh` — add `#check`-based correctness
  section after existing ripgrep-based existence checks

**Proof maintenance**: None. `#check` is read-only.

**Exit evidence**:
- `test_full.sh` passes with new Tier 3 checks
- Renaming a theorem (temporary, reverted) causes Tier 3 to fail with a
  clear error message

#### Part C: CDT Decomposition Lemmas for CSpace NI Proofs (R-15)

**Problem**: Four CSpace operations (`cspaceCopy`, `cspaceMove`,
`cspaceDeleteSlot`, `retypeFromUntyped`) take their underlying NI property
as a hypothesis in bridge theorems rather than proving it outright. This is
documented as pending CDT frame lemmas (WS-F4 deferral).

**Deliverables**:

1. Prove CDT frame lemmas establishing that CDT operations (add edge, remove
   edge, reparent) preserve the `projectState` low-equivalence relation when
   the affected nodes are non-observable:
   ```lean
   theorem addEdge_preserves_lowEquivalent
       (ctx : LabelingContext) (observer : IfObserver)
       (parent child : CdtNodeId)
       (hParentHigh : cdtNodeObservable ctx observer parent = false)
       (hChildHigh : cdtNodeObservable ctx observer child = false)
       (s₁ s₂ : SystemState)
       (hLow : lowEquivalent ctx observer s₁ s₂) :
       lowEquivalent ctx observer
         (s₁.addCdtEdge parent child op)
         (s₂.addCdtEdge parent child op)
   ```

2. Use the CDT frame lemmas to discharge the hypothesis in the four bridge
   theorems in `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean`.

3. Update the `NonInterferenceStep` composition in
   `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` to use the
   proven versions instead of hypothesis-carrying constructors.

**Files modified**:
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean` — add CDT frame lemmas
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` — discharge
  hypothesis in 4 bridge theorems
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean` — update
  constructors if needed

**Proof maintenance**: This IS proof work. Each new lemma must be proven without
sorry. The CDT projection is part of `projectState`, so frame lemmas must show
that CDT changes on non-observable nodes do not affect the observable projection.

**Proof sketch**:
- CDT edges are not part of `ObservableState` (the projection does not include
  CDT structure)
- CDT operations only modify `cdt`, `cdtSlotNode`, `cdtNodeSlot`, `cdtNextNode`
- These fields are not projected by `projectState`
- Therefore, CDT operations trivially preserve `lowEquivalent`
- The key insight: CDT is kernel-internal metadata, not observable state

**Exit evidence**:
- Zero sorry in the 4 bridge theorems
- `lake build` succeeds
- `test_full.sh` passes

#### Part D: VSpace Memory Projection Domain Ownership Model (R-16)

**Problem**: Memory content is not currently part of `ObservableState`
projection. Adding it requires a domain ownership model that maps memory
regions to security domains, enabling per-domain filtering of observable
memory content.

**Deliverables**:

1. Define a `MemoryDomainOwnership` structure mapping physical address ranges
   to security domains:
   ```lean
   structure MemoryDomainOwnership where
     regionOwner : PAddr → Option DomainId
   ```

2. Extend `LabelingContext` with an optional `memoryOwnership` field:
   ```lean
   structure LabelingContext where
     -- existing fields...
     memoryOwnership : Option MemoryDomainOwnership := none
   ```

3. When `memoryOwnership` is `some`, extend `projectState` to include
   observable memory regions (those owned by domains the observer can see).
   When `none`, memory projection is empty (backward-compatible with current
   behavior).

4. Prove that VSpace operations (`vspaceMapPage`, `vspaceUnmapPage`) preserve
   low-equivalence when the affected physical address region is owned by a
   non-observable domain.

**Files modified**:
- `SeLe4n/Kernel/InformationFlow/Policy.lean` — add `MemoryDomainOwnership`
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — extend `projectState`
  with optional memory projection
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` — prove VSpace
  NI under memory projection

**Proof maintenance**: Significant. Memory projection adds a new dimension to
`ObservableState` equality. All existing NI proofs must be shown compatible
(they are, because memory projection is opt-in via `Option`).

**Proof sketch**:
- When `memoryOwnership = none`: existing proofs unchanged (projection empty)
- When `memoryOwnership = some mo`: VSpace map/unmap on non-observable regions
  does not affect projected memory (observer cannot see those addresses)
- Backward compatibility: `none` is the default; all existing tests and proofs
  continue to work

**Exit evidence**:
- `MemoryDomainOwnership` structure defined
- `projectState` extended with backward-compatible memory projection
- At least one VSpace NI proof discharged under memory projection
- `lake build` succeeds with zero sorry
- Existing tests pass unchanged (backward compatibility)

---

### WS-I3: Test Coverage Expansion — Operations

**Objective**: Add multi-operation chain tests, scheduler stress tests, and
information-flow declassification tests to catch compositional bugs and
edge cases not covered by single-operation isolation tests.

**Priority**: MEDIUM — Phase 3
**Estimated effort**: 8–10 hours
**Dependencies**: WS-I1 recommended (chain tests benefit from inter-transition
assertions)
**Recommendations addressed**: R-06, R-07, R-08

#### Part A: Multi-Operation Chain Tests (R-06)

**Problem**: `NegativeStateSuite.lean` tests each operation in isolation on
fresh base states. Multi-operation sequences (retype → mint, send → send →
receive, map → lookup → unmap → lookup) are not validated. Compositional
bugs — where state corruption from one operation causes a subsequent operation
to silently misbehave — remain undetected.

**Deliverables**:

1. Add a new test file `tests/OperationChainSuite.lean` containing at least
   6 multi-operation chain tests:

   **Chain 1: Retype → Mint → Revoke**
   ```lean
   -- Retype from untyped, creating a new endpoint
   let (_, st1) ← expectOkState "chain: retype creates endpoint"
     (lifecycleRetypeObject authSlot untypedId .endpoint retypeArgs st0)
   -- Mint a capability from the new endpoint into a destination slot
   let (_, st2) ← expectOkState "chain: mint from retype result"
     (cspaceMint srcSlot dstSlot [.read, .grant] none st1)
   -- Revoke the entire subtree from the minted capability
   let (_, st3) ← expectOkState "chain: revoke minted subtree"
     (cspaceRevokeCdtStrict dstSlot st2)
   -- Verify: CDT is clean, no orphaned nodes
   assertStateInvariants "chain: retype→mint→revoke" st3
   ```

   **Chain 2: Send → Send → Receive (FIFO ordering)**
   ```lean
   -- Two threads send messages to the same endpoint
   let (_, st1) ← expectOkState "chain: send msg1"
     (endpointSendDual epId tid1 msg1 st0)
   let (_, st2) ← expectOkState "chain: send msg2"
     (endpointSendDual epId tid2 msg2 st1)
   -- Receive should get tid1's message first (FIFO)
   let ((recvMsg, senderId), st3) ← expectOkState "chain: receive"
     (endpointReceiveDual epId tid3 st2)
   -- Verify FIFO ordering
   if senderId = tid1 then ... else throw ...
   assertStateInvariants "chain: send→send→receive" st3
   ```

   **Chain 3: Map → Lookup → Unmap → Lookup (VSpace roundtrip)**
   ```lean
   let (_, st1) ← expectOkState "chain: map page"
     (vspaceMapPage asid vaddr paddr perms st0)
   let ((pa, _), _) ← expectOkState "chain: lookup after map"
     (vspaceLookup asid vaddr st1)
   if pa = paddr then ... else throw ...
   let (_, st2) ← expectOkState "chain: unmap page"
     (vspaceUnmapPage asid vaddr st1)
   expectError "chain: lookup after unmap"
     (vspaceLookup asid vaddr st2) .translationFault
   ```

   **Chain 4: Service Start → Start Dependent → Stop → Verify**
   ```lean
   let (_, st1) ← expectOkState "chain: start base service"
     (serviceStart baseSvcId st0)
   let (_, st2) ← expectOkState "chain: start dependent"
     (serviceStart depSvcId st1)
   let (_, st3) ← expectOkState "chain: stop base"
     (serviceStop baseSvcId st2)
   -- Dependent should remain running (stop does not cascade)
   -- but restart of dependent should fail if base is stopped
   ```

   **Chain 5: Copy → Move → Delete (CSpace lifecycle)**
   ```lean
   let (_, st1) ← expectOkState "chain: copy cap"
     (cspaceCopy srcSlot copyDst st0)
   let (_, st2) ← expectOkState "chain: move copied cap"
     (cspaceMove copyDst moveDst st1)
   let (_, st3) ← expectOkState "chain: delete moved cap"
     (cspaceDeleteSlot moveDst st2)
   assertStateInvariants "chain: copy→move→delete" st3
   ```

   **Chain 6: Notification Signal → Signal → Wait (badge accumulation)**
   ```lean
   let (_, st1) ← expectOkState "chain: signal badge 0x01"
     (notificationSignal ntfnId (Badge.ofNat 0x01) st0)
   let (_, st2) ← expectOkState "chain: signal badge 0x10"
     (notificationSignal ntfnId (Badge.ofNat 0x10) st1)
   let ((badge, _), st3) ← expectOkState "chain: wait"
     (notificationWait ntfnId tid st2)
   -- Verify badge is OR accumulation: 0x01 ||| 0x10 = 0x11
   if badge = Badge.ofNat 0x11 then ... else throw ...
   ```

2. Integrate into `scripts/test_tier2_negative.sh`:
   ```bash
   run_check "TRACE" lake env lean --run tests/OperationChainSuite.lean
   ```

**Files modified**:
- `tests/OperationChainSuite.lean` — new file (~250 lines)
- `scripts/test_tier2_negative.sh` — add execution line

**Proof maintenance**: None. These are runtime tests.

**Exit evidence**:
- All 6 chain tests pass
- `test_smoke.sh` passes with chain suite included

#### Part B: Scheduler Stress Tests (R-07)

**Problem**: Scheduler tests use only 2–3 threads for EDF tie-breaking. Bugs
under high concurrency (priority bucket overflow, non-deterministic HashMap
iteration leaking into selection order) remain undetected.

**Deliverables**:

1. Add parameterized scheduler stress tests to `tests/OperationChainSuite.lean`
   using the existing `buildParameterizedTopology` helper (MainTraceHarness.lean,
   line 1229):

   **Test 1: High Thread Count (16 threads)**
   ```lean
   let st := buildParameterizedTopology 16 10 4 1
   -- Run schedule 50 times, verify invariants every 10 steps
   let (_, finalSt) ← scheduleNTimes 50 st (assertEvery := 10)
   assertStateInvariants "scheduler-stress-16" finalSt
   ```

   **Test 2: Same Priority Contention (8 threads, all priority 100)**
   ```lean
   let st := buildParameterizedTopology 8 100 4 1
   -- All threads same priority — EDF must deterministically select
   -- Verify: chosen thread is consistent across 20 schedule calls
   ```

   **Test 3: Multi-Domain (4 domains, 4 threads each)**
   ```lean
   -- Build state with 16 threads across 4 domains
   -- Run domain switch + schedule in alternation
   -- Verify: threads only run in their assigned domain
   ```

2. Add a helper `scheduleNTimes` that iterates `schedule` N times with
   optional periodic invariant assertions.

**Files modified**:
- `tests/OperationChainSuite.lean` — add scheduler stress section

**Proof maintenance**: None.

**Exit evidence**:
- 16-thread stress test passes deterministically
- Same-priority contention produces consistent ordering
- Multi-domain test verifies domain isolation

#### Part C: Information-Flow Declassification Tests (R-08)

**Problem**: `InformationFlowSuite.lean` validates same-domain allow and
cross-domain deny paths but does not test controlled declassification
operations (`declassifyStore` in `Enforcement/Soundness.lean`).

**Deliverables**:

1. Add declassification test cases to `tests/InformationFlowSuite.lean`:

   **Test 1: Declassification requires flow to be denied normally**
   ```lean
   -- Setup: secret source, public destination
   -- Attempt declassifyStore with policy that authorizes downgrade
   -- Verify: succeeds (flow was denied normally, declass authorized)
   ```

   **Test 2: Declassification fails when normal flow is allowed**
   ```lean
   -- Setup: public source, public destination (same domain)
   -- Attempt declassifyStore
   -- Verify: fails with flowDenied (cannot declassify when flow is allowed)
   ```

   **Test 3: Declassification fails when policy denies**
   ```lean
   -- Setup: secret source, public destination
   -- Attempt declassifyStore with policy that does NOT authorize
   -- Verify: fails with declassificationDenied
   ```

   **Test 4: Multi-level lattice (3 domains)**
   ```lean
   -- Setup: 3-domain linear order (0 < 1 < 2)
   -- Verify: domain 2 → domain 0 denied
   -- Verify: domain 2 → domain 0 with declassification succeeds
   -- Verify: domain 0 → domain 2 allowed normally (no declassification needed)
   ```

2. Each test should validate both the return value and the resulting state
   (if successful, the capability was transferred).

**Files modified**:
- `tests/InformationFlowSuite.lean` — add declassification test section
  (~60 lines)

**Proof maintenance**: None. Runtime tests only.

**Exit evidence**:
- All 4 declassification tests pass
- `test_smoke.sh` passes

---

### WS-I4: Test Coverage Expansion — Subsystems

**Objective**: Add targeted tests for VSpace multi-ASID coherency, IPC
interleaved send ordering, and lifecycle cascading operations.

**Priority**: LOW — Phase 3
**Estimated effort**: 4–6 hours
**Dependencies**: WS-I1 recommended
**Recommendations addressed**: R-09, R-10, R-11

#### Part A: VSpace Multi-ASID Sharing Tests (R-09)

**Problem**: VSpace tests cover single-ASID operations and cross-ASID
isolation, but do not test shared physical pages (same PAddr mapped into
two different ASIDs) or coherency after unmap in one ASID.

**Deliverables**:

1. Add test cases to `tests/OperationChainSuite.lean`:

   **Test 1: Shared page across ASIDs**
   ```lean
   -- Map paddr=0x1000 into ASID 1 at vaddr 0x2000
   -- Map paddr=0x1000 into ASID 2 at vaddr 0x3000
   -- Verify: both lookups return paddr=0x1000
   -- Unmap from ASID 1
   -- Verify: ASID 2 lookup still returns paddr=0x1000
   -- Verify: ASID 1 lookup returns translationFault
   ```

   **Test 2: Different permissions on shared page**
   ```lean
   -- Map paddr=0x1000 into ASID 1 with read-only
   -- Map paddr=0x1000 into ASID 2 with read-write
   -- Verify: permissions are per-ASID (ASID 1 read-only, ASID 2 read-write)
   -- W^X not violated (neither is write+execute)
   ```

**Files modified**:
- `tests/OperationChainSuite.lean` — add VSpace multi-ASID section

#### Part B: IPC Interleaved Send Tests (R-10)

**Problem**: IPC tests validate single sender → single receiver paths but do
not test multiple concurrent senders on the same endpoint with interleaved
operations.

**Deliverables**:

1. Add test cases:

   **Test 1: Three senders, FIFO ordering**
   ```lean
   -- Thread A sends msg_a to endpoint E
   -- Thread B sends msg_b to endpoint E
   -- Thread C sends msg_c to endpoint E
   -- Thread D receives from E → should get msg_a (first sender)
   -- Thread D receives from E → should get msg_b (second sender)
   -- Thread D receives from E → should get msg_c (third sender)
   ```

   **Test 2: Interleaved send/receive**
   ```lean
   -- Thread A sends to E
   -- Thread D receives from E (gets A's message)
   -- Thread B sends to E
   -- Thread D receives from E (gets B's message)
   -- Verify: no queue corruption between interleaved ops
   ```

**Files modified**:
- `tests/OperationChainSuite.lean` — add IPC interleaving section

#### Part C: Lifecycle Transaction Chain Tests (R-11)

**Problem**: Lifecycle tests validate single retype/revoke/delete operations
but not cascading multi-level revoke or authority degradation chains.

**Deliverables**:

1. Add test cases:

   **Test 1: Cascading revoke (grandparent → parent → child)**
   ```lean
   -- Mint: root → child_a (copy)
   -- Mint: child_a → grandchild_b (mint)
   -- Revoke root → should delete child_a AND grandchild_b
   -- Verify: CDT completely clean, no orphaned nodes
   ```

   **Test 2: Authority degradation chain**
   ```lean
   -- Root has {read, write, grant}
   -- Mint with rights attenuation: root → child with {read, write}
   -- Mint with further attenuation: child → grandchild with {read}
   -- Verify: grandchild has only {read}
   -- Verify: grandchild cannot mint (no grant right)
   ```

**Files modified**:
- `tests/OperationChainSuite.lean` — add lifecycle chain section

**Exit evidence (all of WS-I4)**:
- All VSpace, IPC, and lifecycle chain tests pass
- `test_smoke.sh` passes
- No sorry introduced

---

### WS-I5: Documentation & Code Quality Polish

**Objective**: Close documentation gaps identified in the audit, improve
developer guidance for test infrastructure, and apply minor code quality
improvements that were deferred.

**Priority**: LOW — Phase 3
**Estimated effort**: 4–6 hours
**Dependencies**: None (fully independent)
**Recommendations addressed**: R-12, R-13, R-14, R-17, R-18

#### Part A: Document RegName/RegValue Design Decision (R-12)

**Problem**: `Machine.lean` defines `RegName` and `RegValue` as `abbrev Nat`
(lines 14, 17), inconsistent with the typed-identifier convention used for all
other identifiers (wrapper structures in `Prelude.lean`). The design decision
is intentional but undocumented.

**Deliverables**:

1. Add a documentation comment block above lines 14–17 in `Machine.lean`:
   ```lean
   /-- Register names and values are intentionally defined as bare `Nat` aliases
   (not wrapper structures like `ObjId`, `ThreadId`, etc.) for two reasons:

   1. **Abstract machine simplicity**: The register file is a mathematical
      function `RegName → RegValue` used only within `MachineState`. It never
      interacts with kernel object identifiers, so the type-safety benefit of
      wrapping is minimal while the syntactic overhead is significant.

   2. **Proof ergonomics**: Register read-after-write lemmas
      (`readReg_writeReg_eq`, `readReg_writeReg_ne`) rely on `Nat` decidable
      equality for `if r' = r then v else rf.gpr r'`. Wrapping would require
      additional `DecidableEq` boilerplate with no safety improvement.

   See `SeLe4n/Prelude.lean` for the project's typed-identifier convention and
   the rationale for wrapping kernel-facing identifiers. -/
   ```

**Files modified**:
- `SeLe4n/Machine.lean` — add documentation comment (~12 lines)

#### Part B: Information-Flow Architecture Readers' Guide (R-13)

**Problem**: The three-layer information-flow proof architecture (enforcement →
bridge → composition) is sophisticated but has no readers' guide explaining how
the layers connect.

**Deliverables**:

1. Create `docs/guides/INFORMATION_FLOW_ARCHITECTURE.md` with:
   - Overview diagram (ASCII art) showing the three layers
   - Layer 1 (Enforcement): Purpose, key files
     (`Enforcement/Wrappers.lean`, `Enforcement/Soundness.lean`), 7 policy-gated
     wrappers listed with their flow checks
   - Layer 2 (Non-Interference): Purpose, key files
     (`Invariant/Operations.lean`, `Invariant/Helpers.lean`), bridge theorem
     pattern explained with one concrete example
   - Layer 3 (Composition): Purpose, key files
     (`Invariant/Composition.lean`), 22-operation `NonInterferenceStep`
     inductive, trace composition theorem
   - How to verify NI for a new operation (step-by-step guide)
   - Current proof status table (26/30 fully proved, 4 deferred with
     prerequisites)

**Files modified**:
- `docs/guides/INFORMATION_FLOW_ARCHITECTURE.md` — new file (~200 lines)

#### Part C: Test Fixture Update Process Documentation (R-14)

**Problem**: When trace output changes (intentionally or not), developers must
update `tests/fixtures/main_trace_smoke.expected`. The current guidance is a
single log line in `test_tier2_trace.sh` (line 111). No documented process
exists for verifying the change is intentional.

**Deliverables**:

1. Add a section to `docs/DEVELOPMENT.md` under a new heading "Updating Test
   Fixtures":
   ```markdown
   ## Updating Test Fixtures

   When a code change alters the trace output of `lake exe sele4n`, the Tier 2
   trace fixture comparison (`test_tier2_trace.sh`) will fail. To update the
   fixture:

   1. Run the trace and capture new output:
      ```bash
      source ~/.elan/env && lake exe sele4n > /tmp/new_trace.txt
      ```

   2. Compare with the existing fixture:
      ```bash
      diff tests/fixtures/main_trace_smoke.expected /tmp/new_trace.txt
      ```

   3. For each changed line, verify:
      - The change is a direct consequence of your code change
      - The new output is semantically correct (not a regression)
      - The scenario ID (if present) still maps to the correct test function

   4. Update the fixture file with the new expectations.

   5. In your PR description, include a "Fixture Changes" section explaining
      why each expectation changed.
   ```

**Files modified**:
- `docs/DEVELOPMENT.md` — add fixture update section (~30 lines)

#### Part D: HashMap.fold Migration (R-17)

**Problem**: `detachCNodeSlots` in capability operations uses `.toList.foldl`
instead of `.fold` for HashMap iteration. The `.fold` variant avoids an
intermediate list allocation.

**Deliverables**:

1. Identify all `.toList.foldl` or `.toList.foldr` patterns on HashMap values
   in the production Lean source.

2. Where proof tooling permits (the replacement does not break existing
   theorems), migrate to `.fold`.

3. Where proof tooling does not permit (HashMap.fold lemmas are insufficient
   for existing proof obligations), document the limitation inline and defer.

**Files modified**:
- `SeLe4n/Kernel/Capability/Operations.lean` — migrate if proof-safe
- Other files as identified in step 1

**Proof maintenance**: Low. HashMap.fold and toList.foldl produce the same
result; the proof obligation is showing equivalence.

#### Part E: Metrics Regeneration Automation (R-18)

**Problem**: Documentation metrics (production LoC, test LoC, proved
declarations, total declarations) must be manually regenerated via
`./scripts/generate_codebase_map.py --pretty` and propagated to 8+ files.
This is error-prone and leads to stale metrics.

**Deliverables**:

1. Create `scripts/sync_documentation_metrics.sh` that:
   - Runs `./scripts/generate_codebase_map.py --pretty` to regenerate
     `docs/codebase_map.json`
   - Extracts `readme_sync` values from the JSON
   - Updates `README.md`, `docs/spec/SELE4N_SPEC.md`, and GitBook files
     using `sed` with the extracted values
   - Runs `test_docs_sync.sh` to verify consistency

2. Add as a recommended pre-PR step in `docs/DEVELOPMENT.md`:
   ```markdown
   ## Before Submitting a PR

   If your changes modify Lean source files, regenerate documentation metrics:
   ```bash
   ./scripts/sync_documentation_metrics.sh
   ```
   ```

**Files modified**:
- `scripts/sync_documentation_metrics.sh` — new file (~40 lines)
- `docs/DEVELOPMENT.md` — add pre-PR step

**Exit evidence (all of WS-I5)**:
- `Machine.lean` documents RegName/RegValue rationale
- IF readers' guide exists and is accurate
- Fixture update process documented
- HashMap.fold migrated where proof-safe
- Metrics sync script works end-to-end

---

## 6. Coverage Verification

Every recommendation from the v0.14.9 audit is accounted for in exactly one
workstream:

| Recommendation | WS | Part | Status |
|---------------|----|------|--------|
| R-01: Inter-transition invariant assertions | WS-I1 | A | Planned |
| R-02: Mandatory determinism validation | WS-I1 | B | Planned |
| R-03: Scenario ID traceability | WS-I1 | C | Planned |
| R-04: Semantic L-08 proof validation | WS-I2 | A | Planned |
| R-05: Tier 3 property correctness checks | WS-I2 | B | Planned |
| R-06: Multi-operation chain tests | WS-I3 | A | Planned |
| R-07: Scheduler stress tests | WS-I3 | B | Planned |
| R-08: Declassification tests | WS-I3 | C | Planned |
| R-09: VSpace multi-ASID sharing tests | WS-I4 | A | Planned |
| R-10: IPC interleaved send tests | WS-I4 | B | Planned |
| R-11: Lifecycle transaction chain tests | WS-I4 | C | Planned |
| R-12: RegName/RegValue documentation | WS-I5 | A | Planned |
| R-13: IF architecture readers' guide | WS-I5 | B | Planned |
| R-14: Fixture update process documentation | WS-I5 | C | Planned |
| R-15: CDT decomposition lemmas | WS-I2 | C | Planned |
| R-16: VSpace memory projection model | WS-I2 | D | Planned |
| R-17: HashMap.fold migration | WS-I5 | D | Planned |
| R-18: Metrics regeneration automation | WS-I5 | E | Planned |

**Coverage**: 18/18 recommendations assigned. Zero orphans.

---

## 7. Risk Assessment

| Risk | Likelihood | Impact | Mitigation |
|------|-----------|--------|------------|
| Inter-transition assertions add significant runtime overhead to trace harness | Medium | Low | Assert every 3–5 ops, not every op. Measure wall-clock time delta; if >2x, reduce frequency |
| CDT frame lemmas (WS-I2C) are harder than anticipated | Low | Medium | CDT is not projected; lemmas should be trivial. If blocked, document as tracked deferral with TPI-D annotation |
| VSpace memory projection (WS-I2D) requires extensive re-proof | Medium | Medium | Use `Option` wrapper for backward compatibility. If re-proof effort exceeds 1 week, defer to hardware-binding workstream (H3) where VSpace backend is fully implemented |
| Scenario ID changes break existing CI/CD fixture matching | Low | Low | Fixture format already supports pipe-delimited fields; IDs are additive, not replacing existing fragments |
| Determinism check doubles smoke test runtime | Medium | Low | Trace harness runs in ~2 seconds; doubling to ~4 seconds is acceptable. If `lake build` is the bottleneck, determinism check adds negligible time |
| Multi-operation chain tests create maintenance burden | Low | Low | Chain tests reuse existing `BootstrapBuilder` and `expectOkState` infrastructure. Maintenance cost proportional to single-operation tests |
| HashMap.fold migration breaks existing proofs | Medium | Low | Migrate only where proof-safe. Document limitations inline. Fall back to `.toList.foldl` where needed |
| Semantic L-08 script has false positives | Medium | Low | Keep regex as fallback. Script should flag, not fail, on uncertain cases. Manual review for flagged items |

---

## 8. Execution Summary

### Parallelism Opportunities

- **WS-I1** and **WS-I2** are independent and can execute in parallel
- **WS-I3**, **WS-I4**, and **WS-I5** are independent of each other and can
  execute in parallel after WS-I1 completes
- Within WS-I2, Parts A/B (testing) are independent of Parts C/D (proofs)
- Within WS-I5, all 5 parts are independent

### Estimated Effort Summary

| Workstream | Parts | Est. Hours | Files Modified | New Files |
|------------|-------|-----------|----------------|-----------|
| WS-I1 | A, B, C | 6–8 | 5 | 3 |
| WS-I2 | A, B, C, D | 10–14 | 6 | 1 |
| WS-I3 | A, B, C | 8–10 | 2 | 1 |
| WS-I4 | A, B, C | 4–6 | 1 | 0 |
| WS-I5 | A, B, C, D, E | 4–6 | 5 | 3 |
| **Total** | **18 parts** | **32–44** | **~19** | **~8** |

### Command Evidence Patterns

Each workstream's exit criteria can be verified by the following commands:

```bash
# WS-I1: Critical Infrastructure
source ~/.elan/env && lake build                # Build succeeds
./scripts/test_smoke.sh                         # Smoke passes with determinism
python3 scripts/scenario_catalog.py validate-registry  # Scenario IDs valid

# WS-I2: Proof & Validation Depth
source ~/.elan/env && lake build                # Zero sorry in NI proofs
./scripts/test_full.sh                          # Full suite passes
python3 scripts/check_proof_depth.py SeLe4n/Kernel/*/Invariant.lean  # L-08 semantic

# WS-I3: Coverage Expansion — Operations
lake env lean --run tests/OperationChainSuite.lean  # Chain tests pass
./scripts/test_smoke.sh                             # All tiers pass

# WS-I4: Coverage Expansion — Subsystems
lake env lean --run tests/OperationChainSuite.lean  # Subsystem tests pass
./scripts/test_smoke.sh                             # All tiers pass

# WS-I5: Documentation & Polish
source ~/.elan/env && lake build                    # Build clean
./scripts/sync_documentation_metrics.sh             # Metrics in sync
./scripts/test_docs_sync.sh                         # Docs sync passes
```

### Confidence Projection

| State | Testing Confidence | Evidence |
|-------|-------------------|----------|
| **Current (v0.14.9)** | MEDIUM | Broad coverage; vulnerable to state corruption and compositional bugs |
| **After WS-I1** | HIGH | Inter-transition checks + mandatory determinism eliminate most risks |
| **After WS-I1 + WS-I2** | HIGH+ | Semantic proof validation + CDT lemmas strengthen proof surface |
| **After Full Portfolio** | VERY HIGH | Comprehensive coverage across all dimensions; all audit recommendations addressed |

---

## 9. Canonical References

- **Baseline audit**: `docs/audits/AUDIT_CODEBASE_v0.13.6.md`
- **Prior workstream plans**: `docs/audits/AUDIT_v0.12.15_WORKSTREAM_PLAN.md`,
  `docs/audits/AUDIT_v0.12.2_WORKSTREAM_PLAN.md`
- **Workstream history**: `docs/WORKSTREAM_HISTORY.md`
- **Development conventions**: `docs/DEVELOPMENT.md`
- **Testing infrastructure**: `SeLe4n/Testing/`, `tests/`, `scripts/test_*.sh`
- **Information-flow proof surface**: `SeLe4n/Kernel/InformationFlow/`
- **Invariant proof surface**: `SeLe4n/Kernel/*/Invariant*.lean`

