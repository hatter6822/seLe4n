# WS-H Workstream Plan — v0.12.15 Audit Remediation

**Created:** 2026-03-02
**Findings baseline:** [`AUDIT_CODEBASE_v0.12.15_v1.md`](AUDIT_CODEBASE_v0.12.15_v1.md), [`AUDIT_CODEBASE_v0.12.15_v2.md`](AUDIT_CODEBASE_v0.12.15_v2.md)
**Prior portfolio:** WS-G (kernel performance optimization, WS-G1..G9 completed at v0.12.15)
**Project direction:** Production microkernel targeting Raspberry Pi 5 (ARM64)
**Constraint:** No sorry/axiom — all changes preserve the zero-escape-hatch proof surface

---

## 1. Planning Objective

Close all findings from two independent v0.12.15 codebase audits, advancing the
kernel from "strong with actionable gaps" to production-ready. Combined findings
from both audits: **10 CRITICAL, 14 HIGH, 21 MEDIUM** across correctness bugs,
proof coverage gaps, model fidelity limitations, information-flow incompleteness,
and infrastructure debt.

After deduplication (18 findings overlap between the two audits), there are
**~56 distinct findings** organized into **16 workstreams across 5 execution
phases**. The critical path runs through Phase 1 (correctness bugs) and Phase 2
(proof surface strengthening), which must complete before any stable release claim.
Phase 3 (information flow) is required before any security certification claim.
Phases 4-5 (model fidelity, quality) advance toward hardware deployment readiness.

## 2. Planning Principles

1. **Correctness first**: semantic bugs (C-01) and safety guard failures (H-05, H-06)
   are fixed before proof extensions. A correct kernel with fewer proofs is always
   preferable to a buggy kernel with more proofs.
2. **Proof-first implementation**: no operation ships without invariant preservation
   theorems. New predicates must be non-trivially meaningful (lesson from C-03).
3. **Evidence-gated**: every workstream closes with reproducible command evidence.
4. **Coherent slices**: each workstream is a self-contained, independently testable
   change with clear entry and exit criteria.
5. **No sorry/axiom**: zero tolerance in production proof surface.
6. **Deterministic semantics**: all transitions remain explicit success/failure.
7. **Foundation-first ordering**: infrastructure changes (HashMap BEq, state field
   migration) land before subsystem-specific proof work that depends on them.
8. **Canonical-first docs**: root docs updated before GitBook mirrors.

---

## 3. Finding-to-Workstream Matrix

### Cross-reference: v1 audit (A-01..A-45) + v2 audit (C-01..C-05, H-01..H-12, M-01..M-21)

| v1 Finding | v2 Finding | Severity | Description | Workstream |
|------------|------------|----------|-------------|------------|
| — | C-01 | CRITICAL | endpointCall blocking path semantic bug | WS-H1 |
| — | M-02 | MEDIUM | endpointReply doesn't verify caller-target | WS-H1 |
| A-26, A-27 | H-06 | HIGH | retypeFromUntyped childId collision/freshness | WS-H2 |
| — | H-05 | HIGH | TCB retype without scheduler/IPC cleanup | WS-H2 |
| A-11 | — | HIGH | CDT slot-node cleanup on CNode replacement | WS-H2 |
| A-28 | — | MEDIUM | Non-atomic dual-store in retypeFromUntyped | WS-H2 |
| — | H-12 | HIGH | run_check returns success on failure | WS-H3 |
| — | M-19 | MEDIUM | CI doesn't run test_docs_sync.sh | WS-H3 |
| — | M-20 | MEDIUM | Tier 3 hard-depends on rg without fallback | WS-H3 |
| — | C-03 | CRITICAL | Capability invariant bundle trivially true | WS-H4 |
| A-20 | M-08 | HIGH | CDT completeness not proven | WS-H4 |
| — | M-03 | MEDIUM | CDT acyclicity not maintained after addEdge | WS-H4 |
| — | M-07 | MEDIUM | cspaceRevokeCdt swallows deletion failures | WS-H4 |
| A-22 | C-04 | CRITICAL | No intrusive queue structural invariant | WS-H5 |
| A-23 | — | HIGH | Unvalidated queue link dereference | WS-H5 |
| A-24 | — | HIGH | Message extraction after popHead loses data | WS-H5 |
| A-14, A-15 | H-08 | CRITICAL | EDF + timeSlice invariants zero proofs | WS-H6 |
| A-16, A-17 | M-05, M-06 | HIGH | maxPriority cache + chooseBest unproven | WS-H6 |
| — | M-04 | MEDIUM | Missing RunQueue.flat_wf_rev invariant | WS-H6 |
| A-07 | — | CRITICAL | BEq for HashMap types uses toList order | WS-H7 |
| A-10 | H-09 | CRITICAL | Function-typed state fields (closure chains) | WS-H7 |
| A-35 | H-07 | CRITICAL | Enforcement-NI bridge disconnected | WS-H8 |
| A-36, A-37 | H-11 | HIGH | Domain timing / TCB metadata visible | WS-H8 |
| A-40 | C-02 | CRITICAL | NI coverage ~25% of kernel operations | WS-H9 |
| — | M-15 | MEDIUM | NonInterferenceStep inductive not exhaustive | WS-H9 |
| A-38 | C-05 | CRITICAL | MachineState not projected in IF model | WS-H10 |
| A-34 | — | CRITICAL | Non-standard security lattice | WS-H10 |
| A-39 | — | MEDIUM | No declassification model | WS-H10 |
| — | M-16 | MEDIUM | Per-endpoint flow override not well-formed | WS-H10 |
| A-32 | H-02 | HIGH | VSpace flat HashMap, no page permissions | WS-H11 |
| — | H-10 | HIGH | No TLB/cache maintenance model | WS-H11 |
| A-05 | M-12 | HIGH | endAddr overflow / physical width unchecked | WS-H11 |
| A-12 | — | HIGH | No global ASID uniqueness invariant | WS-H11 |
| — | M-14 | MEDIUM | boundedAddressTranslation not integrated | WS-H11 |
| — | H-04 | HIGH | Running thread stays in ready queue | WS-H12 |
| A-08 | M-01 | HIGH | Redundant legacy endpoint fields | WS-H12 |
| A-09 | — | HIGH | IpcMessage unbounded payload | WS-H12 |
| A-25 | — | MEDIUM | Legacy O(n) IPC retained without path | WS-H12 |
| — | H-03 | HIGH | No per-TCB register context | WS-H12 |
| — | H-01 | HIGH | No multi-level CSpace resolution | WS-H13 |
| A-29 | — | HIGH | Service ops don't verify backing-object | WS-H13 |
| A-21 | — | MEDIUM | cspaceMove not atomic | WS-H13 |
| A-30 | — | MEDIUM | Service restart partial-failure | WS-H13 |
| A-31 | M-17 | MEDIUM | serviceCountBounded not maintained | WS-H13 |
| A-02 | — | HIGH | Typed identifier wrappers bypassable | WS-H14 |
| A-01 | — | MEDIUM | Inhabited defaults generate sentinels | WS-H14 |
| A-03 | — | MEDIUM | Missing EquivBEq instances | WS-H14 |
| A-04 | M-11 | MEDIUM | No LawfulMonad for KernelM | WS-H14 |
| A-06 | — | MEDIUM | isPowerOfTwo correctness unproven | WS-H14 |
| — | M-09 | MEDIUM | Prelude identifier boilerplate (~390 lines) | WS-H14 |
| — | M-10 | MEDIUM | OfNat instances defeat type safety | WS-H14 |
| A-41 | — | MEDIUM | RPi5 platform stubs minimal | WS-H15 |
| A-42 | — | MEDIUM | No capability-checking at API boundary | WS-H15 |
| A-33 | — | MEDIUM | Adapter depends on parameterized contracts | WS-H15 |
| — | M-13 | MEDIUM | InterruptBoundaryContract no decidability | WS-H15 |
| A-43 | — | MEDIUM | Tier 3 tests anchor-based, not proof-based | WS-H16 |
| A-45 | M-21 | MEDIUM | Documentation statistics outdated | WS-H16 |
| A-13 | — | MEDIUM | objectIndex grows without bounds proof | WS-H16 |
| — | M-18 | MEDIUM | No negative tests for lifecycle ops | WS-H16 |
| A-18 | — | MEDIUM | O(n) membership check in schedule | WS-H16 |
| A-19 | — | MEDIUM | threadPriority consistency implicit | WS-H16 |

---

## 4. Phase Overview

| Phase | Focus | Workstreams | Blocking? |
|-------|-------|-------------|-----------|
| **1** | Critical Correctness | WS-H1, WS-H2, WS-H3 | Yes — before next release |
| **2** | Proof Surface Strengthening | WS-H4, WS-H5, WS-H6, WS-H7 | Yes — before stable release |
| **3** | Information Flow Hardening | WS-H8, WS-H9, WS-H10 | Yes — before security claims |
| **4** | seL4 Model Fidelity | WS-H11, WS-H12, WS-H13 | Before hardware deployment |
| **5** | Quality & Maintenance | WS-H14, WS-H15, WS-H16 | Ongoing improvement |

### Dependency Graph

```
Phase 1 (parallel):  WS-H1 ──┐
                     WS-H2 ──┼── Phase 2 gate
                     WS-H3 ──┘
Phase 2:             WS-H7 ──→ WS-H4, WS-H5, WS-H6  (H7 foundation-first)
Phase 3:             WS-H6 ──→ WS-H9  (scheduler proofs needed for scheduler NI)
                     WS-H5 ──→ WS-H9  (IPC invariants needed for IPC NI)
                     WS-H8, WS-H9 ──→ WS-H10  (bridge + coverage before model)
Phase 4:             WS-H7 ──→ WS-H11, WS-H12a  (HashMap state needed)
                     WS-H1, WS-H5 ──→ WS-H12a  (IPC fix + dual-queue invariant before legacy removal)
                     WS-H12a ──→ WS-H12b ──→ WS-H12c  (sequential: cleanup → dispatch → context)
                     WS-H12a ──→ WS-H12d  (parallel with H12b/c: message bounds)
                     WS-H12b, WS-H12c, WS-H12d ──→ WS-H12e ──→ WS-H12f
Phase 5:             Independent — can interleave with Phases 2-4
```

---

## 5. Workstream Definitions

### WS-H1: IPC Call-Path Semantic Fix (CRITICAL)

**Objective:** Fix the `endpointCall` blocking-path semantic bug where a blocked
caller erroneously transitions to `.ready` instead of `blockedOnReply` when a
receiver later dequeues the sender, and add reply-target scoping to `endpointReply`.

**Entry criteria:** Current codebase compiles with zero sorry. `test_smoke.sh` passes.

**Findings addressed:**
- **C-01** (CRITICAL): `endpointCall` blocking path — when no receiver is available,
  the caller enqueues on `sendQ` with `blockedOnSend`. When a receiver later
  processes this sender via `endpointReceiveDual`, the sender transitions to
  `.ready` instead of `blockedOnReply`, violating the Call contract (caller must
  remain blocked awaiting a reply).
- **M-02** (MEDIUM): `endpointReply` only checks `blockedOnReply` state but does
  not verify the replier is the intended server. Any thread can reply to any
  blocked thread, creating a confused-deputy risk.

**Deliverables:**

*Part A — blockedOnCall IPC state:*
1. Add `blockedOnCall` variant to the IPC state enum in `Model/Object.lean`.
   A Call sender blocked on the send queue carries `blockedOnCall endpointId`
   (distinct from `blockedOnSend endpointId`) to signal that upon dequeue, it
   should transition to `blockedOnReply`, not `.ready`.
2. Update `endpointCall` in `IPC/DualQueue.lean` to use `blockedOnCall` when
   enqueuing on the send queue (no-receiver path).
3. Update `endpointReceiveDual` to check for `blockedOnCall` on the dequeued
   sender: if Call, transition to `blockedOnReply` (not `.ready`); if Send,
   transition to `.ready` as before.
4. Update all pattern matches on IPC state to handle the new variant (exhaustive
   match compilation will guide this).
5. Update `ipcSchedulerContractPredicates` to include `blockedOnCall` in the
   "not runnable" set alongside `blockedOnSend` and `blockedOnReceive`.

*Part B — Reply target scoping:*
6. Add an optional `replyTarget : Option ThreadId` field to the `blockedOnReply`
   state, recording which server thread is authorized to reply.
7. Update `endpointReply` to validate that the replier matches `replyTarget`
   (when set). Return an error if a non-authorized thread attempts to reply.
8. Update `endpointCall` to populate `replyTarget` with the receiver's ThreadId
   when a direct rendezvous occurs, or leave it `none` when enqueuing (the
   receiver is unknown at enqueue time; it is set when `endpointReceiveDual`
   dequeues the Call sender).

*Part C — Proof maintenance:*
9. Re-prove all IPC invariant preservation theorems in `IPC/Invariant.lean` for
   the updated state transitions. The compositional proof architecture should
   require only local updates where `blockedOnCall` cases parallel existing
   `blockedOnSend` cases.
10. Add new theorem: `endpointCall_blocked_stays_blocked` — a Call sender that
    enters `blockedOnCall` does not become runnable until explicitly replied to.
11. Update `ipcSchedulerContractPredicates` preservation proofs.

**Files modified:**
- `SeLe4n/Model/Object.lean` — IPC state enum, `blockedOnReply` variant
- `SeLe4n/Kernel/IPC/DualQueue.lean` — `endpointCall`, `endpointReceiveDual`,
  `endpointReply`, `endpointReplyRecv`
- `SeLe4n/Kernel/IPC/Invariant.lean` — preservation theorems
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — projection updates for new state
- `SeLe4n/Testing/MainTraceHarness.lean` — trace scenarios
- `tests/fixtures/main_trace_smoke.expected` — updated expected output

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- New trace scenario demonstrates: Call → block on sendQ → receiver dequeues →
  caller transitions to `blockedOnReply` (not `.ready`) → explicit Reply unblocks.
- `endpointCall_blocked_stays_blocked` theorem compiles.

**Dependencies:** None. This is the highest-priority correctness fix.

---

### WS-H2: Lifecycle Safety Guards (HIGH) — COMPLETED (v0.12.16)

**Objective:** Harden lifecycle operations with runtime safety checks that match
the preconditions assumed by invariant proofs, preventing silent object overwrites,
dangling scheduler/IPC references, and stale CDT entries.

**Entry criteria:** Current codebase compiles with zero sorry. `test_smoke.sh` passes.

**Findings addressed:**
- **H-05** (HIGH): `lifecycleRetypeObject` does not clean up scheduler queues or
  IPC endpoint references when replacing a TCB. The theorem
  `lifecycleRetypeObject_ok_runnable_membership` *proves* the dangling reference
  persists — a retyped TCB's ThreadId can remain in the run queue pointing at
  what is now an endpoint.
- **H-06 / A-26 / A-27** (HIGH): `retypeFromUntyped` does not verify
  `childId ≠ untypedId` or that `childId` is globally unused. Silent overwrite
  of existing objects. The freshness hypothesis (`hFresh`) in proofs is never
  dynamically validated.
- **A-11** (HIGH): CDT slot-node cleanup incomplete — when a CNode is replaced
  via `storeObject`, `cdtSlotNode` and `cdtNodeSlot` mappings for orphaned slots
  are not cleaned up, leaving dangling CDT references.
- **A-28** (MEDIUM): Non-atomic dual-store in `retypeFromUntyped` — two sequential
  `storeObject` calls lack transactional semantics. If the second fails, the
  untyped watermark is advanced but no child was created.

**Deliverables:**

*Part A — TCB retype cleanup (H-05):*
1. Add a `cleanupTcbReferences` helper that, given a ThreadId being retyped away:
   - Removes the ThreadId from the scheduler run queue (`removeRunnable`).
   - Scans IPC endpoint queues for the ThreadId and dequeues it (both legacy
     and dual-queue paths).
   - Clears any `blockedOnSend/blockedOnReceive/blockedOnReply` references.
2. Call `cleanupTcbReferences` in `lifecycleRetypeObject` before the `storeObject`
   call, guarded by a check that the object being replaced is a `.tcb`.
3. Prove: `lifecycleRetypeObject_ok_runnable_no_dangling` — after retype of a
   TCB, the old ThreadId is not in the run queue.

*Part B — childId validation (H-06/A-26/A-27):*
4. Add explicit runtime checks to `retypeFromUntyped`:
   - `childId ≠ untypedId` — return error if self-overwrite attempted.
   - `st.objects.find? childId = none` — return error if childId collides with
     an existing object.
5. Remove the `hFresh` hypothesis from invariant proofs and derive it from the
   new runtime check (the proof obligation shifts from precondition to operation
   semantics).

*Part C — CDT cleanup on CNode replacement (A-11):*
6. Add a `detachCNodeSlots` helper that iterates the CNode's slot HashMap and
   removes each `(CPtr, Slot)` pair from `cdtSlotNode`/`cdtNodeSlot`.
7. Call `detachCNodeSlots` in `storeObject` when the existing object at the target
   ObjId is a `.cnode` and the replacement is not a `.cnode`.
8. Prove: CDT slot references are consistent after CNode replacement.

*Part D — Atomic retype (A-28):*
9. Refactor `retypeFromUntyped` to compute both the updated untyped and the new
   child object before performing any state mutations, then apply both updates
   in a single composed state transition. If either computation fails, no state
   changes occur.

**Files modified:**
- `SeLe4n/Kernel/Lifecycle/Operations.lean` — `retypeFromUntyped`, `lifecycleRetypeObject`
- `SeLe4n/Kernel/Lifecycle/Invariant.lean` — updated preservation proofs
- `SeLe4n/Model/State.lean` — `storeObject` CDT cleanup, `cleanupTcbReferences`
- `SeLe4n/Kernel/Scheduler/Operations.lean` — `removeRunnable` if not already exposed
- `SeLe4n/Testing/MainTraceHarness.lean` — trace scenarios for retype safety
- `tests/NegativeStateSuite.lean` — negative tests for childId collision, self-overwrite

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- Negative test: `retypeFromUntyped` with existing `childId` returns error.
- Negative test: `retypeFromUntyped` with `childId = untypedId` returns error.
- Trace scenario: retype a TCB, verify ThreadId removed from run queue.
- `lifecycleRetypeObject_ok_runnable_no_dangling` theorem compiles.

**Dependencies:** None. Can run in parallel with WS-H1.

---

### WS-H3: Build/CI Infrastructure Fixes (HIGH) — COMPLETED (v0.12.17)

**Objective:** Fix the `run_check` return value bug, integrate documentation sync
into CI, and add a `rg` availability guard to Tier 3 tests.

**Entry criteria:** Current CI passes on main branch.

**Findings addressed:**
- **H-12** (HIGH): `run_check` in `test_lib.sh` falls through to implicit
  `return 0` after recording a failure when `CONTINUE_MODE=1`. Callers receive
  success from `run_check` even when the underlying command failed.
- **M-19** (MEDIUM): `test_docs_sync.sh` exists but no CI workflow invokes it.
  Documentation sync relies entirely on manual developer execution.
- **M-20** (MEDIUM): Tier 3 script has ~440 `rg` invocations with no `grep`
  fallback. If ripgrep is unavailable, the entire tier is broken.

**Deliverables:**
1. Fix `run_check` in `scripts/test_lib.sh`: add explicit `return 1` in the
   continue-mode failure path after `record_failure`.
2. Add `test_docs_sync.sh` invocation to the appropriate CI workflow (e.g.,
   the smoke or full test workflow). Documentation drift should be caught
   automatically on every PR.
3. Add an `rg` availability guard at the top of `test_tier3_invariant_surface.sh`:
   if `rg` is not available, emit a clear error message and exit with a
   descriptive failure rather than silently producing 440 command-not-found errors.
   Optionally, provide a `grep -rP` fallback for environments without ripgrep.

**Files modified:**
- `scripts/test_lib.sh` — `run_check` fix
- `scripts/test_tier3_invariant_surface.sh` — `rg` availability guard
- `.github/workflows/` — CI workflow update for `test_docs_sync.sh`

**Exit evidence:**
- `run_check` returns non-zero on failure in both normal and continue mode.
- `test_docs_sync.sh` executes in CI (visible in workflow logs).
- Tier 3 script fails gracefully when `rg` is absent (tested by temporarily
  renaming `rg`).

**Dependencies:** None. Can run in parallel with WS-H1 and WS-H2.

---

### WS-H4: Capability Invariant Redesign (CRITICAL)

**Objective:** Replace the trivially-true capability invariant bundle with
meaningful security predicates, and establish CDT structural invariants that
enable sound revocation.

**Entry criteria:** WS-H7 completed (HashMap BEq fix needed for CDT HashMap
operations). Alternatively, can start Part A immediately if BEq changes are
scoped to not affect CDT types.

**Findings addressed:**
- **C-03** (CRITICAL): `capabilityInvariantBundle` is trivially true. `slotsUnique`
  is defined as `True` (HashMap keys are structurally unique). All 1,861 lines of
  preservation proofs prove preservation of a trivially-true predicate.
- **M-08 / A-20** (HIGH): CDT completeness not proven. `cspaceMint` does not add
  CDT edges; only `cspaceMintWithCdt` does. Orphaned capabilities escape revocation.
- **M-03** (MEDIUM): CDT acyclicity not maintained after `addEdge`. The `acyclic`
  property is defined but has no preservation theorem, and `descendantsOf`
  completeness depends on acyclicity.
- **M-07** (MEDIUM): `cspaceRevokeCdt` silently swallows deletion failures. Failed
  deletions during CDT-based revocation leave orphaned capabilities without CDT
  tracking.

**Deliverables:**

*Part A — Replace trivially-true predicates:*
1. Replace `slotsUnique` (currently `True`) with a meaningful predicate:
   `cspaceSlotCountBounded st` — every CNode has at most `2^radixBits` occupied
   slots (matching the CNode guard/radix semantics).
2. Add `cdtCompleteness st` — every capability in any CNode that was derived
   (via mint) from another capability has a corresponding CDT edge. Formally:
   if slot `s` holds a capability that was minted from slot `s'`, then
   `cdtEdge s' s` exists.
3. Add `cdtAcyclicity st` — the CDT graph has no cycles. This is required for
   `descendantsOf` termination and revocation completeness.
4. Update `capabilityInvariantBundle` to compose these new predicates alongside
   the existing `cspaceLookupSound` and `lifecycleAuthorityMonotonicity`.

*Part B — CDT acyclicity preservation (M-03):*
5. Prove `addEdge_preserves_acyclicity` — adding an edge from parent to child
   preserves acyclicity when the child is not an ancestor of the parent.
6. Add the ancestor check to `cspaceMintWithCdt` as a precondition (return error
   if adding the edge would create a cycle).
7. Prove `cspaceMintWithCdt_preserves_cdtAcyclicity`.

*Part C — CDT completeness enforcement (M-08/A-20):*
8. Deprecate the non-CDT `cspaceMint` path by making it internal (unexported
   from `API.lean`). The public API should always use `cspaceMintWithCdt` to
   ensure CDT edges are recorded.
9. Alternatively, if `cspaceMint` must remain public, add an invariant annotation
   documenting that capabilities created via `cspaceMint` are "untracked" and
   will not be affected by CDT-based revocation.
10. Prove `cspaceMintWithCdt_preserves_cdtCompleteness`.

*Part D — Revocation failure handling (M-07):*
11. Change `cspaceRevokeCdt` to return a structured result indicating which
    deletions failed (if any), rather than silently swallowing errors.
12. Add theorem: if all deletions succeed, the revoked subtree is fully removed.

*Part E — Re-prove preservation:*
13. Re-prove all `capabilityInvariantBundle` preservation theorems against the
    new (non-trivial) predicates. This is the bulk of the work — each operation
    that modifies CNodes must now prove slot-count bounds, CDT completeness, and
    CDT acyclicity preservation.

**Proof strategy:**
- CDT acyclicity proofs will follow the same structural pattern as the service
  dependency acyclicity proof in `Service/Invariant.lean` (~600 lines of graph
  theory already in the codebase). Reuse the DFS completeness infrastructure.
- Slot-count bounds follow directly from CNode structure (radix bits determine
  maximum addressable slots, and `HashMap.size` is bounded by insertion count).
- CDT completeness is an inductive property: maintained by `cspaceMintWithCdt`
  (adds edge), `cspaceDeleteSlot` (removes slot and edge), and `cspaceRevokeCdt`
  (removes subtree).

**Files modified:**
- `SeLe4n/Model/Object.lean` — CDT predicate definitions
- `SeLe4n/Kernel/Capability/Operations.lean` — revocation error handling, mint path
- `SeLe4n/Kernel/Capability/Invariant.lean` — all preservation theorems (major rework)
- `SeLe4n/Kernel/API.lean` — public interface updates (deprecate raw mint)

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `capabilityInvariantBundle` no longer contains `True` as a conjunct.
- `cdtAcyclicity` and `cdtCompleteness` appear as conjuncts in the bundle.
- Preservation theorems for all CSpace operations compile against new bundle.

**Dependencies:** WS-H7 (HashMap BEq fix) recommended but not strictly required.

---

### WS-H5: IPC Dual-Queue Structural Invariant (CRITICAL) — COMPLETED (v0.12.19)

**Objective:** Define and prove a structural well-formedness invariant for the
intrusive dual-queue IPC implementation, closing the gap where 1,676 lines of
dual-queue code have zero formal well-formedness guarantees.

**Entry criteria:** WS-H1 completed (Call-path fix lands `blockedOnCall` state
which affects queue semantics). `test_smoke.sh` passes.

**Findings addressed:**
- **C-04 / A-22** (CRITICAL): `endpointInvariant` only checks legacy queue fields.
  The dual-queue intrusive list structure (`sendQ`/`receiveQ`, TCB `queueNext`/
  `queuePrev` linkage) has no formal well-formedness predicate. No machine-checked
  guarantee that the DualQueue implementation maintains structural integrity.
- **A-23** (HIGH): `endpointQueuePopHead` directly dereferences `headTcb.queueNext`
  without validating link consistency. Corrupted queue links would cause silent
  undefined behavior in the model.
- **A-24** (HIGH): `endpointReceiveDual` calls `lookupTcb st' sender` after dequeue.
  If lookup fails, the message is silently `none` rather than returning an error.
  Relies on external lifecycle enforcement.

**Deliverables:**

*Part A — Define intrusive queue well-formedness:*
1. Define `intrusiveQueueWellFormed (q : IntrusiveQueue) (st : SystemState) : Prop`:
   - **Link consistency**: for every TCB `t` in the queue, `t.queueNext` and
     `t.queuePrev` point to valid TCBs also in the queue (or are `none` for
     head/tail).
   - **Doubly-linked integrity**: if `a.queueNext = some b`, then
     `b.queuePrev = some a` (and vice versa).
   - **No cross-queue contamination**: a TCB appears in at most one queue
     (`sendQ` or `receiveQ`) of at most one endpoint at any time.
   - **Size consistency**: the queue length matches the number of reachable
     nodes from head following `queueNext` links.
   - **TCB existence**: every ThreadId in the queue corresponds to an existing
     TCB in `st.objects`.
2. Define `dualQueueEndpointWellFormed (epId : ObjId) (st : SystemState) : Prop`
   composing `intrusiveQueueWellFormed` for both `sendQ` and `receiveQ`, plus
   mutual exclusion (no TCB in both queues simultaneously).

*Part B — Integrate into IPC invariant:*
3. Add `dualQueueEndpointWellFormed` to `endpointInvariant` (or replace the
   legacy-only predicate). The invariant should cover both legacy and dual-queue
   representations.
4. Prove `dualQueueEndpointWellFormed` holds for the initial/empty endpoint state.

*Part C — Preservation proofs:*
5. Prove preservation for all dual-queue operations:
   - `endpointQueueEnqueue_preserves_intrusiveQueueWellFormed`
   - `endpointQueuePopHead_preserves_intrusiveQueueWellFormed`
   - `endpointSendDual_preserves_dualQueueEndpointWellFormed`
   - `endpointReceiveDual_preserves_dualQueueEndpointWellFormed`
   - `endpointCall_preserves_dualQueueEndpointWellFormed`
   - `endpointReply_preserves_dualQueueEndpointWellFormed`
   - `endpointReplyRecv_preserves_dualQueueEndpointWellFormed`
6. For `endpointQueuePopHead` (A-23): prove that the link dereference is safe
   under `intrusiveQueueWellFormed` — if the invariant holds, `headTcb.queueNext`
   is either `none` (tail) or points to a valid TCB.

*Part D — Message safety (A-24):*
7. Prove: under `dualQueueEndpointWellFormed`, the `lookupTcb st' sender` call
   after `popHead` always succeeds (TCB existence is part of the invariant).
   Convert the silent `none` path to an explicit error or prove it unreachable.

**Proof strategy:**
- The intrusive queue is a doubly-linked list with explicit head/tail pointers.
  Well-formedness is a standard linked-list invariant. The key insight is that
  `intrusiveQueueWellFormed` can be expressed as a recursive property over the
  chain from head to tail, making inductive proofs tractable.
- Each queue operation modifies at most 3 TCBs (the inserted/removed node and
  its neighbors). Preservation proofs are local: show the 3 modified nodes
  maintain link consistency, and all other nodes are unaffected.

**Files modified:**
- `SeLe4n/Kernel/IPC/Invariant.lean` — new predicates and preservation theorems
- `SeLe4n/Kernel/IPC/DualQueue.lean` — potential guard additions for A-23/A-24
- `SeLe4n/Model/Object.lean` — if predicate definitions live with object types

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `intrusiveQueueWellFormed` and `dualQueueEndpointWellFormed` definitions compile.
- Preservation theorems for all 7 dual-queue operations compile.
- `endpointQueuePopHead_link_safe` theorem (A-23 closure) compiles.
- `endpointReceiveDual_sender_exists` theorem (A-24 closure) compiles.

**Dependencies:** WS-H1 (blockedOnCall state affects queue membership semantics).

---

### WS-H6: Scheduler Proof Completion (CRITICAL)

**Objective:** Prove preservation of the orphaned scheduler invariants (EDF
correctness, time-slice positivity, maxPriority cache correctness, candidate
selection optimality) and add the missing RunQueue structural invariant, or
remove unproven definitions that create false assurance.

**Entry criteria:** Phase 1 completed (WS-H1..H3). `test_smoke.sh` passes.

**Findings addressed:**
- **A-14 / H-08** (CRITICAL): `edfCurrentHasEarliestDeadline` is defined but has
  zero preservation theorems. The scheduler claims EDF semantics but provides no
  formal backing.
- **A-15 / H-08** (CRITICAL): `timeSlicePositive` is defined but unproven. No
  theorem shows all runnable threads have `timeSlice > 0`.
- **A-16** (HIGH): `maxPriority` cache correctness unproven. The cached value is
  updated by `recomputeMaxPriority` (a HashMap fold) but no theorem proves the
  result equals the actual maximum priority.
- **A-17 / M-05 / M-06** (HIGH): `chooseBestRunnableBy` optimality unproven.
  `isBetterCandidate` has irreflexivity and asymmetry but no transitivity. The
  bucket-first and full-scan strategies have no equivalence proof.
- **M-04** (MEDIUM): Only the `flat → membership` direction of RunQueue consistency
  is proved. The reverse (`membership → flat`) is missing, blocking O(1) membership
  check migration.

**Deliverables:**

*Part A — EDF invariant preservation (A-14):*
1. Prove `schedule_preserves_edfCurrentHasEarliestDeadline` — after `schedule`
   selects a new current thread, it has the earliest deadline among same-priority
   runnable threads. This follows from `chooseBestRunnableBy` selecting by
   deadline within each priority bucket.
2. Prove `timerTick_preserves_edfCurrentHasEarliestDeadline` — timer tick does
   not change deadlines, so the property is preserved.
3. Prove `handleYield_preserves_edfCurrentHasEarliestDeadline` — yield moves the
   current thread to the back of its priority bucket; if it had the earliest
   deadline, the new head must now have the earliest remaining deadline.

*Part B — Time-slice positivity (A-15):*
4. Prove `schedule_preserves_timeSlicePositive` — when `schedule` selects a thread,
   its `timeSlice` is reset to the configured default (which is positive by
   machine configuration well-formedness).
5. Prove `timerTick_preserves_timeSlicePositive` — after decrement, if
   `timeSlice` reaches 0, the thread is preempted (removed from current) and
   re-enqueued with a fresh time slice.
6. Add `timeSlicePositive` and `edfCurrentHasEarliestDeadline` to
   `schedulerInvariantBundle` (they are currently orphaned outside the bundle).

*Part C — maxPriority cache correctness (A-16):*
7. Prove `recomputeMaxPriority_correct` — the fold over `priorityBuckets` returns
   the actual maximum priority present in the run queue. This is a straightforward
   fold correctness proof.
8. Prove `enqueue_preserves_maxPriority_correct` — inserting a thread updates the
   cache correctly (max of old cache and inserted priority).
9. Prove `dequeue_preserves_maxPriority_correct` — removing a thread triggers
   recomputation only when removing the last thread at the max priority level.

*Part D — Candidate selection optimality (A-17/M-05/M-06):*
10. Prove `isBetterCandidate_transitive` — strict partial order completion. This
    enables the fold-based selection to be proven optimal.
11. Prove `chooseBestRunnableBy_optimal` — the selected candidate has no strictly
    better alternative in the run queue.
12. Prove `bucketFirst_fullScan_equivalence` — the WS-G4 bucket-first optimization
    (try `maxPriority` bucket first, fall back to full scan) produces the same
    result as always scanning all buckets. This validates the optimization.

*Part E — RunQueue reverse consistency (M-04):*
13. Prove `membership_implies_flat` — if `tid ∈ rq.membership`, then `tid ∈ rq.flat`.
    This is the reverse direction of the existing `flat_wf` invariant.
14. Together with the existing forward direction, this establishes full bidirectional
    consistency: `tid ∈ rq.membership ↔ tid ∈ rq.flat`.

**Proof strategy:**
- EDF preservation follows from `chooseBestRunnableBy` selection semantics: the
  fold selects the thread with minimum deadline at the highest priority. Once
  `chooseBestRunnableBy_optimal` is proven (Part D), EDF preservation is a
  corollary.
- Time-slice positivity requires tracking the initial `timeSlice` value. The
  scheduler must reset `timeSlice` to a positive value on selection. Prove this
  by showing `MachineConfig.defaultTimeSlice > 0` (a `wellFormed` check) and
  tracing through the reset path.
- `maxPriority` cache correctness is a standard max-over-collection proof.
  Lean's `Std.HashMap.fold` provides the iteration mechanism; the proof shows
  the fold accumulator tracks the maximum.
- Transitivity of `isBetterCandidate` requires showing: if `a` is better than
  `b` (higher priority, or same priority with earlier deadline) and `b` is better
  than `c`, then `a` is better than `c`. This follows from transitivity of `>`
  on `Priority` and `<` on `Deadline`.

**Files modified:**
- `SeLe4n/Kernel/Scheduler/Invariant.lean` — all new preservation theorems
- `SeLe4n/Kernel/Scheduler/Operations.lean` — if any operations need guards
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` — `membership_implies_flat`

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `timeSlicePositive` and `edfCurrentHasEarliestDeadline` appear as conjuncts
  in `schedulerInvariantBundle`.
- All 12+ new preservation theorems compile.
- `isBetterCandidate_transitive` theorem compiles.
- `bucketFirst_fullScan_equivalence` theorem compiles.

**Dependencies:** Phase 1 completed. Independent of WS-H4, WS-H5, WS-H7.

---

### WS-H7: HashMap Equality Fix & State Closure Migration (CRITICAL)

**Objective:** Fix the order-dependent `BEq` instances for HashMap-backed types
and migrate the remaining function-typed state fields to HashMap, eliminating
O(k) closure chain accumulation.

**Entry criteria:** Phase 1 completed. `test_smoke.sh` passes.

**Findings addressed:**
- **A-07** (CRITICAL): `BEq` instances for `VSpaceRoot` and `CNode` rely on
  `HashMap.toList` iteration order. The pattern
  `a.mappings.toList.all (fun (k,v) => b.mappings[k]? == some v)` may produce
  false inequality for semantically equal HashMaps if iteration order differs.
- **H-09 / A-10** (CRITICAL/HIGH): `capabilityRefs`, `services`, `irqHandlers`,
  `cdtSlotNode`, and `cdtNodeSlot` remain function-typed (closures). Each update
  wraps the previous closure, creating O(k) lookup chains after k updates.

**Deliverables:**

*Part A — HashMap BEq fix (A-07):*
1. Replace the `BEq` instance for `VSpaceRoot` with a bidirectional entry
   verification that does not depend on `toList` order:
   - Check `a.mappings.size == b.mappings.size`.
   - Check `a.mappings.fold (init := true) fun acc k v => acc && b.mappings[k]? == some v`.
   The size check + forward containment guarantees bidirectional equality without
   depending on iteration order (the fold visits every key in `a`, and size
   equality ensures `b` has no extra keys).
2. Apply the same fix to `CNode` BEq.
3. Prove `beq_correct : ∀ a b : VSpaceRoot, (a == b) = true ↔ a = b` (soundness
   and completeness of the new BEq).
4. Add `LawfulBEq` instances deriving from the correctness proof.

*Part B — capabilityRefs migration (A-10):*
5. Replace `capabilityRefs : SlotRef → Option CapTarget` in `LifecycleMetadata`
   with `capabilityRefs : Std.HashMap SlotRef CapTarget`.
6. Add `Hashable` and `BEq` instances for `SlotRef` (a product type — hash by
   combining component hashes).
7. Update `storeCapabilityRef` to use `HashMap.insert` instead of closure wrapping.
8. Update all `st.lifecycle.capabilityRefs ref` call sites to
   `st.lifecycle.capabilityRefs.find? ref`.
9. Prove bisimulation bridge lemma for `capabilityRefs` (same pattern as WS-G2
   object store migration).

*Part C — Remaining closure fields:*
10. Migrate `services : ServiceId → Option ServiceState` to
    `Std.HashMap ServiceId ServiceState`.
11. Migrate `irqHandlers : Irq → Option ObjId` to `Std.HashMap Irq ObjId`.
12. Migrate `cdtSlotNode : SlotRef → Option CdtNodeId` to
    `Std.HashMap SlotRef CdtNodeId`.
13. Migrate `cdtNodeSlot : CdtNodeId → Option SlotRef` to
    `Std.HashMap CdtNodeId SlotRef`.
14. For each migration: update the accessor pattern, prove a bisimulation bridge,
    and re-prove affected downstream theorems.

*Part D — Proof maintenance:*
15. Re-prove all theorems that pattern-match on `BEq` for `VSpaceRoot` or `CNode`.
16. Re-prove all theorems that reference the migrated state fields.
17. Verify no `sorry` introduced during migration.

**Proof strategy:**
- The BEq fix follows the same pattern as HashMap equality in Lean's `Std` library.
  The key lemma is that `HashMap.fold` visits all entries exactly once, and
  `size` equality ensures no extras. The proof is self-contained.
- Closure-to-HashMap migration reuses the bisimulation bridge approach from WS-G2.
  Define `field_fn (hm : HashMap K V) := hm.find?` and prove equivalence. Existing
  theorems bridge through the equivalence without immediate rewrite.

**Files modified:**
- `SeLe4n/Model/Object.lean` — VSpaceRoot BEq, CNode BEq
- `SeLe4n/Model/State.lean` — `LifecycleMetadata`, `SystemState` field types
- `SeLe4n/Prelude.lean` — `Hashable`/`BEq` for `SlotRef`, `CdtNodeId` if needed
- `SeLe4n/Kernel/Service/Operations.lean` — service field access
- `SeLe4n/Kernel/Service/Invariant.lean` — service preservation theorems
- `SeLe4n/Kernel/Capability/Operations.lean` — CDT field access
- `SeLe4n/Kernel/Capability/Invariant.lean` — CDT preservation theorems
- `SeLe4n/Kernel/Architecture/VSpace.lean` — VSpaceRoot equality usage

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `grep -r "→ Option" SeLe4n/Model/State.lean` returns zero matches for the
  migrated fields (no closure-chain stores remain).
- `VSpaceRoot` and `CNode` BEq do not use `toList`.
- `beq_correct` lemma for VSpaceRoot compiles.

**Dependencies:** Phase 1 completed. Should complete before WS-H4 (CDT HashMap
operations benefit from BEq fix) and before WS-H11 (VSpace BEq used in proofs).

---

### WS-H8: Enforcement-NI Bridge & Missing Wrappers (CRITICAL)

**Objective:** Bridge the enforcement layer to the non-interference proof layer
so that passing a `securityFlowsTo` check is formally connected to domain-separation
guarantees, and add enforcement wrappers for all security-critical operations that
currently lack them.

**Entry criteria:** Phase 2 completed (particularly WS-H6 for scheduler proofs
and WS-H5 for IPC invariants). `test_smoke.sh` passes.

**Findings addressed:**
- **A-35 / H-07** (CRITICAL): Enforcement-NI bridge is disconnected. There is
  no theorem connecting `securityFlowsTo` checks (enforcement) to domain-separation
  hypotheses (non-interference). Cannot automatically conclude "if the checked
  operation succeeds, NI is preserved."
- **H-07** (HIGH): `notificationSignal`, `cspaceCopy`, `cspaceMove`,
  `endpointReceive` lack information-flow enforcement wrappers. No
  `endpointSendDualChecked_NI` bridge theorem exists for the dual-queue path.
- **A-36 / A-37 / H-11** (HIGH): `activeDomain`, TCB fields (priority, timeSlice,
  ipcState, domain) are fully visible in projections. Domain scheduling metadata
  (`domainTimeRemaining`, `domainSchedule`, `domainScheduleIndex`) not projected,
  enabling timing-channel attacks.

**Deliverables:**

*Part A — Enforcement bridge theorems:*
1. Define `enforcementSoundness` — a meta-theorem connecting enforcement to NI:
   ```
   ∀ op st, enforcedOperation op st = .ok st' →
     ∀ d, ¬securityFlowsTo (opDomain op st) d →
       projectState d st = projectState d st'
   ```
   This states: if an enforced operation succeeds, then for any domain `d` that
   the operation's domain cannot flow to, the observable state is unchanged.
2. Prove `enforcementSoundness` for each existing enforced operation
   (`endpointSendDualChecked`, `cspaceMintChecked`, etc.).
3. Add `endpointSendDualChecked_NI` bridge theorem for the recommended dual-queue
   IPC path.

*Part B — Missing enforcement wrappers:*
4. Add `notificationSignalChecked` — enforces information-flow check before
   `notificationSignal`. A high-domain thread signaling a low-domain notification
   leaks one bit; the wrapper should gate on `securityFlowsTo`.
5. Add `cspaceCopyChecked` and `cspaceMoveChecked` — enforce flow check on
   capability transfer between CNodes in different domains.
6. Add `endpointReceiveChecked` — enforce flow check on receive (the receiver
   may learn about the sender's domain).
7. Prove NI bridge theorems for each new wrapper.

*Part C — Projection hardening (A-36/A-37/H-11):*
8. Filter `activeDomain` in `projectState` — only expose it to observers in the
   same domain (or document as a deliberate security assumption with threat model
   justification if it must remain visible).
9. Filter TCB scheduling metadata (priority, timeSlice) from projections for
   threads in different domains. A low observer should not see high-domain thread
   scheduling parameters.
10. Add `domainTimeRemaining`, `domainSchedule`, `domainScheduleIndex` to the
    projection with appropriate domain filtering.
11. Re-prove all NI theorems against the updated projection.

**Files modified:**
- `SeLe4n/Kernel/InformationFlow/Enforcement.lean` — new wrappers + bridge theorems
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — projection hardening
- `SeLe4n/Kernel/InformationFlow/Invariant.lean` — re-prove NI theorems
- `SeLe4n/Kernel/IPC/Operations.lean` — if checked wrappers are added here

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `enforcementSoundness` meta-theorem compiles for all enforced operations.
- All 4 new `*Checked` wrappers have corresponding NI bridge theorems.
- `activeDomain` filtered by domain in projection (or documented exception).
- `domainTimeRemaining` appears in `ObservableState` projection.

**Dependencies:** WS-H6 (scheduler proofs for scheduler metadata projection),
WS-H5 (IPC invariants for IPC enforcement bridge).

---

### WS-H9: Non-Interference Coverage Extension (CRITICAL) — COMPLETED (v0.13.4)

**Objective:** Extend non-interference proofs from ~25% to >80% of kernel
operations, prioritizing scheduler operations (which modify globally-visible
state) and IPC receive/reply.

**Entry criteria:** WS-H8 completed (enforcement bridge provides the framework
for new NI proofs). WS-H6 completed (scheduler invariants needed as hypotheses).

**Findings addressed:**
- **C-02 / A-40** (CRITICAL): Only 12 of 30+ kernel operations have NI proofs.
  Missing: all scheduler operations, IPC receive/reply, VSpace operations, several
  CSpace operations. Current proofs cover ~25% of the full obligation.
- **M-15** (MEDIUM): `NonInterferenceStep` inductive is not exhaustive — only
  covers 11 operation families. `composedNonInterference_trace` applies only to
  traces of "safe" operations, not real kernel executions.

**Deliverables:**

*Part A — Scheduler NI (highest priority):*
1. Prove `schedule_NI` — scheduling a thread in a non-observable domain does not
   change the observable projection. This is the most important missing NI proof
   because `schedule` modifies globally-visible state (`currentThread`,
   `activeDomain`).
2. Prove `timerTick_NI` — timer tick in a non-observable domain does not change
   the observable projection. Timer tick modifies `timeSlice` and potentially
   triggers rescheduling.
3. Prove `handleYield_NI` — yield in a non-observable domain is unobservable.
4. Prove `switchDomain_NI` — domain switch does not leak cross-domain information
   (this interacts with the `activeDomain` projection from WS-H8).

*Part B — IPC NI completion:*
5. Prove `endpointReceive_NI` / `endpointReceiveDual_NI` — receiving from a
   non-observable sender does not change the observable projection.
6. Prove `endpointReply_NI` — replying to a non-observable caller is unobservable.
7. Prove `endpointCall_NI` — the full Call path (send + block + receive reply)
   preserves NI.
8. Prove `endpointReplyRecv_NI` — the compound ReplyRecv operation.

*Part C — CSpace NI completion:*
9. Prove `cspaceDelete_NI` — deleting a capability in a non-observable CNode.
10. Prove `cspaceCopy_NI` — copying a capability between non-observable CNodes.
11. Prove `cspaceMove_NI` — moving a capability between non-observable CNodes.

*Part D — VSpace NI:*
12. Prove `vspaceMapPage_NI` — mapping a page in a non-observable VSpace.
13. Prove `vspaceUnmapPage_NI` — unmapping a page in a non-observable VSpace.
14. Prove `vspaceLookup_NI` — address translation in a non-observable VSpace
    (read-only, should be straightforward).

*Part E — Observable-state NI:*
15. Prove at least one NI theorem for an operation on *observable* state — every
    existing theorem requires the entity to be non-observable. The observable case
    requires showing that the operation's effect is consistent across low-equivalent
    states (the standard NI unwinding condition).
16. Target: `endpointSendDual` on an observable endpoint — show that if two
    low-equivalent states have the same observable endpoint, sending produces
    low-equivalent result states.

*Part F — Exhaustive NonInterferenceStep:*
17. Extend the `NonInterferenceStep` inductive to include all operation families
    from Parts A-E.
18. Update `composedNonInterference_trace` to cover the extended inductive.
19. Document remaining uncovered operations (if any) with explicit justification
    for deferral.

**Proof strategy:**
- Scheduler NI proofs follow the standard unwinding approach: show that
  `projectState d (schedule st) = projectState d st` when the scheduled thread's
  domain is not `d` and `d` cannot observe the thread's domain. The key lemma is
  that `schedule` only modifies `currentThread` and the selected TCB's `timeSlice`,
  both of which are filtered by the projection when non-observable.
- IPC NI proofs build on the enforcement bridge from WS-H8: if the enforcement
  check passes, the operation's domain can flow to the affected domain, and the
  NI obligation is satisfied by the flow relation.
- Observable-state NI is harder: requires showing the operation is "functionally
  deterministic" on the observable portion — given the same observable input, it
  produces the same observable output regardless of high-domain state.

**Files modified:**
- `SeLe4n/Kernel/InformationFlow/Invariant.lean` — all new NI proofs (major expansion)
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — if projection helpers needed

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `NonInterferenceStep` inductive has 25+ constructors (up from 12).
- Scheduler NI proofs (`schedule_NI`, `timerTick_NI`, `handleYield_NI`,
  `switchDomain_NI`) all compile.
- At least one observable-state NI theorem compiles.
- `composedNonInterference_trace` covers the extended inductive.

**Dependencies:** WS-H8 (enforcement bridge), WS-H6 (scheduler invariants),
WS-H5 (IPC invariants for IPC NI proofs).

---

### WS-H10: Security Model Foundations (CRITICAL)

**Objective:** Resolve the non-standard security lattice, add MachineState to the
information-flow projection, introduce a declassification model, and add
well-formedness requirements for per-endpoint flow policies.

**Entry criteria:** WS-H8 completed (enforcement bridge established). Can
partially overlap with WS-H9.

**Findings addressed:**
- **C-05 / A-38** (CRITICAL): `ObservableState` omits `MachineState` entirely.
  Machine state is the primary information carrier between security domains in
  real kernels. NI results apply only to abstract kernel state.
- **A-34** (CRITICAL): The integrity dimension of the security lattice flows
  upward (untrusted → trusted is permitted), contrary to standard BIBA model.
  Documented as intentional but unjustified by a threat model.
- **A-39** (MEDIUM): No declassification model. No explicit declassification
  points; no mechanism for controlled information downgrade.
- **M-16** (MEDIUM): Per-endpoint `DomainFlowPolicy` overrides have no
  well-formedness requirement (reflexive + transitive). Misconfigured policy
  could violate reflexivity.

**Deliverables:**

*Part A — MachineState projection (C-05/A-38):*
1. Extend `ObservableState` to include relevant `MachineState` fields:
   register file (filtered by domain), timer state (filtered), memory regions
   (filtered by VSpace mapping ownership).
2. Define `projectMachineState (d : DomainId) (ms : MachineState) : MachineState`
   that filters machine state to only what domain `d` can observe.
3. Update `projectState` to include `projectMachineState`.
4. Re-prove all existing NI theorems with the extended projection. Operations
   that don't modify `MachineState` should require only trivial extensions
   (`congrArg` on the unchanged field).
5. For operations that do modify `MachineState` (adapter operations), prove NI
   or document as out-of-scope for the abstract model.

*Part B — Security lattice resolution (A-34):*
6. Correct the integrity dimension to standard BIBA:
   - Flip the integrity comparison so that `integrityLevel a ≤
     integrityLevel b` requires `a.integrity ≥ b.integrity` (standard BIBA).
     This affects all `securityFlowsTo` checks and downstream enforcement.
7. Add a theorem `securityLattice_reflexive` and
   `securityLattice_transitive` proving the lattice properties.

*Part C — Declassification model (A-39):*
8. Define `DeclassificationPolicy` — a structure specifying which domains may
   declassify information to which other domains, under what conditions.
9. Add `declassify` operation to the enforcement layer: gates on the
   `DeclassificationPolicy` before allowing a controlled information downgrade.
10. Prove `declassify_NI` — declassification preserves NI for non-target domains
    (only the explicitly authorized target domain sees the declassified data).

*Part D — Endpoint policy well-formedness (M-16):*
11. Define `flowPolicyWellFormed (p : DomainFlowPolicy) : Prop` requiring
    reflexivity (`∀ d, p.flowsTo d d`) and transitivity.
12. Add a well-formedness check to `endpointSetFlowPolicy` (or wherever endpoint
    policies are configured). Return error if the policy is not well-formed.
13. Add `flowPolicyWellFormed` to the information-flow invariant bundle.
14. Prove preservation across all operations that don't modify flow policies.

**Files modified:**
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — MachineState projection
- `SeLe4n/Kernel/InformationFlow/Policy.lean` — lattice, declassification, policy WF
- `SeLe4n/Kernel/InformationFlow/Enforcement.lean` — declassify operation
- `SeLe4n/Kernel/InformationFlow/Invariant.lean` — re-prove NI + new invariants
- `docs/spec/SELE4N_SPEC.md` — threat model documentation (if Option A)

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `MachineState` appears in `ObservableState` (or scope limitation formally documented).
- Security lattice has `reflexive` and `transitive` theorems.
- Integrity semantics either corrected or justified in threat model document.
- `flowPolicyWellFormed` appears in IF invariant bundle.

**Dependencies:** WS-H8 (enforcement bridge). Can overlap with WS-H9.

---

### WS-H11: VSpace & Architecture Enrichment (HIGH) — COMPLETED (v0.13.7)

**Objective:** Enrich the VSpace model with page permissions, address bounds
enforcement, and TLB/cache maintenance modeling to close the gap between the
abstract flat-HashMap translation model and real ARM64 hardware requirements.

**Entry criteria:** WS-H7 completed (VSpaceRoot BEq fix). Phase 2 completed.

**Findings addressed:**
- **H-02 / A-32** (HIGH): VSpace maps `VAddr → PAddr` with no permission metadata.
  Real ARM64 page table entries carry read/write/execute permissions, cacheability,
  and shareability attributes.
- **H-10** (HIGH): No TLB/cache maintenance model or adapter. Real ARM64 VSpace
  operations require TLBI instructions, DSB/ISB barriers, and cross-core TLB
  shootdowns.
- **A-05 / M-12** (HIGH): `MemoryRegion.endAddr` does not check for address
  overflow. `wellFormed` does not enforce `endAddr ≤ 2^physicalAddressWidth`.
- **A-12** (HIGH): No global ASID uniqueness invariant. Two VSpaceRoots could
  claim the same ASID simultaneously.
- **M-14** (MEDIUM): `boundedAddressTranslation` defined but not integrated into
  `vspaceInvariantBundle` or consumed by preservation theorems.

**Deliverables:**

*Part A — Page permissions (H-02):*
1. Define `PagePermissions` structure with `read`, `write`, `execute`, `user`,
   `cacheable` boolean fields.
2. Replace `VSpaceRoot.mappings : HashMap VAddr PAddr` with
   `VSpaceRoot.mappings : HashMap VAddr (PAddr × PagePermissions)`.
3. Update `vspaceMapPage` to accept permissions and store them with the mapping.
4. Update `vspaceLookup` to return permissions alongside the physical address.
5. Add `wxExclusive` invariant: no mapping has both `write` and `execute` set
   (W^X enforcement).
6. Prove `vspaceMapPage_preserves_wxExclusive` (guarded by a check in the
   operation).
7. Update VSpace round-trip theorems for the enriched mapping type.

*Part B — Address bounds (A-05/M-12/M-14):*
8. Add `endAddr ≤ 2^machineConfig.physicalAddressWidth` check to
   `MachineConfig.wellFormed` and `MemoryRegion.wellFormed`.
9. Integrate `boundedAddressTranslation` into `vspaceInvariantBundle`.
10. Prove `vspaceMapPage_preserves_boundedAddressTranslation` — the mapped
    physical address is within the physical address space.

*Part C — ASID uniqueness (A-12):*
11. Define `asidUnique st` — no two VSpaceRoots in `st.objects` share the same
    ASID, and `st.asidTable` is consistent with VSpaceRoot ASID assignments.
12. Add `asidUnique` to `vspaceInvariantBundle`.
13. Prove preservation for `storeObject` (VSpaceRoot case) and `vspaceMapPage`.

*Part D — TLB/cache maintenance model (H-10):*
14. Define `TlbState` as an abstract model: a set of cached `(ASID, VAddr, PAddr)`
    entries that may be stale relative to the page table.
15. Add `adapterFlushTlb` and `adapterFlushTlbByAsid` adapter operations that
    clear the TLB cache (full flush or per-ASID flush).
16. Add `tlbConsistent` invariant: all TLB entries match the current page table.
17. Prove: `adapterFlushTlb` restores `tlbConsistent` from any TLB state.
18. Document that `vspaceMapPage` and `vspaceUnmapPage` must be followed by a
    TLB flush to maintain `tlbConsistent`. (Proof obligation: the composed
    `vspaceMapPage + adapterFlushTlb` preserves `tlbConsistent`.)

**Files modified:**
- `SeLe4n/Model/Object.lean` — `VSpaceRoot`, `PagePermissions`
- `SeLe4n/Machine.lean` — `MemoryRegion.wellFormed`, `TlbState`
- `SeLe4n/Kernel/Architecture/VSpace.lean` — mapping operations
- `SeLe4n/Kernel/Architecture/VSpaceBackend.lean` — backend with permissions
- `SeLe4n/Kernel/Architecture/VSpaceInvariant.lean` — new invariants
- `SeLe4n/Kernel/Architecture/Adapter.lean` — TLB adapter operations
- `SeLe4n/Model/State.lean` — `asidTable` invariant, TLB state

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `PagePermissions` type exists with `wxExclusive` invariant proven preserved.
- `boundedAddressTranslation` included in `vspaceInvariantBundle`.
- `asidUnique` invariant proven preserved.
- `adapterFlushTlb` operation and `tlbConsistent` invariant defined.

**Dependencies:** WS-H7 (VSpaceRoot BEq fix), Phase 2 completed.

---

### WS-H12: Scheduler & IPC Semantic Alignment (HIGH) — Refined Breakdown

**Objective:** Align the scheduler and IPC model with real seL4 semantics:
implement dequeue-on-dispatch scheduling with inline context save/restore,
bound IPC message payloads, and complete the legacy-to-dual-queue migration by
removing all deprecated endpoint fields and operations.

**Entry criteria:** WS-H1 completed (IPC bug fix), WS-H7 completed (state field
migration). Phase 2 completed.

**Findings addressed:**
- **H-04** (HIGH): Running thread stays in ready queue — inverted from seL4's
  dequeue-on-dispatch semantics. Real seL4 dequeues the running thread on
  dispatch and re-enqueues on preemption/yield/block.
- **H-03** (HIGH): TCBs do not embed a register save area. Context switches
  cannot be modeled at the per-thread level.
- **A-09** (HIGH): `IpcMessage` has unbounded payload. `registers : List Nat`
  and `caps : List Capability` have no size limits.
- **A-08 / M-01** (HIGH): Endpoint has redundant legacy + dual-queue fields with
  no consistency invariant between the two representations.
- **A-25** (MEDIUM): Legacy O(n) IPC operations retained without deprecation or
  migration path documentation.

**Rationale for refined decomposition:** The original 17-deliverable monolithic
workstream touches scheduler invariants, IPC invariants, model structures, and
information-flow projections simultaneously. A single change that inverts a core
scheduler invariant while also removing legacy IPC fields creates an
un-bisectable proof failure surface. The refined breakdown below sequences each
concern so that at every sub-workstream boundary the kernel builds with zero
sorry and `test_full.sh` passes, enabling independent review, revert, and
bisection.

**Execution order:** WS-H12a → WS-H12b → WS-H12c → WS-H12d → WS-H12e → WS-H12f

---

#### WS-H12a: Legacy Endpoint Field & Operation Removal (A-08/M-01/A-25)

**Objective:** Remove the deprecated WS-E3 legacy fields (`state`, `queue`,
`waitingReceiver`) from the `Endpoint` structure and delete all legacy O(n) IPC
operations and their associated invariant proofs. This is sequenced first because
it eliminates ~60 theorems and 3 deprecated operations that would otherwise need
to be re-proved when subsequent sub-workstreams change scheduler invariants.

**Findings addressed:** A-08, M-01, A-25

**Deliverables:**

*Part 1 — Remove legacy Endpoint fields from the model:*
1. Delete the `EndpointState` inductive type (`.idle`, `.send`, `.receive`)
   from `Model/Object.lean` (lines 131-135). This type exists solely to
   support the legacy three-state endpoint model.
2. Remove the three legacy fields from the `Endpoint` structure
   (`Model/Object.lean` lines 152-158):
   - `state : EndpointState` — delete
   - `queue : List SeLe4n.ThreadId` — delete
   - `waitingReceiver : Option SeLe4n.ThreadId` — delete
   The structure retains only `sendQ : IntrusiveQueue` and
   `receiveQ : IntrusiveQueue`.
3. Update all `Endpoint` construction sites across the codebase to remove
   the deleted fields. Affected files:
   - `SeLe4n/Kernel/IPC/Operations.lean` — endpoint construction in legacy ops
     (will be deleted in Part 2)
   - `SeLe4n/Testing/MainTraceHarness.lean` — fixture endpoint creation
   - `tests/NegativeStateSuite.lean` — test endpoint construction
   - `tests/InformationFlowSuite.lean` — test endpoint construction
   - Any other file that constructs an `Endpoint` value
4. Fix all pattern matches and field accesses (`ep.state`, `ep.queue`,
   `ep.waitingReceiver`) that no longer compile. Exhaustive match compilation
   will guide this.

*Part 2 — Delete legacy IPC operations:*
5. Delete the three deprecated O(n) IPC operations from
   `SeLe4n/Kernel/IPC/Operations.lean`:
   - `endpointSend` (lines 96-129)
   - `endpointAwaitReceive` (lines 140-157)
   - `endpointReceive` (lines 168-189)
   These are fully superseded by `endpointSendDual`/`endpointReceiveDual`
   in `IPC/DualQueue.lean` (WS-E4/WS-G7). Production trace code
   (`MainTraceHarness.lean`) already uses exclusively dual-queue operations.
6. Delete `endpointSendChecked` from
   `SeLe4n/Kernel/InformationFlow/Enforcement.lean` (line 47-55) — the legacy
   information-flow wrapper over `endpointSend`. The modern
   `endpointSendDualChecked` (line 68+) is the sole enforcement path.
7. Remove the legacy operation entries from the `KernelOperation` inductive
   type in `SeLe4n/Kernel/Architecture/Assumptions.lean` (lines 21-23):
   `endpointSend`, `endpointAwaitReceive`, `endpointReceive`. Update any
   exhaustive matches on `KernelOperation`.
8. Remove the deprecated entries from the API stability table in
   `SeLe4n/Kernel/API.lean` (line 47, line 56).

*Part 3 — Rewrite `endpointInvariant` to reference only dual-queue fields:*
9. Delete `endpointQueueWellFormed` and `endpointObjectValid` from
   `SeLe4n/Kernel/IPC/Invariant.lean` (lines 71-83). These predicates check
   `ep.state`, `ep.queue`, and `ep.waitingReceiver` — fields that no longer
   exist.
10. Redefine `endpointInvariant` to compose only dual-queue well-formedness:
    ```lean
    def endpointInvariant (epId : ObjId) (st : SystemState) : Prop :=
      dualQueueEndpointWellFormed epId st
    ```
    This makes the intrusive-queue structural invariant (`sendQ`/`receiveQ`
    head/tail consistency, TCB link integrity) the sole endpoint correctness
    predicate.
11. Update `ipcInvariant` (lines 164-166) to use the new `endpointInvariant`
    signature. Since `endpointInvariant` now takes `(epId : ObjId)` and
    `(st : SystemState)` (to access TCB links), the quantifier changes from
    `∀ ep, ... → endpointInvariant ep` to
    `∀ epId, ... → endpointInvariant epId st`.
12. Delete all legacy-only preservation theorems from
    `SeLe4n/Kernel/IPC/Invariant.lean`. These theorems prove invariant
    preservation for the deleted legacy operations and reference deleted
    fields. Identified theorems to delete (~26):
    - `endpointObjectValid_of_queueWellFormed`
    - `endpointSend_ok_implies_endpoint_object`
    - `endpointAwaitReceive_ok_implies_endpoint_object`
    - `endpointReceive_ok_implies_endpoint_object`
    - `endpointSend_result_wellFormed`
    - `endpointAwaitReceive_result_wellFormed`
    - `endpointReceive_result_wellFormed`
    - `endpointSend_preserves_cnode` / `_notification` / `_other_endpoint`
    - `endpointAwaitReceive_preserves_cnode` / `_notification` / `_other_endpoint`
    - `endpointReceive_preserves_cnode` / `_notification` / `_other_endpoint`
    - `endpointSend_preserves_ipcInvariant`
    - `endpointAwaitReceive_preserves_ipcInvariant`
    - `endpointReceive_preserves_ipcInvariant`
    - `endpointSend_preserves_schedulerInvariantBundle`
    - `endpointAwaitReceive_preserves_schedulerInvariantBundle`
    - `endpointReceive_preserves_schedulerInvariantBundle`
    - `endpointSend_preserves_ipcSchedulerContractPredicates`
    - `endpointAwaitReceive_preserves_ipcSchedulerContractPredicates`
    - `endpointReceive_preserves_ipcSchedulerContractPredicates`
    - `endpointAwaitReceive_preserves_runnableThreadIpcReady`
    - `endpointAwaitReceive_preserves_blockedOnSendNotRunnable`
    - `endpointAwaitReceive_preserves_blockedOnReceiveNotRunnable`
    - `endpointAwaitReceive_preserves_dualQueueSystemInvariant`
    - Any remaining lemmas solely supporting the above
13. Delete legacy preservation theorems from
    `SeLe4n/Kernel/Capability/Invariant.lean`:
    - `endpointSend_preserves_capabilityInvariantBundle` (line 2367)
    - `endpointAwaitReceive_preserves_capabilityInvariantBundle` (line 2421)
    - `endpointReceive_preserves_capabilityInvariantBundle` (line 2451)
    - `endpointSend_preserves_coreIpcInvariantBundle` (line 2486)
    - `endpointAwaitReceive_preserves_coreIpcInvariantBundle` (line 2499)
    - `endpointReceive_preserves_coreIpcInvariantBundle` (line 2512)
    - `endpointSend_preserves_ipcSchedulerCouplingInvariantBundle` (line 2525)
14. Delete legacy non-interference theorems from
    `SeLe4n/Kernel/InformationFlow/Invariant.lean`:
    - `endpointSend_projection_preserved` (line 489)
    - `endpointSend_preserves_lowEquivalent` (line 556)
    - `endpointSendChecked_NI` (line 1222)
15. Delete the `endpointSendChecked_eq_endpointSend_when_allowed` theorem
    from `SeLe4n/Kernel/InformationFlow/Enforcement.lean` (line 124).

*Part 4 — Update dual-queue invariant proofs for new `endpointInvariant`:*
16. Update all existing `*_preserves_ipcInvariant` theorems for dual-queue
    operations (`endpointQueuePopHead`, `endpointQueueEnqueue`,
    `endpointQueueRemoveDual`, `endpointSendDual`, `endpointReceiveDual`,
    `endpointReply`, `endpointReplyRecv`, `notificationSignal`,
    `notificationWait`) to use the new `endpointInvariant` definition.
    Since the new definition delegates to `dualQueueEndpointWellFormed`,
    these proofs should simplify — the prior proofs already showed that
    dual-queue operations preserve legacy fields unchanged (comments at
    lines 1989-1991, 3079-3081 of `IPC/Invariant.lean`), which is now moot.
17. Verify that `ipcInvariantFull` (line 170-171) still composes correctly
    with the redefined `ipcInvariant`. Since `ipcInvariantFull` is
    `ipcInvariant ∧ dualQueueSystemInvariant`, and the new `ipcInvariant`
    subsumes `dualQueueEndpointWellFormed`, evaluate whether
    `ipcInvariantFull` should be simplified to avoid redundancy.

*Part 5 — Migrate affected tests:*
18. Rewrite test cases in `tests/NegativeStateSuite.lean` (lines 355, 359,
    385, 461) to use `endpointReceiveDual` and `endpointSendDual` instead
    of the deleted legacy operations. Preserve the negative-test intent
    (testing error paths).
19. Rewrite test cases in `tests/InformationFlowSuite.lean` (lines 239-254,
    403-411) to use `endpointSendDualChecked` instead of the deleted
    `endpointSendChecked` and `endpointSend`. The dual-queue information-flow
    path is `endpointSendDualChecked` (already defined).
20. Update `tests/fixtures/main_trace_smoke.expected` if endpoint creation
    output changes due to removed fields.

**Files modified:**
- `SeLe4n/Model/Object.lean` — Endpoint structure, EndpointState deletion
- `SeLe4n/Kernel/IPC/Operations.lean` — legacy operation deletion
- `SeLe4n/Kernel/IPC/Invariant.lean` — endpointInvariant rewrite, theorem deletion
- `SeLe4n/Kernel/Capability/Invariant.lean` — legacy theorem deletion
- `SeLe4n/Kernel/InformationFlow/Enforcement.lean` — legacy wrapper deletion
- `SeLe4n/Kernel/InformationFlow/Invariant.lean` — legacy NI theorem deletion
- `SeLe4n/Kernel/Architecture/Assumptions.lean` — KernelOperation cleanup
- `SeLe4n/Kernel/API.lean` — stability table update
- `SeLe4n/Testing/MainTraceHarness.lean` — endpoint fixture update
- `tests/NegativeStateSuite.lean` — test migration
- `tests/InformationFlowSuite.lean` — test migration

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `Endpoint` structure contains only `sendQ` and `receiveQ` fields.
- `EndpointState` type deleted from codebase.
- No references to `endpointSend`, `endpointAwaitReceive`, `endpointReceive`
  remain in `.lean` source files.
- `endpointInvariant` references only dual-queue well-formedness.
- Grep verification: `grep -r 'endpointSend[^D]' SeLe4n/ tests/` returns
  zero matches.

**Dependencies:** WS-H1 (IPC bug fix), WS-H5 (dual-queue invariant).

---

#### WS-H12b: Dequeue-on-Dispatch Scheduler Semantics (H-04)

**Objective:** Invert the scheduler's current-thread membership invariant from
`current ∈ runnable` to `current ∉ runnable`, matching seL4's dequeue-on-dispatch
semantics where the running thread is removed from the ready queue at dispatch
time and re-enqueued only on preemption, yield, or blocking.

**Findings addressed:** H-04

**Deliverables:**

*Part 1 — Core scheduler transition changes:*
1. Modify `schedule` in `Scheduler/Operations.lean` (line 216-228) to dequeue
   the selected thread from `runQueue` after validation succeeds and before
   setting it as `currentThread`. The transition becomes:
   ```
   chooseThread → validate membership + domain → runQueue.remove tid →
   setCurrentThread (some tid)
   ```
   The thread is dispatched (set as current) but no longer in the runnable
   queue, matching seL4's `switchToThread` which calls `tcbSchedDequeue`.
2. Modify `timerTick` (line 264-287) to re-enqueue the current thread before
   calling `schedule` when the time-slice expires. On preemption:
   ```
   reset timeSlice → runQueue.insert current priority → schedule
   ```
   This mirrors seL4's `timerInterrupt` → `rescheduleRequired` →
   `tcbSchedEnqueue(current)` → `schedule()` path.
3. Modify `handleYield` (line 232-242) to re-enqueue the current thread at
   the back of its priority bucket before calling `schedule`:
   ```
   runQueue.insert current priority → runQueue.rotateToBack current →
   schedule
   ```
   This mirrors seL4's `handleYield` which calls `tcbSchedDequeue` +
   `tcbSchedAppend` (append = enqueue at tail).
4. Modify `switchDomain` (line 305-321) to re-enqueue the current thread (if
   any) before clearing `current` and advancing the domain schedule. The
   outgoing thread must return to the runnable pool for its next domain slot.

*Part 2 — Invariant inversion:*
5. Replace the `queueCurrentConsistent` invariant in
   `Scheduler/Invariant.lean` (line 30-33):
   - **Old:** `current = some tid → tid ∈ runnable`
   - **New:** `current = some tid → tid ∉ runnable`
   This is the semantic inversion that aligns with seL4.
6. Verify that `runQueueUnique` (line 43-44) remains unchanged — the
   dequeued current thread trivially satisfies uniqueness (it's not in the
   queue at all).
7. Verify that `currentThreadValid` (line 48-51) remains unchanged — it
   checks TCB existence in the object store, not run-queue membership.
8. Verify that `currentThreadInActiveDomain` (line 56-62) remains unchanged
   — it checks TCB domain, not run-queue membership.
9. Update `timeSlicePositive` (line 106-110) to exclude the current thread
   from the "all runnable threads" quantifier (since the current thread is
   no longer in the runnable set).
10. Update `edfCurrentHasEarliestDeadline` (line 125-139) — the current
    thread is compared against runnable threads, which no longer includes
    itself. Verify the deadline comparison remains meaningful.

*Part 3 — Re-prove scheduler preservation theorems:*
11. Re-prove `schedule_preserves_queueCurrentConsistent` (line 479-483)
    with the inverted invariant. The key proof step changes: previously,
    membership was assumed; now, the `runQueue.remove` call in `schedule`
    establishes non-membership.
12. Re-prove `schedule_preserves_runQueueUnique`. After `remove`, the
    dequeued thread cannot duplicate.
13. Re-prove `schedule_preserves_currentThreadValid`.
14. Re-prove `schedule_preserves_currentThreadInActiveDomain`.
15. Re-prove `schedule_preserves_kernelInvariant` (composes 11-14).
16. Re-prove `handleYield_preserves_*` (5 theorems). The re-enqueue +
    schedule sequence must preserve all invariant components.
17. Re-prove `timerTick_preserves_schedulerInvariantBundleFull`. The
    preemption path (re-enqueue + schedule) and the non-preemption path
    (decrement only, current unchanged) both preserve invariants.
18. Re-prove `switchDomain_preserves_schedulerInvariantBundle`.

*Part 4 — Update cross-subsystem invariant dependencies:*
19. Update IPC invariant theorems in `IPC/Invariant.lean` that reference
    `runnableThreadIpcReady` or assume `current ∈ runnable`. The
    `removeRunnable` helper is unchanged (it removes from the queue), but
    `ensureRunnable` callers must account for the possibility that the
    unblocked thread becomes current without being in the queue.
20. Update capability invariant theorems in `Capability/Invariant.lean` that
    compose scheduler invariants. These should need only signature updates,
    not structural proof changes, since capability operations do not modify
    scheduler membership.
21. Update service invariant theorems in `Service/Invariant.lean` if any
    compose `schedulerInvariantBundle`. Service operations do not touch
    scheduler state, so these should be trivial.

**Files modified:**
- `SeLe4n/Kernel/Scheduler/Operations.lean` — `schedule`, `timerTick`,
  `handleYield`, `switchDomain`, all preservation theorems
- `SeLe4n/Kernel/Scheduler/Invariant.lean` — `queueCurrentConsistent` inversion,
  `timeSlicePositive`, `edfCurrentHasEarliestDeadline`
- `SeLe4n/Kernel/IPC/Invariant.lean` — cross-subsystem theorem updates
- `SeLe4n/Kernel/Capability/Invariant.lean` — composition updates
- `SeLe4n/Kernel/Service/Invariant.lean` — composition updates (if applicable)

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `queueCurrentConsistent` states `current = some tid → tid ∉ runnable`.
- Trace scenario: after `schedule`, the dispatched thread is absent from
  `runQueue.toList` but present as `scheduler.current`.
- After `timerTick` preemption, the preempted thread reappears in
  `runQueue.toList`.

**Dependencies:** WS-H12a (legacy cleanup — eliminates ~60 dead theorems that
would otherwise need re-proving under the inverted invariant).

---

#### WS-H12c: Per-TCB Register Context with Inline Context Switch (H-03)

**Objective:** Add a per-TCB register save area (`registerContext`) and implement
context save/restore directly inline within the `schedule` transition, so that
dispatching a new thread atomically saves the outgoing thread's registers and
restores the incoming thread's registers in a single pure-functional state step.

**Design rationale — inline over separate helpers:** The context switch is
implemented directly inside `schedule` rather than as separate `saveContext`/
`restoreContext` helper functions called before and after `schedule`. This
matches seL4's `switchToThread` design where the context switch is an integral
part of thread dispatch, not a caller responsibility. Inlining ensures:
(a) no caller can forget to save/restore, (b) the invariant
"MachineState.regs = currentThread.registerContext" is established atomically
by `schedule` itself, and (c) preservation proofs compose locally within the
single transition rather than requiring cross-call composition.

**Findings addressed:** H-03

**Deliverables:**

*Part 1 — TCB register context field:*
1. Add `registerContext : RegisterFile := default` to the `TCB` structure in
   `Model/Object.lean` (after line 128). The `RegisterFile` type already
   exists in `Machine.lean` (line 32-35) with `pc`, `sp`, and `gpr` fields.
   Default is zero-initialized (`Inhabited RegisterFile` instance at line 37).
2. Update all TCB construction sites to include the new field (or rely on
   the `default` value). Affected files:
   - `SeLe4n/Testing/MainTraceHarness.lean` — fixture TCB creation
   - `tests/NegativeStateSuite.lean` — test TCB construction
   - Any other file that constructs a `TCB` value

*Part 2 — Inline context switch in `schedule`:*
3. Modify `schedule` in `Scheduler/Operations.lean` to perform inline context
   save/restore as part of the dispatch transition. The updated transition:
   ```
   chooseThread → validate → dequeue (WS-H12b) →
   save outgoing: if current = some outTid, store machine.regs into
                  outTid.tcb.registerContext →
   restore incoming: load inTid.tcb.registerContext into machine.regs →
   setCurrentThread (some inTid)
   ```
   When `current = none` (no outgoing thread), the save step is skipped.
   When `chooseThread` returns `none` (no eligible thread), both save and
   restore are skipped and `current` is set to `none`.
4. The save operation is a `storeObject` call that updates the outgoing TCB's
   `registerContext` field:
   ```lean
   let outTcb' := { outTcb with registerContext := st.machine.regs }
   storeObject outTid.toObjId (.tcb outTcb') st
   ```
5. The restore operation updates `MachineState.regs` from the incoming TCB:
   ```lean
   { st with machine := { st.machine with regs := inTcb.registerContext } }
   ```
6. Add the invariant `contextMatchesCurrent` to `Scheduler/Invariant.lean`:
   ```lean
   def contextMatchesCurrent (st : SystemState) : Prop :=
     match st.scheduler.current with
     | some tid =>
         match st.objects[tid.toObjId]? with
         | some (.tcb tcb) => st.machine.regs = tcb.registerContext
         | _ => True
     | none => True
   ```
   This states: when a thread is current, the machine's register file
   matches that thread's saved context. Established by the restore step in
   `schedule`.
7. Prove `schedule_preserves_contextMatchesCurrent`. The proof follows
   directly from the inline restore step.

*Part 3 — Update information-flow projection:*
8. Add per-TCB register context to the `ObservableState` in
   `InformationFlow/Projection.lean`. The existing `machineRegs` field
   (line 72) already projects the machine register file gated by current-
   thread observability. With the inline context switch, this projection
   remains correct: `machineRegs` reflects the current thread's context
   because `schedule` synchronizes them.
9. Verify that `projectState` / `projectStateFast` correctly handle the new
   TCB field. Since `projectObjects` projects full `KernelObject` values
   (including TCBs), the `registerContext` field is automatically included
   in object projections. No additional projection logic is needed — the
   existing object observability gate provides domain filtering.
10. Update `projectMachineRegs` documentation to note that the machine
    register file is guaranteed to equal `currentThread.registerContext`
    when `contextMatchesCurrent` holds.

*Part 4 — Preservation proofs:*
11. Prove that `handleYield` preserves `contextMatchesCurrent`. Since
    `handleYield` calls `schedule` (which re-establishes the invariant),
    this follows transitively.
12. Prove that `timerTick` preserves `contextMatchesCurrent`. The preemption
    path calls `schedule`; the non-preemption path does not change `current`
    or `machine.regs`, so the invariant holds trivially.
13. Prove that IPC operations preserve `contextMatchesCurrent`. IPC
    operations modify TCB IPC state and queue links but do not modify
    `registerContext` or `machine.regs`. The invariant holds by frame
    reasoning (fields unchanged → predicate unchanged).

**Files modified:**
- `SeLe4n/Model/Object.lean` — TCB `registerContext` field
- `SeLe4n/Kernel/Scheduler/Operations.lean` — inline context switch in
  `schedule`, preservation proofs
- `SeLe4n/Kernel/Scheduler/Invariant.lean` — `contextMatchesCurrent` invariant
- `SeLe4n/Kernel/InformationFlow/Projection.lean` — documentation update
- `SeLe4n/Testing/MainTraceHarness.lean` — trace verification of context switch

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `TCB.registerContext` field exists with `RegisterFile` type.
- `schedule` performs inline save/restore (no separate helper functions).
- `contextMatchesCurrent` invariant defined and preserved by `schedule`,
  `handleYield`, `timerTick`.
- Trace scenario: after `schedule` with a thread switch, `machine.regs`
  equals the incoming thread's `registerContext`.

**Dependencies:** WS-H12b (dequeue-on-dispatch — `schedule` body is modified
in H12b; context switch is added on top of the dequeue-on-dispatch version).

---

#### WS-H12d: IPC Message Payload Bounds (A-09)

**Objective:** Replace the unbounded `List` types in `IpcMessage` with bounded
`Array` types and enforce payload size limits at IPC send boundaries, matching
seL4's fixed message-register and extra-capability limits.

**Findings addressed:** A-09

**Deliverables:**

*Part 1 — Bounded message type:*
1. Define message size constants in `Model/Object.lean`:
   ```lean
   def maxMessageRegisters : Nat := 120
   def maxExtraCaps : Nat := 3
   ```
   These match seL4's standard configuration (`seL4_MsgMaxLength = 120`,
   `seL4_MsgMaxExtraCaps = 3`).
2. Replace `IpcMessage.registers : List Nat` with `registers : Array Nat`.
3. Replace `IpcMessage.caps : List Capability` with `caps : Array Capability`.
4. Update `IpcMessage.empty` to use `#[]` (empty array) instead of `[]`.
5. Update all `IpcMessage` construction sites across the codebase. Affected:
   - `SeLe4n/Kernel/IPC/DualQueue.lean` — message construction in send/receive
   - `SeLe4n/Testing/MainTraceHarness.lean` — test message creation
   - `tests/InformationFlowSuite.lean` — test message creation

*Part 2 — Bounds enforcement at send boundary:*
6. Add a bounds-check guard to `endpointSendDual` in `IPC/DualQueue.lean`.
   Before enqueuing or performing a handshake, validate:
   ```lean
   if msg.registers.size > maxMessageRegisters then .error .ipcMessageTooLarge
   else if msg.caps.size > maxExtraCaps then .error .ipcMessageTooManyCaps
   else <proceed with send>
   ```
7. Add `ipcMessageTooLarge` and `ipcMessageTooManyCaps` variants to the
   `KernelError` type (or reuse an existing error variant if semantically
   appropriate).
8. Add the same bounds check to `endpointSendDualChecked` in
   `InformationFlow/Enforcement.lean`.
9. Add the same bounds check to `endpointCall` and `endpointReplyRecv` in
   `IPC/DualQueue.lean` — these also carry message payloads.

*Part 3 — Invariant and proof updates:*
10. Add `ipcMessageBounded` predicate:
    ```lean
    def ipcMessageBounded (msg : IpcMessage) : Prop :=
      msg.registers.size ≤ maxMessageRegisters ∧
      msg.caps.size ≤ maxExtraCaps
    ```
11. Prove that all IPC send operations produce only bounded messages:
    `endpointSendDual_message_bounded` — if the operation succeeds, the
    staged message satisfies `ipcMessageBounded`.
12. Update IPC invariant preservation theorems to account for the `Array`
    type change. Since proofs reference `IpcMessage` structurally (not by
    list length), most updates should be mechanical type changes.
13. Update `pendingMessage` handling in `storeTcbPendingMessage` and
    `storeTcbIpcStateAndMessage` — no semantic change, just `List` → `Array`
    type propagation.

**Files modified:**
- `SeLe4n/Model/Object.lean` — `IpcMessage` type, size constants
- `SeLe4n/Kernel/IPC/DualQueue.lean` — bounds checks in send operations
- `SeLe4n/Kernel/IPC/Invariant.lean` — `ipcMessageBounded` predicate
- `SeLe4n/Kernel/InformationFlow/Enforcement.lean` — bounds check in checked send
- `SeLe4n/Testing/MainTraceHarness.lean` — message fixture update
- `tests/InformationFlowSuite.lean` — test message update

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_smoke.sh` passes (Tier 0-2).
- `IpcMessage.registers` has type `Array Nat`.
- `IpcMessage.caps` has type `Array Capability`.
- Sending a message with > 120 registers returns `ipcMessageTooLarge` error.
- Sending a message with > 3 caps returns `ipcMessageTooManyCaps` error.
- `ipcMessageBounded` predicate defined and proven for send operations.

**Dependencies:** WS-H12a (legacy cleanup — avoids needing to update legacy
`endpointSend` with bounded types).

---

#### WS-H12e: Cross-Subsystem Invariant Reconciliation

**Objective:** Reconcile all cross-subsystem invariant compositions after the
changes in WS-H12a–d. Verify that the full invariant bundle (`ipcInvariantFull`,
`coreIpcInvariantBundle`, `schedulerInvariantBundleFull`, and information-flow
invariants) composes correctly with the updated definitions.

**Findings addressed:** Systemic — ensures no invariant gaps from H12a–d changes.

**Deliverables:**

1. Verify and re-prove `ipcInvariantFull` (IPC/Invariant.lean line 170-171).
   After WS-H12a, `ipcInvariant` subsumes `dualQueueEndpointWellFormed`.
   If `dualQueueSystemInvariant` adds only `tcbQueueLinkIntegrity` beyond
   per-endpoint well-formedness, simplify `ipcInvariantFull` to avoid
   redundant sub-proofs.
2. Re-prove all `*_preserves_ipcInvariantFull` theorems for dual-queue
   operations. These compose `ipcInvariant` and `dualQueueSystemInvariant`
   preservation — both of which were updated in WS-H12a.
3. Re-prove `coreIpcInvariantBundle` compositions in
   `Capability/Invariant.lean` for dual-queue operations. The bundle
   composes scheduler + capability + IPC invariants; verify all three
   components are updated.
4. Verify `schedulerInvariantBundleFull` in `Scheduler/Invariant.lean`
   composes correctly with `contextMatchesCurrent` (WS-H12c) and the
   inverted `queueCurrentConsistent` (WS-H12b). Add
   `contextMatchesCurrent` to the full bundle if appropriate.
5. Re-prove information-flow non-interference theorems in
   `InformationFlow/Invariant.lean` that compose IPC and scheduler
   invariants. The dual-queue NI theorems (`endpointSendDual_NI`,
   `endpointSendDualChecked_NI`, etc.) should only need signature updates.
6. Verify that `schedulerPriorityMatch` (Scheduler/Invariant.lean line
   172-177) is unaffected by dequeue-on-dispatch. The priority mapping
   covers run-queue members; the current thread is no longer a member,
   so the quantifier range shrinks. Verify this is semantically correct.

**Files modified:**
- `SeLe4n/Kernel/IPC/Invariant.lean` — `ipcInvariantFull` reconciliation
- `SeLe4n/Kernel/Capability/Invariant.lean` — bundle compositions
- `SeLe4n/Kernel/Scheduler/Invariant.lean` — full bundle update
- `SeLe4n/Kernel/InformationFlow/Invariant.lean` — NI theorem updates

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- All `*InvariantBundle*` definitions compile and compose.
- All `*_preserves_*InvariantBundle*` theorems compile.
- No theorem references deleted definitions from WS-H12a.

**Dependencies:** WS-H12a, WS-H12b, WS-H12c, WS-H12d (all prior sub-workstreams).

---

#### WS-H12f: Test Harness Update & Documentation Sync

**Objective:** Update the executable trace harness, test fixtures, and all
project documentation to reflect the WS-H12 changes. Verify end-to-end
correctness through trace scenarios that exercise dequeue-on-dispatch, context
switching, bounded messages, and dual-queue-only endpoints.

**Findings addressed:** Documentation component of all H12 findings.

**Deliverables:**

*Part 1 — Trace harness updates:*
1. Add a trace scenario to `SeLe4n/Testing/MainTraceHarness.lean` that
   demonstrates dequeue-on-dispatch:
   - Create two runnable threads at different priorities.
   - Call `schedule` — verify the higher-priority thread becomes `current`
     and is absent from `runQueue.toList`.
   - Call `timerTick` until preemption — verify the preempted thread
     reappears in `runQueue.toList`.
2. Add a trace scenario demonstrating inline context switch:
   - Set `machine.regs` to a distinctive register file.
   - Call `schedule` to switch threads — verify the outgoing thread's
     `registerContext` was saved and the incoming thread's `registerContext`
     was restored into `machine.regs`.
3. Add a trace scenario demonstrating bounded message rejection:
   - Attempt `endpointSendDual` with > 120 registers — verify error.
   - Attempt `endpointSendDual` with > 3 caps — verify error.
   - Attempt `endpointSendDual` with valid payload — verify success.
4. Update `tests/fixtures/main_trace_smoke.expected` to match all new
   trace output.

*Part 2 — Documentation sync:*
5. Update `CHANGELOG.md` with a WS-H12 entry documenting:
   - Legacy endpoint fields and operations removed (A-08/M-01/A-25)
   - Dequeue-on-dispatch scheduler semantics (H-04)
   - Per-TCB register context with inline context switch (H-03)
   - Bounded IPC message payloads (A-09)
6. Update `docs/spec/SELE4N_SPEC.md`:
   - Scheduler section: dequeue-on-dispatch semantics
   - IPC section: bounded message payloads, dual-queue-only endpoints
   - TCB section: register context field
7. Update `docs/DEVELOPMENT.md`:
   - Migration note: legacy `endpointSend`/`endpointReceive`/
     `endpointAwaitReceive` deleted — use `endpointSendDual`/
     `endpointReceiveDual`
8. Update `docs/CLAIM_EVIDENCE_INDEX.md` if claims about scheduler
   semantics or IPC invariants change.
9. Update `docs/codebase_map.json` if file-level descriptions change.
10. Update affected GitBook chapters:
    - `docs/gitbook/11-codebase-reference.md` — remove legacy IPC references
    - `docs/gitbook/12-proof-and-invariant-map.md` — update invariant names
    - `docs/gitbook/08-kernel-performance-optimization.md` — if applicable
11. Update `scripts/test_tier3_invariant_surface.sh` to remove anchors for
    deleted legacy theorems and add anchors for new invariants
    (`contextMatchesCurrent`, bounded message predicates).

**Files modified:**
- `SeLe4n/Testing/MainTraceHarness.lean` — new trace scenarios
- `tests/fixtures/main_trace_smoke.expected` — expected output update
- `CHANGELOG.md` — WS-H12 entry
- `docs/spec/SELE4N_SPEC.md` — spec updates
- `docs/DEVELOPMENT.md` — migration guide
- `docs/CLAIM_EVIDENCE_INDEX.md` — claim updates
- `docs/codebase_map.json` — description updates
- `docs/gitbook/11-codebase-reference.md` — legacy reference removal
- `docs/gitbook/12-proof-and-invariant-map.md` — invariant map update
- `scripts/test_tier3_invariant_surface.sh` — anchor updates

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- Trace harness exercises dequeue-on-dispatch, context switch, and bounded
  messages.
- `main_trace_smoke.expected` fixture matches `lake exe sele4n` output.
- All documentation files updated per PR checklist.
- `scripts/test_tier3_invariant_surface.sh` anchors match current codebase.

**Dependencies:** WS-H12a–e (all implementation sub-workstreams complete).

---

#### WS-H12 Composite Summary

| Sub-workstream | Findings | Estimated Theorems | Risk |
|----------------|----------|--------------------|------|
| **WS-H12a** | A-08, M-01, A-25 | -60 (deletion), +10 (migration) | Low — removes dead code |
| **WS-H12b** | H-04 | ~20 re-proofs | High — invariant inversion |
| **WS-H12c** | H-03 | ~5 new proofs | Medium — new field + inline logic |
| **WS-H12d** | A-09 | ~5 updates | Low — mechanical type change |
| **WS-H12e** | (systemic) | ~15 re-compositions | Medium — cross-cutting |
| **WS-H12f** | (docs/tests) | 0 | Low — documentation only |

**Total execution order:** H12a → H12b → H12c → H12d → H12e → H12f

**Rationale for ordering:**
- **H12a first:** Eliminates ~60 dead legacy theorems before the invariant
  inversion in H12b. Without this, H12b would need to re-prove all 60
  theorems under the new invariant, only to delete them in H12a — wasted work.
- **H12b before H12c:** The `schedule` function body changes in H12b
  (dequeue-on-dispatch). H12c adds inline context switch on top of the H12b
  version. Reversing this order would require modifying `schedule` twice.
- **H12d independent of H12b/c:** Message bounds are orthogonal to scheduler
  changes. Sequenced after H12a (avoids updating deleted legacy operations)
  but could theoretically run in parallel with H12b/c.
- **H12e after all implementation:** Cross-subsystem reconciliation requires
  all individual changes to be in place.
- **H12f last:** Documentation and test fixtures depend on final behavior.

**Composite dependencies:** WS-H1 (IPC bug fix), WS-H5 (dual-queue invariant),
WS-H7 (state field migration). Phase 2 completed.

**Composite exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `Endpoint` structure contains only `sendQ`/`receiveQ`.
- `schedule` dequeues on dispatch with inline context save/restore.
- `IpcMessage` payload bounded by `maxMessageRegisters`/`maxExtraCaps`.
- All invariant bundles compose correctly.
- Documentation and trace fixtures synchronized.

---

### WS-H13: CSpace, Lifecycle & Service Model Enrichment (HIGH)

**Objective:** Add multi-level CSpace resolution, atomic capability move,
service backing-object verification, and establish the `serviceCountBounded`
invariant.

**Entry criteria:** WS-H4 completed (capability invariant redesign provides the
foundation for multi-level CSpace reasoning). Phase 2 completed.

**Findings addressed:**
- **H-01** (HIGH): No multi-level CSpace resolution. Real seL4 implements
  recursive multi-level CSpace resolution where resolving one CNode can yield a
  capability pointing to another CNode. seLe4n resolves exactly one CNode level.
- **A-21** (MEDIUM): `cspaceMove` is not atomic — performs insert-then-delete,
  creating a window where the capability exists in both slots.
- **A-29** (HIGH): Service operations do not verify that `svc.identity.backingObject`
  exists in the object store. `serviceStart` succeeds even if the backing object
  was deleted.
- **A-30** (MEDIUM): Service restart has partial-failure semantics — if stop
  succeeds but start fails, the service remains stopped with no rollback.
- **M-17 / A-31** (MEDIUM): `serviceCountBounded` assumption required for
  acyclicity preservation but never proved as an invariant.

**Deliverables:**

*Part A — Multi-level CSpace resolution (H-01):*
1. Implement `cspaceResolvePath` — a recursive resolution function that follows
   CNode capabilities through multiple levels, with a fuel parameter to bound
   recursion depth (matching seL4's configurable CSpace depth limit).
2. At each level, extract the guard and radix bits from the CNode capability,
   validate the guard match, and use the radix bits to index into the CNode's
   slot table.
3. If the resolved capability points to another CNode, recurse with remaining
   address bits and decremented fuel.
4. Replace single-level `cspaceLookupSlot` in the API with `cspaceResolvePath`.
5. Prove `cspaceResolvePath_terminates` — resolution terminates within fuel
   steps (trivial from fuel parameter).
6. Prove `cspaceResolvePath_deterministic` — the same path always resolves to
   the same capability.
7. Add guard-bit manipulation validation: prove that guard bits are correctly
   matched during resolution (this is the primary CSpace attack surface in
   real kernels).

*Part B — Atomic capability move (A-21):*
8. Refactor `cspaceMove` to compute the final state (source empty, destination
   occupied) before performing any mutation. Apply as a single state update.
9. Prove atomicity: either both source is cleared and destination is populated,
   or neither change occurs.

*Part C — Service backing-object verification (A-29):*
10. Add `st.objects.find? svc.identity.backingObject = some _` check to
    `serviceStart`. Return error if the backing object does not exist.
11. Add the same check to `serviceStop` and `serviceRestart`.
12. Prove: if `serviceStart` succeeds, the backing object exists.

*Part D — Service restart atomicity (A-30):*
13. Refactor `serviceRestart` to capture the pre-stop state and restore it if
    `serviceStart` fails after `serviceStop` succeeds. This provides rollback
    semantics.
14. Prove: `serviceRestart` either fully restarts (stop + start both succeed)
    or leaves the service in its original state.

*Part E — serviceCountBounded invariant (M-17/A-31):*
15. Prove `serviceCountBounded` as a maintained invariant: the number of services
    in the service graph is bounded by `serviceBfsFuel`.
16. Add `serviceCountBounded` to the service invariant bundle.
17. Prove preservation for `serviceRegisterDependency` (the only operation that
    grows the service graph).
18. This closes the gap in the acyclicity preservation proof chain.

**Files modified:**
- `SeLe4n/Kernel/Capability/Operations.lean` — multi-level resolution, atomic move
- `SeLe4n/Kernel/Capability/Invariant.lean` — resolution proofs
- `SeLe4n/Kernel/Service/Operations.lean` — backing-object check, restart atomicity
- `SeLe4n/Kernel/Service/Invariant.lean` — `serviceCountBounded` invariant
- `SeLe4n/Kernel/API.lean` — replace single-level lookup with resolution path

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `cspaceResolvePath` handles multi-level resolution (trace scenario with 2+ levels).
- `cspaceMove` atomicity theorem compiles.
- `serviceStart` fails with error when backing object is missing (negative test).
- `serviceCountBounded` appears as conjunct in service invariant bundle.

**Dependencies:** WS-H4 (capability invariant redesign), Phase 2 completed.

---

### WS-H14: Type Safety & Prelude Foundations (MEDIUM)

**Objective:** Harden the type safety of the foundation layer by encapsulating
typed identifiers, eliminating boilerplate through a derive macro, removing
OfNat instances that bypass type wrappers, and proving foundational lemmas.

**Entry criteria:** Independent — can start at any time. Recommended after
Phase 2 to avoid churn on Prelude during active proof work.

**Findings addressed:**
- **A-02** (HIGH): Typed identifier wrappers are bypassable. All structures have
  public `val` fields. Any code can construct arbitrary IDs via `⟨n⟩` syntax.
- **M-09** (MEDIUM): ~390 lines of near-identical identifier boilerplate. A
  `declare_id` derive macro would eliminate ~300 lines.
- **M-10** (MEDIUM): `OfNat` instances for every identifier type allow
  `(42 : ObjId)` anywhere, silently bypassing the type-safety wrapper.
- **A-01** (MEDIUM): `Inhabited` defaults generate sentinel values (0) without
  guard. Code using `default : ObjId` gets the sentinel silently.
- **A-03** (MEDIUM): Missing explicit `EquivBEq` instances for typed identifiers.
- **M-11 / A-04** (MEDIUM): No `LawfulMonad` instance for `KernelM`.
- **A-06** (MEDIUM): `isPowerOfTwo` correctness unproven.

**Deliverables:**

*Part A — Identifier encapsulation (A-02/M-10):*
1. Make `val` fields private for all 13 typed identifier structures in
   `Prelude.lean`. Expose only `ofNat`/`toNat` converters.
2. Remove `OfNat` instances for typed identifiers. Replace with explicit
   `ObjId.ofNat` calls at construction sites. This prevents accidental
   `(42 : ObjId)` usage while still allowing intentional construction.
3. Update all `⟨n⟩` anonymous constructor patterns across the codebase to
   use `TypeName.mk n` or `TypeName.ofNat n`.
4. Audit `Inhabited` instances: ensure the sentinel (0) is documented as
   invalid and not used in production paths. Add a `isSentinel` predicate.

*Part B — Derive macro (M-09):*
5. Create a `declare_typed_id` macro or derive handler that generates:
   - The structure with private `val : Nat`
   - `DecidableEq`, `Repr`, `Inhabited`, `Hashable`, `BEq`, `LawfulHashable`
   - `toNat`, `ofNat`, `mk` (controlled constructor)
   - Injectivity theorem (`ofNat_injective`)
   - `LawfulBEq` and `EquivBEq` instances (A-03)
6. Replace all 13 identifier blocks with macro invocations.
7. Verify identical semantics by checking that all existing tests pass.

*Part C — Foundational proofs (M-11/A-04/A-06):*
8. Prove `LawfulMonad` for `KernelM`: left identity, right identity,
   associativity. These follow directly from the `Except` monad laws composed
   with state threading.
9. Prove `isPowerOfTwo_correct : isPowerOfTwo n ↔ ∃ k, n = 2^k`. The bitwise
   check `n > 0 && (n &&& (n - 1)) == 0` is standard; the proof uses the
   binary representation of powers of two.

**Files modified:**
- `SeLe4n/Prelude.lean` — major rework (macro, encapsulation, proofs)
- All files using `⟨n⟩` syntax for identifiers — updated to `TypeName.mk n`
- `SeLe4n/Machine.lean` — `isPowerOfTwo_correct` theorem

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- `Prelude.lean` reduced by ~250+ lines via macro.
- `grep -r "OfNat.*ObjId\|OfNat.*ThreadId" SeLe4n/` returns zero matches.
- `LawfulMonad KernelM` instance compiles.
- `isPowerOfTwo_correct` theorem compiles.

**Dependencies:** Independent. Recommended after Phase 2 to minimize churn.

---

### WS-H15: Platform & API Hardening (MEDIUM)

**Objective:** Strengthen the platform binding contracts beyond placeholder
validators and add capability-checking wrappers at the kernel API boundary.

**Entry criteria:** WS-H4 completed (capability invariant redesign for capability
checking), WS-H13 completed (multi-level CSpace for resolution).

**Findings addressed:**
- **A-41** (MEDIUM): RPi5 platform stubs are minimal. Boot and runtime contracts
  use placeholder validators.
- **A-42** (MEDIUM): No capability-checking wrapper at the API boundary. The API
  directly exposes raw kernel operations without verifying caller capabilities.
- **A-33** (MEDIUM): Architecture adapter operations depend on a parameterized
  `RuntimeBoundaryContract`, not a concrete one. Correctness is contingent on
  the platform binding providing correct contracts.
- **M-13** (MEDIUM): `InterruptBoundaryContract` lacks `Decidable` fields,
  creating an asymmetry with `RuntimeBoundaryContract`.

**Deliverables:**

*Part A — API capability checking (A-42):*
1. Define a `SyscallWrapper` that takes a caller ThreadId, an operation, and the
   required capability type, and:
   - Resolves the caller's CSpace root capability.
   - Looks up the required capability via `cspaceResolvePath` (from WS-H13).
   - Validates that the capability has sufficient rights for the operation.
   - Invokes the underlying kernel operation only if all checks pass.
2. Wrap all public API operations in `API.lean` with `SyscallWrapper`.
3. Prove: if a syscall wrapper succeeds, the caller held the required capability
   with sufficient rights.

*Part B — RPi5 platform contracts (A-41):*
4. Replace `interruptRoutingValid` placeholder with a substantive check that
   validates GIC-400 interrupt routing for BCM2712 peripherals.
5. Add `mmioRegionValid` contract checking that MMIO regions (UART, GPIO,
   interrupt controller) do not overlap with kernel memory regions.
6. Add `memorySafetyContract` checking that DMA-capable devices cannot access
   kernel memory regions.
7. Prove that the RPi5 platform binding satisfies `PlatformBinding` typeclass
   with substantive (non-trivial) contract proofs.

*Part C — Adapter concretization (A-33/M-13):*
8. Instantiate `RuntimeBoundaryContract` concretely for the Sim platform,
   providing real implementations of all contract predicates.
9. Add `Decidable` fields to `InterruptBoundaryContract` matching the pattern
   in `RuntimeBoundaryContract`.
10. Prove that the Sim platform's concrete contracts satisfy the adapter's
    parameterized requirements (closing the "AdapterProofHooks never instantiated"
    gap from the v1 audit finding F-18).

**Files modified:**
- `SeLe4n/Kernel/API.lean` — syscall wrappers
- `SeLe4n/Platform/RPi5/RuntimeContract.lean` — substantive contracts
- `SeLe4n/Platform/RPi5/BootContract.lean` — boot validation
- `SeLe4n/Platform/Sim/RuntimeContract.lean` — concrete instantiation
- `SeLe4n/Kernel/Architecture/Assumptions.lean` — `InterruptBoundaryContract`
- `SeLe4n/Kernel/Architecture/Invariant.lean` — adapter proof hooks instantiation

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- All API operations wrapped with capability checks.
- RPi5 `interruptRoutingValid` performs non-trivial GIC-400 validation.
- Sim platform `RuntimeBoundaryContract` instantiated concretely.
- `InterruptBoundaryContract` has `Decidable` fields.

**Dependencies:** WS-H4 (capability invariants), WS-H13 (multi-level CSpace resolution).

---

### WS-H16: Testing, Documentation & Cleanup (MEDIUM)

**Objective:** Close remaining testing gaps, update documentation to match the
current codebase, and address minor structural issues.

**Entry criteria:** Independent — can start at any time and proceed incrementally
as other workstreams complete.

**Findings addressed:**
- **M-18** (MEDIUM): No negative tests for lifecycle operations
  (`lifecycleRetypeObject`, `lifecycleRevokeDeleteRetype`).
- **A-43** (MEDIUM): Tier 3 tests are anchor-based, not proof-based. They verify
  definitions/theorems exist but not what they prove.
- **M-21 / A-45** (MEDIUM): Documentation statistics outdated — CLAUDE.md file
  sizes, README line counts, theorem counts, workstream references all stale.
- **A-13** (MEDIUM): `objectIndex` grows monotonically without bounds. No proof
  connects `id ∈ objectIndex` to `objects[id]? = some _` (liveness).
- **A-18** (MEDIUM): O(n) membership check in `schedule` — `tid ∈ st'.scheduler.runnable`
  uses list membership despite O(1) HashSet available.
- **A-19** (MEDIUM): `threadPriority` consistency in RunQueue not type-enforced.

**Deliverables:**

*Part A — Lifecycle negative tests (M-18):*
1. Add structured negative tests to `tests/NegativeStateSuite.lean` for:
   - `lifecycleRetypeObject` with non-existent source object → expect error.
   - `lifecycleRetypeObject` with active (running) TCB → expect error or cleanup.
   - `lifecycleRevokeDeleteRetype` with non-existent object → expect error.
   - `retypeFromUntyped` with exhausted untyped → expect error.
   - `retypeFromUntyped` with invalid object type → expect error.
2. Each negative test uses `expectError` or `expectOkState` pattern matching
   existing suite conventions.

*Part B — Semantic test assertions (A-43):*
3. Add a new test category to the Tier 3 script (or a new Tier 3.5) that checks
   semantic properties rather than just name anchors:
   - Verify that `capabilityInvariantBundle` contains at least N non-`True`
     conjuncts (prevents regression to trivially-true predicates).
   - Verify that `schedulerInvariantBundle` includes `timeSlicePositive` and
     `edfCurrentHasEarliestDeadline` (after WS-H6).
   - Verify that `NonInterferenceStep` has at least 20 constructors (after WS-H9).
4. These assertions are more robust than name-based checks because they survive
   refactoring while catching substantive regressions.

*Part C — Documentation sync (M-21/A-45):*
5. Update CLAUDE.md "Known large files" with accurate line counts for all files.
6. Update README.md statistics: LoC, file counts, theorem counts, build jobs,
   active workstream references.
7. Update `docs/spec/SELE4N_SPEC.md` with any behavioral changes from WS-H1..H15.
8. Update `docs/CLAIM_EVIDENCE_INDEX.md` if claims changed.
9. Add a "v0.12.15 audit remediation" section to `CHANGELOG.md`.

*Part D — Minor structural fixes (A-13/A-18/A-19):*
10. Add `objectIndex_liveness` theorem: `id ∈ st.objectIndex → st.objects.find? id ≠ none`.
    This connects index membership to object existence, preventing stale index
    entries from creating false positives.
11. Replace `tid ∈ st'.scheduler.runnable` in `schedule` with
    `st'.scheduler.runQueue.contains tid` for O(1) membership check (A-18).
    Prove equivalence via the `flat_wf` + `membership_implies_flat` bidirectional
    invariant from WS-H6.
12. Add structural enforcement for `threadPriority` consistency in RunQueue (A-19):
    define a `runQueueWellFormed` predicate requiring every `tid ∈ membership`
    to have a corresponding `threadPriority[tid]?` entry. Add to
    `schedulerInvariantBundle`.

**Files modified:**
- `tests/NegativeStateSuite.lean` — lifecycle negative tests
- `scripts/test_tier3_invariant_surface.sh` — semantic assertions
- `CLAUDE.md` — file size updates
- `README.md` — statistics updates
- `docs/spec/SELE4N_SPEC.md` — behavioral updates
- `docs/CLAIM_EVIDENCE_INDEX.md` — claim updates
- `CHANGELOG.md` — audit remediation section
- `SeLe4n/Model/State.lean` — `objectIndex_liveness` theorem
- `SeLe4n/Kernel/Scheduler/Operations.lean` — O(1) membership check
- `SeLe4n/Kernel/Scheduler/RunQueue.lean` — `runQueueWellFormed`
- `SeLe4n/Kernel/Scheduler/Invariant.lean` — `runQueueWellFormed` preservation

**Exit evidence:**
- `lake build` passes with zero errors/warnings and zero sorry.
- `test_full.sh` passes (Tier 0-3).
- 5+ new lifecycle negative tests pass.
- Semantic Tier 3 assertions pass for invariant bundle composition.
- CLAUDE.md file sizes match `wc -l` output.
- README.md statistics match actual codebase metrics.
- `objectIndex_liveness` theorem compiles.
- `runQueueWellFormed` appears in `schedulerInvariantBundle`.

**Dependencies:** WS-H6 (for `membership_implies_flat` needed by A-18 fix).
Documentation sync should wait until other workstreams stabilize.

---

## 6. Coverage Verification

### All v1 findings accounted for:

| v1 ID | Severity | Workstream | Status |
|-------|----------|------------|--------|
| A-01 | MEDIUM | WS-H14 | Covered |
| A-02 | HIGH | WS-H14 | Covered |
| A-03 | MEDIUM | WS-H14 | Covered |
| A-04 | MEDIUM | WS-H14 | Covered |
| A-05 | HIGH | WS-H11 | Covered |
| A-06 | MEDIUM | WS-H14 | Covered |
| A-07 | CRITICAL | WS-H7 | Covered |
| A-08 | HIGH | WS-H12 | Covered |
| A-09 | HIGH | WS-H12 | Covered |
| A-10 | CRITICAL | WS-H7 | Covered |
| A-11 | HIGH | WS-H2 | Covered |
| A-12 | HIGH | WS-H11 | Covered |
| A-13 | MEDIUM | WS-H16 | Covered |
| A-14 | CRITICAL | WS-H6 | Covered |
| A-15 | CRITICAL | WS-H6 | Covered |
| A-16 | HIGH | WS-H6 | Covered |
| A-17 | HIGH | WS-H6 | Covered |
| A-18 | MEDIUM | WS-H16 | Covered |
| A-19 | MEDIUM | WS-H16 | Covered |
| A-20 | HIGH | WS-H4 | Covered |
| A-21 | MEDIUM | WS-H13 | Covered |
| A-22 | CRITICAL | WS-H5 | Covered |
| A-23 | HIGH | WS-H5 | Covered |
| A-24 | HIGH | WS-H5 | Covered |
| A-25 | MEDIUM | WS-H12 | Covered |
| A-26 | HIGH | WS-H2 | Covered |
| A-27 | HIGH | WS-H2 | Covered |
| A-28 | MEDIUM | WS-H2 | Covered |
| A-29 | HIGH | WS-H13 | Covered |
| A-30 | MEDIUM | WS-H13 | Covered |
| A-31 | MEDIUM | WS-H13 | Covered |
| A-32 | MEDIUM | WS-H11 | Covered |
| A-33 | MEDIUM | WS-H15 | Covered |
| A-34 | CRITICAL | WS-H10 | Covered |
| A-35 | CRITICAL | WS-H8 | Covered |
| A-36 | HIGH | WS-H8 | Covered |
| A-37 | HIGH | WS-H8 | Covered |
| A-38 | MEDIUM | WS-H10 | Covered |
| A-39 | MEDIUM | WS-H10 | Covered |
| A-40 | MEDIUM | WS-H9 | Covered |
| A-41 | MEDIUM | WS-H15 | Covered |
| A-42 | MEDIUM | WS-H15 | Covered |
| A-43 | MEDIUM | WS-H16 | Covered |
| A-44 | LOW | — | Subsumed by WS-H16 Tier 3 improvements |
| A-45 | MEDIUM | WS-H16 | Covered |

### All v2 findings accounted for:

| v2 ID | Severity | Workstream | Status |
|-------|----------|------------|--------|
| C-01 | CRITICAL | WS-H1 | Covered |
| C-02 | CRITICAL | WS-H9 | Covered |
| C-03 | CRITICAL | WS-H4 | Covered |
| C-04 | CRITICAL | WS-H5 | Covered |
| C-05 | CRITICAL | WS-H10 | Covered |
| H-01 | HIGH | WS-H13 | Covered |
| H-02 | HIGH | WS-H11 | Covered |
| H-03 | HIGH | WS-H12 | Covered |
| H-04 | HIGH | WS-H12 | Covered |
| H-05 | HIGH | WS-H2 | Covered |
| H-06 | HIGH | WS-H2 | Covered |
| H-07 | HIGH | WS-H8 | Covered |
| H-08 | HIGH | WS-H6 | Covered |
| H-09 | HIGH | WS-H7 | Covered |
| H-10 | HIGH | WS-H11 | Covered |
| H-11 | HIGH | WS-H8 | Covered |
| H-12 | HIGH | WS-H3 | Covered |
| M-01 | MEDIUM | WS-H12 | Covered |
| M-02 | MEDIUM | WS-H1 | Covered |
| M-03 | MEDIUM | WS-H4 | Covered |
| M-04 | MEDIUM | WS-H6 | Covered |
| M-05 | MEDIUM | WS-H6 | Covered |
| M-06 | MEDIUM | WS-H6 | Covered |
| M-07 | MEDIUM | WS-H4 | Covered |
| M-08 | MEDIUM | WS-H4 | Covered |
| M-09 | MEDIUM | WS-H14 | Covered |
| M-10 | MEDIUM | WS-H14 | Covered |
| M-11 | MEDIUM | WS-H14 | Covered |
| M-12 | MEDIUM | WS-H11 | Covered |
| M-13 | MEDIUM | WS-H15 | Covered |
| M-14 | MEDIUM | WS-H11 | Covered |
| M-15 | MEDIUM | WS-H9 | Covered |
| M-16 | MEDIUM | WS-H10 | Covered |
| M-17 | MEDIUM | WS-H13 | Covered |
| M-18 | MEDIUM | WS-H16 | Covered |
| M-19 | MEDIUM | WS-H3 | Covered |
| M-20 | MEDIUM | WS-H3 | Covered |
| M-21 | MEDIUM | WS-H16 | Covered |

**Coverage:** 100% of findings from both audits are assigned to workstreams.

---

## 7. Risk Assessment

| Risk | Mitigation |
|------|------------|
| WS-H4 capability invariant redesign invalidates many existing proofs | Use incremental approach: add new predicates alongside existing ones, prove preservation, then remove trivial predicates. Never break the build. |
| WS-H12b dequeue-on-dispatch inverts a core scheduler invariant | Sequenced after WS-H12a (legacy removal) so ~60 dead theorems are deleted before the inversion, avoiding wasted re-proof work. The inverted invariant is proven in isolation within WS-H12b before cross-subsystem reconciliation in WS-H12e. |
| WS-H9 NI coverage is a large proof surface (~18 new theorems) | Prioritize scheduler NI first (highest security impact). Ship in incremental batches rather than one monolithic PR. |
| WS-H7 state field migration touches many downstream proofs | Reuse bisimulation bridge pattern from WS-G2. Bridge first, migrate proofs incrementally. |
| WS-H1 introduces a new IPC state variant affecting all pattern matches | Lean 4's exhaustive match checking will identify all affected locations. Mechanical update. |
| WS-H13 multi-level CSpace resolution introduces recursion | Bound by fuel parameter (matching seL4). Termination is trivially proven by fuel decrement. |
| Phase 5 Prelude changes (WS-H14) cause codebase-wide churn | Schedule after Phases 2-3 stabilize. The derive macro change is mechanical but high-touch. |

---

## 8. Execution Summary

| Phase | Workstreams | Total Findings | Critical Path? |
|-------|-------------|----------------|----------------|
| **Phase 1** | WS-H1, WS-H2, WS-H3 | 10 | Yes — correctness blockers |
| **Phase 2** | WS-H4, WS-H5, WS-H6, WS-H7 | 17 | Yes — proof assurance |
| **Phase 3** | WS-H8, WS-H9, WS-H10 | 14 | Yes — security claims |
| **Phase 4** | WS-H11, WS-H12, WS-H13 | 20 | Hardware readiness |
| **Phase 5** | WS-H14, WS-H15, WS-H16 | 20 | Ongoing quality |
| **Total** | **16** | **~56 distinct** | |

### Parallelism opportunities:
- **Phase 1**: WS-H1, WS-H2, WS-H3 are fully independent — run in parallel.
- **Phase 2**: WS-H7 should complete first (foundation). WS-H4, WS-H5, WS-H6
  can then run in parallel.
- **Phase 3**: WS-H8 should complete before WS-H9. WS-H10 can overlap with both.
- **Phase 4**: WS-H11, WS-H12, WS-H13 are mostly independent after dependencies.
- **Phase 5**: WS-H14, WS-H15, WS-H16 are independent. WS-H16 documentation
  sync should be last.

---

*End of workstream plan — AUDIT_v0.12.15_WORKSTREAM_PLAN.md*
