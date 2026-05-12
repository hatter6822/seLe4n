# WS-RC R5 Deferred-Work Completion Plan

**Status:** PLANNED (planning artefact only; no code changes yet).
**Workstream:** WS-RC (audit remediation v0.30.11 → v0.31.0 → v1.0.0).
**Predecessors landed:**
- `d8e03b9` — initial R5.A..R5.G landing (PR #771).
- `7ffeaf4` — R5 audit pass: closure-form IF helpers, substantive PIP
  test, R5.E comment fix.
- `7a21e18` — R5 deferred-work partial completion (R5.F.1 + R5.C.1
  prominent caller migrated; R5.B.2 + R5.G.3 plan-named theorems
  added in closure form).
**Audit findings driving this plan:** the post-landing audit
identified five plan items (R5.B.2 × 2 named theorems, R5.G.3
preservation, R5.C.1 full unification, §9.12 per-sub-task commits)
that the initial landing avoided or under-delivered.  Items R5.F.1
and R5.C.1's prominent caller landed in `7a21e18`; the present plan
closes the remaining four.
**Target version:** **v1.0.0** — bootable verified microkernel
release.  Per the user directive, **all R5 sub-tasks must be
substantively complete prior to the v1.0.0 cut**.
**Sub-PR count:** 8 atomic units across 5 phases (P, Q, R, S, V).
**Estimated LoC:** ~1250 net (Phase P ≈ 290; Phase Q ≈ 370; Phase R ≈
380; Phase S ≈ 100; Phase V ≈ 110).  See §18 for the detailed
breakdown.
**Files touched:** ~12 source modules + 4 test suites + 4
documentation files.
**Axiom / sorry budget:** 0 (every proof obligation discharged via
existing in-tree lemmas + new lemmas introduced in Phase P).
**Source-of-truth refs:**
- `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §9 — canonical R5 plan.
- `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` §3.H — closure-form
  obligations registered post-landing.
- PR #771 audit comments (chat transcript, deferred-work enumeration).

## Table of contents

1. [Context and motivation](#1-context-and-motivation)
2. [Inventory of remaining R5 tasks](#2-inventory-of-remaining-r5-tasks)
3. [Headline architectural decisions](#3-headline-architectural-decisions)
4. [Sub-PR partition](#4-sub-pr-partition)
5. [Phase P — Foundational lemmas (additive, purely supporting)](#5-phase-p--foundational-lemmas)
6. [Phase Q — R5.B.2 substantive discharges](#6-phase-q--r5b2-substantive-discharges)
7. [Phase R — R5.G.3 substantive discharge](#7-phase-r--r5g3-substantive-discharge)
8. [Phase S — R5.C.1 full deprecation of `effectivePriority`](#8-phase-s--r5c1-full-deprecation-of-effectivepriority)
9. [Phase V — Tests, surface anchors, discharge index, release marker](#9-phase-v--tests-surface-anchors-discharge-index-release-marker)
10. [Commit ordering, dependencies, and per-sub-PR validation](#10-commit-ordering-dependencies-and-per-sub-pr-validation)
11. [Consolidated verification matrix](#11-consolidated-verification-matrix)
12. [Failure-mode register](#12-failure-mode-register)
13. [Discharge-index updates](#13-discharge-index-updates)
14. [Documentation synchronization](#14-documentation-synchronization)
15. [Pre-flight checklist (per sub-PR)](#15-pre-flight-checklist-per-sub-pr)
16. [Rollback strategy](#16-rollback-strategy)
17. [Acceptance criteria](#17-acceptance-criteria)
18. [Total scope summary](#18-total-scope-summary)

---

## 1. Context and motivation

WS-RC R5 (`AUDIT_v0.30.11_WORKSTREAM_PLAN.md §9`, "Scheduler /
Lifecycle behaviour symmetry") closed the seven scheduler/lifecycle
audit findings whose remediation is a behavioural symmetry or
function-split.  The initial PR #771 landed the operational changes
(R5.A split, R5.B PIP recomputation, R5.C `effectiveSchedParams`
addition, R5.D restoreToReady extraction, R5.E
`missingSchedContext` surfacing, R5.F precondition assertion
theorems, R5.G domain propagation) plus 30+ regression tests.

A post-landing audit identified four substantive obligations that
were deferred:

| Plan ref | Obligation | Initial-PR delivery | Audit verdict |
|---|---|---|---|
| §9.4 R5.B.2 | `resumeThread_preserves_blockingAcyclic` (named theorem) | Not delivered; replaced with weaker structural lemmas at intermediate states | AVOIDED |
| §9.4 R5.B.2 | `resumeThread_pipBoost_consistent_with_blocking_graph` (named theorem) | Not delivered; replaced with `_post_restore` variant at an intermediate state | AVOIDED |
| §9.5 R5.C.1 | Unify both helpers to total form ("removing the Option wrapping at the call site") | Added third helper `effectiveSchedParams`; `effectivePriority` retained, callers not migrated | UNDER-DELIVERED |
| §9.8 R5.F.1 | Replace `getD ⟨0⟩` with `match | none => panic!` or restructure call site | Neither delivered; only the assertion theorem (R5.F.2) was added | AVOIDED |
| §9.9 R5.G.3 | Substantive `schedContextConfigure_preserves_boundThreadDomainConsistent` proof | Added closure-form tautology; no substantive discharge | AVOIDED (tautological) |
| §9.12 | Land each sub-task as a separate commit | Single monolithic commit + audit-pass commit | PROCESS VIOLATION |

A subsequent commit (`7a21e18`) substantively closed **R5.F.1** (the
`panic!` form) and **R5.C.1 for `computeMaxWaiterPriority`** (the
prominent caller); the present plan closes the remaining four
obligations to bring R5 to substantive completeness ahead of v1.0.0.

### Why this matters for v1.0.0

The deferred obligations are formal proofs of invariant preservation
across the kernel's resume / configure operations.  Operationally,
these invariants are already held by the implementation (R5.B's PIP
recomputation, R5.G's domain propagation block); what is missing is
the *machine-checked proof* that the post-operation state satisfies
the invariant.  For a "verified microkernel" v1.0.0 release, the
absence of these proofs leaves a gap between operational correctness
and formal guarantee — exactly the gap the plan's
"implement-the-improvement" rule forbids.  Discharging them
substantively before v1.0.0 closes the gap.

### Plan-author audit observations

During plan authoring, three additional micro-concerns were noted
and rolled into the relevant phases:

- **(A)** The `effectivePriority` partial helper, even after its
  most prominent caller migrates to `effectiveSchedParams`, remains
  reachable from `Liveness/TraceModel.lean`, `Preservation.lean`'s
  test theorem, and 4 places in `PriorityInheritanceSuite.lean`.
  Full deprecation requires migrating all five reference sites and
  removing the helper definition itself (Phase S).
- **(B)** The plan's pseudocode for R5.B.2's
  `_pipBoost_consistent_with_blocking_graph` references
  `st'.scheduler.blockingGraph` — but `SystemState.scheduler` has no
  `blockingGraph` field; the blocking graph is derived dynamically
  from `objects.ipcState`.  The correct theorem statement
  substitutes `computeMaxWaiterPriority st' vtid.val` for the
  pseudocode's `computeMaxWaiterPriority st'.scheduler.blockingGraph
  tid` (Phase Q2).  The plan's pseudocode is recorded as
  ERRATA-R5-1 in `AUDIT_v0.30.11_ERRATA.md` (Phase V).
- **(C)** R5.G.3's substantive proof requires
  `schedContextBindingConsistent` as an additional pre-state
  hypothesis beyond the plan's stated `hInv :
  boundThreadDomainConsistent st`.  Without it, a dangling-binding
  corner case (TCB binds to `vScId.val.toNat` but
  `sc.boundThread ≠ some tid`) could be silently broken by R5.G's
  domain rewrite.  Phase R's theorem signature is strengthened to
  require both invariants; the strengthening is justified by the
  observation that both are conjuncts of
  `schedulerInvariantBundleExtended` (Phase R2).  The strengthening
  is recorded as ERRATA-R5-2 in `AUDIT_v0.30.11_ERRATA.md`.

These three micro-observations represent the "implement-the-
improvement" rule applied uniformly to plan text that drifted
inadequately from the live source.

---

## 2. Inventory of remaining R5 tasks

| Phase | Plan ref | Task ID | Description | Severity | Estimated LoC | Owning sub-PR |
|---|---|---|---|---|---|---|
| P | §9.4 R5.B.2a | `blockingAcyclic_of_subgraph` lemma | Subgraph-of-acyclic-graph preserves acyclicity (induction on chain) | Foundational | 80–120 | P1 |
| P | §9.4 R5.B.2b | `computeMaxWaiterPriority_frame` lemma | Frame argument for unchanged ipcState/priority/binding | Foundational | 40–60 | P1 |
| P | §9.9 R5.G.3 | `objects_insert_at_other_preserves_boundThreadDomainConsistent` frame | Frame for object updates at non-bound non-SC ObjIds | Foundational | 60–80 | P2 |
| P | §9.9 R5.G.3 | `objects_update_sync_domain_preserves_boundThreadDomainConsistent` frame | Joint SC + bound-TCB synchronous-domain update | Foundational | 80–150 | P2 |
| Q | §9.4 R5.B.2 | `restoreToReady_preserves_blockingAcyclic` | Composition step 1: H3a subgraph reduces blocking graph monotonically | Substantive | 60–100 | Q1 |
| Q | §9.4 R5.B.2 | `resumeThread_preserves_blockingAcyclic` | Full operational composition: H3a + H3c + H4 + H5 | Substantive | 100–150 | Q1 |
| Q | §9.4 R5.B.2 | `ensureRunnable_preserves_computeMaxWaiterPriority` | Frame for H4 step | Auxiliary | 30–50 | Q2 |
| Q | §9.4 R5.B.2 | `schedule_preserves_computeMaxWaiterPriority` | Frame for H5 step | Auxiliary | 40–80 | Q2 |
| Q | §9.4 R5.B.2 | `resumeThread_pipBoost_consistent_with_blocking_graph` | Substantive post-state pipBoost-vs-graph theorem | Substantive | 80–120 | Q2 |
| R | §9.9 R5.G.3 | `schedContextConfigure_post_state_shape` (or equivalent decomposition) | Operational characterisation of the success path | Substantive | 100–150 | R1 |
| R | §9.9 R5.G.3 | `schedContextConfigure_preserves_boundThreadDomainConsistent` | Full composition via Phase P frame lemmas | Substantive | 150–250 | R2 |
| S | §9.5 R5.C.1 | Migrate remaining `effectivePriority` callers | `TraceModel.lean`, `Preservation.lean`, 4× `PriorityInheritanceSuite.lean` | Mechanical | 40–60 | S1 |
| S | §9.5 R5.C.1 | Delete `effectivePriority` definition + its 4 dependent theorems (3 helpers + 1 bridge) | Once migrations land, all are dead code (statements reference the deleted `effectivePriority`) | Mechanical | 30–50 | S1 |
| V | All | Test additions (substantive surface anchors) | `LivenessSuite.lean` adds 6 new surface anchors for the new theorems | Mechanical | 10–15 | V1 |
| V | All | Discharge index, errata, CHANGELOG, CLAUDE.md, WORKSTREAM_HISTORY | Document the substantive landing | Mechanical | 60–100 | V1 |

**Total estimated**: ~1100 LoC net across ~12 source modules + 4 test
suites + 4 documentation files.  Axiom / sorry budget: **0**.

---

## 3. Headline architectural decisions

### 3.1 Proof-engineering strategy: small composable lemmas

Each substantive theorem is decomposed into **3–5 named sub-lemmas**
proven independently in Phase P, then composed in Phase Q / R.  This
trades one ~250 LOC monolithic proof for 5 × ~50 LOC focused proofs
that each carry their own meaning.

**Justification**: prior monolithic-proof attempts (the failed
proof in commit `7a21e18`'s diff) ran into:
- Syntax parsing failures on multi-line `let`-in-`have` bindings.
- `split at hOk` producing branches in unexpected orders that
  invalidated the proof's branch ordering.
- Frame-rewriting through nested `RHTable.insert` calls failing on
  `RHTable_get?_insert_ne` projection name mismatches.

Each sub-lemma scoped to a single state update sidesteps all three
issues by keeping the term tree shallow.

### 3.2 Frame lemma vs operational unfolding

For Phase R (`schedContextConfigure_preserves_boundThreadDomainConsistent`),
the proof is decomposed as:

  Phase R1: **Operational characterisation** — a lemma stating
  "if `schedContextConfigure ... = .ok ((), st')`, then
  `st'.objects[oid]?` is determined by an explicit function of
  `oid`, `st`, `vScId`, and the configured values, derived from a
  case-split on the binding/TCB-lookup result."

  Phase R2: **Invariant transfer** — uses Phase R1's operational
  characterisation to apply the Phase P2 frame lemmas at the four
  modified ObjIds (in the worst case: vScId.val for the SC,
  boundTid.toObjId for the post-domain-propagation TCB; plus
  potentially the same TCB at the post-priority-propagation step,
  if the priority differs).

This decomposition is the same shape used by the existing
`AK6-F.18 suspendThread_preserves_projection` (which uses 9 sub-helpers
for its 9 phases).

### 3.3 Hypothesis strengthening: `schedContextBindingConsistent`

R5.G.3's plan signature uses only `hInv : boundThreadDomainConsistent
st`.  The plan author's audit observation (C above) noted this is
insufficient — a dangling-binding corner case (TCB has `.bound scId`
but `sc.boundThread ≠ some tid`) would be silently broken by R5.G's
domain rewrite.

**Decision**: strengthen the theorem's signature to require BOTH
`boundThreadDomainConsistent` AND `schedContextBindingConsistent` as
pre-state hypotheses.  Justification:

- Both invariants are conjuncts of
  `schedulerInvariantBundleExtended` (defined at
  `SeLe4n/Kernel/Scheduler/Invariant.lean:875`).  Wherever R5.G.3
  is consumed in a production-call-chain proof, the bundle is
  available, so the strengthening costs nothing at the call site.
- The strengthening is recorded as **ERRATA-R5-2** in
  `AUDIT_v0.30.11_ERRATA.md` (Phase V).
- The plan-named theorem's signature (with the strengthening) is
  the SUBSTANTIVE version; the closure-form variant currently in
  place is removed after substantive landing (no namespace
  collision).

### 3.4 `effectivePriority` deletion vs `@[deprecated]` retention

R5.C.1 asks for unifying the two helpers under one convention.
Two options:

| Option | Operational change | Maintenance burden |
|---|---|---|
| **A. Delete `effectivePriority`** | Remove the def + 3 helper theorems; update all callers. | One-shot mechanical effort; clean codebase afterward. |
| **B. Mark `@[deprecated]`** | Keep both; emit Lean linter warning at usage sites. | Persistent maintenance burden; legacy API never goes away. |

**Decision: Option A** (deletion).  Justification:

- The plan explicitly recommended unification.  Keeping both is the
  "or document" alternative that CLAUDE.md's implement-the-
  improvement rule strikes.
- The 4 caller sites (`TraceModel.lean` × 1,
  `Preservation.lean` × 1, `PriorityInheritanceSuite.lean` × 4) are
  all mechanical migrations.
- After migration, `effectivePriority` (the def) plus its 3 helper
  theorems (`effectivePriority_unbound`, `effectivePriority_ge_pipBoost`,
  `effectivePriority_noPip`) are dead code; deleting them shrinks
  the proof surface.
- The witness theorem
  `effectivePriority_some_eq_effectiveSchedParams` is renamed to
  `effectiveSchedParams_eq_partial_resolution` and kept as
  historical documentation — it's still proven and is useful as a
  bridge to old papers/audit reports that reference the partial
  API.

### 3.5 Sub-PR atomicity and reviewability

Per §9.12's deferred-process item, this plan commits to **one
substantive change per sub-PR**.  Every sub-PR:

1. Passes `lake build` (default target, 312+ jobs) cleanly.
2. Passes `scripts/test_smoke.sh`.
3. Passes `scripts/ak7_cascade_check_monotonic.sh`.
4. Touches files that fit in a single coherent review.
5. Carries a `Refs:` line pointing at this plan's relevant phase
   section.

Sub-PRs land as individual commits (not squashed) so `git bisect`
can isolate regressions to the specific sub-task.

### 3.6 No `axiom` / `sorry` budget

Every proof obligation introduced in this plan is dischargeable from
existing in-tree lemmas plus the Phase P additions.  The
`axiom_count` and `sorry_count` AK7 monotonicity gates remain at 0
through every sub-PR.

If, during execution, a proof obligation appears intractable, the
correct response is:

- Decompose into smaller named lemmas (Phase P augmentation).
- NOT introduce `sorry` even temporarily — the pre-commit hook
  rejects staged content with `sorry`.

---

## 4. Sub-PR partition

| Sub-PR | Phase | Slice | Files touched | Est. LoC | Builds |
|---|---|---|---|---|---|
| P1 | P | `blockingAcyclic_of_subgraph` + `computeMaxWaiterPriority_frame` foundational lemmas | `SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean`, `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean` | ~150 | All of `SeLe4n.Kernel.Scheduler.PriorityInheritance.*` |
| P2 | P | `objects_*_preserves_boundThreadDomainConsistent` frame lemmas | `SeLe4n/Kernel/Scheduler/Invariant.lean` (or a new `Scheduler/Invariant/Frame.lean`) | ~140 | Scheduler invariant chain |
| Q1 | Q | `restoreToReady_preserves_blockingAcyclic` + `resumeThread_preserves_blockingAcyclic` substantive | `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` | ~180 | Lifecycle preservation chain |
| Q2 | Q | `*_preserves_computeMaxWaiterPriority` frames + `resumeThread_pipBoost_consistent_with_blocking_graph` substantive | `SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean` | ~190 | Same chain |
| R1 | R | Operational characterisation of `schedContextConfigure`'s success path | `SeLe4n/Kernel/SchedContext/Invariant/Preservation.lean` | ~130 | SchedContext preservation chain |
| R2 | R | Substantive `schedContextConfigure_preserves_boundThreadDomainConsistent` | Same | ~250 | Same |
| S1 | S | `effectivePriority` full deprecation | `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean`, `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean`, `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`, `tests/PriorityInheritanceSuite.lean` | ~100 | All R5 chains green |
| V1 | V | Tests + surface anchors + discharge index + CHANGELOG/CLAUDE.md/WORKSTREAM_HISTORY + errata | `tests/LivenessSuite.lean`, `tests/SuspendResumeSuite.lean`, 5 docs files | ~110 | Test smoke green |

Total: **8 sub-PRs**, **~1250 LoC** (including documentation).

---

## 5. Phase P — Foundational lemmas

### Phase P goal

Add reusable, self-contained foundational lemmas that the substantive
proofs in Phase Q and Phase R consume.  Phase P additions are
**purely additive** (no existing function or theorem changes) and
purely **proof-layer** (no operational semantics change).

### Sub-PR P1 — Blocking-graph subgraph + computeMaxWaiterPriority frame

**Location**:
`SeLe4n/Kernel/Scheduler/PriorityInheritance/BlockingGraph.lean` (new
theorems append at the end); `SeLe4n/Kernel/Scheduler/PriorityInheritance/Compute.lean`
(new frame theorem).

**Theorems to add**:

1. `blockingAcyclic_of_subgraph` — substantive new lemma.

   ```lean
   /-- WS-RC R5.B.2 / Phase P1: If the post-state's blocking graph is
       a subgraph of the pre-state's (each node either has the same
       server or no server), and the object-index length is
       preserved, then post-state acyclicity follows from pre-state
       acyclicity.

       Proof: by induction on the blockingChain fuel.  Any chain in
       the post-state at node `t` is either:
       - empty (server = none), trivially acyclic-respecting;
       - a head edge `t → t'` where `t'` is the post-state server;
         post-state server = pre-state server (by hypothesis), so the
         tail recurses on the pre-state chain at `t'`.
       Thus the post-state chain at `t` is a (prefix of the) pre-
       state chain at `t`.  By pre-state acyclicity, `t` is not in
       the pre-state chain at `t`, hence not in any prefix; not in
       the post-state chain at `t`. -/
   theorem blockingAcyclic_of_subgraph
       (st st' : SystemState)
       (hPre : blockingAcyclic st)
       (hServer : ∀ tid,
         blockingServer st' tid = none ∨
         blockingServer st' tid = blockingServer st tid)
       (hObjLen : st'.objectIndex.length = st.objectIndex.length) :
       blockingAcyclic st'
   ```

   Proof: induction on `objectIndex.length` (the fuel of
   `blockingChain`).  Key step: `t ∈ blockingChain st' t fuel ⇒
   t ∈ blockingChain st t fuel` by structural induction.  The base
   case (fuel = 0) is `simp [blockingChain]`.  The induction step
   uses `blockingChain_step` and case-splits on `blockingServer st'
   t`.

   Estimated LoC: 80–120.

2. `computeMaxWaiterPriority_frame` — substantive new lemma.

   ```lean
   /-- WS-RC R5.B.2 / Phase P1: If the post-state's objects table
       agrees with the pre-state on every TCB's ipcState,
       schedContextBinding, priority, deadline, domain, and pipBoost
       (the fields that `computeMaxWaiterPriority` reads), AND
       agrees on every SchedContext's priority/deadline/domain (read
       by `effectiveSchedParams` for bound waiters), then
       `computeMaxWaiterPriority` is invariant. -/
   theorem computeMaxWaiterPriority_frame
       (st st' : SystemState) (tid : ThreadId)
       (hTcb : ∀ t tcb,
         st.objects[t.toObjId]? = some (.tcb tcb) →
         ∃ tcb', st'.objects[t.toObjId]? = some (.tcb tcb') ∧
                 tcb'.ipcState = tcb.ipcState ∧
                 tcb'.schedContextBinding = tcb.schedContextBinding ∧
                 tcb'.priority = tcb.priority ∧
                 tcb'.deadline = tcb.deadline ∧
                 tcb'.domain = tcb.domain ∧
                 tcb'.pipBoost = tcb.pipBoost)
       (hSc : ∀ scId sc,
         st.objects[scId.toObjId]? = some (.schedContext sc) →
         ∃ sc', st'.objects[scId.toObjId]? = some (.schedContext sc') ∧
                sc'.priority = sc.priority ∧
                sc'.deadline = sc.deadline ∧
                sc'.domain = sc.domain)
       (hObjIdx : st'.objectIndex = st.objectIndex) :
       computeMaxWaiterPriority st' tid = computeMaxWaiterPriority st tid
   ```

   Proof: unfold `computeMaxWaiterPriority`; `waitersOf` reads
   `tcb.ipcState` (invariant via hTcb); the fold-body reads
   `effectiveSchedParams` which reads `tcb.{priority, deadline,
   domain, schedContextBinding, pipBoost}` (all invariant) and
   `sc.{priority, deadline, domain}` (all invariant).  The fold
   produces the same accumulator at every step.

   Estimated LoC: 40–60.

**Build verification**:
- `lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.BlockingGraph`
- `lake build SeLe4n.Kernel.Scheduler.PriorityInheritance.Compute`
- `lake build` (default target, 312 jobs).

**Test verification**:
- `scripts/test_fast.sh` (Tier 0+1).

**Failure modes**:
- The chain-induction for `blockingAcyclic_of_subgraph` may hit a
  termination issue on `fuel + 1 → fuel`.  Mitigation: use
  `Nat.rec` with explicit motive instead of `induction fuel`.

### Sub-PR P2 — boundThreadDomainConsistent frame lemmas

**Location**:
`SeLe4n/Kernel/Scheduler/Invariant.lean` (or split into
`SeLe4n/Kernel/Scheduler/Invariant/Frame.lean` if line count exceeds
the file's current 922 LoC limit).

**Theorems to add**:

1. `objects_insert_at_non_bound_non_sc_preserves_boundThreadDomainConsistent`
   — frame lemma for object updates at ObjIds OTHER than the
   bound-TCB and the configured SC.

   ```lean
   /-- WS-RC R5.G.3 / Phase P2: An object-table update at an ObjId
       that is NEITHER the configured SC's slot NOR the bound TCB's
       slot preserves `boundThreadDomainConsistent`.  This is the
       "frame" component used in Phase R2 to discharge the
       non-modified (tid, scId) pairs. -/
   theorem objects_insert_at_other_preserves_boundThreadDomainConsistent
       (st : SystemState) (oid : ObjId) (obj : KernelObject)
       (hDom : boundThreadDomainConsistent st) :
       boundThreadDomainConsistent
         { st with objects := st.objects.insert oid obj }
   ```

   Wait — this is too coarse: an insert at `oid` could break the
   invariant if `oid` happens to be a bound thread's slot.  The
   correct frame lemma is conditional on `oid`'s nature:

   ```lean
   /-- Frame lemma: an insert at `oid` of a non-TCB / non-SC object
       (e.g., endpoint or notification) is always safe because the
       invariant body case-splits on TCB and SC variants. -/
   theorem objects_insert_non_tcb_non_sc_preserves_boundThreadDomainConsistent
       (st : SystemState) (oid : ObjId) (obj : KernelObject)
       (hObj : ∀ tcb, obj ≠ .tcb tcb)
       (hSc : ∀ sc, obj ≠ .schedContext sc)
       (hDom : boundThreadDomainConsistent st) :
       boundThreadDomainConsistent
         { st with objects := st.objects.insert oid obj }
   ```

   Proof: for any (tid, scId) pair, the post-state lookup at
   `tid.toObjId` is either the inserted value (which is neither TCB
   nor SC, so the outer match falls into the catch-all `True`
   branch) or the pre-state lookup (frame via `getElem?_insert_ne`).
   Similar reasoning for `scId.toObjId`.

   Estimated LoC: 60–80.

2. `objects_update_sync_domain_preserves_boundThreadDomainConsistent`
   — joint SC + TCB synchronous-domain frame lemma.

   ```lean
   /-- WS-RC R5.G.3 / Phase P2: A joint update that rewrites a
       SchedContext's `domain` to `⟨domain⟩` AND rewrites its bound
       TCB's `domain` to `⟨domain⟩` (synchronously) preserves
       `boundThreadDomainConsistent`, under the additional
       hypotheses that the SC's bound thread is the modified TCB and
       no other binding inconsistency exists pre-state
       (`schedContextBindingConsistent`). -/
   theorem objects_update_sync_domain_preserves_boundThreadDomainConsistent
       (st : SystemState) (scObjId : ObjId) (sc : SchedContext)
       (boundTid : ThreadId) (boundTcb : TCB) (domain : Nat)
       (hSc : st.objects[scObjId]? = some (.schedContext sc))
       (hSCBT : sc.boundThread = some boundTid)
       (hTcb : st.objects[boundTid.toObjId]? = some (.tcb boundTcb))
       (hTcbBind : boundTcb.schedContextBinding = .bound ⟨scObjId.toNat⟩)
       (hNeq : boundTid.toObjId ≠ scObjId)
       (hDom : boundThreadDomainConsistent st)
       (hBind : schedContextBindingConsistent st)
       (sc' : SchedContext) (tcb' : TCB)
       (hSCDom' : sc'.domain = ⟨domain⟩)
       (hSCBT' : sc'.boundThread = sc.boundThread)
       (hTcbDom' : tcb'.domain = ⟨domain⟩)
       (hTcbBind' : tcb'.schedContextBinding = boundTcb.schedContextBinding) :
       let st' : SystemState := { st with objects :=
         (st.objects.insert scObjId (.schedContext sc')).insert boundTid.toObjId (.tcb tcb') }
       boundThreadDomainConsistent st'
   ```

   This is the **already-attempted** frame lemma from commit
   `7a21e18` (`SeLe4n/Kernel/SchedContext/Invariant/Preservation.lean`
   diff).  It encountered build errors in the original attempt; the
   fixes will:

   a) Move the `let st' := ...` to a `have hSt'Eq` clause to avoid
      the multi-line record-with-in-statement-type parse issue.
   b) Use `RobinHood.RHTable.getElem?_insert_self` /
      `RobinHood.RHTable.getElem?_insert_ne` directly (not the bare
      `RHTable.get?_insert_*` variants).
   c) Take `st.objects.invExt` as an explicit hypothesis (consistent
      with `VSpaceInvariant.lean`'s pattern at lines 304, 461, 590,
      640, 691, 736, 786, 831).
   d) Use `ObjId.toNat_ofNat` and `ObjId.ofNat_toNat` as named
      lemmas (added in Phase P2 if not already present) to bridge
      `scId.toObjId.toNat = scId.toNat`.

   Estimated LoC: 80–150 (target ~120 with the fixes).

**Build verification**:
- `lake build SeLe4n.Kernel.Scheduler.Invariant` (or
  `SeLe4n.Kernel.Scheduler.Invariant.Frame` if split).
- `lake build` (default target).

**Failure modes**:
- The `scId.toObjId = scObjId` lifting may require an explicit
  `ObjId.ofNat` / `SchedContextId.toObjId` round-trip lemma.
  Mitigation: prove
  `theorem SchedContextId.toObjId_ofNat (n : Nat) : (⟨n⟩ :
  SchedContextId).toObjId = ObjId.ofNat n := rfl` if not already
  present.
- If `st.objects.invExt` isn't accessible as a structure projection
  (it's a Prop), the lemma must take it explicitly as a hypothesis.
  All Phase R consumers route through `crossSubsystemInvariant` or
  `schedulerInvariantBundleExtended`, both of which include it.

---

## 6. Phase Q — R5.B.2 substantive discharges

### Phase Q goal

Discharge the two plan-named theorems for `resumeThread` substantively,
replacing the closure-form variants currently in place
(`resumeThread_preserves_blockingAcyclic`,
`resumeThread_pipBoost_consistent_with_blocking_graph` — both
take `hProp` as the closure).  After Phase Q, both theorems are
direct proofs from the operation's success hypothesis.

### Sub-PR Q1 — blockingAcyclic preservation

**Location**:
`SeLe4n/Kernel/Lifecycle/Invariant/SuspendPreservation.lean`.

**Theorems to add / strengthen**:

1. `restoreToReady_preserves_blockingAcyclic` — composition step 1.

   ```lean
   /-- WS-RC R5.B.2 / Phase Q1: `restoreToReady` preserves
       `blockingAcyclic`.  Operational rationale: setting
       `ipcState := .ready` on the target TCB removes its outgoing
       edge in the blocking graph; removing edges preserves
       acyclicity (subgraph lemma).

       The proof uses Phase P1's `blockingAcyclic_of_subgraph` after
       establishing:
       1. `restoreToReady_objectIndex_eq` (already present): the
          object-index length is preserved.
       2. The per-thread blockingServer is either `none` (for the
          target tid) or unchanged (for all other tids). -/
   theorem restoreToReady_preserves_blockingAcyclic
       (st : SystemState) (tid : ThreadId)
       (hAcyclic : PriorityInheritance.blockingAcyclic st) :
       PriorityInheritance.blockingAcyclic (restoreToReady st tid)
   ```

   Proof: invoke `blockingAcyclic_of_subgraph` with:
   - `hServer t` case-splits on `t = tid`:
     - If yes: `blockingServer (restoreToReady st tid) tid = none`
       (because the post-state TCB at tid has `ipcState = .ready`,
       and `blockingServer` returns `none` for any non-`.blockedOnReply
       _ (some _)` ipcState).
     - If no: `restoreToReady` only modifies the TCB at `tid`, so
       the TCB at `t` is unchanged; `blockingServer` reads only the
       TCB, so unchanged.
   - `hObjLen`: directly by `restoreToReady_objectIndex_eq`.

   Estimated LoC: 60–100.

2. `resumeThread_preserves_blockingAcyclic` (substantive
   replacement of the current closure form).

   ```lean
   /-- WS-RC R5.B.2 / Phase Q1: `resumeThread` preserves
       `blockingAcyclic`.

       Operational composition:
       - H3a (`restoreToReady`): subgraph reduction (use
         `restoreToReady_preserves_blockingAcyclic`).
       - H3c (TCB insert with threadState/pipBoost update):
         `blockingServer` reads only `ipcState`, which is unchanged
         at this step (the inserted TCB has `ipcState := .ready`
         from H3a, same as before H3c).  Frame via
         `blockingAcyclic_frame` (existing).
       - H4 (`ensureRunnable`): modifies `scheduler.runQueue` only;
         `blockingServer` is invariant.  Frame.
       - H5 (optional `schedule`): modifies `machine.regs` and
         possibly `tcb.registerContext`; `blockingServer` reads
         `ipcState`, unchanged.  Frame. -/
   theorem resumeThread_preserves_blockingAcyclic
       (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
       (hAcyclic : PriorityInheritance.blockingAcyclic st)
       (hOk : resumeThread st vtid = .ok st') :
       PriorityInheritance.blockingAcyclic st'
   ```

   Proof: unfold `resumeThread`; `split` on H1; for the success
   path, sequentially apply:
   - `restoreToReady_preserves_blockingAcyclic` for H3a.
   - `blockingAcyclic_frame` for H3c (after establishing
     blockingServer-invariance at the H3c TCB insert — the inserted
     TCB has the same ipcState as the post-H3a TCB at tid).
   - `blockingAcyclic_frame` for H4 (ensureRunnable doesn't touch
     objects).
   - For H5 (conditional schedule): if `needsReschedule = false`,
     no further state change; if true, `schedule_preserves_blockingAcyclic`
     (existing, or new in Phase Q2 if absent).

   Estimated LoC: 100–150.

**Test additions**:

- `tests/SuspendResumeSuite.lean::sr027c_resumeThread_preserves_blockingAcyclic`:
  runtime test exercising the theorem on a concrete suspend/resume
  trace with reply-blocked waiters.  (~15 LoC)

**Build verification**:
- `lake build SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation`.

**Failure modes**:
- The `restoreToReady` blockingServer-invariance proof may fail at
  the `t = tid` case if the post-state TCB's `ipcState` projection
  doesn't simplify cleanly.  Mitigation: use
  `restoreToReady_objects_eq_at_tid` (existing) to obtain the
  post-state TCB shape, then read `ipcState = .ready` directly.

### Sub-PR Q2 — pipBoost-consistent-with-blocking-graph

**Location**: same.

**Theorems to add**:

1. `ensureRunnable_preserves_computeMaxWaiterPriority` —
   auxiliary frame.

   ```lean
   /-- WS-RC R5.B.2 / Phase Q2: `ensureRunnable` modifies only
       `scheduler.runQueue`; it does not touch `objects`, so
       `computeMaxWaiterPriority` is invariant. -/
   theorem ensureRunnable_preserves_computeMaxWaiterPriority
       (st : SystemState) (tid : ThreadId) (target : ThreadId) :
       computeMaxWaiterPriority (ensureRunnable st tid) target
       = computeMaxWaiterPriority st target
   ```

   Proof: `ensureRunnable` is defined in `Kernel/IPC/Operations/Endpoint.lean`;
   it pattern-matches and modifies `scheduler.runQueue`.  Object
   table is unchanged across both branches.  Apply
   `computeMaxWaiterPriority_frame` from Phase P1 with the identity
   witnesses.

   Estimated LoC: 30–50.

2. `schedule_preserves_computeMaxWaiterPriority` — auxiliary frame.

   ```lean
   /-- WS-RC R5.B.2 / Phase Q2: `schedule` modifies machine.regs and
       (optionally) one TCB's `registerContext`; the fields read by
       `computeMaxWaiterPriority` (ipcState, schedContextBinding,
       priority, deadline, domain, pipBoost on TCBs;
       priority/deadline/domain on SCs) are invariant.  Hence
       `computeMaxWaiterPriority` is preserved. -/
   theorem schedule_preserves_computeMaxWaiterPriority
       (st st' : SystemState) (target : ThreadId)
       (hSched : schedule st = .ok ((), st')) :
       computeMaxWaiterPriority st' target
       = computeMaxWaiterPriority st target
   ```

   Proof: unfold `schedule`; observe that `saveOutgoingContext` and
   `restoreIncomingContext` only modify `registerContext` and
   `machine.regs`, which are not read by
   `computeMaxWaiterPriority` (it reads `ipcState`, binding,
   priority, deadline, domain, pipBoost).  Apply Phase P1 frame.

   Estimated LoC: 40–80.

3. `resumeThread_pipBoost_consistent_with_blocking_graph` —
   substantive replacement of the closure form.

   ```lean
   /-- WS-RC R5.B.2 / Phase Q2: After `resumeThread`, the resumed
       TCB's `pipBoost` equals
       `computeMaxWaiterPriority st' vtid.val`. -/
   theorem resumeThread_pipBoost_consistent_with_blocking_graph
       (st st' : SystemState) (vtid : SeLe4n.ValidThreadId)
       (hOk : resumeThread st vtid = .ok st') :
       ∀ tcb', st'.getTcb? vtid.val = some tcb' →
         tcb'.pipBoost = PriorityInheritance.computeMaxWaiterPriority st' vtid.val
   ```

   Proof:
   - From `resumeThread_pipBoost_consistent_post_restore` (existing),
     the post-H3c TCB at tid has `pipBoost = computeMaxWaiterPriority
     (restoreToReady st tid) tid`.
   - From `ensureRunnable_preserves_computeMaxWaiterPriority`, H4
     preserves `computeMaxWaiterPriority`.
   - From `schedule_preserves_computeMaxWaiterPriority`, optional H5
     preserves it.
   - From `restoreToReady`-related frame lemmas, H3c (the TCB
     insert) preserves `computeMaxWaiterPriority` for the resumed
     thread (since the insert only changes tid's TCB, not the
     waiters reading from waitersOf st tid).
   - Compose: post-state `computeMaxWaiterPriority st' tid =
     computeMaxWaiterPriority (restoreToReady st tid) tid = newPipBoost
     = tcb'.pipBoost`.

   Estimated LoC: 80–120.

**Test additions**:

- `tests/SuspendResumeSuite.lean::sr027d_resumeThread_pipBoost_matches_graph`:
  runtime test exercising the theorem with a concrete waiter +
  resume trace.  (~20 LoC)

**Build verification**:
- `lake build SeLe4n.Kernel.Lifecycle.Invariant.SuspendPreservation`.
- `lake build SeLe4n.Kernel.IPC.Operations.Endpoint` (for
  `ensureRunnable`'s definition site).
- `lake build SeLe4n.Kernel.Scheduler.Operations.Core` (for
  `schedule`).

**Failure modes**:
- `schedule_preserves_computeMaxWaiterPriority` may need to thread
  through `saveOutgoingContextChecked` instead of
  `saveOutgoingContext` if the unchecked form's TCB-lookup-failure
  path is reachable.  Mitigation: case-split on
  `currentThreadValid` (a sub-conjunct of
  `schedulerInvariantBundleExtended`).

---

## 7. Phase R — R5.G.3 substantive discharge

### Phase R goal

Discharge `schedContextConfigure_preserves_boundThreadDomainConsistent`
substantively, replacing the closure-form variant currently in place.
This is the largest single proof in the deferred work; we decompose
into operational characterisation (R1) + invariant composition (R2).

### Sub-PR R1 — Operational characterisation

**Location**:
`SeLe4n/Kernel/SchedContext/Invariant/Preservation.lean`.

**Theorems to add**:

1. `schedContextConfigure_success_objects_shape` — characterise
   `st'.objects` as a function of inputs.

   ```lean
   /-- WS-RC R5.G.3 / Phase R1: Operational characterisation of
       `schedContextConfigure`'s success path.

       If `schedContextConfigure vScId budget period priority
       deadline domain st = .ok ((), st')`, then `st'.objects` has
       one of four explicit shapes determined by `sc.boundThread`
       and the bound-TCB lookup result. -/
   theorem schedContextConfigure_success_objects_shape
       (vScId : ValidObjId) (budget period priority deadline domain : Nat)
       (st st' : SystemState)
       (hOk : schedContextConfigure vScId budget period priority deadline domain st
                = .ok ((), st')) :
       ∃ sc : SchedContext,
         st.getSchedContext? (SchedContextId.ofObjId vScId.val) = some sc ∧
         validateSchedContextParams budget period priority deadline domain = .ok () ∧
         (
           -- Case A: sc.boundThread = none
           (sc.boundThread = none ∧ st'.objects =
             st.objects.insert vScId.val
               (.schedContext (applyConfigureParamsFull sc budget period priority
                 deadline domain st.machine.timer))) ∨
           -- Case B: sc.boundThread = some boundTid, bound TCB missing
           (∃ boundTid, sc.boundThread = some boundTid ∧
             st.getTcb? boundTid = none ∧
             st'.objects = st.objects.insert vScId.val
               (.schedContext (applyConfigureParamsFull sc budget period priority
                 deadline domain st.machine.timer))) ∨
           -- Case C: sc.boundThread = some boundTid, bound TCB exists
           (∃ boundTid boundTcb,
             sc.boundThread = some boundTid ∧
             st.getTcb? boundTid = some boundTcb ∧
             -- Concrete characterisation of stProp + stFinal:
             ∃ tcb',
               tcb'.schedContextBinding = boundTcb.schedContextBinding ∧
               tcb'.domain = ⟨domain⟩ ∧
               tcb'.priority = ⟨priority⟩ ∧
               st'.objects =
                 (st.objects.insert vScId.val
                   (.schedContext (applyConfigureParamsFull sc budget period priority
                     deadline domain st.machine.timer))).insert boundTid.toObjId
                   (.tcb tcb'))
         )
   ```

   **Plan-author observation**: at first glance, Case C's
   `tcb'.priority = ⟨priority⟩` and `tcb'.domain = ⟨domain⟩` only
   appear to hold when the corresponding propagation block fires
   (i.e., when the existing value differs from the new value).
   However, on closer inspection both hold UNCONDITIONALLY:

   - **No-op case (priorities or domains equal)**: the propagation
     block returns the pre-state TCB unchanged.  But the check is
     `boundTcb.priority.val = priority` (resp. `domain.val =
     domain`), which by definition implies
     `boundTcb.priority = ⟨priority⟩` (resp.
     `boundTcb.domain = ⟨domain⟩`) — see
     `schedContextConfigure_domain_noop_when_eq` (already proven).
     So `tcb'.priority = boundTcb.priority = ⟨priority⟩` even in
     the no-op case.
   - **Rewrite case (priorities or domains differ)**: the
     propagation block writes `tcb'.priority := ⟨priority⟩` (resp.
     `tcb'.domain := ⟨domain⟩`) directly.

   In both cases, the post-state TCB has `tcb'.priority =
   ⟨priority⟩` and `tcb'.domain = ⟨domain⟩`.  No refinement is
   needed; the statement of Case C as written is correct.

   Proof: unfold `schedContextConfigure`; `split at hOk` on each
   nested match; assemble the witnesses.  Each branch's discharge is
   mechanical (use `cases hOk` on the `.ok` constructor).

   Estimated LoC: 100–150.

**Build verification**:
- `lake build SeLe4n.Kernel.SchedContext.Invariant.Preservation`.

**Failure modes**:
- The 5-level nested-`split` may produce branches in non-obvious
  order.  Mitigation: use `rename_i` aggressively to label each
  branch; if order confusion persists, structure as `match hOk with
  | ... => ...` for each known shape.

### Sub-PR R2 — Substantive composition

**Location**: same.

**Theorems to add**:

1. `schedContextConfigure_preserves_boundThreadDomainConsistent`
   — substantive replacement of the closure-form variant.

   ```lean
   /-- WS-RC R5.G.3 / Phase R2: `schedContextConfigure` preserves
       `boundThreadDomainConsistent`.

       Required hypotheses: `boundThreadDomainConsistent` AND
       `schedContextBindingConsistent` on the pre-state.  The latter
       rules out a dangling-binding corner case (TCB has `.bound scId`
       but `sc.boundThread ≠ some tid`); without it, R5.G's domain
       rewrite could silently break the invariant for the dangling
       pair.  Both hypotheses are conjuncts of
       `schedulerInvariantBundleExtended`, so the strengthening
       costs nothing at the call site.

       (Plan-named theorem; see audit-plan §9.9 R5.G.3.  The
       strengthening with `hBind` is recorded as ERRATA-R5-2 in
       `AUDIT_v0.30.11_ERRATA.md`.) -/
   theorem schedContextConfigure_preserves_boundThreadDomainConsistent
       (vScId : ValidObjId) (budget period priority deadline domain : Nat)
       (st st' : SystemState)
       (hDom : boundThreadDomainConsistent st)
       (hBind : schedContextBindingConsistent st)
       (hObjInv : st.objects.invExt)
       (hOk : schedContextConfigure vScId budget period priority deadline domain st
                = .ok ((), st')) :
       boundThreadDomainConsistent st'
   ```

   Proof: invoke `schedContextConfigure_success_objects_shape` to
   obtain the three-way disjunction on `st'.objects`.  For each
   case:

   - **Case A** (`sc.boundThread = none`):
     - Only ObjId `vScId.val` is modified (the SC).
     - For any (tid, scId) pair in the post-state:
       - If `scId.toObjId ≠ vScId.val`: SC unchanged, TCB unchanged
         (since vScId.val is not a TCB slot pre-state).  Pre-state
         `hDom` applies.
       - If `scId.toObjId = vScId.val`: post-state SC has
         `domain := ⟨domain⟩`.  For the antecedent
         `tcb.schedContextBinding = .bound scId` to hold, by
         `hBind` reverse direction on the pre-state, we'd need
         `sc.boundThread = some tid` — but `sc.boundThread = none`
         by assumption.  Vacuous.
     - Use `objects_insert_non_tcb_non_sc_preserves_...` (Phase P2)
       — wait, but the insert IS a SC.  The right frame is
       `objects_insert_sc_at_other_preserves_...`.  Let me reconsider.

     Actually the cleanest discharge is direct: enumerate the four
     possible (tid.toObjId, scId.toObjId) configurations:
     (vScId.val, vScId.val), (vScId.val, other), (other, vScId.val),
     (other, other).  Each is handled by the appropriate
     `getElem?_insert_*` rewrite.

   - **Case B** (TCB missing): same as Case A — only SC is modified.

   - **Case C** (joint update): invoke
     `objects_update_sync_domain_preserves_boundThreadDomainConsistent`
     (Phase P2's frame lemma) with the witnesses from Phase R1's
     characterisation.  The frame's preconditions match:
     - SC at `vScId.val`: pre-state `sc` with new state
       `applyConfigureParamsFull ...` whose domain is `⟨domain⟩`.
     - TCB at `boundTid`: pre-state `boundTcb` with new state `tcb'`
       whose domain is `⟨domain⟩` and whose schedContextBinding
       matches.
     - `hNeq`: `boundTid.toObjId ≠ vScId.val` follows from the
       pre-state's TCB lookup at `boundTid` (TCB present) and SC
       lookup at `vScId.val` (SC present) — they cannot be the
       same ObjId because objects.insert would have overwritten
       one with the other.

   Estimated LoC: 150–250.

**Closure-form removal**: with the substantive theorem in place, the
closure-form variant currently named
`schedContextConfigure_preserves_boundThreadDomainConsistent` is
**deleted** (no name collision; the substantive version takes the
name).  The deletion is part of this sub-PR.

**Test additions**:

- `tests/PriorityManagementSuite.lean::pm_r5g_04_substantive_invariant_preservation`:
  runtime test asserting that
  `boundThreadDomainConsistent` holds on a post-`schedContextConfigure`
  state.  (~20 LoC)

**Build verification**:
- `lake build SeLe4n.Kernel.SchedContext.Invariant.Preservation`.
- `lake build` (default target).

**Failure modes**:
- Case C's frame-lemma instantiation requires
  `boundTid.toObjId ≠ vScId.val`.  If this isn't derivable from
  Phase R1's characterisation alone, an additional pre-state
  hypothesis may be needed.  Mitigation: derive it from
  `schedContextBindingConsistent` (a bound thread cannot share an
  ObjId with its SC because the variants are distinct in the
  objects table).

---

## 8. Phase S — R5.C.1 full deprecation of `effectivePriority`

### Phase S goal

Complete R5.C.1's unification recommendation by:

1. Migrating remaining 6 caller sites from `effectivePriority` to
   `effectiveSchedParams`.
2. Deleting the `effectivePriority` definition + 3 helper theorems.
3. Retaining the bridge witness theorem
   (`effectivePriority_some_eq_effectiveSchedParams`) renamed to
   `effectiveSchedParams_partial_resolution_bridge` for historical
   documentation.

### Sub-PR S1 — Full migration + deletion

**Locations**:
- `SeLe4n/Kernel/Scheduler/Liveness/TraceModel.lean` (1 call site).
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean` (1 test
  theorem at line 3654).
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean` (definition +
  3 helpers).
- `tests/PriorityInheritanceSuite.lean` (4 call sites).

**Steps**:

1. Migrate `TraceModel.lean` line 224:

   ```lean
   -- OLD:
   | some (.tcb tcb) => effectivePriority st tcb
   -- NEW (returns total triple, not Option):
   | some (.tcb tcb) => some (effectiveSchedParams st tcb)
   -- OR (better: have the function return the triple directly):
   ```

   The exact form depends on the consumer.  If the consumer expects
   `Option`, wrap in `some`.  If it expects the triple directly,
   remove the wrapping.

2. Migrate `Preservation.lean` line 3654 (the test theorem):

   ```lean
   -- OLD:
   theorem ... :
     effectivePriority st tcb = some (tcb.priority, tcb.deadline, tcb.domain) := by
     simp [effectivePriority, hUnbound, hNoPip]
   -- NEW:
   theorem ... :
     effectiveSchedParams st tcb = (tcb.priority, tcb.deadline, tcb.domain) := by
     simp [effectiveSchedParams, hUnbound, hNoPip]
   ```

3. Migrate `PriorityInheritanceSuite.lean` 4 sites (each has a
   pattern-match on `some/none`).  The `none` branch becomes dead
   code; replace with direct destructure.

4. In `Selection.lean`:
   - Delete `def effectivePriority`.
   - Delete `theorem effectivePriority_unbound`.
   - Delete `theorem effectivePriority_ge_pipBoost`.
   - Delete `theorem effectivePriority_noPip`.
   - Rename `theorem effectivePriority_some_eq_effectiveSchedParams`
     to `theorem effectiveSchedParams_partial_resolution_bridge` —
     state it as a witness that the (now-deleted) partial form
     would have agreed on `some` cases.  The renamed theorem keeps
     the proof identical to the current
     `effectivePriority_some_eq_effectiveSchedParams` (or just becomes
     unprovable if `effectivePriority` is deleted — in which case
     we delete this theorem too).

   **Sub-decision**: since `effectivePriority` is deleted, the
   bridge theorem becomes unprovable (its statement references
   `effectivePriority`).  **Decision: delete the bridge theorem
   too** — it served only as a migration aid.  Future readers can
   consult `WORKSTREAM_HISTORY.md` for the migration record.

5. Update CLAUDE.md's `tests/` notes section if it mentions
   `effectivePriority`.

**Build verification**:
- `lake build` (default target).
- `lake env lean --run tests/PriorityInheritanceSuite.lean`.

**Failure modes**:
- TraceModel's consumer may expect `Option` for case-split
  semantics.  If so, wrap as `some (effectiveSchedParams ...)` to
  preserve type compatibility.  Or migrate the consumer to total
  semantics.

---

## 9. Phase V — Tests, surface anchors, discharge index, release marker

### Phase V goal

Tie off the workstream: add test surface anchors for the new
substantive theorems, update the discharge index, refresh
documentation, and mark R5 as substantively complete in the
plan-author audit observations.

### Sub-PR V1 — Final close-out

**Surface anchor additions** in `tests/LivenessSuite.lean`:

```lean
-- WS-RC R5.B.2 substantive (Phase Q1/Q2 landing):
#check @SeLe4n.Kernel.Lifecycle.Suspend.restoreToReady_preserves_blockingAcyclic
#check @SeLe4n.Kernel.Lifecycle.Suspend.resumeThread_preserves_blockingAcyclic
#check @SeLe4n.Kernel.Lifecycle.Suspend.ensureRunnable_preserves_computeMaxWaiterPriority
#check @SeLe4n.Kernel.Lifecycle.Suspend.schedule_preserves_computeMaxWaiterPriority
#check @SeLe4n.Kernel.Lifecycle.Suspend.resumeThread_pipBoost_consistent_with_blocking_graph
-- WS-RC R5.G.3 substantive (Phase R2 landing):
#check @SeLe4n.Kernel.SchedContextOps.schedContextConfigure_success_objects_shape
-- (`schedContextConfigure_preserves_boundThreadDomainConsistent` already anchored)
-- Phase P additions:
#check @SeLe4n.Kernel.PriorityInheritance.blockingAcyclic_of_subgraph
#check @SeLe4n.Kernel.PriorityInheritance.computeMaxWaiterPriority_frame
#check @SeLe4n.Kernel.objects_insert_non_tcb_non_sc_preserves_boundThreadDomainConsistent
#check @SeLe4n.Kernel.objects_update_sync_domain_preserves_boundThreadDomainConsistent
```

**Test runtime additions** in `tests/SuspendResumeSuite.lean`:

- `sr027c_resumeThread_preserves_blockingAcyclic` (Q1 runtime).
- `sr027d_resumeThread_pipBoost_matches_graph` (Q2 runtime).

**Test runtime additions** in `tests/PriorityManagementSuite.lean`:

- `pm_r5g_04_substantive_invariant_preservation` (R2 runtime).

**Discharge-index updates** in
`docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md`:

- §3.H rows H.5/H.6/H.7 (R5.B-related): mark as SUBSTANTIVE after
  Q1/Q2 landing.
- §3.H row H.16 (R5.G.3): mark as SUBSTANTIVE after R2 landing;
  remove the closure-form parenthetical.
- §3.H new row H.25: ERRATA-R5-2 cross-reference for the
  `schedContextBindingConsistent` strengthening on R5.G.3.

**Errata update** in `docs/audits/AUDIT_v0.30.11_ERRATA.md`:

- **ERRATA-R5-1**: plan pseudocode
  `computeMaxWaiterPriority st'.scheduler.blockingGraph tid` —
  `SystemState.scheduler` has no `blockingGraph` field; the correct
  reference is `computeMaxWaiterPriority st' tid`.
- **ERRATA-R5-2**: R5.G.3 plan signature
  `hInv : boundThreadDomainConsistent st` is insufficient for the
  substantive proof; the strengthened version requires both
  `boundThreadDomainConsistent` and `schedContextBindingConsistent`
  to rule out dangling-binding corner cases.

**CHANGELOG, CLAUDE.md, WORKSTREAM_HISTORY** updates documenting the
substantive landing.

**Build verification**:
- `./scripts/test_full.sh` passes end-to-end.

**Failure modes**:
- Documentation churn may produce spurious "stale docstring" warnings
  in the test_full pipeline.  Mitigation: every doc update reviewed
  for accuracy against the live tree.

---

## 10. Commit ordering, dependencies, and per-sub-PR validation

### 10.1 Commit graph (linearised)

```
P1 (foundational lemmas: blocking graph + compute frame)
 └── P2 (foundational lemmas: domain frame)
      ├── Q1 (R5.B.2a: preserves_blockingAcyclic substantive)
      │    └── Q2 (R5.B.2b: pipBoost_consistent_with_blocking_graph substantive)
      └── R1 (R5.G.3: operational characterisation)
           └── R2 (R5.G.3: substantive preservation)

S1 (effectivePriority full deprecation) — depends on nothing in P/Q/R
   directly; can land anytime, but recommended after R2 for safe
   review.

V1 (tests + docs + release marker) — depends on Q2, R2, S1 all
   landed.
```

### 10.2 Hard dependencies

- **Q1 → Q2**: Q2 uses the `restoreToReady_preserves_blockingAcyclic`
  lemma from Q1 (transitively, via the operational composition).
- **P1 → Q1**: Q1's `restoreToReady_preserves_blockingAcyclic` uses
  `blockingAcyclic_of_subgraph` from P1.
- **P1 → Q2**: Q2's `*_preserves_computeMaxWaiterPriority` frames
  use `computeMaxWaiterPriority_frame` from P1.
- **P2 → R2**: R2's Case C discharge uses
  `objects_update_sync_domain_preserves_boundThreadDomainConsistent`
  from P2.
- **R1 → R2**: R2 uses the operational characterisation from R1.

### 10.3 Soft dependencies / recommended ordering

- **S1 after R2**: S1's `Selection.lean` edits remove the partial-
  resolution helper; landing S1 last leaves the bridge theorem
  available for any unforeseen substantive proof needs in R2.

### 10.4 Per-sub-PR validation commands

Every sub-PR commit runs (locally + CI):

```bash
# 1. Build (Tier 0+1)
source ~/.elan/env && lake build

# 2. Smoke (Tier 0–2)
./scripts/test_smoke.sh

# 3. AK7 monotonicity
bash scripts/ak7_cascade_check_monotonic.sh

# 4. Surface-anchor check (Q1/Q2/R1/R2/V1)
lake env lean --run tests/LivenessSuite.lean

# 5. Per-suite runtime tests (after V1's additions)
lake env lean --run tests/SuspendResumeSuite.lean
lake env lean --run tests/PriorityManagementSuite.lean

# 6. Rust workspace (no Rust-side changes expected; this is a safety
#    check that nothing leaked into the FFI boundary)
( cd rust && cargo test --workspace )
```

Sub-PR is **NOT mergeable** until all six commands return 0.

---

## 11. Consolidated verification matrix

| Sub-PR | `lake build` | `test_fast` | `test_smoke` | `test_full` | `cargo test` | AK7 monotonicity | Surface anchors |
|---|---|---|---|---|---|---|---|
| P1 | ✓ | ✓ | ✓ | ✓ | ✓ (unchanged) | ✓ (no metric change) | n/a (no new anchors) |
| P2 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | n/a |
| Q1 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 2 new (Q1's substantive theorems) |
| Q2 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 3 new (Q2's frames + theorem) |
| R1 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | 1 new (R1's shape lemma) |
| R2 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | (already anchored from initial R5; closure-form removal) |
| S1 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | n/a (deletions only) |
| V1 | ✓ | ✓ | ✓ | ✓ | ✓ | ✓ | (anchors consolidated in V1) |

**AK7 expectations**:
- `sorry_count`: stays at 0 through every sub-PR.
- `axiom_count`: stays at 0.
- `raw_match_tcb`: stays at 44 (no new raw matches introduced).
- `gettcb_adoption`: stays ≥ 100 (no decrease).

---

## 12. Failure-mode register

| ID | Phase | Risk | Probability | Impact | Mitigation |
|---|---|---|---|---|---|
| F-P1-1 | P1 | `blockingChain` induction termination check fails | Low | High (blocks Q1, Q2) | Use `Nat.rec` with explicit motive; if still failing, prove via fuel-decreasing well-founded recursion. |
| F-P1-2 | P1 | `computeMaxWaiterPriority_frame`'s hypothesis is too strong (caller can't easily satisfy) | Medium | Medium | Iterate the hypothesis shape; weaken to per-field invariance using `effectiveSchedParams_frame` as an intermediate. |
| F-P2-1 | P2 | `objects.invExt` projection fails — invExt is a Prop, not a structure | Low | Low | Pass `invExt` explicitly as a hypothesis (consistent with VSpaceInvariant.lean pattern). |
| F-Q1-1 | Q1 | Deriving `blockingServer (restoreToReady st tid) tid = none` requires case-splitting on `st.getTcb? tid`: the existing pre-state TCB could be missing (returns `st` unchanged → blockingServer's projection still reads pre-state's ipcState — which could be any value) or already non-`.blockedOnReply` (blockingServer was `none` pre-state) or `.blockedOnReply` (blockingServer was `some _` pre-state, becomes `none` post-state).  All three cases satisfy "blockingServer post-state ∈ {none, blockingServer pre-state}", but the proof must enumerate them. | Medium | Medium | Add a derived corollary `restoreToReady_blockingServer` in Q1's prep step; case-split on `getTcb?` success. |
| F-Q1-2 | Q1 | H5 schedule's `saveOutgoingContext` may modify objects.ipcState transitively (no — it doesn't, but the proof gate must verify) | Low | Medium | Use `saveOutgoingContext_ipcState_eq` (add in Q2 if not present). |
| F-Q2-1 | Q2 | `ensureRunnable_preserves_computeMaxWaiterPriority` requires `ensureRunnable_objects_eq` | Low | Low | Add the prerequisite lemma in Q2's prep step. |
| F-R1-1 | R1 | 5-level `split at hOk` produces branches in wrong order | Medium | Medium | Use `rename_i` aggressively; if confusion persists, restructure as explicit `match hOk` with named patterns. |
| F-R1-2 | R1 | `applyConfigureParamsFull`'s shape doesn't exactly match the inline record-with in `schedContextConfigure` | Medium | Low | Both should be definitionally equal; if not, prove an `applyConfigureParamsFull_eq_inline` bridge lemma. |
| F-R2-1 | R2 | `boundTid.toObjId ≠ vScId.val` doesn't follow from Phase R1's characterisation alone | Medium | High | Derive from `schedContextBindingConsistent`: SC and TCB have distinct variants, so they can't share an ObjId in the well-typed objects table. |
| F-R2-2 | R2 | The frame lemma's preconditions don't quite match the Case C witnesses | Medium | High | Iterate the frame lemma's signature; the synchronous-domain frame is the substantive content. |
| F-S1-1 | S1 | `TraceModel.lean` consumer requires `Option` for type compatibility | Low | Low | Wrap as `some (effectiveSchedParams ...)`. |
| F-S1-2 | S1 | `PriorityInheritanceSuite.lean` tests rely on the `none` branch for negative cases | Medium | Low | Restructure the test to use a different negative case (e.g., a TCB that doesn't exist). |
| F-V1-1 | V1 | Documentation drift between CHANGELOG/CLAUDE.md/WORKSTREAM_HISTORY | Medium | Low | One author pass at the start of V1; cross-check with `grep -rn 'R5.B.2\|R5.G.3'`. |

---

## 13. Discharge-index updates

After every Phase Q / R / V sub-PR lands, update
`docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` §3.H:

Note on "replaced in place": Q1, Q2, R2 do not delete and re-add
theorems by name — they redefine the body of the existing closure-form
theorem to the substantive proof.  The theorem's *name* persists; only
the proof body and hypotheses change.  This is signature-stable for
the (single, surface-anchor) caller in `LivenessSuite.lean`.

**At Q1 landing**:
- Row H.5 (`restoreToReady_objectIndex_eq`): unchanged.
- Row H.6 (`restoreToReady_objects_eq_at_tid`): unchanged.
- Row H.7 (`resumeThread_pipBoost_consistent_post_restore`): unchanged.
- **NEW row H.19**: `restoreToReady_preserves_blockingAcyclic` — LANDED at Q1.
- **NEW row H.20**: `resumeThread_preserves_blockingAcyclic` (substantive) — LANDED at Q1.  Closure-form body REPLACED with substantive proof (theorem name reused; signature drops `hProp`).

**At Q2 landing**:
- **NEW row H.21**: `ensureRunnable_preserves_computeMaxWaiterPriority` — LANDED at Q2.
- **NEW row H.22**: `schedule_preserves_computeMaxWaiterPriority` — LANDED at Q2.
- **NEW row H.23**: `resumeThread_pipBoost_consistent_with_blocking_graph` (substantive) — LANDED at Q2.  Closure-form body REPLACED.

**At R1 landing**:
- **NEW row H.24**: `schedContextConfigure_success_objects_shape` (operational characterisation) — LANDED at R1.

**At R2 landing**:
- Row H.16 (`schedContextConfigure_preserves_boundThreadDomainConsistent`): closure-form body REPLACED with substantive proof; hypothesis strengthened to require both `boundThreadDomainConsistent` and `schedContextBindingConsistent` (plus `hObjInv : st.objects.invExt`).  Closure-form parenthetical removed.
- **NEW row H.25**: ERRATA-R5-2 cross-reference for the `schedContextBindingConsistent` strengthening (records the hypothesis change as a plan-text correction).

**Closing summary update**:
- §3.H rolls from "18 of 18 rows LANDED (closure form on H.16/H.17/H.18)" to **"25 of 25 rows LANDED (all substantive)"**.

---

## 14. Documentation synchronization

Each sub-PR's commit message ends with:

```
Refs: docs/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md §<phase>
```

Documentation files updated in **V1**:

| File | Update |
|---|---|
| `CHANGELOG.md` | New v1.0.0 entry: "WS-RC R5 deferred-work substantive completion" |
| `CLAUDE.md` | Replace "R5 deferred-work completion (follow-up audit pass)" section with the substantive completion narrative |
| `docs/WORKSTREAM_HISTORY.md` | "R5 deferred-work completion" subsection refreshed; H.19–H.24 rows mentioned |
| `docs/spec/SELE4N_SPEC.md` §8.10.8 | Note substantive R5.B.2 + R5.G.3 + R5.C.1 completion |
| `docs/gitbook/12-proof-and-invariant-map.md` | WS-RC R5 entry mentions substantive R5.B.2 + R5.G.3 |
| `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` | §3.H rows H.19–H.24 added; H.16 updated to SUBSTANTIVE |
| `docs/audits/AUDIT_v0.30.11_ERRATA.md` | ERRATA-R5-1 + ERRATA-R5-2 added |

**README.md**: no update required (the test/declaration counts will
shift slightly; the count refresh happens at the v1.0.0 cut, not at
this plan's completion).

---

## 15. Pre-flight checklist (per sub-PR)

Before opening a sub-PR for review:

- [ ] **Branch**: descended from the most recent commit on
      `claude/audit-scheduler-phase-r5-nWFdz` (i.e., the deferred-
      completion branch).  Each sub-PR commits on this branch as a
      separate commit.
- [ ] **Single coherent slice**: the sub-PR touches files in one
      phase; no cross-phase mixing.
- [ ] **Lake build clean**: `lake build` exits 0; zero warnings.
- [ ] **Tier-2 smoke**: `./scripts/test_smoke.sh` exits 0.
- [ ] **AK7 monotonicity**: `bash scripts/ak7_cascade_check_monotonic.sh`
      exits 0.  `sorry_count` and `axiom_count` both 0.
- [ ] **No `sorry`/`axiom` introduced**: grep verification.
- [ ] **No session URL in commit message**: per CLAUDE.md "Session
      URL hygiene".
- [ ] **Refs line**: commit message ends with
      `Refs: docs/audits/WS_RC_R5_DEFERRED_COMPLETION_PLAN.md §<phase>`.
- [ ] **Discharge-index updated**: if the sub-PR adds a closure-form
      or substantive theorem, the matching row in §3.H is added in
      the same commit (or planned for V1 if cumulative).
- [ ] **Surface anchors**: if the sub-PR adds a public theorem, a
      `#check` line is added to `tests/LivenessSuite.lean` in the
      same commit (or V1 for batch).
- [ ] **Plan section reference**: code comments cite the relevant
      plan section.

---

## 16. Rollback strategy

If a sub-PR introduces a regression after merge:

1. **Identify scope**: was the regression caused by the substantive
   theorem itself (proof unsound)?  Or by a downstream consumer
   that depends on the theorem's new form (e.g., a consumer that
   was previously consuming the closure form)?
2. **Local revert**: `git revert <sha>` for the offending sub-PR
   commit.  Since sub-PRs are atomic, the revert is clean.
3. **Reschedule**: re-open the rolled-back sub-PR with the fix; do
   NOT bundle the fix with other sub-PRs.

**Anti-pattern**: do NOT amend a landed commit on the shared branch
to fix a regression — always create a new revert commit.

---

## 17. Acceptance criteria

The deferred-work completion is **DONE** when:

1. **All 8 sub-PRs (P1, P2, Q1, Q2, R1, R2, S1, V1)** are merged to
   `claude/audit-scheduler-phase-r5-nWFdz`.
2. **Substantive proofs verified**:
   - `resumeThread_preserves_blockingAcyclic` is a non-tautological
     proof (no `hProp` closure parameter).
   - `resumeThread_pipBoost_consistent_with_blocking_graph` ditto.
   - `schedContextConfigure_preserves_boundThreadDomainConsistent`
     takes `hDom` + `hBind` + `hObjInv` + `hOk` and proves
     `boundThreadDomainConsistent st'` without `hProp`.
3. **`effectivePriority` deleted**: the definition is not in the
   codebase; grep returns zero substantive matches outside
   documentation.
4. **Discharge index §3.H**: 25 of 25 rows LANDED (H.1–H.18
   pre-existing + H.19–H.25 added by this completion plan;
   H.25 cross-references ERRATA-R5-2); closure-form parentheticals
   on H.16/H.17/H.18 either removed (H.16) or replaced with
   substantive-name renames (H.17/H.18 retained for the per-arm IF
   helpers).
5. **All tests pass**: `test_full.sh` exits 0.
6. **No regressions**: AK7 baseline preserved; cargo test passes;
   no new warnings.
7. **Documentation synced**: CHANGELOG / CLAUDE.md /
   WORKSTREAM_HISTORY entries reflect the substantive landing.
8. **Errata recorded**: ERRATA-R5-1 + ERRATA-R5-2 in the errata
   file.
9. **Plan-author audit-pass**: a final review pass confirms no
   plan items remain "avoided" or "under-delivered".

---

## 18. Total scope summary

| Phase | Sub-PRs | LoC (proof + test) | Files touched | Theorems added | Theorems / defs deleted |
|---|---|---|---|---|---|
| P | P1, P2 | ~290 | 3 | 4 (frame lemmas) | 0 |
| Q | Q1, Q2 | ~370 | 1 | 5 (3 substantive + 2 auxiliary) | 2 (closure forms — replaced in place) |
| R | R1, R2 | ~380 | 1 | 2 (1 substantive + 1 shape) | 1 (closure form — replaced in place) |
| S | S1 | ~100 | 4 | 0 | 5 (`effectivePriority` def + 3 helpers + 1 bridge theorem `effectivePriority_some_eq_effectiveSchedParams`) |
| V | V1 | ~110 | 4 + 5 docs | 0 | 0 |
| **TOTAL** | **8** | **~1250** | **~13** | **11** | **8** |

**Axiom / sorry budget**: 0 introduced, 0 retained.  AK7 monotonicity
preserved at the v0.30.11 floor.  No backwards-compatibility shims
remain after Phase S.

**Target completion**: prior to v1.0.0 cut.  At completion, R5 is
substantively complete with no plan items in "avoided" or "under-
delivered" state.

---

## Plan-author signature

This plan was authored after the comprehensive audit identified five
deferred R5 items in PR #771.  R5.F.1 and R5.C.1 (prominent caller)
were closed in the follow-up commit `7a21e18`; the present plan
addresses the remaining four (R5.B.2 × 2 substantive proofs, R5.G.3
substantive proof, R5.C.1 full deprecation).

The plan applies the implement-the-improvement rule uniformly — no
"or document" alternatives, no `sorry`-based shortcuts, no closure-
form deferrals.  Every theorem named in the audit plan §9 is
delivered substantively before v1.0.0.

Plan author: Adam Hall
Last revised: 2026-05-12
