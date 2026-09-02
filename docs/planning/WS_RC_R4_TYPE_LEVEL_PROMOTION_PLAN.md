# WS-RC R4.A + R4.C — Type-level Structural Promotion of `CNode.slots` and `Notification.waitingThreads`

**Status**: **COMPLETE** — both R4.A (`UniqueSlotMap`-backed `CNode.slots`) and R4.C (`NoDupList ThreadId`-backed `Notification.waitingThreads`) landed; foundation modules + field-type switches + all consumer migrations + tests all green.
**Workstream**: WS-RC (audit remediation v0.30.11 → v0.31.0 → v1.0.0)
**Audit findings remediated**: DEEP-MODEL-01 (R4.A) — LANDED; DEEP-IPC-05 (R4.C) — LANDED; DEEP-IPC-01 (subsumed by R4.C) — LANDED structurally.
**Predecessors landed**: WS-RC R4.B (DEEP-CAP-04 — `RetypeTarget` ScrubToken) and WS-RC R4.D (DEEP-CAP-02 — `cspaceMutate` null-cap witnesses) at commit `7da2572`. The R4.A foundation module `SeLe4n/Model/Object/UniqueSlotMap.lean` and the R4.C foundation module `SeLe4n/Model/Object/NoDupList.lean` are LANDED at the current commit with the complete API surfaces (`empty`, `insert`, `erase`, `filter`, `ofListWF` for `UniqueSlotMap`; `empty`, `consWithGuard`, `consWithGuard?`, `tail?`, `filter` for `NoDupList`); the field-type switches on `CNode.slots` and `Notification.waitingThreads` are LANDED; all ~55 consumer files migrated; `lake build` (312 jobs) + `./scripts/test_smoke.sh` + `./scripts/test_full.sh` all green.
**Target version**: v0.31.0 — verified-specification release
**Sub-PR count**: 15 atomic units across 2 parallel tracks (R4.A: 7, R4.C: 8)
**Estimated LoC**: ~1860 net (R4.A ~890, R4.C ~970)
**Files touched**: ~55 (with overlap on `Types.lean` and `CrossSubsystem.lean` only)
**Axiom / sorry budget**: 0 (all proof obligations discharged via existing in-tree lemmas)
**Source plan**: distilled from `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §8.3 / §8.5
**Related discharge index**: `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` §3.D D.1, D.3 and §3.E E.1

## Table of contents

1. [Context](#context) — why this work, what state-level invariants get promoted
2. [Headline architectural decisions](#headline-architectural-decisions) — type form, coercion, pattern-match accounting, hard-case API
3. [Track A — UniqueSlotMap (7 sub-PRs)](#track-a--uniqueslotmap-7-sub-prs-890-loc-total)
   - R4.A.1 Introduce `UniqueSlotMap`
   - R4.A.2 Switch `CNode.slots` field
   - R4.A.3 Migrate test fixtures
   - R4.A.4 Rewire FrozenOps (or collapse)
   - R4.A.5 Deprecate `cspaceSlotUnique` to `True`
   - R4.A.6 Bundle cleanup (4 in-PR commits)
   - R4.A.7 Witness theorem + index + marker
4. [Track C — NoDupList ThreadId (8 sub-PRs)](#track-c--noduplist-threadid-8-sub-prs-970-loc-total)
   - R4.C.1 Introduce `NoDupList`
   - R4.C.2 Switch `Notification.waitingThreads` field + manual `DecidableEq`
   - R4.C.3 Operational rewire (Endpoint, Cleanup, FrozenOps)
   - R4.C.4 Proof-side rewire (NotificationPreservation, StoreObjectFrame)
   - R4.C.5 Migrate test fixtures and `MainTraceHarness`
   - R4.C.6 Deprecate `uniqueWaiters` to `True`
   - R4.C.7 Bundle cleanup (4 in-PR commits)
   - R4.C.8 Witness theorem + index + marker
5. [Commit ordering and dependencies](#commit-ordering-and-dependencies)
6. [Verification matrix](#verification-matrix-consolidated)
7. [Failure-mode register](#failure-mode-register)
8. [Discharge index entries](#discharge-index-entries-docsauditsaudit_v030_11_discharge_indexmd)
9. [Out of scope](#out-of-scope-deliberate-deferrals)
10. [Critical files for implementation](#critical-files-for-implementation)
11. [Verification — end-to-end (full workstream close)](#verification--end-to-end-full-workstream-close)
12. [Documentation synchronization](#documentation-synchronization-per-claudemd-documentation-rules)
13. [Open questions for the implementer](#open-questions-for-the-implementer-resolve-before-r4a2--r4c2)
14. [Total scope summary](#total-scope-summary)
15. [Pre-flight checklist (per sub-PR)](#pre-flight-checklist-per-sub-pr)
16. [Rollback strategy](#rollback-strategy)
17. [Best-practices compliance checklist](#best-practices-compliance-checklist-claudemd-alignment)

## Context

The seLe4n v0.30.11 audit-remediation workstream (`docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §8.3 / §8.5) calls for converting two state-level invariants into **type-level** invariants on the underlying data so that future regressions cannot silently bypass the runtime guards:

- **R4.A (DEEP-MODEL-01)** — promote `cspaceSlotUnique` (no duplicate keys in any `CNode.slots` `RHTable`) from a state invariant proven preserved by every kernel transition into a structural property carried by a new `UniqueSlotMap` wrapper around `RHTable Slot Capability`.
- **R4.C (DEEP-IPC-05; subsumes DEEP-IPC-01)** — promote `uniqueWaiters` (`Notification.waitingThreads.Nodup`) from a state invariant into a structural property carried by a new `NoDupList ThreadId` wrapper around `List ThreadId`.

The earlier R4 sub-tasks have already landed: R4.B added an opaque-token-backed `cleanupHookDischarged` strengthening to `RetypeTarget`, and R4.D added two `cspaceMutate` null-cap witness theorems. R4.A and R4.C remain because each touches >300 use sites across ~30–38 files, with non-trivial cross-subsystem proof obligations that demand careful PR partitioning.

**The intended outcome.** After R4.A and R4.C land, every `CNode.slots` access is provably unique-keyed by construction (smart-constructor preservation lemmas discharge `invExtK` at every mutation), every `Notification.waitingThreads` access is provably duplicate-free by construction, and the corresponding state-level invariants (`cspaceSlotUnique`, `uniqueWaiters`) are deprecated to `True` because their work is now structural. The runtime duplicate guard at `Endpoint.lean` is replaced by a runtime-checked smart constructor (`NoDupList.consWithGuard?`) that fails closed via `.alreadyWaiting` when the cons would violate Nodup — provably equivalent to the old check under the existing `notificationWaiterConsistent` invariant.

**Why this plan partitions into 11 sub-PRs.** Each refactor touches ~30+ files. Landing them as a single PR would exceed reviewable scope and risk a half-broken state mid-merge. The partition below keeps every commit `lake build`-green end-to-end, splits the highest-risk piece (manual `DecidableEq` for `Notification`) into its own canary PR, and uses a deprecation-alias pattern for state-invariant retirement so downstream proof callers continue to elaborate while their cleanup is staged into a follow-up commit.

## Headline architectural decisions

| Decision | R4.A — `UniqueSlotMap` | R4.C — `NoDupList ThreadId` |
|---|---|---|
| **Type form** | wrapper `structure` with named field | wrapper `structure` with named field |
| **Underlying** | `RHTable SeLe4n.Slot Capability` | `List ThreadId` |
| **Invariant carrier** | `hWF : table.invExtK` | `hNodup : val.Nodup` |
| **Coercion** | `CoeHead UniqueSlotMap (RHTable Slot Capability)` | `CoeHead (NoDupList α) (List α)` |
| **Hard-case API** | n/a | `NoDupList.consWithGuard` (proof-carrying) **and** `consWithGuard?` (runtime-checked) |
| **Deriving impact** | none — `CNode` only derives `Repr`; manual `Repr UniqueSlotMap` | `Notification` derives `Repr, DecidableEq` — drop `DecidableEq` and add manual instance |

**Why `structure` over refinement abbrev (`abbrev T := { x // P x }`).** A structure with a named field gives a stable global identifier (`UniqueSlotMap.table`, `NoDupList.val`), supports per-instance `Repr` independent of subtype-name leakage in pretty-printed goals, lets us attach `@[reducible] def` accessors selectively, and crucially gives us a dedicated namespace (`UniqueSlotMap.insert`, `NoDupList.consWithGuard`) where smart constructors live. The `RHSet` precedent at `SeLe4n/Kernel/RobinHood/Set.lean` is the closest in-tree template for `UniqueSlotMap` and confirms the `structure` shape scales to the larger surface. The `NonNullCap` refinement abbrev at `SeLe4n/Model/Object/Types.lean` is a counter-example we deliberately do not mirror: it works for a 1-field, 1-method API; both R4.A and R4.C have multi-method APIs where namespace matters.

**Why `CoeHead` over `Coe` / `CoeFun`.** `CoeHead` (vs `Coe`) allows the unification head to be a metavariable while still firing the coercion — this is what makes `cn.slots.fold f init` continue to elaborate when `cn.slots : UniqueSlotMap`, because Lean searches for `RHTable.fold` after coercing the head. `CoeFun` is for treating a value as a function (`f x` syntax) and does not apply.

**Where the coercion does NOT fire (and what to do).** Three Lean 4 elaboration paths bypass `CoeHead` and need explicit rewiring:

1. **`match` expressions** (`match ntfn.waitingThreads with | [] => … | x :: rest => …`) — the `match` discriminant is unified against the constructor's type directly; coercion does not fire. **Migration:** rewrite to `match ntfn.waitingThreads.val with` (proof-side, mechanical) **or** to `match ntfn.waitingThreads.tail? with | none => … | some (x, rest) => …` (operational-side, abstraction-preserving). The plan picks per-site (operational sites use `tail?`, proof sites use `.val` to keep proof tactics working).
2. **`{ cn with slots := … }` record-update syntax** — the RHS is unified against the field's declared type. Under the new typing, RHS values must produce `UniqueSlotMap`, which is what the smart constructors return. No coercion needed; the call site already type-checks if the smart constructor is invoked correctly.
3. **`if h : x ∈ list then …` conditional decidability** — Lean resolves `Membership α (NoDupList α)` from the `instance` we declare in `R4.C.1`; coercion is not consulted. Solved by the explicit `Membership` instance.

**Where the coercion DOES fire (the bulk of consumer sites).** Dot notation (`cn.slots.fold`, `cn.slots.size`, `cn.slots.get?`, `cn.slots.capacity`, `cn.slots.toList`, `ntfn.waitingThreads.length`, `ntfn.waitingThreads.head?`, `ntfn.waitingThreads.isEmpty`, `ntfn.waitingThreads.contains`, `tid ∈ ntfn.waitingThreads.val` membership) — all keep working unchanged because Lean's dot-notation resolution: (1) tries the structure's own namespace (`UniqueSlotMap.fold`, `NoDupList.length`); (2) if that fails, applies `CoeHead` and retries on the underlying type. To keep elaboration fast and unambiguous, the plan adds **explicit `@[inline] def` wrappers** for the most common methods inside the structure's namespace (see R4.A.1 / R4.C.1 sketches) so Lean never has to consult coercion for the hot path.

**Pattern-match migration accounting.** The waitingThreads surface report counts 5 `match … waitingThreads with` sites; for slots, no direct match-on-`slots` sites were observed (consumer access is via `.fold`, `.get?`, `.toList`). Each `match`-on-waitingThreads site is enumerated by file:line in §R4.C.3 below and migrated to either `tail?` (1 operational site each in `Endpoint.lean` and `FrozenOps/Operations.lean`) or `.val` (3 proof sites in `NotificationPreservation/{Wait,Signal}.lean` and `InformationFlow/Invariant/Helpers.lean`).

**Why `consWithGuard?` (runtime-checked) over signature threading at `notificationWait`.** The hard case for R4.C is the cons site at `IPC/Operations/Endpoint.lean/1134`, which prepends a waiter onto `ntfn.waitingThreads`. Three candidate APIs:
1. **Proof-carrying `consWithGuard (h : x ∉ l.val)`.** Used at proof sites (preservation theorems) where the bridge `not_mem_waitingThreads_of_ipcState_ne` (`IPC/Invariant/Defs.lean`) is in scope.
2. **Runtime-checked `consWithGuard?` returning `Option (NoDupList α)`.** Used at the operational site. When membership is detected at runtime, returns `none`, which the caller maps to `.error .alreadyWaiting`. This **subsumes** the line-723 runtime guard: the typed smart constructor IS the duplicate guard.
3. **Thread `notificationWaiterConsistent` through `notificationWait`'s signature.** Rejected: pollutes the public Kernel-monad surface, breaks every dispatch wire site, conflates state-level invariants with per-call obligations.

**The plan offers both (1) and (2).** The bridge theorem `notificationWait_runtime_check_implied_by_nodup` (already landed at `IPC/Invariant/QueueNoDup.lean` from the in-flight R4.C structural-witness step) becomes the equivalence proof linking the two paths under `notificationWaiterConsistent`. Its name and citation survive R4.C's full type-level promotion unchanged, so the discharge index reachability check `#check @SeLe4n.Kernel.notificationWait_runtime_check_implied_by_nodup` keeps elaborating across the workstream.

## Track A — `UniqueSlotMap` (7 sub-PRs, ~890 LoC total)

| Sub | Scope |
|-----|-------|
| R4.A.1 | Introduce `UniqueSlotMap` type, smart constructors, preservation lemmas |
| R4.A.2 | Switch `CNode.slots` field type; rewire builders and core methods |
| R4.A.3 | Migrate test fixtures (~10 sites) |
| R4.A.4 | Rewire `FrozenOps` mutation sites (or collapse into A2 if FrozenCNode is unrelated) |
| R4.A.5 | Deprecate `cspaceSlotUnique` to `True` (state-level invariant becomes trivial) |
| R4.A.6 | Bundle cleanup: remove `cspaceSlotUnique` from `capabilityInvariantBundle` |
| R4.A.7 | Witness theorem, discharge index, marker theorem (workstream close) |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

## Track C — `NoDupList ThreadId` (8 sub-PRs, ~970 LoC total)

| Sub | Scope |
|-----|-------|
| R4.C.1 | Introduce `NoDupList`, smart constructors, `consWithGuard` and `consWithGuard?` APIs |
| R4.C.2 | Switch `Notification.waitingThreads` field type; manual `DecidableEq Notification` |
| R4.C.3 | Rewire **operational** mutation sites in `Endpoint.lean` and `Cleanup.lean` |
| R4.C.4 | Rewire **proof-side** mutation sites in `NotificationPreservation` and `StoreObjectFrame` |
| R4.C.5 | Migrate Notification test fixtures and `MainTraceHarness` |
| R4.C.6 | Deprecate `uniqueWaiters` to `True` (state-level invariant becomes trivial) |
| R4.C.7 | Bundle cleanup: remove `uniqueWaiters` from `ipcInvariantFull` and downstream |
| R4.C.8 | Witness theorem, discharge index, marker theorem (workstream close) |

*Landed. The implementation is the source; what each cut changed is in
[`CHANGELOG.md`](../../CHANGELOG.md) under the versions above.*

## Commit ordering and dependencies

Tracks A and C are **independent** at the file level — no module on track A imports a module modified on track C, and vice versa. Two implementers can develop in parallel, or a single implementer can interleave.

```
Track A (R4.A):                       Track C (R4.C):
  A.1 (UniqueSlotMap intro)             C.1 (NoDupList intro)
       │                                       │
  A.2 (CNode field switch + builders)    C.2 (Notification field switch + DecidableEq)
       │                                       │
  A.3 (test fixtures)                    C.3 (Endpoint + Cleanup operational rewire)
       │                                       │
  A.4 (FrozenOps; may collapse)          C.4 (NotificationPreservation proof rewire)
       │                                       │
  A.5 (deprecate cspaceSlotUnique)       C.5 (test fixtures)
       │                                       │
  A.6 (bundle cleanup, 4 sub-commits)    C.6 (deprecate uniqueWaiters)
       │                                       │
  A.7 (witness + index + marker)         C.7 (bundle cleanup, 4 sub-commits)
                                                │
                                          C.8 (witness + index + marker)
```

**Recommended serial interleaving (single implementer):**

`A.1 → A.2 → A.3 → C.1 → C.2 → C.3 → C.4 → C.5 → A.4 → A.5 → A.6 → A.7 → C.6 → C.7 → C.8`

Rationale:
- A.1 and C.1 are pure additions; doing A.1 first puts the smart-constructor template in place before either field switch.
- A.2 lands before C.2 because A.2 is mechanical (no `DecidableEq` complication); landing A.2 first lets reviewers see the `CoeHead` + `@[inline]` wrapper pattern in a low-risk PR before they encounter the same pattern in the higher-risk C.2.
- A.3 lands immediately after A.2 to keep the test suite green.
- C.2 (the manual `DecidableEq` canary) lands before C.3 so that any `DecidableEq Notification` issues surface before the operational rewiring work.
- C.3 (operational rewire) precedes C.4 (proof rewire); C.3+C.4 are a stack on the same feature branch.
- C.5 (test fixtures) immediately after C.4 so the smoke suite stays green.
- A.4 sits between C.5 and A.5 so the `FrozenOps` decision tree (collapse-or-rewire) is taken with the rest of the workstream stable.
- A.5+A.6+A.7 (R4.A close-out) and C.6+C.7+C.8 (R4.C close-out) are independent close-out chains.

**Parallel-implementer order.** If two implementers work simultaneously:
- Implementer 1 owns track A: A.1, A.2, A.3, A.4, A.5, A.6, A.7.
- Implementer 2 owns track C: C.1, C.2, C.3, C.4, C.5, C.6, C.7, C.8.
- They synchronise only at the end (A.7 / C.8 both touch `CrossSubsystem.lean` for marker theorems and `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` — these merges are mechanically resolvable).

**Commit message format** (per the existing repo convention from `git log`):
```
WS-RC R4.A.1: introduce UniqueSlotMap smart constructor

[…body…]

Refs: docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md §8.3
```

## Verification matrix (consolidated)

Per CLAUDE.md, every commit must pass `lake build <ModulePath>` for each touched module before the pre-commit hook accepts it. The matrix below lists the **mandatory** targets at each PR boundary.

| Sub-PR | `lake build` targets | Test suites | Hook |
|---|---|---|---|
| R4.A.1 | `SeLe4n.Model.Object.UniqueSlotMap`, `SeLe4n` | none (additive only) | pre-commit |
| R4.A.2 | `SeLe4n.Model.Object.{Types,Structures}`, `SeLe4n.Model.Builder`, `SeLe4n.Kernel.InformationFlow.Projection` | `tests/RobinHoodSuite`, `tests/InformationFlowSuite` (smoke) | pre-commit |
| R4.A.3 | full `SeLe4n` | every fixture-touching test | pre-commit |
| R4.A.4 | `SeLe4n.Kernel.FrozenOps.Operations` | `tests/FrozenOpsSuite` | pre-commit |
| R4.A.5 | full `SeLe4n` | `./scripts/test_smoke.sh` | pre-commit |
| R4.A.6 | full `SeLe4n` (per in-PR commit) | `./scripts/test_full.sh` after final commit | pre-commit |
| R4.A.7 | full `SeLe4n` | `./scripts/test_full.sh`, `bash scripts/check_website_links.sh` | pre-commit + Tier 0 hygiene |
| R4.C.1 | `SeLe4n.Model.Object.NoDupList` | unit-test fixture in same PR | pre-commit |
| R4.C.2 | `SeLe4n.Model.Object.Types` (canary: `KernelObject` `BEq` derivation) | new `decide (n1 = n2)` cases in `tests/ModelIntegritySuite.lean` | pre-commit |
| R4.C.3 | `SeLe4n.Kernel.IPC.Operations.Endpoint`, `SeLe4n.Kernel.Lifecycle.Operations.Cleanup`, `SeLe4n.Kernel.FrozenOps.Operations` | `tests/NegativeStateSuite` (alreadyWaiting path) | pre-commit |
| R4.C.4 | `SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`, `SeLe4n.Kernel.IPC.Invariant.Structural.StoreObjectFrame`, `SeLe4n.Kernel.IPC.Invariant.CallReplyRecv`, `SeLe4n.Kernel.InformationFlow.Invariant` | `tests/InformationFlowSuite` | pre-commit |
| R4.C.5 | `SeLe4n.Testing.MainTraceHarness` | `./scripts/test_full.sh` | pre-commit |
| R4.C.6 | full `SeLe4n` | `./scripts/test_smoke.sh` | pre-commit |
| R4.C.7 | full `SeLe4n` (per in-PR commit) | `./scripts/test_full.sh` after final commit | pre-commit |
| R4.C.8 | full `SeLe4n` | `./scripts/test_full.sh`, link gate | pre-commit + Tier 0 hygiene |

**Every PR also runs `./scripts/test_smoke.sh` minimally per `CLAUDE.md`.** Final workstream-close commits (A.6 and C.5) additionally run `./scripts/test_full.sh`.

## Failure-mode register

| Sub-PR | Highest-risk failure | Mitigation |
|---|---|---|
| R4.A.1 | `deriving Repr` over the Prop field `hWF` fails | Manual `instance : Repr UniqueSlotMap` (1 line) — sketch in §R4.A.1 |
| R4.A.2 | `cn.slots[s]?` syntax breaks because `GetElem` not lifted | Add explicit `GetElem UniqueSlotMap …` instance (~5 lines) in R4.A.1 |
| R4.A.3 | Over-migration into `FrozenStateSuite.lean` `freezeMap` calls (which are `FrozenMap`-typed, not CNode) | Grep precisely for `slots :=` literal; do not migrate `mappings :=` or `freezeMap` |
| R4.A.4 | `FrozenCNode.slots` is unrelated to `CNode.slots` (likely `FrozenMap`-typed) | Read `SeLe4n/Model/FrozenState.lean` first; if confirmed, collapse R4.A.4 into R4.A.2's verification step |
| R4.A.5 | Downstream proof body destructures `hUnique : True` and fails | Locally rewrite each `obtain ⟨…⟩ := hUnique` to `obtain _ := hUnique`; defer deeper cleanup to R4.A.6 |
| R4.A.6 | Intermediate non-buildable state during 4-commit bundle cleanup | Each in-PR commit is `lake build`-green by construction; pre-commit hook gates each |
| R4.A.6 | An `rcases ⟨hU, …⟩ := hBundle` is deeply nested across multiple files | Use `rg 'cspaceSlotUnique'` after each in-PR commit to find remaining sites |
| R4.A.7 | Discharge index link gate fails (`scripts/check_website_links.sh`) | Verify the index file path remains stable; do not rename `AUDIT_v0.30.11_DISCHARGE_INDEX.md` |
| R4.C.1 | `List.Nodup.filter` / `List.Nodup.of_cons` / `List.nodup_cons` name drift in Lean 4 v4.28.0 (mathlib-free) | If absent in core, write local proofs in `NoDupList.lean` (~10 LoC each via list induction) |
| R4.C.2 | Manual `DecidableEq Notification` is wrong → silent miscompare | Add **positive AND negative** unit-test cases in same PR; gate review on those passing |
| R4.C.2 | `KernelObject.beq` chain breaks because `BEq Notification` not auto-derived from manual `DecidableEq` | Add explicit `instance : BEq Notification where beq a b := decide (a = b)` immediately after the manual `DecidableEq` |
| R4.C.3 | `match … waitingThreads with | x :: rest => …` operational sites have `match` arms that internally re-bind `rest` and reference it later | Use `tail?`-based migration: `match l.tail? with | some (x, rest) => … | none => …`. The `rest` here is `NoDupList`-typed |
| R4.C.4 | Proof elaboration time grows >2x in `NotificationPreservation/{Wait,Signal}.lean` | Add `@[reducible]` to `NoDupList.val` and the `CoeHead` instance; if still slow, factor proof bodies into named `private` lemmas |
| R4.C.4 | A proof-site `match` rebuild requires constructing a fresh `Nodup` proof, but the surrounding hypothesis has been deprecated to `True` | Schedule R4.C.4 to land BEFORE R4.C.6 (deprecation); the surrounding `uniqueWaiters` hypothesis is still meaningful at C.4 time |
| R4.C.5 | Deep `do`-chain nesting in `NegativeStateSuite.lean` triggers clang `-fbracket-depth=256` (per `CLAUDE.md` build-fragile pattern) | Apply the thin-dispatcher pattern: split any new test helper into ≤150-line sub-helpers per CLAUDE.md guidance |
| R4.C.5 | `by decide` timeout on long literal lists | None of the existing fixtures are long; if encountered, fall back to `by simp [List.Nodup]` or explicit cons-by-cons proof |
| R4.C.6 | Downstream proof body destructures `hUnique : uniqueWaiters st` (now `True`) and fails | Same mitigation as R4.A.5: locally rewrite to `obtain _ := hUnique` |
| R4.C.7 | Deprecation churn breaks `coreIpcInvariantBundle_to_uniqueWaiters` (`Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean`) | The 4-commit in-PR cleanup explicitly handles this caller; trivial alias keeps build green between commits |
| R4.C.7 | A bundle includes `uniqueWaiters` as a non-final conjunct, breaking tuple-extraction in callers | Update bundle definition first (commit 1), then preservation theorems (commit 2), then callers (commit 3); pre-commit hook gates each |
| R4.C.8 | Marker theorem name conflict with R4.A.7 in `CrossSubsystem.lean` | Use distinct names: `cspaceSlotUnique_promoted_to_structural` and `uniqueWaiters_promoted_to_structural` |

## Discharge index entries (`docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md`)

The current placeholder rows in §3.D , §3.E , and §3.F are populated by these full-shape rows when the workstream lands.

### §3.D — Type-level promotion entries

**D.1 — R4.A landing (DEEP-MODEL-01):**

| Field | Value |
|-------|-------|
| Theorem name | `SeLe4n.UniqueSlotMap.keys_unique` |
| File:Line | `SeLe4n/Model/Object/UniqueSlotMap.lean:<line>` |
| Promoted invariant | `cspaceSlotUnique` (formerly `Builder.lean` runtime obligation, now structural) |
| Discharge site | `UniqueSlotMap.{empty,insert,erase,filter,ofListWF}` smart constructors — each carries `hWF : table.invExtK` |
| Reachability check | `#check @SeLe4n.UniqueSlotMap.keys_unique` |

**D.3 — R4.C landing (DEEP-IPC-05):**

| Field | Value |
|-------|-------|
| Theorem name | `SeLe4n.notification_waiters_nodup` |
| File:Line | `SeLe4n/Model/Object/NoDupList.lean:<line>` |
| Promoted invariant | `uniqueWaiters` (formerly per-transition state-level invariant, now structural) |
| Discharge site | `NoDupList.{empty,consWithGuard,consWithGuard?,tail?,filter}` smart constructors — each carries `hNodup : val.Nodup` |
| Reachability check | `#check @SeLe4n.notification_waiters_nodup` |

### §3.E — Predecessor reroutings

**E.1 — DEEP-IPC-01 reroute (R4.C subsumes):**

| Field | Value |
|-------|-------|
| Subsumed finding | DEEP-IPC-01 (`notificationWait` runtime NoDup at `IPC/Operations/Endpoint.lean`) |
| Subsuming structural promotion | R4.C (§3.D D.3); the line-723 guard is replaced by `NoDupList.consWithGuard?`'s `none` return |
| Equivalence theorem | `SeLe4n.Kernel.notificationWait_runtime_check_implied_by_nodup` (already in tree at `IPC/Invariant/QueueNoDup.lean`; survives R4.C unchanged) |
| Reachability check | `#check @SeLe4n.Kernel.notificationWait_runtime_check_implied_by_nodup` |

### §3.F — False-positive structural witnesses (already populated by R4.D)

R4.A and R4.C **do not** add §3.F rows — those are reserved for false-positive remediations (per the §1.5 structural-fix policy). R4.A and R4.C are true-positive structural promotions, recorded in §3.D and §3.E.

### Companion marker theorems

Per the existing CrossSubsystem.lean closure-form discharge index pattern, after both tracks land, append to `SeLe4n/Kernel/CrossSubsystem.lean`:

```lean
/-- WS-RC R4.A landing: cspaceSlotUnique state-level invariant promoted to
    structural via UniqueSlotMap.hWF. Marker theorem for the discharge-index
    reachability gate. -/
theorem cspaceSlotUnique_promoted_to_structural : True := trivial

/-- WS-RC R4.C landing: uniqueWaiters state-level invariant promoted to
    structural via NoDupList.hNodup. Marker theorem for the discharge-index
    reachability gate. -/
theorem uniqueWaiters_promoted_to_structural : True := trivial
```

## Out of scope (deliberate deferrals)

- **R4.B** (`RetypeTarget` ScrubToken non-bypassability) — already landed in the in-flight WS-RC R4 work.
- **R4.D** (`cspaceMutate` null-cap witness theorems) — already landed.
- **`Endpoint.queue` / `Endpoint.recvQueue`** — these are `IntrusiveQueue`-backed (not `List`-backed) and already have their own `tcbQueueChainAcyclic` invariant. They are *separate* candidates for type-level promotion via a `NoDupQueue` wrapper; budget a follow-up workstream after R4.C lands.
- **Other `RHTable`-shaped state fields** — `state.objects`, `VSpaceRoot.mappings`, `AsidPool` mappings — all carry `invExt`/`invExtK` invariants in tree but lack `UniqueSlotMap`-style wrappers. After R4.A lands and the pattern is proven on `CNode.slots`, propose a follow-up that promotes one per PR using the same template (the smart-constructor sketch from R4.A.1 generalises).
- **Mathlib import** — none of this work introduces a Mathlib dependency. The required `List.Nodup`, `List.Nodup.filter`, `List.Nodup.of_cons` lemmas are either in Lean 4 v4.28.0 core or proven inline in `NoDupList.lean` as fallbacks.

## Critical files for implementation

These are the files an implementer should re-read before each sub-PR (paths absolute):

**For R4.A:**
- `/home/user/seLe4n/SeLe4n/Model/Object/Types.lean` — CNode field declaration 
- `/home/user/seLe4n/SeLe4n/Model/Object/Structures.lean` — `CNode.empty`, `CNode.mk'`, `CNode.insert`, `CNode.remove`, `slotsUnique`, `BEq CNode` instance 
- `/home/user/seLe4n/SeLe4n/Kernel/RobinHood/Bridge.lean` — existing `invExtK` preservation lemmas 
- `/home/user/seLe4n/SeLe4n/Kernel/RobinHood/Set.lean` — `RHSet` precedent template (the closest in-tree shape match)
- `/home/user/seLe4n/SeLe4n/Model/Builder.lean` — proof discharge
- `/home/user/seLe4n/SeLe4n/Kernel/InformationFlow/Projection.lean` — filter site
- `/home/user/seLe4n/SeLe4n/Kernel/FrozenOps/Operations.lean` — verify FrozenCNode independence
- `/home/user/seLe4n/SeLe4n/Kernel/Capability/Invariant/Defs.lean` — `cspaceSlotUnique` definition and bundle composition

**For R4.C:**
- `/home/user/seLe4n/SeLe4n/Model/Object/Types.lean` — Notification field declaration and `deriving DecidableEq` 
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Operations/Endpoint.lean` — `notificationWait` , `notificationSignal` , the line-723 runtime guard, the cons sites at 726 and 1134
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Invariant/Defs.lean` — `uniqueWaiters` , `notificationWaiterConsistent` , bridge theorem `not_mem_waitingThreads_of_ipcState_ne` 
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Invariant/QueueNoDup.lean` — existing `notification_waitingThreads_nodup_witness` and `notificationWait_runtime_check_implied_by_nodup` (the §3.E equivalence theorem; survives R4.C unchanged)
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Wait.lean` — preservation proofs that adapt mechanically
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` — preservation proofs that adapt mechanically
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` — frame-lemma record literals 
- `/home/user/seLe4n/SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean` — `removeFromAllNotificationWaitLists` filter site 
- `/home/user/seLe4n/SeLe4n/Testing/MainTraceHarness.lean` — fixture sites 

## Verification — end-to-end (full workstream close)

After all 15 sub-PRs land, the workstream-close verification is:

```bash
# 1. Pre-commit hook check (per CLAUDE.md)
./scripts/install_git_hooks.sh --check

# 2. Tier-0 hygiene (website link gate, sorry/axiom audit)
./scripts/test_tier0_hygiene.sh

# 3. Module-level builds
source ~/.elan/env
lake build SeLe4n.Model.Object.UniqueSlotMap
lake build SeLe4n.Model.Object.NoDupList
lake build SeLe4n.Model.Object.Types
lake build SeLe4n.Model.Object.Structures
lake build SeLe4n.Kernel.IPC.Operations.Endpoint
lake build SeLe4n.Kernel.IPC.Invariant.QueueNoDup
lake build SeLe4n.Kernel.Lifecycle.Operations.Cleanup
lake build SeLe4n.Kernel.Capability.Invariant.Defs
lake build SeLe4n.Kernel.CrossSubsystem

# 4. Discharge index reachability gate (compiles only if §3.D D.1, D.3 and §3.E E.1 are correctly named)
lake env lean -e '#check @SeLe4n.UniqueSlotMap.keys_unique'
lake env lean -e '#check @SeLe4n.notification_waiters_nodup'
lake env lean -e '#check @SeLe4n.Kernel.notificationWait_runtime_check_implied_by_nodup'
lake env lean -e '#check @SeLe4n.Kernel.cspaceSlotUnique_promoted_to_structural'
lake env lean -e '#check @SeLe4n.Kernel.uniqueWaiters_promoted_to_structural'

# 5. Manual DecidableEq Notification canary
lake env lean --run tests/ModelIntegritySuite.lean

# 6. Full test suite
./scripts/test_smoke.sh
./scripts/test_full.sh

# 7. Manual MainTraceHarness fixture comparison
lake exe sele4n > /tmp/main_trace.out
diff -q /tmp/main_trace.out tests/fixtures/main_trace_smoke.expected
```

All commands must complete with exit code 0. Step 7 specifically must show no diff — the trace fixture is the canonical sanity check that `Notification` and `CNode` literal-construction in `MainTraceHarness.lean` is correct after migration.

## Documentation synchronization (per CLAUDE.md "Documentation rules")

When the workstream lands, update in the same PR (R4.A.6 and R4.C.5 take partial responsibility each):

1. `README.md` — sync metrics from `docs/codebase_map.json` (`readme_sync` key)
2. `docs/spec/SELE4N_SPEC.md` — describe the `UniqueSlotMap` and `NoDupList` types in §6 (kernel data structures)
3. `docs/DEVELOPMENT.md` — note the type-level invariant promotion in the v0.31.0 changelog summary
4. `docs/gitbook/12-proof-and-invariant-map.md` — update the entry for `cspaceSlotUnique` and `uniqueWaiters` to point to their structural promotions
5. `docs/CLAIM_EVIDENCE_INDEX.md` — update if claims around state-level NoDup invariants are cited
6. `docs/REGISTERED_DEBT.md` — record R4.A.1..A.6 and R4.C.1..C.5 landing
7. `CHANGELOG.md` — add a v0.31.0 line for "WS-RC R4.A: CNode.slots type-level uniqueness via UniqueSlotMap" and similar for R4.C
8. `docs/codebase_map.json` — regenerate via `python3 scripts/regenerate_codebase_map.py` (or whatever the existing script is)

The `CLAUDE.md` source-layout block must also gain entries:
- `SeLe4n/Model/Object/UniqueSlotMap.lean` — UniqueSlotMap smart-constructor wrapper around RHTable
- `SeLe4n/Model/Object/NoDupList.lean` — NoDupList smart-constructor wrapper around List

## Open questions for the implementer (resolve before R4.A.2 / R4.C.2)

1. **`RHTable.ofList_invExtK`** — does Lean's existing `Bridge.lean` define this lemma? If yes, `UniqueSlotMap.ofListWF` becomes a 2-line lift; if no, `ofListWF` uses the fold-over-`insert` pattern (still 2 lines but slower at compile time).
2. **`FrozenOps/Operations.lean`** — is `FrozenCNode.slots` typed as `RHTable Slot Capability` (in which case R4.A.4 rewires it) or `FrozenMap …` (in which case R4.A.4 is a no-op)? Reading `SeLe4n/Model/FrozenState.lean` answers this — recommended action is to confirm in the R4.A.4 first commit.
3. **`KernelObject.beq` ** — does dropping `deriving DecidableEq` on `Notification` cascade into a `BEq Notification` requirement on the manual-`BEq KernelObject` instance? Verify by reading the instance body — it does `a == b` on each variant; the `Notification` arm needs `BEq Notification`. The manual `DecidableEq` provides this via Lean's standard `BEq`-from-`DecidableEq` derivation, but if not, R4.C.2 adds an explicit `instance : BEq Notification` immediately after.
4. **Lean 4 v4.28.0 lemma names** — `List.Nodup.of_cons` vs `List.nodup_cons.mp` vs `List.Nodup.cons` — verify the canonical name; if absent, the inline list-induction proof is ~10 LoC.

These four questions can be answered by direct code reads at the start of R4.A.2 / R4.C.2 in ~10 minutes; deferring them to plan-execution time keeps the plan tractable.

## Total scope summary

| Track | Sub-PRs | Estimated LoC | Files touched | Risk class |
|-------|---------|---------------|---------------|------------|
| R4.A | 7 | ~890 | ~30 | Medium (mechanical mostly; FrozenOps decision and bundle cleanup are the judgment calls) |
| R4.C | 8 | ~970 | ~38 | High (manual `DecidableEq Notification` is the canary; pattern-match migration is the second-largest risk) |
| **Total** | **15** | **~1860** | **~55 (with overlap on Types.lean and CrossSubsystem.lean only)** | — |

The earlier 11-sub-PR estimate (in a prior draft of this plan) under-counted by collapsing the **bundle cleanup** work (now A.6 and C.7) into the deprecation step, and by collapsing the **proof-side rewire** into the operational rewire (now C.3 + C.4). The 15-sub-PR breakdown surfaces those as their own coherent slices, each ≤200 LoC, each with its own pre-commit gate.

This plan converts two state-level invariants — `cspaceSlotUnique` (proven preserved by every CSpace operation) and `uniqueWaiters` (proven preserved by every notification operation) — into structural type-level invariants. The conversion is **redundant for correctness** (the state-level invariants are already proven), but is a true *faithfulness* improvement: it makes the property impossible to violate by construction rather than provable-but-bypassable. The runtime guard at `Endpoint.lean` becomes structurally subsumed by the typed `consWithGuard?` smart constructor, and the discharge index gains three reachability-gated witness theorems that future audits can re-derive from a single `#check` per closure.

No shortcuts: the plan does not weaken any docstring or downgrade any invariant. The state-level `_preserves_cspaceSlotUnique` and `_preserves_uniqueWaiters` theorem chains are first deprecated to `True` (preserving callability for downstream proofs) and then cleaned up in trailing sub-PRs. Every commit is `lake build`-green end-to-end. Every sub-PR has its own verification matrix entry. The highest-risk piece (manual `DecidableEq Notification`) is isolated into its own canary PR with positive **and** negative unit tests gating review.

## Pre-flight checklist (per sub-PR)

Before starting any sub-PR, the implementer should verify:

- [ ] **Local environment matches CLAUDE.md.** `./scripts/setup_lean_env.sh --skip-test-deps` has been run; `source ~/.elan/env` is active; `lake build` (default target) succeeds on the current branch.
- [ ] **Pre-commit hook installed.** `./scripts/install_git_hooks.sh --check` exits 0.
- [ ] **Branch off the right base.** R4.A.1 / R4.C.1 branch off the latest landed R4 commit (post-R4.B / post-R4.D). Subsequent sub-PRs branch off the parent's HEAD.
- [ ] **Surface report regenerated** if files have moved since the plan was written. Run a focused grep to confirm line numbers in the plan still match the codebase.
- [ ] **Test smoke baseline.** `./scripts/test_smoke.sh` passes on the parent commit. If not, fix that first; do not paper over it inside the new PR.

After completing each sub-PR (before requesting review):

- [ ] **Module-specific build.** `lake build <Module>` for every file touched (CLAUDE.md mandate).
- [ ] **Smoke + relevant suite.** `./scripts/test_smoke.sh` plus the suite(s) in the verification matrix for this PR.
- [ ] **Sorry / axiom audit.** `rg 'sorry|axiom' SeLe4n/` returns no new hits. Pre-existing sentinel-tracked exceptions are recorded under `TPI-D*` annotations and have not changed.
- [ ] **Internal-first naming.** No new identifier names contain workstream IDs (`WS-RC`, `R4`, etc.) per CLAUDE.md's internal-first naming rule. Such IDs are allowed in docstrings and commit messages, never in code identifiers.
- [ ] **No backwards-compat hacks.** No `// removed` comments, no renamed-to-`_` variables, no re-exported types unused by anything. Per CLAUDE.md, delete-completely is the convention.
- [ ] **Documentation sync.** If theorems / invariants / source layout changed, the relevant `docs/` files (`README.md` metrics, `docs/spec/SELE4N_SPEC.md`, `docs/gitbook/*.md`, `CHANGELOG.md`, `docs/REGISTERED_DEBT.md`) are updated in the same commit.
- [ ] **Website-linked path check.** No file in `scripts/website_link_manifest.txt` was renamed or deleted; if it was, update the manifest in the same PR.
- [ ] **Commit message format.** Matches `WS-RC R4.X.Y: <summary>` plus body plus `Refs:` line (per the in-tree `git log` convention).

## Rollback strategy

This plan is intentionally split into small commits so any individual sub-PR can be reverted in isolation without cascading failures.

**Rolling back a single sub-PR.** `git revert <sha>` on the offending commit. The deprecation-alias pattern (R4.A.5 / R4.C.6) means even a partial workstream landing leaves the codebase in a working state — the state-level invariants `cspaceSlotUnique` / `uniqueWaiters` are still defined (as `True`), the `_preserves_*` theorems still elaborate (with trivial proof bodies), and the structural `UniqueSlotMap` / `NoDupList` types coexist with the deprecated invariants without conflict.

**Rolling back a whole track mid-flight.**
- **R4.A track:** revert in reverse order A.7 → A.6 → A.5 → A.4 → A.3 → A.2 → A.1. Each revert is `lake build`-green by construction.
- **R4.C track:** revert in reverse order C.8 → C.7 → C.6 → C.5 → C.4 → C.3 → C.2 → C.1. Same property.
- **R4.A and R4.C are independent.** A failure mid-track A does not block track C, and vice versa.

**Recovering from an irrecoverable bundle-cleanup mistake.** If R4.A.6 or R4.C.7 (the bundle cleanups) introduce a subtle proof regression that's hard to identify, the sub-PR's 4 in-PR commits give natural rollback points: revert from the final commit backward until builds pass; the deprecation alias from R4.A.5 / R4.C.6 still keeps things working at the partial state.

**Recovering from a `DecidableEq Notification` miscompilation.** R4.C.2 is the canary. If the unit-test gate (positive + negative `decide (n1 = n2)` cases) catches a bug, revert R4.C.2; track A is unaffected. Patch R4.C.2's manual instance and re-land. Rolling back C.2 cascades to reverting C.3..C.8 — but those have not yet landed at C.2-canary time.

## Best-practices compliance checklist (CLAUDE.md alignment)

Cross-checked against `CLAUDE.md` "Doing tasks", "Key conventions", "Implement-the-improvement rule", "Documentation rules", and "Vulnerability reporting":

- [x] **Implement-the-improvement rule.** This plan implements the audit's recommendation (type-level structural invariant promotion) rather than weakening docstrings. The plan deliberately does NOT propose adding "phantom-like" caveats to the structural witness theorems.
- [x] **No `axiom` / `sorry`.** Every smart-constructor proof obligation is discharged via existing `RHTable._preserves_invExtK` lemmas (R4.A) or `List.Nodup.{cons,of_cons,filter,nil}` lemmas (R4.C). No new `axiom` or `sorry` is introduced.
- [x] **Deterministic semantics.** `UniqueSlotMap.{insert,erase,filter}` and `NoDupList.{empty,consWithGuard,consWithGuard?,tail?,filter}` are pure deterministic functions; no non-deterministic branches.
- [x] **Internal-first naming.** Identifiers in the plan (`UniqueSlotMap`, `NoDupList`, `consWithGuard`, `keys_unique`, `notification_waiters_nodup`) describe semantics, not workstream IDs. Workstream IDs (`WS-RC R4.A`, etc.) appear only in docstrings, commit messages, and discharge index citations.
- [x] **Module build verification.** Every sub-PR's verification matrix includes module-specific `lake build <Module>` per CLAUDE.md's mandate.
- [x] **Pre-commit hook compliance.** No `--no-verify` bypasses are required; the hook's `lake build <Module>` and sorry-check both pass for every commit in this plan.
- [x] **Documentation sync.** R4.A.7 and R4.C.8 explicitly synchronise `README.md`, `docs/spec/SELE4N_SPEC.md`, `docs/DEVELOPMENT.md`, `docs/gitbook/12-proof-and-invariant-map.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/REGISTERED_DEBT.md`, `CHANGELOG.md`, and `docs/codebase_map.json` per CLAUDE.md "Documentation rules".
- [x] **Website-linked-path protection.** No file in `scripts/website_link_manifest.txt` is renamed or deleted by this plan. The new files (`SeLe4n/Model/Object/UniqueSlotMap.lean`, `SeLe4n/Model/Object/NoDupList.lean`) are additions; if the manifest contains them post-landing, that is a website-update concern (out of scope for this plan).
- [x] **Background-agent file-change protection.** This plan is sequential per implementer track; no background agent overlapping file edits are proposed.
- [x] **Vulnerability reporting.** This plan introduces no security-sensitive code; it strengthens an existing structural invariant. No CVE-class findings are produced. If implementation surfaces one (e.g., a `DecidableEq` mistake yielding a silent miscompare), the implementer follows CLAUDE.md's "Vulnerability reporting" mandate to halt and surface immediately.
- [x] **`lake build` default target inadequate per CLAUDE.md.** The verification matrix explicitly enumerates module-specific build targets so the new `UniqueSlotMap` and `NoDupList` modules are exercised even before they're imported by `Main.lean` or any test harness.
- [x] **Tier-0 hygiene at workstream close.** R4.A.7 and R4.C.8 both run `bash scripts/check_website_links.sh` (the Tier-0 hygiene gate) per the protocol.
- [x] **No deep `do`-chain nesting in new tests.** Per CLAUDE.md's clang `-fbracket-depth=256` guidance, any new test helpers in R4.A.3 / R4.C.5 stay ≤150 Lean lines via the thin-dispatcher pattern (the canonical example being `tests/NegativeStateSuite.lean`'s `runNegativeChecks`).
- [x] **Reading large files in chunks.** Implementers reading `Notification`-touching files (e.g., `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/{Wait,Signal}.lean`, ~850/688 LoC) per CLAUDE.md's "Reading large files" guidance must use `Read(file_path, offset, limit)` rather than reading the whole file.
- [x] **Writing large files in chunks.** New file `SeLe4n/Model/Object/UniqueSlotMap.lean` is ~250 LoC; per CLAUDE.md's "Writing and editing large files" rule, this is built incrementally (skeleton ≤100 LoC + Edit appends ≤80 LoC each) or via Bash heredoc.
