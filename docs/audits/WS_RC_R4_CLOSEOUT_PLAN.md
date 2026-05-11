# WS-RC R4 Close-out Workstream Plan

**Status:** PLANNED
**Workstream:** WS-RC (audit remediation v0.30.11 → v0.31.0 → v1.0.0)
**Predecessors landed:** WS-RC R4 partial landing at commits `7da2572` (R4.B/D witness theorems), `f27defd` (NoDupList foundation + audit-pass marker), `6f3188a` (full R4.A/R4.C type-level field-type switches + ~55 consumer migrations), `7dd1958` (15 dedicated R4 API regression tests + stale-docstring fixes); see PR #769.
**Audit findings remediated by close-out:** DEEP-MODEL-01 (R4.A) — close-out only; DEEP-CAP-04 (R4.B) — opacity + token-threading completion; DEEP-IPC-05 (R4.C) — close-out only; structural-fix policy §1.5.
**Target version:** v0.31.0 — verified-specification release.
**Sub-PR count:** 9 atomic units across 5 phases (P, A, B, C, V).
**Estimated LoC:** ~1300 net (Phase P ≈ 80; Phase A ≈ 380; Phase B ≈ 450; Phase C ≈ 320; Phase V ≈ 70).
**Files touched:** ~50 (high overlap with PR #769 surface).
**Axiom / sorry budget:** 0 (all proof obligations discharged via existing in-tree lemmas).
**Source-of-truth refs:** `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §8; `docs/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md`; PR #769 audit findings (chat transcript).

## Table of contents

1. [Context](#1-context) — why this work, audit findings from PR #769.
2. [Inventory of remaining tasks](#2-inventory-of-remaining-tasks) — table mapping plan-spec items to current state.
3. [Headline architectural decisions](#3-headline-architectural-decisions) — opacity form, threading form, deprecation strategy.
4. [Sub-PR partition](#4-sub-pr-partition) — 5 phases, 9 sub-PRs.
5. [Phase P — Foundational additions](#5-phase-p--foundational-additions-purely-additive) (1 sub-PR).
6. [Phase A — `cspaceSlotUnique` retirement](#6-phase-a--cspaceslotunique-retirement) (2 sub-PRs).
7. [Phase B — `ScrubToken` structural close-out](#7-phase-b--scrubtoken-structural-close-out) (3 sub-PRs).
8. [Phase C — `uniqueWaiters` retirement](#8-phase-c--uniquewaiters-retirement) (2 sub-PRs).
9. [Phase V — Version bump and final docs](#9-phase-v--version-bump-and-final-docs) (1 sub-PR).
10. [Commit ordering and dependencies](#10-commit-ordering-and-dependencies).
11. [Verification matrix (consolidated)](#11-verification-matrix-consolidated).
12. [Failure-mode register](#12-failure-mode-register).
13. [Discharge-index updates](#13-discharge-index-updates).
14. [Documentation synchronization](#14-documentation-synchronization).
15. [Pre-flight checklist (per sub-PR)](#15-pre-flight-checklist-per-sub-pr).
16. [Rollback strategy](#16-rollback-strategy).
17. [Total scope summary](#17-total-scope-summary).

## 1. Context

PR #769 (`claude/review-codebase-audit-78WmZ`) landed the bulk of WS-RC R4 — the type-level structural promotions of `CNode.slots` to `SeLe4n.UniqueSlotMap Capability` (R4.A) and `Notification.waitingThreads` to `SeLe4n.NoDupList SeLe4n.ThreadId` (R4.C), the `ScrubToken` witness for `RetypeTarget` (R4.B), the `cspaceMutate` null-cap witness theorems (R4.D), and 15 dedicated regression tests. A post-merge audit identified **eight unfinished close-out tasks** from the original §8 plan and the type-level promotion plan:

- **A.5 / A.6** — Deprecate `cspaceSlotUnique` to `True` and remove from `capabilityInvariantBundle`.
- **B.1 / B.2 / B.3 / B.6** — Make `ScrubToken` structurally opaque, thread it through `lifecyclePreRetypeCleanup`'s return type, capture it at `lifecycleRetypeWithCleanup` and feed `mkRetypeTarget`.
- **C.6 / C.7** — Deprecate `uniqueWaiters` to `True` and remove from `ipcInvariantFull`.
- **Plan-named theorems** — Add `cnode_slots_unique`, `notification_waiters_nodup`, `cspaceSlotUnique_promoted_to_structural`, `uniqueWaiters_promoted_to_structural`, `cspaceSlotUnique_trivial`, `uniqueWaiters_trivial`.
- **Version bump** — The original plan referenced a v0.31.0 release cut; current version remains v0.30.11.

This close-out plan completes the R4 workstream so it can be retired before the v0.31.0 cut. The remaining work is mechanical-but-large (the bundle cleanups touch ~50 files between them); we partition it into 9 sub-PRs across 5 phases so every intermediate state is `lake build`-green and reviewable.

## 2. Inventory of remaining tasks

| Plan source | Task ID | Description | Current state | Severity | Owning phase |
|---|---|---|---|---|---|
| §8 R4.A.5 | `cnode_slots_unique` named theorem | `∀ (cn : CNode), cn.slots.uniqueSlots` regression | Missing under that name; equivalent `slotsUnique_holds` exists | Low | Phase P |
| §8 R4.B.1 | Make `ScrubToken` opaque/private | Currently a transparent `def ... : Prop`; plan asked for `private opaque ... : Type` | Structural opacity absent — security is proof-obligation-only | Medium | Phase B (B1) |
| §8 R4.B.2 | `lifecyclePreRetypeCleanup` returns `Kernel ScrubToken` | Still returns `Except KernelError SystemState` | Token not threaded | Medium | Phase B (B2) |
| §8 R4.B.3 | `lifecycleRetypeWithCleanup` captures token; passes to `mkRetypeTarget` | Call chain doesn't carry token; no `mkRetypeTarget` helper | Discharge happens at the proof layer, not the operational layer | Medium | Phase B (B3) |
| §8 R4.B.6 | Visibility: `ScrubToken` private, `RetypeTarget` public | `RetypeTarget` is public ✓; `ScrubToken` is public/transparent | Partial deviation | Low (covered by B1) |
| §8 R4.C.5 | `notification_waiters_nodup` named theorem | `∀ (n : Notification), n.waitingThreads.val.Nodup` — missing under that name | Equivalent `NoDupList.nodup_witness` exists | Low | Phase P |
| TL Plan R4.A.5 | Deprecate `cspaceSlotUnique` to `True` | Substantive definition still present | Medium (callers depend on it) | Phase A (A1) |
| TL Plan R4.A.6 | Remove `cspaceSlotUnique` from `capabilityInvariantBundle` | First conjunct at line 179; ~15 callers extract it | Medium | Phase A (A2) |
| TL Plan R4.A.7 | Marker theorem `cspaceSlotUnique_promoted_to_structural` | Missing; subsumed by umbrella marker `r4_structural_fix_discharge_index_documented` but not by literal name | Low | Phase P |
| TL Plan R4.C.6 | Deprecate `uniqueWaiters` to `True` | Substantive definition still present | Medium | Phase C (C1) |
| TL Plan R4.C.7 | Remove `uniqueWaiters` from `ipcInvariantFull` | Present in bundle and named-projection structure | Medium | Phase C (C2) |
| TL Plan R4.C.8 | Marker theorem `uniqueWaiters_promoted_to_structural` | Missing | Low | Phase P |
| Both plans | `cspaceSlotUnique_trivial`/`uniqueWaiters_trivial` helpers | Missing | Low | Phase P |
| Both plans | CHANGELOG v0.31.0 line + version bump | Logged under v0.30.11; version not bumped | Low | Phase V |

**Quantitative surface area** (verified at plan-author time, 2026-05-11):

- `cspaceSlotUnique`: 77 references across 14 files (14 production + 0 test).
- `uniqueWaiters`: 53 references across 11 files.
- `capabilityInvariantBundle`: referenced in 17 files; affects every `_preserves_capabilityInvariantBundle` theorem.
- `ipcInvariantFull`: referenced in 12 files; affects every `_preserves_ipcInvariantFull` theorem.
- `lifecyclePreRetypeCleanup`: called in 8 files (including `Lifecycle/Operations/RetypeWrappers.lean` and `Capability/Invariant/Preservation/*`).
- `ScrubToken`/`cleanupHookDischarged`: 3 files (Defs, RetypeWrappers, Cleanup tests).
- `hInv oid ntfn ...` application sites (uniqueWaiters): ~20 in `EndpointPreservation.lean` + 9 in `WaitingThreadHelpers.lean` + 1 in `QueueNoDup.lean`.

## 3. Headline architectural decisions

| Decision | Choice | Rationale |
|---|---|---|
| **Token type form for `ScrubToken`** | Private structure with private `mk ::` constructor + `Prop`-valued `Nonempty` wrapper | Keeps `cleanupHookDischarged` as `Prop` (proof-irrelevant, no runtime presence required), but the inner structure's constructor is file-private so external code can only inhabit via `ScrubToken.fromCleanup`. Avoids the Lean-4 `axiom`-equivalent forced by raw `opaque` on `Prop`. |
| **Threading form for cleanup return** | `lifecyclePreRetypeCleanup` returns `Except KernelError (Σ' stClean : SystemState, ScrubToken stClean target)` | Dependent sum (`Σ'`) carries the post-state and the matching token. Callers destructure `⟨stClean, token⟩`; `RetypeTarget` consumers feed `token` into `cleanupHookDischarged`. Alternative `Σ` requires `Type` value; `Σ'` keeps `Prop`-valued token. |
| **Deprecation strategy** | Two-step: collapse to `True` (Phase A1/C1) → bundle cleanup (Phase A2/C2) | Keeps every intermediate commit buildable. The `True` transitional form is a no-op for `lake build` once all destructure sites have been migrated. Aligns with §8.5 and the type-level plan's R4.A.5/R4.C.6 strategy. |
| **Migration order** | P → A1 → A2 → C1 → C2 → B1 → B2 → B3 → V1 | Phase P lands first (purely additive). A and C are mechanical retirements; landing them before B locks in the simpler work. B is the highest-risk path (signature change with cascading proof-side impact); it lands after A and C are stable so its risk surface is well-defined. V1 is the editorial-only version bump that anchors the cut. |
| **`@[deprecated]` vs collapse-to-True** | Collapse to `True` + `@[deprecated]` together | The collapse forces migration of *every* substantive use site (any `hUnique cnodeId cn h` application breaks). `@[deprecated]` alone leaves substantive uses in place — they continue to compile, defeating the bundle-cleanup follow-up. Per the type-level plan §R4.A.5 / §R4.C.6, collapse-to-True is the staged retirement vehicle. |
| **Dependent return for cleanup tokenized form** | `Except KernelError { stClean : SystemState // ScrubToken stClean target }` (`Subtype`) | `Subtype` is the cleaner Lean 4 idiom for "a value plus a proof about it" — proof-irrelevant, no `PSigma`/`Sigma` decision burden. The post-state-dependent `ScrubToken` lives in the second component. |
| **`@[deprecated]` attribute** | Used on the `True`-collapsed definitions during the transitional state (Phase A1/C1) | Surfaces obsolescence at the symbol level. The attribute is removed when the definition itself is deleted in Phase A2/C2 commit 4. |
| **Hypothesis migration recipe** | `obtain ⟨...⟩ := hUnique` → `obtain _ := hUnique` + direct projection (`slotsUnique_holds _` or `uniqueWaiters_holds _`) | Mechanical; aligns with the plan's failure-mode mitigation. The direct projections are provided by Phase P's purely-additive theorems. |
| **`hInv oid ntfn ...` application sites** (uniqueWaiters) | After Phase C1's collapse-to-True, every `hInv oid ntfn hObj` call becomes ill-typed. Recipe: replace with `(ntfn.waitingThreads.hNodup)` direct projection, or with `(uniqueWaiters_holds st oid ntfn hObj)` if state-level entry is preferred for proof economy. | Same migration as for `cspaceSlotUnique`. |
| **Marker theorem placement** | All R4 markers in `SeLe4n/Kernel/CrossSubsystem.lean` alongside the existing `r4_structural_fix_discharge_index_documented` | Single landing site for tier-3 invariant-surface gate. The plan-named markers (`cspaceSlotUnique_promoted_to_structural`, `uniqueWaiters_promoted_to_structural`) are companion `: True := trivial` siblings of the umbrella marker. |
| **Version bump** | Bump to v0.31.0 in Phase V after all close-out lands | v0.31.0 is the audit-plan's "verified specification release" cut. The bump touches `lakefile.toml`, `README.md` badge, `docs/codebase_map.json` regenerate, and the CHANGELOG anchor moves under `## v0.31.0`. |
| **No backwards-compat shims** | None. The deprecated names are deleted in Phase A2/C2's final commits. | Per CLAUDE.md "no backwards-compatibility hacks". The transitional `_trivial` helpers are also deleted at the end. |

### 3.1 Why the dependent-sum threading is correct

The plan's R4.B.2 specifies threading `ScrubToken` through `lifecyclePreRetypeCleanup`'s return type. The proper Lean 4 idiom is the dependent-pair `Σ' stClean, ScrubToken stClean target` (or its `Subtype`-equivalent), because the token's *type* depends on the *value* of the post-state. A non-dependent `Except KernelError (SystemState × ScrubToken)` would not type-check because `ScrubToken` requires a concrete `st`.

`Σ'` (the proof-irrelevant variant) is preferred over `Σ` because `ScrubToken` is `Prop`-valued, and `Σ'` keeps the entire return type proof-irrelevant where appropriate.

```lean
def lifecyclePreRetypeCleanup
    (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) :
    Except KernelError (Σ' stClean : SystemState, SeLe4n.Kernel.ScrubToken stClean target) := ...
```

Callers destructure:
```lean
match lifecyclePreRetypeCleanup st target currentObj newObj with
| .error e => .error e
| .ok ⟨stClean, scrubToken⟩ =>
    -- scrubToken : ScrubToken stClean target
    ...
```

### 3.2 Why the deprecation-to-True transitional state is sound

After collapsing `cspaceSlotUnique (_ : SystemState) : Prop := True`:
1. Every preservation theorem `_ → cspaceSlotUnique st'` is trivially provable: `fun _ => trivial`.
2. Every caller that holds `hUnique : cspaceSlotUnique st` now holds `True.intro`; they cannot destructure but can pattern-match on `trivial` or ignore.
3. Application sites `hUnique cnodeId cn hLookup` become ill-typed; the migration recipe replaces these with `slotsUnique_holds cn`.

The migration is mechanical because the substantive proof has already moved to `slotsUnique_holds` (Phase P), which discharges the same property unconditionally from the structural `UniqueSlotMap.hWF` field.

## 4. Sub-PR partition

| Phase | Sub-PR | Description | LoC | Files | Risk |
|---|---|---|---|---|---|
| P | **P1** | Foundational additions (named theorems, trivials, markers) | ~80 | 4 | Very low |
| A | **A1** | Deprecate `cspaceSlotUnique` to `True`; migrate application sites | ~180 | 8 | Medium |
| A | **A2** | Bundle cleanup — remove `cspaceSlotUnique` from `capabilityInvariantBundle` | ~200 | 12 | Medium |
| B | **B1** | Make `ScrubToken` private-structure with private `mk ::` constructor | ~80 | 3 | Medium |
| B | **B2** | Thread `ScrubToken` through `lifecyclePreRetypeCleanup`'s return type | ~220 | 8 | Medium-High |
| B | **B3** | Update `lifecycleRetypeWithCleanup` to capture token + add `mkRetypeTarget` helper | ~150 | 4 | Medium |
| C | **C1** | Deprecate `uniqueWaiters` to `True`; migrate application sites | ~170 | 7 | Medium |
| C | **C2** | Bundle cleanup — remove `uniqueWaiters` from `ipcInvariantFull` | ~150 | 10 | Medium |
| V | **V1** | Version bump 0.30.11 → 0.31.0 + doc sync | ~70 | 6 | Low |

Total: 9 sub-PRs, ~1300 LoC net, ~50 files touched. Each sub-PR keeps `lake build` green end-to-end and is reviewable in isolation.

## 5. Phase P — Foundational additions (purely additive)

**Goal.** Land the named theorems and marker theorems that subsequent phases depend on. This is a low-risk, no-mutation PR that anchors the discharge-index closures and is a prerequisite for Phases A/C's deprecation strategy.

### 5.1 Sub-PR P1 — Named theorems, trivials, and markers

**Scope:** ~80 LoC, all-additive.

**Files:**
- `SeLe4n/Model/Object/Structures.lean` — append `cnode_slots_unique` alias for `slotsUnique_holds`.
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` — append `cspaceSlotUnique_trivial` (substantive proof for now).
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` — append `uniqueWaiters_trivial` (substantive proof for now; alias of `uniqueWaiters_holds`).
- `SeLe4n/Kernel/IPC/Invariant/QueueNoDup.lean` — append `notification_waiters_nodup` canonical witness.
- `SeLe4n/Kernel/CrossSubsystem.lean` — append `cspaceSlotUnique_promoted_to_structural` and `uniqueWaiters_promoted_to_structural` marker theorems (companions of the existing `r4_structural_fix_discharge_index_documented`).
- `tests/ModelIntegritySuite.lean` — append reachability tests.

**Concrete code sketch (target final state after P1):**

`SeLe4n/Model/Object/Structures.lean` (inside `namespace CNode`, after `slotsUnique_holds`):
```lean
/-- WS-RC R4.A / DEEP-MODEL-01: plan-named alias for the structural
    CNode-level uniqueness witness.  Identical to `slotsUnique_holds`;
    retained under the plan's canonical name for discharge-index
    reachability. -/
theorem cnode_slots_unique : ∀ (cn : CNode), cn.slotsUnique := slotsUnique_holds
```

`SeLe4n/Kernel/Capability/Invariant/Defs.lean` (after the existing `cspaceSlotUnique` definition):
```lean
/-- WS-RC R4.A.5 (transitional): substantive trivial-discharge of
    `cspaceSlotUnique`.  After Phase A1 collapses the definition to
    `True`, this body becomes `trivial`; the theorem signature is
    unchanged so callers depending on the named identifier continue to
    elaborate. -/
theorem cspaceSlotUnique_trivial (st : SystemState) : cspaceSlotUnique st :=
  fun _ cn _ => SeLe4n.Model.CNode.slotsUnique_holds cn
```

`SeLe4n/Kernel/IPC/Invariant/Defs.lean` (after `uniqueWaiters_holds`):
```lean
/-- WS-RC R4.C.6 (transitional): plan-named alias for the structural
    state-level Nodup discharge.  After Phase C1 collapses the
    definition to `True`, this body becomes `trivial`. -/
theorem uniqueWaiters_trivial (st : SystemState) : uniqueWaiters st :=
  uniqueWaiters_holds st
```

`SeLe4n/Kernel/IPC/Invariant/QueueNoDup.lean` (after `notification_waitingThreads_nodup_witness`):
```lean
/-- WS-RC R4.C / DEEP-IPC-05: plan-named canonical witness — every
    `Notification` has a Nodup waiter list structurally.  Identical to
    `(fun n => n.waitingThreads.hNodup)`; retained under the plan's
    canonical name. -/
theorem notification_waiters_nodup (n : Notification) :
    n.waitingThreads.val.Nodup :=
  n.waitingThreads.hNodup
```

`SeLe4n/Kernel/CrossSubsystem.lean` (in the WS-RC R4 marker block):
```lean
/-- WS-RC R4.A.7: state-level `cspaceSlotUnique` promoted to structural
    via `UniqueSlotMap.hWF`.  Marker theorem for the discharge-index
    reachability gate. -/
theorem cspaceSlotUnique_promoted_to_structural : True := trivial

/-- WS-RC R4.C.8: state-level `uniqueWaiters` promoted to structural via
    `NoDupList.hNodup`.  Marker theorem for the discharge-index
    reachability gate. -/
theorem uniqueWaiters_promoted_to_structural : True := trivial
```

`tests/ModelIntegritySuite.lean` (append):
```lean
/-- WS-RC R4 close-out P1: plan-named theorem reachability gate.
    Confirms that the six named theorems specified in the original §8
    plan and the type-level promotion plan are reachable via `#check`. -/
def r4_close_out_named_theorems_reachable : IO Unit := do
  let _ := @SeLe4n.Model.CNode.cnode_slots_unique
  let _ := @SeLe4n.Kernel.cspaceSlotUnique_trivial
  let _ := @SeLe4n.Kernel.uniqueWaiters_trivial
  let _ := @SeLe4n.Kernel.notification_waiters_nodup
  let _ := @SeLe4n.Kernel.cspaceSlotUnique_promoted_to_structural
  let _ := @SeLe4n.Kernel.uniqueWaiters_promoted_to_structural
  expect "WS-RC R4 close-out P1: plan-named theorems reachable" true
```

(Plus the registration line in `main`.)

**Detailed action items:**

| # | Action |
|---|---|
| P1.1 | Append `cnode_slots_unique` to `Structures.lean` (CNode namespace). |
| P1.2 | Append `cspaceSlotUnique_trivial` to `Capability/Invariant/Defs.lean` (substantive proof for now; updated to `trivial` in Phase A1). |
| P1.3 | Append `uniqueWaiters_trivial` to `IPC/Invariant/Defs.lean` (alias of `uniqueWaiters_holds`). |
| P1.4 | Append `notification_waiters_nodup` to `IPC/Invariant/QueueNoDup.lean`. |
| P1.5 | Append both marker theorems to `CrossSubsystem.lean` beside the existing umbrella marker. |
| P1.6 | Append the reachability test to `ModelIntegritySuite.lean` and register in `main`. |

**Verification:**
- `lake build SeLe4n.Model.Object.Structures`
- `lake build SeLe4n.Kernel.Capability.Invariant.Defs`
- `lake build SeLe4n.Kernel.IPC.Invariant.Defs`
- `lake build SeLe4n.Kernel.IPC.Invariant.QueueNoDup`
- `lake build SeLe4n.Kernel.CrossSubsystem`
- Full `lake build SeLe4n` (312 jobs).
- `./scripts/test_smoke.sh`
- `lake exe model_integrity_suite` reports the new `r4_named_theorems_reachable` test passes.

**Failure mode:** none expected; the theorems are pure projections of existing structural witnesses.

**Discharge-index update:** `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` §3.D rows D.1, D.3, D.6, D.7 gain the plan-named theorem citations in addition to the existing `slotsUnique_holds`/`uniqueWaiters_holds`/`nodup_witness` ones.

## 6. Phase A — `cspaceSlotUnique` retirement

**Goal.** Retire the state-level `cspaceSlotUnique` invariant — first by collapsing its definition to `True` (Phase A1) so the substantive content moves to `slotsUnique_holds`/`cspaceSlotUnique_trivial`, then by removing it from `capabilityInvariantBundle` and downstream consumers (Phase A2). Final commit of A2 deletes the definition entirely.

### 6.1 Sub-PR A1 — Deprecate `cspaceSlotUnique` to `True`; migrate application sites

**Scope:** ~180 LoC, mostly mechanical migrations.

**Files (verified surface):**
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` — collapse definition; update `cspaceSlotUnique_trivial` proof to `trivial`.
- `SeLe4n/Kernel/Capability/Invariant/Authority.lean` — `_preserves_cspaceSlotUnique` chain becomes trivial.
- `SeLe4n/Kernel/Capability/Invariant/Preservation/*.lean` — same.
- `SeLe4n/Kernel/Capability/Operations.lean` — any `hUnique cnodeId cn hLookup` application site → `slotsUnique_holds cn`.
- `SeLe4n/Kernel/CrossSubsystem.lean` — composition site for `capabilityInvariantBundle` (deferred to Phase A2; only the destructure sites change in A1).
- `SeLe4n/Testing/InvariantChecks.lean` — runtime check returns trivially (the assertion becomes `True`).

**Detailed action items:**

| # | Action |
|---|---|
| A1.1 | At `Defs.lean:27`, replace the substantive definition with `@[deprecated "WS-RC R4.A: cspaceSlotUnique is now structural via UniqueSlotMap.hWF. This alias is retained for downstream callers and removed in A2's bundle cleanup."] def cspaceSlotUnique (_ : SystemState) : Prop := True`. |
| A1.2 | Update `cspaceSlotUnique_trivial` proof body (added in P1) from `fun _ _ _ => slotsUnique_holds _` to `trivial`. The theorem signature is unchanged. |
| A1.3 | Identify every `_preserves_cspaceSlotUnique` theorem with a `grep -rn "_preserves_cspaceSlotUnique"`. For each: replace the proof body with `fun _ _ _ _ _ => trivial` (or the equivalent shape; the conclusion is now `True`). Expected sites: ~5-8. |
| A1.4 | Identify every application of the form `hUnique cnodeId cn hLookup` with `grep -rn "hUnique .* .* .*"` in `Capability/`. Replace with `slotsUnique_holds cn` (direct projection). Expected sites: ~3-5. |
| A1.5 | Identify every destructure of the form `obtain ⟨hUnique, ...⟩ := hBundle` where `hBundle : capabilityInvariantBundle st`. The bundle still contains the `cspaceSlotUnique` conjunct in A1 (A2 removes it), so the destructure still works syntactically — but the bound `hUnique` is now `: True`. Either keep the destructure intact (the `hUnique` binding becomes unused) OR rewrite to `obtain ⟨_, hSound, …⟩ := hBundle`. Recommended: minimal disturbance — keep the destructure, accept the unused-binding warning in A1, and clean it up in A2. |
| A1.6 | At `Testing/InvariantChecks.lean`, the runtime check `cspaceSlotUniqueCheck : SystemState → Bool` (if present) collapses to `fun _ => true`. The assertion in the runtime invariant suite becomes trivially true. |
| A1.7 | Audit `Authority.lean` for any tactic mode that rewrites via `cspaceSlotUnique`'s definition. After collapse to `True`, `unfold cspaceSlotUnique` exposes `True` — tactic sequences that depended on the substantive unfolding break. Mitigation: re-derive via `slotsUnique_holds _`. |

**Verification:**
- After each per-file migration: `lake build SeLe4n.<File>`.
- Full `lake build` (312 jobs) green at the end of the PR.
- `./scripts/test_smoke.sh` green.
- `./scripts/test_full.sh` green.
- `grep -rn "obtain.*hUnique" /home/user/seLe4n/SeLe4n /home/user/seLe4n/tests` returns only sites where `hUnique` is consumed via `obtain _ :=` (no destructure of substantive content).
- `lake build SeLe4n.Kernel.Capability.Operations` remains green (largest consumer; ~1858 LoC).

**Failure mode 1:** A proof body internally calls `hUnique cnodeId cn hLookup` (passing arguments to the universally quantified hypothesis). After collapse to `True`, `hUnique` is no longer applicable — the proof fails. **Mitigation:** systematic replacement with `slotsUnique_holds cn`. Use `grep -rn "hUnique [a-zA-Z]\+ [a-zA-Z]\+ [a-zA-Z]\+"` to enumerate sites.

**Failure mode 2:** A `simp` lemma destructures `capabilityInvariantBundle` and now binds `True`. **Mitigation:** the unused-binding warning is silenced by the underscore replacement; structural destructure shape is preserved.

**Failure mode 3:** A test suite asserts `cspaceSlotUnique` substantively (e.g., constructs a state and queries the predicate). After collapse to `True`, the test trivially passes. **Mitigation:** the test should be updated to assert via `slotsUnique_holds` if it's exercising the structural property; otherwise it remains a no-op assertion (and the runtime suite gains a passing check).

**Commit messages within the sub-PR (recommended):**
- `WS-RC R4 A1: collapse cspaceSlotUnique definition to True; mark deprecated`
- `WS-RC R4 A1: migrate hUnique application sites to slotsUnique_holds`
- `WS-RC R4 A1: collapse _preserves_cspaceSlotUnique proof bodies to trivial`

### 6.2 Sub-PR A2 — Bundle cleanup: remove `cspaceSlotUnique` from `capabilityInvariantBundle`

**Scope:** ~200 LoC. 4 in-PR commits to keep every intermediate state buildable.

**Files (verified surface):**
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` — drop conjunct from `capabilityInvariantBundle` (line 179) and from the named-projection structure `CapabilityInvariantBundle` (line 212).
- `SeLe4n/Kernel/Capability/Invariant/Preservation/*.lean` — every `_preserves_capabilityInvariantBundle` body loses one slot.
- `SeLe4n/Kernel/Capability/Operations.lean` — callers' `rcases ⟨hUnique, hSound, …⟩ := hBundle` lose the `hUnique` slot.
- `SeLe4n/Kernel/CrossSubsystem.lean` — invariant bundle composition site.
- `SeLe4n/Testing/InvariantChecks.lean` — runtime check assertion removed.

**4-commit strategy** (per the plan's mandate that each commit be `lake build`-green):

| Commit | Action | Files modified |
|---|---|---|
| A2.c1 | Drop `cspaceSlotUnique st ∧` from `capabilityInvariantBundle` (line 179) and from the named-projection structure `CapabilityInvariantBundle`'s field list. The bundle now has 6 conjuncts instead of 7. Update the equivalence theorem `capabilityInvariantBundle_iff_CapabilityInvariantBundle` so the iff matches the new shape. | `Defs.lean` |
| A2.c2 | Update every `_preserves_capabilityInvariantBundle` theorem body to drop the `cspaceSlotUnique` slot from the proof-tuple construction. Use `grep -rn "_preserves_capabilityInvariantBundle"` to enumerate (~6 theorems across `Preservation/*.lean`). The tuples shrink by one slot. | `Preservation/*.lean` |
| A2.c3 | Update every caller of `_preserves_capabilityInvariantBundle` to match the new tuple shape. Use `grep -rn "obtain.*hUnique.*hSound.*hBnd\|⟨hUnique, hSound" /home/user/seLe4n/SeLe4n` to enumerate (~10-15 sites). Each site loses the first `.1` extraction or the corresponding pattern position. | `Operations.lean`, `CrossSubsystem.lean`, etc. |
| A2.c4 | Delete the `cspaceSlotUnique` definition itself (it has been `True`-valued and `@[deprecated]` since A1; now no callers reference it). Delete the `cspaceSlotUnique_trivial` helper. Remove the `cspaceSlotUnique` field from `CapabilityInvariantBundle` if it was retained as a named field in A2.c1. | `Defs.lean` (final delete) |

**Verification:**
- After A2.c1: `lake build SeLe4n` green; every site that previously typed against the 7-conjunct shape now elaborates against 6.
- After A2.c2: same; preservation theorems still typecheck.
- After A2.c3: same; callers consume the new tuple shape.
- After A2.c4: `grep -rn "cspaceSlotUnique" /home/user/seLe4n/SeLe4n /home/user/seLe4n/tests` should return zero hits (excluding the discharge index markdown).
- Full `./scripts/test_full.sh` after the final commit.

**Failure mode:** an `rcases` destructure is deeply nested across multiple files; updating commit-by-commit may leave a stale destructure in an intermediate state. **Mitigation:** the 4-commit ordering (definition → preservation → callers → delete) guarantees each commit's edits are self-contained at the elaboration level. The pre-commit hook surfaces any `lake build` regression.

**Discharge-index update:** §3.D row D.6 (`SeLe4n.Model.CNode.slotsUnique_holds`) gains a citation of `cnode_slots_unique` as the plan-named sibling. §3.G (predecessor reconfirmations) adds an entry recording the A.5/A.6 closure.

## 7. Phase B — `ScrubToken` structural close-out

**Goal.** Strengthen `ScrubToken` from a transparent `Prop`-valued `def` (proof-obligation-only security) to a private-structure-backed `Prop` whose only public inhabitation route is `ScrubToken.fromCleanup` (structural opacity). Thread the token through `lifecyclePreRetypeCleanup`'s return type and `lifecycleRetypeWithCleanup`'s call chain so the discipline is enforced at the operational layer in addition to the proof layer.

### 7.1 Sub-PR B1 — Make `ScrubToken` private-structure with private `mk ::` constructor

**Scope:** ~80 LoC, surgical.

**Files:**
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` — rewrite `ScrubToken` from transparent `def` to a `Prop`-valued `Nonempty` of a private structure.
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` — keep `ScrubToken.fromCleanup` as the only public introduction site; update its body to wrap the witness in the private structure.
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` — keep `retypeTarget_implies_scrub_token_held` unchanged (still extracts the third conjunct).

**Detailed action items:**

| # | Action |
|---|---|
| B1.1 | At `Defs.lean:356`, replace `def ScrubToken (st : SystemState) (target : SeLe4n.ObjId) : Prop := ∃ ...` with the private-structure form: <br/> `private structure ScrubTokenImpl (st : SystemState) (target : SeLe4n.ObjId) where`<br/>` private mk ::`<br/>` stPre : SystemState`<br/>` currentObj : KernelObject`<br/>` newObj : KernelObject`<br/>` hCleanup : lifecyclePreRetypeCleanup stPre target currentObj newObj = .ok st`<br/><br/>`def ScrubToken (st : SystemState) (target : SeLe4n.ObjId) : Prop := Nonempty (ScrubTokenImpl st target)` |
| B1.2 | Update `ScrubToken.fromCleanup` to wrap the witness in the private structure: <br/>`theorem ScrubToken.fromCleanup ... (hCleanup : lifecyclePreRetypeCleanup stPre target currentObj newObj = .ok stClean) : SeLe4n.Kernel.ScrubToken stClean target := ⟨{ stPre := stPre, currentObj := currentObj, newObj := newObj, hCleanup := hCleanup }⟩` |
| B1.3 | Verify `retypeTarget_implies_scrub_token_held` still elaborates — its body extracts the third conjunct of `cleanupHookDischarged` which is now `Nonempty (ScrubTokenImpl ...)`. |
| B1.4 | Update the `ScrubToken` docstring to reflect the new structural opacity: "`ScrubTokenImpl`'s constructor is `private mk ::`, so the only public inhabitation route is `ScrubToken.fromCleanup`. External callers cannot wrap an arbitrary cleanup proof; they must produce the canonical `lifecyclePreRetypeCleanup ... = .ok` witness." |
| B1.5 | Add a security-pinning test in `tests/ModelIntegritySuite.lean` that exercises `ScrubToken.fromCleanup` on a concrete cleanup outcome and confirms reachability. The test is positive-only (we cannot test that bypass is impossible — that's a structural property checked at elaboration). |

**Verification:**
- `lake build SeLe4n.Kernel.Capability.Invariant.Defs` green.
- `lake build SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers` green (consumer).
- Full `lake build` green (312 jobs).
- `./scripts/test_smoke.sh` green.
- `./scripts/test_full.sh` green.

**Failure mode 1:** A consumer file destructures `ScrubToken` directly (e.g., `obtain ⟨stPre, currentObj, newObj, hCleanup⟩ := scrubToken`). After B1, this fails because `ScrubTokenImpl.mk` is private. **Mitigation:** search for such sites with `grep -rn "obtain.*ScrubToken\|cases.*ScrubToken"` and replace with the public-API access path (which is opaque). Expected: zero such sites (the token is introduced and consumed only at the public API boundary).

**Failure mode 2:** `cleanupHookDischarged` is now a conjunction including `Nonempty (ScrubTokenImpl ...)`. `simp` may need updating if it tries to unfold across the new opacity. **Mitigation:** the conjunction shape is unchanged from the call-site perspective; only the third conjunct's structure differs. Existing proof bodies that build `cleanupHookDischarged` via `⟨h1, h2, h3⟩` need `h3` to be a `Nonempty (ScrubTokenImpl ...)` rather than a raw existential — recoverable via `ScrubToken.fromCleanup` if a cleanup outcome is in scope.

### 7.2 Sub-PR B2 — Thread `ScrubToken` through cleanup return via `lifecyclePreRetypeCleanupWithToken` wrapper

**Scope:** ~220 LoC. The most-invasive sub-PR in the close-out phase.

**Strategy:** **wrapper formulation, not in-place signature change.**  The plan's literal "change `lifecyclePreRetypeCleanup` to return `Kernel ScrubToken`" is achieved by adding a sibling `lifecyclePreRetypeCleanupWithToken` whose return type carries the token and migrating every operational caller to it.  This avoids the recursive-fixpoint construction problem (a function cannot easily inhabit a value whose type depends on its own output) and lets the bare `lifecyclePreRetypeCleanup` remain for proof-side reasoning that doesn't need the token.

**Files (verified surface):**
- `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean` — add `lifecyclePreRetypeCleanupWithToken` wrapper returning the `Subtype`-paired result.
- `SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean` — add bridge lemmas linking `WithToken` and bare forms.
- `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` — update `lifecycleRetypeWithCleanup` to call `WithToken` and discard the token (B2 keeps it discarded; B3 captures it).
- `SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean` — update proof bodies that pattern-match on the cleanup outcome (~2 sites).
- `SeLe4n/Kernel/Capability/Invariant/Preservation/Revoke.lean` — same (~2 sites).
- `tests/NegativeStateSuite.lean`, `tests/OperationChainSuite.lean` — test fixtures that exercise the cleanup pipeline.

**Concrete code sketch (target final state):**

`SeLe4n/Kernel/Lifecycle/Operations/CleanupPreservation.lean` (additive — keeps the bare form intact):
```lean
/-- WS-RC R4.B.2: tokenized form of `lifecyclePreRetypeCleanup`.
    Returns the post-cleanup state paired with a `ScrubToken` proving
    that the cleanup pipeline produced it. Callers that need to
    construct a `RetypeTarget` consume the token via `mkRetypeTarget`
    (WS-RC R4.B.3); callers that only need the post-state can use the
    bare `lifecyclePreRetypeCleanup` directly. -/
def lifecyclePreRetypeCleanupWithToken
    (st : SystemState) (target : SeLe4n.ObjId)
    (currentObj newObj : KernelObject) :
    Except KernelError { stClean : SystemState // SeLe4n.Kernel.ScrubToken stClean target } :=
  match h : lifecyclePreRetypeCleanup st target currentObj newObj with
  | .error e => .error e
  | .ok stClean =>
      .ok ⟨stClean, SeLe4n.Kernel.ScrubToken.fromCleanup h⟩

/-- WS-RC R4.B.2 bridge: the `WithToken` form is equivalent to the bare
    form on the state component.  Use when porting preservation proofs
    from the bare form to the tokenized form. -/
theorem lifecyclePreRetypeCleanupWithToken_state_eq
    {st : SystemState} {target : SeLe4n.ObjId}
    {currentObj newObj : KernelObject}
    {stClean : SystemState}
    {token : SeLe4n.Kernel.ScrubToken stClean target}
    (hWT : lifecyclePreRetypeCleanupWithToken st target currentObj newObj
        = .ok ⟨stClean, token⟩) :
    lifecyclePreRetypeCleanup st target currentObj newObj = .ok stClean := by
  unfold lifecyclePreRetypeCleanupWithToken at hWT
  split at hWT
  · cases hWT
  · case _ stClean' hBare =>
    rename_i hStComp
    -- hWT : .ok ⟨stClean', ScrubToken.fromCleanup hBare⟩ = .ok ⟨stClean, token⟩
    -- Extract stClean' = stClean from the .ok.injEq + Subtype.mk.injEq chain
    injection hWT with hEq
    have hStEq : stClean' = stClean := (Subtype.mk.injEq _ _ _ _).mp hEq |>.1
    subst hStEq
    exact hBare
```

`SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` (update the body to call `WithToken`):
```lean
def lifecycleRetypeWithCleanup
    (authority : CSpaceAddr)
    (target : SeLe4n.ObjId)
    (newObj : KernelObject) : Kernel Unit :=
  fun st =>
    if ¬ newObj.wellFormed st.objects then
      .error .illegalState
    else
      match st.objects[target]? with
      | none => lifecycleRetypeObject authority target newObj st
      | some currentObj =>
          -- WS-RC R4.B.2: capture the post-cleanup state AND the token.
          -- The token is discarded here (`lifecycleRetypeWithCleanup` returns
          -- `Kernel Unit`); callers that need the token use
          -- `lifecycleRetypeWithCleanupTokenized` (added in B3).
          match lifecyclePreRetypeCleanupWithToken st target currentObj newObj with
          | .error e => .error e
          | .ok ⟨stClean, _scrubToken⟩ =>
            let stScrubbed := scrubObjectMemory stClean target currentObj.objectType
            lifecycleRetypeObject authority target newObj stScrubbed
```

**Detailed action items:**

| # | Action |
|---|---|
| B2.1 | Add `lifecyclePreRetypeCleanupWithToken` in `CleanupPreservation.lean` (after the existing `lifecyclePreRetypeCleanup` and `lifecycleCleanupPipeline`).  The body is the thin wrapper shown above. |
| B2.2 | Add the bridge lemma `lifecyclePreRetypeCleanupWithToken_state_eq` that extracts the bare cleanup equation from the tokenized one. |
| B2.3 | Update `lifecycleRetypeWithCleanup` in `RetypeWrappers.lean` to call `lifecyclePreRetypeCleanupWithToken`.  The captured token is discarded with `_scrubToken` for now (B3 wires it through). |
| B2.4 | Update `lifecycleCleanupPipeline` (the named wrapper at `CleanupPreservation.lean:250-252`) to forward to `lifecyclePreRetypeCleanupWithToken` *and* expose a `Pipeline.WithToken` variant alongside the existing alias.  The bare `lifecyclePreRetypeCleanup` is preserved unchanged. |
| B2.5 | Audit preservation theorems that pattern-match on the cleanup result.  Expected sites:<br/>• `lifecyclePreRetypeCleanup_flat_subset` (`CleanupPreservation.lean:295`)<br/>• Theorems in `EndpointReplyAndLifecycle.lean` and `Revoke.lean` that reason about `hOk : lifecyclePreRetypeCleanup ... = .ok stClean`<br/>For each, use the `lifecyclePreRetypeCleanupWithToken_state_eq` bridge to extract the bare equation when the proof pattern-matches on the tokenized form. |
| B2.6 | Update tests in `NegativeStateSuite.lean` and `OperationChainSuite.lean` that exercise `lifecyclePreRetypeCleanup` outcomes.  Most tests can use the bare form; only tests that exercise the threading should use the `WithToken` form (B3 adds dedicated tests). |
| B2.7 | Verify the bare `lifecyclePreRetypeCleanup` is unchanged.  This is critical: it remains the canonical proof-side entry point for reasoning that doesn't need the token. |

**Verification:**
- `lake build SeLe4n.Kernel.Lifecycle.Operations.CleanupPreservation` green.
- `lake build SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers` green.
- Full `lake build` green (312 jobs).
- `./scripts/test_smoke.sh` green.
- `./scripts/test_full.sh` green.

**Failure mode 1:** `lifecyclePreRetypeCleanupWithToken_state_eq`'s `injection` tactic doesn't reduce the dependent Subtype equation. **Mitigation:** use `Subtype.ext_iff` or explicit `Subtype.mk.injEq` rewriting; the bridge lemma's proof is the one technical proof in B2 — implement and test it first.

**Failure mode 2:** A preservation theorem's `simp` lemma set rewrites through `lifecyclePreRetypeCleanup` directly and breaks when the `WithToken` form is introduced. **Mitigation:** `lifecyclePreRetypeCleanupWithToken_state_eq` provides the bridge; for `simp` cases, register the bridge as `@[simp]` if it helps. Otherwise the bare `lifecyclePreRetypeCleanup` is unchanged, so its `simp` lemmas keep firing.

**Failure mode 3:** A test that captures `match ... with | .ok stClean => ...` breaks because the operational call site now uses `WithToken`. **Mitigation:** the test can either (a) keep using the bare form for proof-side reasoning, or (b) migrate to the `WithToken` form and pattern-match on `⟨stClean, _⟩`.

### 7.3 Sub-PR B3 — Update `lifecycleRetypeWithCleanup` to capture token + add `mkRetypeTarget` helper

**Scope:** ~150 LoC.

**Files:**
- `SeLe4n/Kernel/Lifecycle/Operations/RetypeWrappers.lean` — capture the token from `lifecyclePreRetypeCleanupWithToken` and thread it to `mkRetypeTarget`.
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` — define `mkRetypeTarget` helper that constructs a `RetypeTarget` from a target `ObjId` + the three `cleanupHookDischarged` conjuncts.
- Tests exercising `lifecycleRetypeWithCleanup`.

**Detailed action items:**

| # | Action |
|---|---|
| B3.1 | At `Defs.lean`, add the `mkRetypeTarget` smart constructor:<br/>`def mkRetypeTarget (st : SystemState) (target : SeLe4n.ObjId) (hTypeMeta : ∀ obj, st.objects[target]? = some obj → SystemState.lookupObjectTypeMeta st target = some obj.objectType) (hNoStaleRefs : ∀ tcb, st.objects[target]? = some (.tcb tcb) → ¬(tcb.tid ∈ st.scheduler.runQueue.flat)) (token : SeLe4n.Kernel.ScrubToken st target) : RetypeTarget st := { id := target, cleanupHookDischarged := ⟨hTypeMeta, hNoStaleRefs, token⟩ }` |
| B3.2 | At `RetypeWrappers.lean:58`, update `lifecycleRetypeWithCleanup` to capture the token from `lifecyclePreRetypeCleanupWithToken` and pass it to `mkRetypeTarget` (if the wrapper produces a `RetypeTarget`; if not, the token is captured for later proof-side discharge). The current `lifecycleRetypeWithCleanup` returns `Kernel Unit`, so it does not produce a `RetypeTarget` — but the **proof-side discharge** that uses the token now goes through `ScrubToken.fromCleanup` cleanly. |
| B3.3 | Add a sibling `lifecycleRetypeWithCleanupTokenized` wrapper that produces both the post-state and the post-state's `ScrubToken` for callers that need to construct a `RetypeTarget` from the cleanup outcome (e.g., for downstream lifecycle-aware retype operations). |
| B3.4 | Update the preservation theorems for `lifecycleRetypeWithCleanup` (those that reason about the cleanup outcome) to use the new token directly rather than constructing it externally via `ScrubToken.fromCleanup`. |
| B3.5 | Add a security-pinning test in `tests/ModelIntegritySuite.lean`: `r4b_retypeTarget_constructed_via_mkRetypeTarget` exercises the full chain `lifecycleRetypeWithCleanupTokenized → mkRetypeTarget → RetypeTarget` and confirms the resulting `RetypeTarget` carries the correct `id`. |

**Verification:**
- `lake build SeLe4n.Kernel.Capability.Invariant.Defs` green.
- `lake build SeLe4n.Kernel.Lifecycle.Operations.RetypeWrappers` green.
- Full `lake build` green.
- `lake exe model_integrity_suite` reports the new `r4b_retypeTarget_*` tests pass.

**Failure mode:** `mkRetypeTarget` takes 4 arguments; existing call sites construct `RetypeTarget` via the structure literal directly. **Mitigation:** the structure literal form is preserved (not deprecated); `mkRetypeTarget` is an additive helper. Existing callers continue to work; only new callers are encouraged to use the helper.

## 8. Phase C — `uniqueWaiters` retirement

Mirrors Phase A for the IPC-side invariant. The structure is parallel: collapse to `True` (C1) → bundle cleanup (C2).

### 8.1 Sub-PR C1 — Deprecate `uniqueWaiters` to `True`; migrate application sites

**Scope:** ~170 LoC.

**Files (verified surface):**
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` — collapse definition; update `uniqueWaiters_trivial`.
- `SeLe4n/Kernel/IPC/Invariant/QueueNoDup.lean` — `notification_waitingThreads_nodup_witness` body unchanged (still uses substantive `uniqueWaiters`); preserve the substantive form via `uniqueWaiters_holds`.
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/{Signal,Wait}.lean` — `_preserves_uniqueWaiters` chain becomes trivial.
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean` — ~20 `hInv oid ntfn ...` application sites.
- `SeLe4n/Kernel/IPC/Invariant/WaitingThreadHelpers.lean` — 9 `hInv tid' tcb' hObj` application sites.
- `SeLe4n/Kernel/Architecture/Invariant.lean:434` — `default_uniqueWaiters` becomes trivial.
- `SeLe4n/Testing/InvariantChecks.lean` — runtime check becomes trivial.

**Detailed action items:**

| # | Action |
|---|---|
| C1.1 | At `IPC/Invariant/Defs.lean:590`, replace the substantive definition with `@[deprecated "WS-RC R4.C: uniqueWaiters is now structural via NoDupList.hNodup. This alias is retained for downstream callers and removed in C2's bundle cleanup."] def uniqueWaiters (_ : SystemState) : Prop := True`. |
| C1.2 | Update `uniqueWaiters_trivial` proof from `uniqueWaiters_holds st` to `trivial`. |
| C1.3 | Update `uniqueWaiters_holds` proof from `fun _ ntfn _ => ntfn.waitingThreads.hNodup` to `fun _ => trivial`. The theorem signature is unchanged but the body now produces `True.intro`. |
| C1.4 | At `NotificationPreservation/{Signal,Wait}.lean`, identify every `_preserves_uniqueWaiters` theorem and collapse the proof body to `fun _ _ _ _ _ _ _ => trivial` (or the equivalent shape). Expected: ~5 theorems. |
| C1.5 | At `EndpointPreservation.lean`, identify every `hInv oid ntfn hObj` application site (~20 sites). For each, replace with `ntfn.waitingThreads.hNodup` direct projection. The argument shape changes from `(oid : ObjId) (ntfn : Notification) (hObj : st.objects[oid]? = some (.notification ntfn))` to a no-arg structural projection. |
| C1.6 | At `WaitingThreadHelpers.lean`, identify every `hInv tid' tcb' hObj` application site (~9 sites). These deal with thread-side waiting-thread-pending-message-none. Migration: this hypothesis is `waitingThreadsPendingMessageNone st`, NOT `uniqueWaiters st`. **Audit cross-check needed**: verify whether these `hInv` bindings are for `uniqueWaiters` or for a different invariant. Look at the theorem signatures. |
| C1.7 | At `QueueNoDup.lean:679`, `hUnique oid ntfn hObj` becomes `ntfn.waitingThreads.hNodup` direct projection. |
| C1.8 | At `Architecture/Invariant.lean:434`, `default_uniqueWaiters : uniqueWaiters default` becomes trivial. |
| C1.9 | At `Testing/InvariantChecks.lean`, the runtime check `uniqueWaitersCheck` collapses to `fun _ => true`. |

**Verification:**
- `lake build SeLe4n.Kernel.IPC.Invariant.Defs` green.
- Each consumer file builds green after migration.
- Full `lake build` green (312 jobs).
- `./scripts/test_smoke.sh` and `./scripts/test_full.sh` green.
- `grep -rn "hInv oid ntfn\|hInv .* ntfn .*hObj" /home/user/seLe4n/SeLe4n` should return zero substantive applications.

**Failure mode 1:** `WaitingThreadHelpers.lean`'s `hInv` is for a different invariant; my migration recipe doesn't apply. **Mitigation:** audit each site individually at implementation time; only migrate sites where `hInv : uniqueWaiters st`.

**Failure mode 2:** A proof body uses `hUnique.1` or `hUnique.2` to extract pieces of the substantive form. **Mitigation:** find with `grep -rn "hUnique\.[0-9]"` and replace via direct `nodup_witness` projections.

### 8.2 Sub-PR C2 — Bundle cleanup: remove `uniqueWaiters` from `ipcInvariantFull`

**Scope:** ~150 LoC, 4 in-PR commits.

**Files:**
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` — drop `uniqueWaiters` from `ipcInvariantFull` (line ~1198) and from the named-projection structure (line ~1246).
- `SeLe4n/Kernel/IPC/Invariant/{Signal,Wait}Preservation.lean` — preservation theorem bodies.
- `SeLe4n/Kernel/IPC/Invariant/EndpointPreservation.lean`, `Structural/{StoreObjectFrame,DualQueueMembership}.lean` — callers' destructure shape.
- `SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean:220` — `coreIpcInvariantBundle_to_uniqueWaiters` becomes vacuous (delete or rewrite to `uniqueWaiters_trivial _`).
- `SeLe4n/Kernel/Architecture/Invariant.lean:434` — `default_uniqueWaiters` deleted.

**4-commit strategy** (parallel to A2):

| Commit | Action |
|---|---|
| C2.c1 | Drop `uniqueWaiters st ∧` from `ipcInvariantFull` and from the named-projection structure's field list. Update the equivalence theorem. |
| C2.c2 | Update every `_preserves_ipcInvariantFull` theorem body to drop the `uniqueWaiters` slot. |
| C2.c3 | Update every caller of `_preserves_ipcInvariantFull` to match the new tuple shape. |
| C2.c4 | Delete the `uniqueWaiters` definition, `uniqueWaiters_trivial`, `uniqueWaiters_holds`, `coreIpcInvariantBundle_to_uniqueWaiters`, and `default_uniqueWaiters`. Remove the `notificationWait_preserves_uniqueWaiters` theorem entirely (it has been vacuously trivial since C1). |

**Verification:**
- After each commit: `lake build SeLe4n` green.
- After C2.c4: `grep -rn "uniqueWaiters" /home/user/seLe4n/SeLe4n /home/user/seLe4n/tests` should return zero hits.
- `./scripts/test_full.sh` green.

**Failure mode:** `coreIpcInvariantBundle_to_uniqueWaiters` has callers in tests. **Mitigation:** `grep coreIpcInvariantBundle_to_uniqueWaiters /home/user/seLe4n/tests` — update each caller in the same commit.

## 9. Phase V — Version bump and final docs

**Goal.** Cut v0.31.0 as the verified-specification release the audit plan referenced.

### 9.1 Sub-PR V1 — Version bump 0.30.11 → 0.31.0 + doc sync

**Scope:** ~70 LoC.

**Files:**
- `lakefile.toml` — bump `version = "0.30.11"` to `version = "0.31.0"` (two occurrences).
- `README.md` — update version badge (`shields.io/badge/version-0.30.11-blue` → `0.31.0`) and the version row in the metrics table.
- `CHANGELOG.md` — add a `## v0.31.0` header above the consolidated R4 entries; group all R4 sub-PR entries under it.
- `docs/codebase_map.json` — regenerate via `scripts/generate_codebase_map.py`.
- `docs/spec/SELE4N_SPEC.md` — verify the version reference (if any).
- `docs/WORKSTREAM_HISTORY.md` — add a v0.31.0 entry under WS-RC R4 closure summary recording the close-out PRs.

**Detailed action items:**

| # | Action |
|---|---|
| V1.1 | Bump `lakefile.toml` version. |
| V1.2 | Update README version badge and metrics row. |
| V1.3 | Reorganize CHANGELOG: insert `## v0.31.0 — WS-RC R4 closure: structural-invariant retirement` heading; consolidate the entries from PR #769 and Phases P/A/B/C under it. The pre-existing v0.30.11 entries (WS-RC R0/R1/R2/R3 + R4 partial landing) remain under their original heading. |
| V1.4 | Regenerate `docs/codebase_map.json`. |
| V1.5 | Append a v0.31.0 closure entry to `docs/WORKSTREAM_HISTORY.md`. |
| V1.6 | Verify `scripts/website_link_manifest.txt` — no path renames in this phase, so the manifest should remain consistent. |

**Verification:**
- `lake build` green.
- `./scripts/test_smoke.sh` green (includes the codebase-map staleness check).
- `bash scripts/check_website_links.sh` green.
- `grep "0.30.11" /home/user/seLe4n/lakefile.toml` returns zero hits.
- `grep "0.31.0" /home/user/seLe4n/lakefile.toml /home/user/seLe4n/README.md /home/user/seLe4n/CHANGELOG.md` returns the expected hits.

**Failure mode:** The version bump may cascade into git tag automation. **Mitigation:** the bump is editorial; no tag is created automatically. The release workflow is manual per `docs/DEVELOPMENT.md`.

## 10. Commit ordering and dependencies

Phases P, A, B, C, V have the following dependency graph:

```
                     P1 (foundational additions)
                          │
              ┌───────────┼───────────┐
              │           │           │
             A1          B1*         C1
              │                       │
             A2                      C2
              │                       │
              └───────────┬───────────┘
                          │
                         B1
                          │
                         B2
                          │
                         B3
                          │
                         V1

       * B1 has no upstream dependencies beyond P1, but is
         scheduled after A2/C2 in the serial order so the
         lower-risk retirements land first.
```

**Recommended serial order** (single implementer):

`P1 → A1 → A2 → C1 → C2 → B1 → B2 → B3 → V1`

Rationale:
- **P1 first** — purely additive; anchors the named theorems and trivials that subsequent phases depend on for proof migration.
- **A1 before A2** — A1 is the migration phase (collapse-to-True + destructure rewrite); A2 is the bundle cleanup. A1 must land first so A2's bundle cleanup doesn't trip over substantive uses.
- **A2 before C1** — A2 is the smaller-surface retirement (cspaceSlotUnique: 14 files, 77 references) and exercises the collapse-then-cleanup pattern. Landing A first lets C reuse the validated pattern.
- **C1 before C2** — same rationale as A1/A2.
- **C2 before B1** — A and C are mechanical retirements; B is the highest-risk path (signature-cascading change). Landing A and C first stabilises the foundation so B's risk surface is well-defined and any regressions are clearly localised to B.
- **B1 before B2** — B1 is the structural opacity (smaller); B2 is the return-type threading (larger). Landing B1 first lets B2 use the opaque type throughout.
- **B2 before B3** — B2 adds the `WithToken` wrapper; B3 captures the token in `lifecycleRetypeWithCleanup` and adds `mkRetypeTarget`. B3 cannot land without B2.
- **V1 last** — version bump anchors the entire close-out; no functional changes.

**Parallel-implementer order.** If two implementers work simultaneously:
- Implementer 1 owns the A+C retirement tracks (A1 → A2 → C1 → C2 sequentially; the tracks are independent at the file level, so A and C can also be interleaved).
- Implementer 2 owns the B track (B1 → B2 → B3), starting after P1 lands.  B1 is independent of A and C; B2 and B3 depend on B1.
- V1 lands last after both tracks complete.

**Independence guarantee.** The A track and the C track touch disjoint files (Capability vs. IPC subsystems); they can be developed in parallel.  The B track touches Lifecycle and Capability/Invariant/Preservation files, which have some overlap with A but no overlap with C.  Practically, A1/A2 ↔ B and C1/C2 are pairwise mergeable in any order, but **B should land after both A and C** to minimise the rebase surface for B's wide-impact return-type change.

## 11. Verification matrix (consolidated)

| Sub-PR | `lake build` | `test_smoke.sh` | `test_full.sh` | Reachability checks | LoC | Files |
|---|---|---|---|---|---|---|
| P1 | ✓ | ✓ | ✓ | All P1.1-P1.5 theorems `#check`-able | ~80 | 4 |
| A1 | ✓ (after migration) | ✓ | ✓ | `slotsUnique_holds` reachable; `cspaceSlotUnique = True` | ~180 | 8 |
| A2 | ✓ (per commit) | ✓ (final) | ✓ (final) | `grep cspaceSlotUnique` returns zero hits | ~200 | 12 |
| B1 | ✓ | ✓ | ✓ | `ScrubTokenImpl.mk` private; `fromCleanup` public | ~80 | 3 |
| B2 | ✓ | ✓ | ✓ | `lifecyclePreRetypeCleanupWithToken` reachable | ~220 | 8 |
| B3 | ✓ | ✓ | ✓ | `mkRetypeTarget` reachable; new test passes | ~150 | 4 |
| C1 | ✓ (after migration) | ✓ | ✓ | `uniqueWaiters_holds` reachable; `uniqueWaiters = True` | ~170 | 7 |
| C2 | ✓ (per commit) | ✓ (final) | ✓ (final) | `grep uniqueWaiters` returns zero hits | ~150 | 10 |
| V1 | ✓ | ✓ | ✓ | Version pinned at 0.31.0 across all docs | ~70 | 6 |

**Cumulative validation at workstream close:**

```bash
# Build
source ~/.elan/env && lake build

# Smoke + full tests
./scripts/test_smoke.sh
./scripts/test_full.sh

# Website manifest
bash scripts/check_website_links.sh

# Codebase map fresh
./scripts/generate_codebase_map.py --pretty --output docs/codebase_map.json
git diff --exit-code docs/codebase_map.json   # no diff expected

# Reachability of all R4 markers (the existing probe script)
lake env lean /tmp/r4_full_witness_check.lean

# Zero residual references to deprecated names
grep -rn "cspaceSlotUnique\b\|uniqueWaiters\b" SeLe4n tests   # expect zero hits

# Pre-commit hook coverage
./scripts/install_git_hooks.sh --check
```

## 12. Failure-mode register

| # | Risk | Phase | Severity | Mitigation |
|---|---|---|---|---|
| FM-1 | A1 collapse breaks `hUnique cnodeId cn hLookup` application sites | A1 | Medium | Pre-A1 grep finds all sites; migrate within A1; Phase P's `slotsUnique_holds` is the replacement |
| FM-2 | A2's 4-commit phasing leaves intermediate non-buildable state | A2 | Medium | Each commit is verified `lake build`-green per the plan's mandate; pre-commit hook is the safety net |
| FM-3 | B1's private structure constructor breaks proof bodies that destructure `ScrubToken` directly | B1 | Low | Expected: zero such sites (ScrubToken is only constructed at the introduction site and only destructured via the public projection theorem); pre-B1 grep confirms |
| FM-4 | B2's dependent-sum threading requires a fixpoint witness for `lifecyclePreRetypeCleanup` calling itself | B2 | Medium-High | Use the wrapper formulation (B2.3) instead of the recursive formulation (B2.2); the wrapper avoids the fixpoint |
| FM-5 | B2's `Sigma.mk.injEq` pattern doesn't reduce in preservation proofs | B2 | Medium | Introduce a bridge lemma `WithToken_state_eq` that connects the new and old APIs; preservation proofs can continue to use the old shape via the bridge |
| FM-6 | C1's collapse breaks ~20 `hInv oid ntfn hObj` application sites | C1 | Medium | Pre-C1 grep finds all sites; migrate within C1 using `ntfn.waitingThreads.hNodup` direct projection |
| FM-7 | C2's bundle cleanup affects ~12 files of preservation/structural theorems | C2 | Medium | 4-commit phasing per A2 strategy; pre-commit hook + grep verify each commit |
| FM-8 | V1's version bump leaves stale references | V1 | Low | Grep verification (`grep "0.30.11"` returns zero hits) |
| FM-9 | Pre-commit hook timeout on large bundle-cleanup commits | A2 / C2 | Low | The 4-commit phasing keeps each commit's modified-module set small; the hook builds only modified modules, not the full tree |
| FM-10 | Stack-depth explosion in test suites referencing the new private structure | B1 | Low | The known clang-nesting issue (`CLAUDE.md` §"Known build-fragile pattern"); split test helpers if needed |

## 13. Discharge-index updates

`docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` updates by phase:

| Phase | §3.D update | §3.E update | §3.F update | §3.G update |
|---|---|---|---|---|
| P1 | D.1/D.3/D.6/D.7 gain plan-named theorem citations (`cnode_slots_unique`, `notification_waiters_nodup`, `cspaceSlotUnique_promoted_to_structural`, `uniqueWaiters_promoted_to_structural`) | — | — | — |
| A1 | D.6 docstring notes the deprecation transitional state | — | — | New row: A.5 deprecation transitional landing |
| A2 | D.6 marked "RETIRED" (definition deleted); citation moves to `slotsUnique_holds`-only | — | — | New row: A.6 bundle cleanup |
| B1 | D.2 (`retypeTarget_implies_scrub_token_held`) docstring updated to note the new private-structure opacity | — | — | — |
| B2 | — | — | — | New row: B.2 cleanup-tokenized return |
| B3 | D.2 gains a reference to `mkRetypeTarget` smart constructor | — | — | — |
| C1 | D.7 docstring notes the deprecation transitional state | — | — | New row: C.6 deprecation transitional landing |
| C2 | D.7 marked "RETIRED"; citation moves to `uniqueWaiters_holds`-only (or `NoDupList.nodup_witness` if `_holds` is also deleted) | — | — | New row: C.7 bundle cleanup |
| V1 | §5 closure summary refreshed: "All R4 closures landed; v0.31.0 cut" | — | — | — |

## 14. Documentation synchronization

Per CLAUDE.md "Documentation rules", every change requires updating in the same PR:

| Doc | Phase P1 | Phase A1 | Phase A2 | Phase B1 | Phase B2 | Phase B3 | Phase C1 | Phase C2 | Phase V1 |
|---|---|---|---|---|---|---|---|---|---|
| `README.md` | — | — | — | — | — | — | — | — | Version badge |
| `docs/spec/SELE4N_SPEC.md` §8.10.7 | Refresh theorem citations | Note A.5 transition | Mark A.6 closure | Update B.1 opacity note | Update B.2 cleanup signature | Update B.3 mkRetypeTarget | Note C.6 transition | Mark C.7 closure | v0.31.0 anchor |
| `docs/DEVELOPMENT.md` | — | — | — | — | — | — | — | — | v0.31.0 release note |
| `docs/gitbook/12-proof-and-invariant-map.md` | Add new bullets | Note A.5 transition | Mark A.6 closure | B.1 opacity update | B.2 signature update | B.3 mkRetypeTarget | C.6 transition | C.7 closure | v0.31.0 anchor |
| `docs/CLAIM_EVIDENCE_INDEX.md` | If claims change | — | If claims change | — | — | — | — | If claims change | If claims change |
| `docs/WORKSTREAM_HISTORY.md` | — | — | A.6 closure entry | — | — | B.3 closure entry | — | C.7 closure entry | v0.31.0 closure entry |
| `docs/codebase_map.json` | Regenerate | Regenerate | Regenerate | Regenerate | Regenerate | Regenerate | Regenerate | Regenerate | Regenerate |
| `CHANGELOG.md` | Add P1 entry | Add A1 entry | Add A2 entry | Add B1 entry | Add B2 entry | Add B3 entry | Add C1 entry | Add C2 entry | Reorganize under v0.31.0 |
| `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` | §3.D row refreshes | §3.G row added | §3.G row added; D.6 RETIRED | D.2 update | §3.G row added | D.2 update | §3.G row added | §3.G row added; D.7 RETIRED | §5 closure refresh |
| `docs/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md` | — | — | — | — | — | — | — | — | Mark all close-out sub-PRs LANDED |

## 15. Pre-flight checklist (per sub-PR)

Each sub-PR must satisfy the following before merging (CLAUDE.md alignment):

- [ ] Workstream ID identified (WS-RC R4 close-out, sub-PR <ID>).
- [ ] Scope is one coherent slice (per the partition in §4).
- [ ] Transitions are explicit and deterministic (no non-deterministic branches introduced).
- [ ] Invariant/theorem updates paired with implementation (per §13 discharge-index updates).
- [ ] `lake build` (312 jobs) green.
- [ ] `./scripts/test_smoke.sh` green; `./scripts/test_full.sh` green for theorem-touching sub-PRs (P1, A1, A2, B1, B2, B3, C1, C2).
- [ ] Documentation synchronized (per §14 matrix).
- [ ] No website-linked paths renamed or removed.
- [ ] No `claude.ai/code/session_*` URL in commit messages or PR title/body/summary (CLAUDE.md "Session URL hygiene").
- [ ] No `sorry`/`axiom` introduced (production proof surface).
- [ ] No workstream IDs in identifier names (CLAUDE.md "Internal-first naming"; "WS-RC R4" stays in docstrings and commit messages only).
- [ ] PR title under 70 characters; details go in the body.
- [ ] `Refs: docs/audits/WS_RC_R4_CLOSEOUT_PLAN.md §<phase>` cite line in commit message body.

## 16. Rollback strategy

Each sub-PR is independently revertible. The 4-commit phasing in A2 and C2 means a rollback of those sub-PRs requires reverting all 4 commits as a group; the pre-commit hook ensures no intermediate non-buildable state is left.

Cross-phase rollback constraints:

- **Reverting V1 alone**: trivial; bumps version back to v0.30.11. No code rollback needed.
- **Reverting B3 alone**: removes the `mkRetypeTarget` helper but leaves B2's threading in place. Acceptable transitional state.
- **Reverting B2 alone**: re-introduces the old `lifecyclePreRetypeCleanup` return shape. B3 must also be reverted (depends on B2's threading).
- **Reverting B1 alone**: re-introduces the transparent `ScrubToken` def. B2/B3 may break (they reference the private-structure form). Recommend reverting B1+B2+B3 together if rollback of B1 is needed.
- **Reverting A2 alone**: re-introduces the `cspaceSlotUnique` conjunct in `capabilityInvariantBundle`. A1 (deprecation alias) may remain; the alias evaluates to `True` so the conjunct is trivial. Build remains green.
- **Reverting A1 alone**: re-introduces the substantive `cspaceSlotUnique` definition. A2 (bundle removal) may have already excised the conjunct; build remains green.
- **Reverting C1/C2**: mirror of A1/A2.
- **Reverting P1**: trivial; removes the named theorems. Subsequent phases that reference them would need their `slotsUnique_holds`/`uniqueWaiters_holds` citations swapped back.

**Recommended rollback order** if a later phase needs to be reverted: revert in reverse-merge order (V1 → C2 → C1 → B3 → B2 → B1 → A2 → A1 → P1). The phases are designed to be reversible in this LIFO order.

## 17. Total scope summary

| Metric | Phase P | Phase A | Phase B | Phase C | Phase V | **Total** |
|---|---|---|---|---|---|---|
| Sub-PRs | 1 | 2 | 3 | 2 | 1 | **9** |
| LoC | ~80 | ~380 | ~450 | ~320 | ~70 | **~1300** |
| Files | 4 | 16 | 12 | 14 | 6 | **~50** (with overlap) |
| New theorems | 6 | 0 | 1 (B1 introduction) | 0 | 0 | **7** |
| Deleted definitions | 0 | 1 (cspaceSlotUnique) | 0 | 1 (uniqueWaiters) | 0 | **2** |
| Risk level | Very low | Medium | Medium-High | Medium | Low | — |
| Discharge-index rows touched | 4 | 1 (+ G) | 1 | 1 (+ G) | 1 (§5) | **8** |

**Total scope vs PR #769:** PR #769 landed ~1880 net LoC across ~50 files (foundation modules + field-type switches + 15 tests). This close-out plan adds ~1300 net LoC across ~50 overlapping files, mostly mechanical migrations and surgical strengthening of the existing R4 structures.

**Axiom / sorry budget:** 0 — every proof discharges via existing in-tree lemmas (`slotsUnique_holds`, `uniqueWaiters_holds`, `RHTable._preserves_invExtK` family, `List.Nodup` library, structural smart-constructor discharges).

**Estimated time:** 2–4 implementer-days for a contributor familiar with the WS-RC R4 surface. Phase B is the largest single risk; A2 and C2 are the largest bundle-cleanup phases.

## 18. Closing notes

This plan completes the WS-RC R4 workstream so the v0.31.0 cut can be made cleanly. Every deferred item from the original `AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §8 and `WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md` is owned by a specific sub-PR; the discharge index will read "all R4 closures LANDED" after Phase V1.

After R4 closes, the next WS-RC phase is **R5 — Scheduler / Lifecycle behaviour symmetry** (DEEP-SUSP-01/02, DEEP-SCH-02..06). That phase has its own plan in `docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md` §9 and is independent of R4.

---

**Cross-references:**
- [`docs/audits/AUDIT_v0.30.11_WORKSTREAM_PLAN.md`](AUDIT_v0.30.11_WORKSTREAM_PLAN.md) §8 — canonical R4 plan.
- [`docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md`](AUDIT_v0.30.11_DISCHARGE_INDEX.md) §3 — R4 discharge rows.
- [`docs/planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md`](../planning/WS_RC_R4_TYPE_LEVEL_PROMOTION_PLAN.md) — the 15-sub-PR breakdown (R4.A.1–A.7, R4.C.1–C.8).
- PR #769 — `claude/review-codebase-audit-78WmZ` — the R4 partial landing (R4.A foundation + field switch, R4.B/D witness theorems, R4.C foundation + field switch, 15 API tests).
- CLAUDE.md — implement-the-improvement rule, documentation rules, session URL hygiene, naming conventions.
