# WS-RC R4.A + R4.C — Type-level Structural Promotion of `CNode.slots` and `Notification.waitingThreads`

**Status**: PLANNED
**Workstream**: WS-RC (audit remediation v0.30.11 → v0.31.0 → v1.0.0)
**Audit findings remediated**: DEEP-MODEL-01 (R4.A), DEEP-IPC-05 (R4.C), DEEP-IPC-01 (subsumed by R4.C)
**Predecessors landed**: WS-RC R4.B (DEEP-CAP-04 — `RetypeTarget` ScrubToken), WS-RC R4.D (DEEP-CAP-02 — `cspaceMutate` null-cap witnesses), R4.B/C/D structural-witness commit `7da2572`
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

**The intended outcome.** After R4.A and R4.C land, every `CNode.slots` access is provably unique-keyed by construction (smart-constructor preservation lemmas discharge `invExtK` at every mutation), every `Notification.waitingThreads` access is provably duplicate-free by construction, and the corresponding state-level invariants (`cspaceSlotUnique`, `uniqueWaiters`) are deprecated to `True` because their work is now structural. The runtime duplicate guard at `Endpoint.lean:723` is replaced by a runtime-checked smart constructor (`NoDupList.consWithGuard?`) that fails closed via `.alreadyWaiting` when the cons would violate Nodup — provably equivalent to the old check under the existing `notificationWaiterConsistent` invariant.

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

**Why `structure` over refinement abbrev (`abbrev T := { x // P x }`).** A structure with a named field gives a stable global identifier (`UniqueSlotMap.table`, `NoDupList.val`), supports per-instance `Repr` independent of subtype-name leakage in pretty-printed goals, lets us attach `@[reducible] def` accessors selectively, and crucially gives us a dedicated namespace (`UniqueSlotMap.insert`, `NoDupList.consWithGuard`) where smart constructors live. The `RHSet` precedent at `SeLe4n/Kernel/RobinHood/Set.lean` is the closest in-tree template for `UniqueSlotMap` and confirms the `structure` shape scales to the larger surface. The `NonNullCap` refinement abbrev at `SeLe4n/Model/Object/Types.lean:432` is a counter-example we deliberately do not mirror: it works for a 1-field, 1-method API; both R4.A and R4.C have multi-method APIs where namespace matters.

**Why `CoeHead` over `Coe` / `CoeFun`.** `CoeHead` (vs `Coe`) allows the unification head to be a metavariable while still firing the coercion — this is what makes `cn.slots.fold f init` continue to elaborate when `cn.slots : UniqueSlotMap`, because Lean searches for `RHTable.fold` after coercing the head. `CoeFun` is for treating a value as a function (`f x` syntax) and does not apply.

**Where the coercion does NOT fire (and what to do).** Three Lean 4 elaboration paths bypass `CoeHead` and need explicit rewiring:

1. **`match` expressions** (`match ntfn.waitingThreads with | [] => … | x :: rest => …`) — the `match` discriminant is unified against the constructor's type directly; coercion does not fire. **Migration:** rewrite to `match ntfn.waitingThreads.val with` (proof-side, mechanical) **or** to `match ntfn.waitingThreads.tail? with | none => … | some (x, rest) => …` (operational-side, abstraction-preserving). The plan picks per-site (operational sites use `tail?`, proof sites use `.val` to keep proof tactics working).
2. **`{ cn with slots := … }` record-update syntax** — the RHS is unified against the field's declared type. Under the new typing, RHS values must produce `UniqueSlotMap`, which is what the smart constructors return. No coercion needed; the call site already type-checks if the smart constructor is invoked correctly.
3. **`if h : x ∈ list then …` conditional decidability** — Lean resolves `Membership α (NoDupList α)` from the `instance` we declare in `R4.C.1`; coercion is not consulted. Solved by the explicit `Membership` instance.

**Where the coercion DOES fire (the bulk of consumer sites).** Dot notation (`cn.slots.fold`, `cn.slots.size`, `cn.slots.get?`, `cn.slots.capacity`, `cn.slots.toList`, `ntfn.waitingThreads.length`, `ntfn.waitingThreads.head?`, `ntfn.waitingThreads.isEmpty`, `ntfn.waitingThreads.contains`, `tid ∈ ntfn.waitingThreads.val` membership) — all keep working unchanged because Lean's dot-notation resolution: (1) tries the structure's own namespace (`UniqueSlotMap.fold`, `NoDupList.length`); (2) if that fails, applies `CoeHead` and retries on the underlying type. To keep elaboration fast and unambiguous, the plan adds **explicit `@[inline] def` wrappers** for the most common methods inside the structure's namespace (see R4.A.1 / R4.C.1 sketches) so Lean never has to consult coercion for the hot path.

**Pattern-match migration accounting.** The waitingThreads surface report counts 5 `match … waitingThreads with` sites; for slots, no direct match-on-`slots` sites were observed (consumer access is via `.fold`, `.get?`, `.toList`). Each `match`-on-waitingThreads site is enumerated by file:line in §R4.C.3 below and migrated to either `tail?` (1 operational site each in `Endpoint.lean` and `FrozenOps/Operations.lean`) or `.val` (3 proof sites in `NotificationPreservation/{Wait,Signal}.lean` and `InformationFlow/Invariant/Helpers.lean`).

**Why `consWithGuard?` (runtime-checked) over signature threading at `notificationWait`.** The hard case for R4.C is the cons site at `IPC/Operations/Endpoint.lean:726/1134`, which prepends a waiter onto `ntfn.waitingThreads`. Three candidate APIs:
1. **Proof-carrying `consWithGuard (h : x ∉ l.val)`.** Used at proof sites (preservation theorems) where the bridge `not_mem_waitingThreads_of_ipcState_ne` (`IPC/Invariant/Defs.lean:567`) is in scope.
2. **Runtime-checked `consWithGuard?` returning `Option (NoDupList α)`.** Used at the operational site. When membership is detected at runtime, returns `none`, which the caller maps to `.error .alreadyWaiting`. This **subsumes** the line-723 runtime guard: the typed smart constructor IS the duplicate guard.
3. **Thread `notificationWaiterConsistent` through `notificationWait`'s signature.** Rejected: pollutes the public Kernel-monad surface, breaks every dispatch wire site, conflates state-level invariants with per-call obligations.

**The plan offers both (1) and (2).** The bridge theorem `notificationWait_runtime_check_implied_by_nodup` (already landed at `IPC/Invariant/QueueNoDup.lean:691` from the in-flight R4.C structural-witness step) becomes the equivalence proof linking the two paths under `notificationWaiterConsistent`. Its name and citation survive R4.C's full type-level promotion unchanged, so the discharge index reachability check `#check @SeLe4n.Kernel.notificationWait_runtime_check_implied_by_nodup` keeps elaborating across the workstream.

## Track A — `UniqueSlotMap` (7 sub-PRs, ~890 LoC total)

### R4.A.1 — Introduce `UniqueSlotMap` type, smart constructors, preservation lemmas

**Scope:** ~250 LoC, all-additive, no existing files modified.

**Files:**
- `SeLe4n/Model/Object/UniqueSlotMap.lean` (new)
- `SeLe4n.lean` (one new import line)

**Full API sketch (the file is ~250 LoC complete):**

```lean
-- SPDX-License-Identifier: GPL-3.0-or-later
import SeLe4n.Kernel.RobinHood.Bridge

namespace SeLe4n
open SeLe4n.Kernel.RobinHood

/-- WS-RC R4.A (DEEP-MODEL-01): structural smart-constructor wrapper around
    `RHTable Slot Capability` carrying the `invExtK` no-duplicate-keys
    invariant at construction time. Every smart constructor in this namespace
    discharges the obligation via the corresponding `RHTable._preserves_invExtK`
    lemma, so the structural property cannot be regressed by future refactors
    without breaking elaboration. -/
structure UniqueSlotMap where
  table : RHTable SeLe4n.Slot Capability
  hWF   : table.invExtK

namespace UniqueSlotMap

/-! ## Smart constructors (mutating) -/

@[inline] def empty : UniqueSlotMap :=
  ⟨RHTable.empty 16 (by omega), RHTable.empty_invExtK 16 (by omega)⟩

@[inline] def insert (u : UniqueSlotMap) (s : SeLe4n.Slot) (c : Capability) :
    UniqueSlotMap :=
  ⟨u.table.insert s c, u.table.insert_preserves_invExtK s c u.hWF⟩

@[inline] def erase (u : UniqueSlotMap) (s : SeLe4n.Slot) : UniqueSlotMap :=
  ⟨u.table.erase s, u.table.erase_preserves_invExtK s u.hWF⟩

@[inline] def filter (u : UniqueSlotMap)
    (f : SeLe4n.Slot → Capability → Bool) : UniqueSlotMap :=
  ⟨u.table.filter f, u.table.filter_preserves_invExtK f u.hWF⟩

/-- Build a `UniqueSlotMap` from a list of (slot, cap) pairs by folding `insert`.
    Duplicates in the input list are resolved last-wins (matching the underlying
    `RHTable.insert` semantics). The `invExtK` invariant is preserved at every
    fold step via `insert_preserves_invExtK`. -/
@[inline] def ofListWF (xs : List (SeLe4n.Slot × Capability)) : UniqueSlotMap :=
  xs.foldl (fun acc kv => acc.insert kv.1 kv.2) empty

/-! ## Read-only accessors (explicit `@[inline]` wrappers for the hot path).
    These exist to keep dot-notation elaboration fast: Lean resolves the
    method via this namespace before consulting `CoeHead`. Without them,
    `cn.slots.fold` triggers a `CoeHead` lookup at every call site, which
    measurably slows elaboration on this codebase. -/

@[inline] def get? (u : UniqueSlotMap) (s : SeLe4n.Slot) : Option Capability :=
  u.table.get? s

@[inline] def size (u : UniqueSlotMap) : Nat := u.table.size

@[inline] def capacity (u : UniqueSlotMap) : Nat := u.table.capacity

@[inline] def fold {β : Type} (u : UniqueSlotMap) (init : β)
    (f : β → SeLe4n.Slot → Capability → β) : β :=
  u.table.fold init f

@[inline] def toList (u : UniqueSlotMap) :
    List (SeLe4n.Slot × Capability) := u.table.toList

@[inline] def contains (u : UniqueSlotMap) (s : SeLe4n.Slot) : Bool :=
  (u.get? s).isSome

/-! ## Coercions and instances -/

instance : CoeHead UniqueSlotMap (RHTable SeLe4n.Slot Capability) where
  coe := UniqueSlotMap.table

instance : Repr UniqueSlotMap where
  reprPrec u n := reprPrec u.table n

/-- `cn.slots[s]?` notation: Lean resolves this via `GetElem?` (the `?`
    variant returning `Option`). -/
instance : GetElem? UniqueSlotMap SeLe4n.Slot Capability (fun _ _ => True) where
  getElem  u s _ := (u.table.get? s).get!
  getElem? u s   := u.table.get? s

/-! ## Forwarding lemmas (proof-surface compatibility) -/

@[simp] theorem table_empty : (empty : UniqueSlotMap).table = RHTable.empty 16 (by omega) := rfl

@[simp] theorem table_insert (u : UniqueSlotMap) (s : SeLe4n.Slot) (c : Capability) :
    (u.insert s c).table = u.table.insert s c := rfl

@[simp] theorem table_erase (u : UniqueSlotMap) (s : SeLe4n.Slot) :
    (u.erase s).table = u.table.erase s := rfl

@[simp] theorem table_filter (u : UniqueSlotMap)
    (f : SeLe4n.Slot → Capability → Bool) :
    (u.filter f).table = u.table.filter f := rfl

end UniqueSlotMap
end SeLe4n
```

**Why every wrapper is `@[inline]`.** The wrapper functions are zero-cost projections; marking them `@[inline]` ensures Lean's elaborator and the final compiled code see straight through to the underlying `RHTable` call. Without `@[inline]`, the indirection costs a function call per access — measurable on hot paths like `notificationSignal`'s `cn.slots.fold` traversal.

**Why the four `@[simp]` forwarding lemmas.** Existing proofs in the kernel (e.g. `Capability/Invariant/Authority.lean`) already invoke `simp` over expressions involving `cn.slots.insert` etc. Without these forwarding lemmas, those `simp` calls would fail because the smart constructor wraps the `RHTable` operation in the `UniqueSlotMap` projection. The four `@[simp]` lemmas re-establish the rewrite path: `(u.insert s c).table` reduces to the underlying `u.table.insert s c`, and any downstream `RHTable` lemma keyed on `.insert` continues to fire.

**Reused infrastructure:**
- `RHTable.empty_invExtK` (`Bridge.lean:999`) — empty-discharge.
- `RHTable.insert_preserves_invExtK` (`Bridge.lean:1039`) — cons-discharge.
- `RHTable.erase_preserves_invExtK` (`Bridge.lean:1018`) — erase-discharge.
- `RHTable.filter_preserves_invExtK` (`Bridge.lean:1083`) — filter-discharge.

**If `RHTable.ofList_invExtK` is missing:** the `ofListWF` definition above sidesteps that gap via a fold over `insert`. No new lemma is required.

**Verification:** `lake build SeLe4n.Model.Object.UniqueSlotMap` and `lake build SeLe4n`.

**Failure mode:** `deriving Repr` over a Prop field fails. **Mitigation:** explicit `instance : Repr` shown above (1 line).

---

### R4.A.2 — Switch `CNode.slots` field type; rewire builders and core methods

**Scope:** ~180 LoC, mostly mechanical.

**Files:**
- `SeLe4n/Model/Object/Types.lean` (line ~904: change `slots : RHTable SeLe4n.Slot Capability` → `slots : UniqueSlotMap`)
- `SeLe4n/Model/Object/Structures.lean` (line 530 `CNode.empty`: use `UniqueSlotMap.empty`; line 536 `CNode.mk'`: take `UniqueSlotMap` parameter; lines 603/607: `CNode.insert` and `CNode.remove` route through `UniqueSlotMap.insert/erase`)

**Why this is buildable end-to-end.** Every read-only consumer (`cn.slots.fold`, `cn.slots.get?`, `cn.slots.size`, `cn.slots.capacity`, `cn.slots.toList`, `cn.slots[s]?`) resolves through `CoeHead` + the `GetElem` instance to the underlying `RHTable`. The four `{ cn with slots := … }` mutation sites are the only elaboration risks; under the new typing the RHS becomes a `UniqueSlotMap` value which is exactly what the smart constructors return.

**Mutation site treatment:**
- `Builder.lean:287` — `cn.slots.insert slot cap` now returns `UniqueSlotMap` directly; the proof at line 291 (`RHTable.insert_preserves_invExtK …`) becomes vacuous because `invExtK` is structural. **Replace** the body of the discharge with a comment `-- WS-RC R4.A: invExtK now carried by UniqueSlotMap.insert; obligation discharged structurally.` Do **not** delete the surrounding theorem statement, since other callers may depend on its name; let R4.A.6 retire it.
- `Projection.lean:207` — `cn.slots.filter (…)` now returns `UniqueSlotMap`; proof obligation discharged inside `UniqueSlotMap.filter`. No caller-side change.
- `FrozenOps/Operations.lean:540, 554` — see R4.A.4. Likely on a different `FrozenCNode` structure entirely.

**Verification:**
- `lake build SeLe4n.Model.Object.Types`
- `lake build SeLe4n.Model.Object.Structures`
- `lake build SeLe4n.Model.Builder`
- `lake build SeLe4n.Kernel.InformationFlow.Projection`
- The custom `instance : BEq CNode` at `Structures.lean:954` uses `a.slots.fold` and `a.slots.size` — both lift via `CoeHead`. Verify by elaboration.

**Failure mode:** `cn.slots[s]?` notation breaks because `GetElem` is not defined on `UniqueSlotMap`. **Mitigation:** the explicit `GetElem` instance shown in R4.A.1 (~5 lines).

---

### R4.A.3 — Migrate test fixtures (~10 sites)

**Scope:** ~80 LoC, mechanical.

**Files (literal `slots := …` syntax in tests):**
- `tests/RobinHoodSuite.lean:251` — `CNode.mk' 4 0 0 2 (RHTable.ofList [...])` → wrap in `UniqueSlotMap.ofListWF`
- `tests/Ak8CoverageSuite.lean:137-139` — replace `RHTable.empty 16` and chained `.insert` calls with `UniqueSlotMap.empty.insert ...`
- `tests/NegativeStateSuite.lean:1372` — same
- `tests/OperationChainSuite.lean:336` — `slots := RHTable.empty 16` → `slots := UniqueSlotMap.empty`
- `tests/InformationFlowSuite.lean:565-566` — two `RHTable.ofList` literals → `UniqueSlotMap.ofListWF`
- `tests/FrozenStateSuite.lean:116-129` — chained `.insert` over `RHTable.empty 16` → over `UniqueSlotMap.empty`
- `SeLe4n/Testing/MainTraceHarness.lean:3005` — full literal with `RHTable.ofList cnodeSlots`
- `SeLe4n/Testing/StateBuilder.lean:153` — capacity check on `cn.slots.capacity` and `.size` (both lift via `CoeHead`; no migration unless explicit `RHTable` typing is exposed)

**Migration recipe.** Cannot use `:= by decide` — RHS is constructive (a populated map value), not a proposition. Must be explicit smart-constructor calls. Replace at each site.

**Verification:** full `lake build SeLe4n` + `lake env lean --run tests/<each>.lean` for each touched suite.

**Failure mode:** Over-migration into `FrozenStateSuite`'s `freezeMap` calls (which are `FrozenMap`-typed, not `CNode`-typed). **Mitigation:** grep precisely for `slots :=` literal occurrences before migrating.

---

### R4.A.4 — Rewire `FrozenOps` mutation sites (or collapse into A2 if FrozenCNode is unrelated)

**Scope:** 0–60 LoC depending on FrozenCNode structure.

**Files:**
- `SeLe4n/Kernel/FrozenOps/Operations.lean:540-541, 554-555`

**Decision tree.**
- (a) If `FrozenCNode.slots : FrozenMap …` (a *frozen* reflection of `CNode.slots`) — **this sub-PR is a no-op**, FrozenCNode operates on a different type. Verify by reading `SeLe4n/Model/FrozenState.lean`. If confirmed, **collapse R4.A.4 into the R4.A.2 verification step** (just confirm `lake build SeLe4n.Kernel.FrozenOps.Operations` still passes).
- (b) If `FrozenCNode.slots` is the same `RHTable` (or now `UniqueSlotMap`) — rewire each `let slots' := … ; { cn with slots := slots' }` to compute via `UniqueSlotMap.{insert,erase}` so `slots' : UniqueSlotMap` flows naturally.

**Verification:** `lake build SeLe4n.Kernel.FrozenOps.Operations` + `lake env lean --run tests/FrozenOpsSuite.lean`.

---

### R4.A.5 — Deprecate `cspaceSlotUnique` to `True` (state-level invariant becomes trivial)

**Scope:** ~80 LoC, deprecation-only.

**Files:**
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean:27` — definition site
- `SeLe4n/Kernel/Capability/Invariant/Authority.lean` — preservation theorems become trivial
- `SeLe4n/Kernel/Capability/Invariant/Preservation/*.lean` — all `_preserves_cspaceSlotUnique` proofs collapse to `cspaceSlotUnique_trivial _`
- `SeLe4n/Testing/InvariantChecks.lean` — runtime check uses the alias trivially

**Strategy.**
```lean
@[deprecated "WS-RC R4.A: cspaceSlotUnique is now structural via UniqueSlotMap.hWF. \
This alias is retained for downstream callers and removed in R4.A.6's bundle cleanup."]
def cspaceSlotUnique (_ : SystemState) : Prop := True

theorem cspaceSlotUnique_trivial (st : SystemState) : cspaceSlotUnique st := trivial
```
Every `_preserves_cspaceSlotUnique` theorem body collapses to `cspaceSlotUnique_trivial st'`. **No bundle changes** — those are deferred to R4.A.6.

**Why this PR is small.** It changes one definition and the proof bodies of its preservation chain. No bundle changes, no caller-site signature changes — those are deferred to R4.A.6.

**Verification:**
- `lake build SeLe4n.Kernel.Capability.Invariant.Defs`
- full `lake build SeLe4n`
- `./scripts/test_smoke.sh`

**Failure mode:** A downstream proof body destructures the now-trivial `hUnique` hypothesis (`obtain ⟨hU, …⟩ := hUnique`). **Mitigation:** locally rewrite each `obtain ⟨…⟩ := hUnique` to `obtain _ := hUnique` and supply `cspaceSlotUnique_trivial st'`. Defer caller-side cleanup to R4.A.6.

---

### R4.A.6 — Bundle cleanup: remove `cspaceSlotUnique` from `capabilityInvariantBundle`

**Scope:** ~150 LoC.

**Files:**
- `SeLe4n/Kernel/Capability/Invariant/Defs.lean` — remove `cspaceSlotUnique` conjunct from `capabilityInvariantBundle` (line 179) and `capabilityInvariantBundleWithMintCompleteness` (~line 280) and any other bundle that includes it
- Every `_preserves_capabilityInvariantBundle` theorem (multiple in `Preservation/*.lean`) — drop the `cspaceSlotUnique` slot from the proof body's tuple construction
- Every caller of `_preserves_capabilityInvariantBundle` — drop the `cspaceSlotUnique` extraction (typically the first `.1` of an `rcases` destructure)
- `SeLe4n/Kernel/CrossSubsystem.lean` — invariant bundle composition site, drop the conjunct
- `SeLe4n/Testing/InvariantChecks.lean` — runtime check, drop the assertion

**Strategy: 4 in-PR commits to keep every intermediate state buildable.**

1. **Commit 1 — drop conjunct from bundle definition.** Update `capabilityInvariantBundle` to no longer include `cspaceSlotUnique`. Every theorem `… : capabilityInvariantBundle st` now needs to construct one fewer tuple slot.
2. **Commit 2 — update `_preserves_capabilityInvariantBundle` bodies.** Remove the `cspaceSlotUnique` slot from each proof construction. Roughly ~10 theorems across `Preservation/*.lean`.
3. **Commit 3 — update callers.** Every site that does `obtain ⟨hUnique, hSound, hBnd, …⟩ := hBundle` becomes `obtain ⟨hSound, hBnd, …⟩ := hBundle`. Roughly ~30 sites.
4. **Commit 4 — final delete.** Delete the `cspaceSlotUnique` definition and the `cspaceSlotUnique_trivial` helper from `Defs.lean`.

**Why split into 4 in-PR commits.** Each commit is `lake build`-green end-to-end (mandatory per CLAUDE.md). A single squashed commit risks an intermediate non-buildable state; the staged approach lets the pre-commit hook gate every step.

**Verification:** after each in-PR commit, `lake build SeLe4n`. After final commit: `./scripts/test_full.sh`.

**Failure mode:** an `rcases` destructure may be deeply nested across multiple files. **Mitigation:** use `rg 'cspaceSlotUnique'` after each commit to find remaining sites; the pre-commit hook surfaces any `lake build` regressions.

---

### R4.A.7 — Witness theorem, discharge index, marker theorem (workstream close)

**Scope:** ~50 LoC, all-additive.

**Files:**
- `SeLe4n/Model/Object/UniqueSlotMap.lean` — append the discharge-index witness theorem:
  ```lean
  /-- WS-RC R4.A / DEEP-MODEL-01: every `UniqueSlotMap` has unique keys
      structurally; the witness theorem codifies the §3.D D.1 closure. -/
  theorem UniqueSlotMap.keys_unique (u : UniqueSlotMap) : u.table.invExtK := u.hWF
  ```
- `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` — populate §3.D row D.1
- `SeLe4n/Kernel/CrossSubsystem.lean` — append the marker theorem:
  ```lean
  /-- WS-RC R4.A landing: cspaceSlotUnique state-level invariant promoted to
      structural via UniqueSlotMap.hWF. Marker theorem for the discharge-index
      reachability gate (`#check`-able by future audits). -/
  theorem cspaceSlotUnique_promoted_to_structural : True := trivial
  ```
- `CHANGELOG.md` — add a v0.31.0 line for "WS-RC R4.A: CNode.slots type-level uniqueness via UniqueSlotMap"
- `docs/WORKSTREAM_HISTORY.md` — append the R4.A closure summary

**Verification:** full `lake build SeLe4n` + `./scripts/test_full.sh` + `bash scripts/check_website_links.sh`.

## Track C — `NoDupList ThreadId` (8 sub-PRs, ~970 LoC total)

### R4.C.1 — Introduce `NoDupList`, smart constructors, `consWithGuard` and `consWithGuard?` APIs

**Scope:** ~200 LoC, all-additive new file.

**Files:**
- `SeLe4n/Model/Object/NoDupList.lean` (new)

**Sketch:**
```lean
namespace SeLe4n

/-- WS-RC R4.C (DEEP-IPC-05; subsumes DEEP-IPC-01): structural smart-constructor
    wrapper around `List α` for `[DecidableEq α]` element types, carrying
    `Nodup` invariantly at construction time. Smart constructors discharge the
    obligation; the runtime-checked `consWithGuard?` constructor folds the
    runtime duplicate-guard responsibility into the type. -/
structure NoDupList (α : Type) [DecidableEq α] where
  val    : List α
  hNodup : val.Nodup

namespace NoDupList
variable {α : Type} [DecidableEq α]

@[inline] def empty : NoDupList α := ⟨[], List.nodup_nil⟩

/-- Proof-carrying cons. Used at proof sites under `notificationWaiterConsistent`,
    where `not_mem_waitingThreads_of_ipcState_ne` supplies `h`. -/
@[inline] def consWithGuard (x : α) (l : NoDupList α) (h : x ∉ l.val) :
    NoDupList α :=
  ⟨x :: l.val, List.nodup_cons.mpr ⟨h, l.hNodup⟩⟩

/-- Runtime-checked cons: returns `none` if the element is already present.
    This subsumes the line-723 runtime guard at `IPC/Operations/Endpoint.lean`. -/
@[inline] def consWithGuard? (x : α) (l : NoDupList α) : Option (NoDupList α) :=
  if h : x ∈ l.val then none
  else some ⟨x :: l.val, List.nodup_cons.mpr ⟨h, l.hNodup⟩⟩

/-- Pop the head; preserves Nodup unconditionally via `Nodup.of_cons`. -/
@[inline] def tail? (l : NoDupList α) : Option (α × NoDupList α) :=
  match h : l.val with
  | []          => none
  | x :: rest   =>
      some (x, ⟨rest, by have := l.hNodup; rw [h] at this; exact this.of_cons⟩)

/-- Filter; preserves Nodup unconditionally via `List.Nodup.filter`. -/
@[inline] def filter (l : NoDupList α) (p : α → Bool) : NoDupList α :=
  ⟨l.val.filter p, l.hNodup.filter p⟩

instance : CoeHead (NoDupList α) (List α) where coe := NoDupList.val
instance : Inhabited (NoDupList α) := ⟨empty⟩
instance : Membership α (NoDupList α) where mem x l := x ∈ l.val

instance : DecidableEq (NoDupList α) := fun a b =>
  if h : a.val = b.val
  then isTrue (by cases a; cases b; cases h; rfl)
  else isFalse (fun heq => by cases heq; exact h rfl)

instance : Repr (NoDupList α) where
  reprPrec l n := reprPrec l.val n

end NoDupList
end SeLe4n
```

**Reused infrastructure:**
- `List.nodup_nil` — empty discharge.
- `List.nodup_cons` — cons discharge as a biconditional.
- `List.Nodup.of_cons` — pop discharge.
- `List.Nodup.filter` — filter discharge.

**Why this answers the hard-case question.** The `notificationWait` cons site at `Endpoint.lean:726` uses `consWithGuard?`. The match-on-`none` path returns `.error .alreadyWaiting`; the match-on-`some wt'` path proceeds. The line-723 runtime guard is **subsumed** because the typed smart constructor IS the duplicate guard. Proof sites (preservation theorems) use `consWithGuard` with the bridge from `not_mem_waitingThreads_of_ipcState_ne`. The two paths are bridged by `notificationWait_runtime_check_implied_by_nodup` — already in tree at `IPC/Invariant/QueueNoDup.lean:691`.

**Verification:** `lake build SeLe4n.Model.Object.NoDupList`.

**Failure mode:** `List.Nodup.filter` / `List.Nodup.of_cons` may have name drift in Lean 4 v4.28.0 core (vs Mathlib). **Mitigation:** if missing, write local proofs in this file (~10 LoC each via list induction). No external dependency.

---

### R4.C.2 — Switch `Notification.waitingThreads` field type; manual `DecidableEq Notification`

**Scope:** ~150 LoC; this is the **canary** PR for the entire workstream because of the `DecidableEq` derivation chain.

**Files:**
- `SeLe4n/Model/Object/Types.lean`:
  - line ~884: `waitingThreads : List SeLe4n.ThreadId` → `waitingThreads : NoDupList SeLe4n.ThreadId`
  - line ~886: drop `deriving Repr, DecidableEq` and replace with `deriving Repr` plus a manual `DecidableEq Notification` instance immediately after the structure
  - the manual instance must precede the `KernelObject` inductive declaration (line 2566+) so its `deriving DecidableEq` (if present) or the manual `BEq KernelObject` instance (line 2578) can find `Notification` equality

**Manual `DecidableEq Notification` (complete, verified):**

```lean
-- Sequence the three field-wise decidable equalities.
-- Field order matches the structure declaration: state, waitingThreads, pendingBadge.
-- We rely on:
--   (a) DecidableEq NotificationState  -- inductive at Types.lean:840
--   (b) DecidableEq (NoDupList ThreadId) -- from R4.C.1's instance
--   (c) DecidableEq (Option Badge)      -- already in tree
-- The `isTrue` body uses `Notification.mk.injEq` (auto-generated by `structure`)
-- to reduce structural equality to field-wise equality, then closes via
-- the three field equalities.

instance : DecidableEq Notification := fun a b =>
  match decEq a.state b.state with
  | isFalse hs => isFalse fun h => hs (h ▸ rfl)
  | isTrue  hs =>
    match decEq a.waitingThreads b.waitingThreads with
    | isFalse hw => isFalse fun h => hw (h ▸ rfl)
    | isTrue  hw =>
      match decEq a.pendingBadge b.pendingBadge with
      | isFalse hp => isFalse fun h => hp (h ▸ rfl)
      | isTrue  hp =>
        isTrue (by
          -- Reduce structural equality to field-wise equality
          rcases a with ⟨sa, wa, pa⟩
          rcases b with ⟨sb, wb, pb⟩
          -- The destructured field hypotheses now refer to the projections
          subst hs; subst hp
          cases hw   -- discharges waitingThreads equality (NoDupList structural)
          rfl)
```

**Why `match decEq … with` instead of nested `if h : … = … then`.**
1. `match` pattern-binds the `Decidable` evidence (`isFalse hs` or `isTrue hs`) directly, avoiding the need for `decide_eq_…` lemmas.
2. The `isFalse` arm produces a closed-form proof `fun h => hs (h ▸ rfl)`: given `h : a = b`, transport along `h` reduces `a.state = b.state` to `a.state = a.state` (a definitionally true `rfl`), and `hs` rejects this. This is the standard Lean 4 pattern for piecewise `DecidableEq`.
3. The terminal `isTrue` arm uses tactic mode only at the very end, so most of the proof is term-mode and elaborates fast.

**Why the `cases hw` (not `subst hw`) in the final `isTrue`.** After `subst hs; subst hp`, the remaining goal is `(⟨sa, wa, pa⟩ : Notification) = ⟨sa, wb, pa⟩` (only `wa` differs from `wb`). The hypothesis `hw : wa = wb` is between `NoDupList` values; `subst hw` would fail because `wa` and `wb` may not be free variables (they could be projections from the original `a` and `b`). `cases hw` deconstructs the equality into reflexivity, which then resolves via `rfl`.

**Required prerequisite: `DecidableEq (NoDupList ThreadId)` from R4.C.1.** The instance there:
```lean
instance [DecidableEq α] : DecidableEq (NoDupList α) := fun a b =>
  match decEq a.val b.val with
  | isTrue  h => isTrue (by cases a; cases b; cases h; rfl)
  | isFalse h => isFalse fun heq => h (heq ▸ rfl)
```
relies on proof irrelevance for the `hNodup` field: once `a.val = b.val`, the proof fields are propositionally equal automatically (Lean 4's `Prop` types are subsingletons), so `cases h; rfl` closes the goal. This is a standard pattern; it elaborates in <100ms on a populated `Notification` literal.

**Companion `BEq Notification` instance (defensive — see failure-mode register).** Lean's `decide_eq_iff` machinery should give `BEq` from `DecidableEq` automatically, but if `KernelObject.beq` (`Structures.lean:2578`) elaborates against a missing `BEq Notification`, add immediately after the manual `DecidableEq`:
```lean
instance : BEq Notification where
  beq a b := decide (a = b)
```
This makes the `BEq` derivation explicit and bypasses any `Decidable`-search ambiguity.

**`KernelObject.beq` impact** (`Structures.lean:2578`): the `notification a, notification b => a == b` arm uses `Notification`'s `BEq`. Since `DecidableEq` implies `BEq`, the manual `DecidableEq` provides a `BEq Notification` instance via the standard derivation. If it doesn't, add a thin `instance : BEq Notification where beq a b := decide (a = b)` immediately after the manual `DecidableEq`.

**Verification:**
- `lake build SeLe4n.Model.Object.Types` (the canary)
- A unit test in this PR (e.g. `tests/ModelIntegritySuite.lean`) exercising `decide (n1 = n2)` on two literal `Notification` values — one equal pair, one differing-by-`waitingThreads`, one differing-by-`state`, one differing-by-`pendingBadge`. This is the gate that proves the manual instance is correct.

**Failure mode:** the manual `DecidableEq` is the highest-risk piece in the entire workstream. If wrong, it can produce false positives (claiming inequality when equal) which are silent — the kernel would not crash but proofs would loop or miscompare. **Mitigation:** the unit-test gate above, with positive **and** negative cases.

---

### R4.C.3 — Rewire **operational** mutation sites in `Endpoint.lean` and `Cleanup.lean`

**Scope:** ~120 LoC.

**Files (operational only — proof-side migration deferred to R4.C.4):**
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean`
- `SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean`
- `SeLe4n/Kernel/FrozenOps/Operations.lean` (FrozenOps `notificationSignal` variant at line 222)

**Site-by-site rewiring:**

**Endpoint.lean:711, 1061, 1111** — `waitingThreads := []`. Becomes `waitingThreads := NoDupList.empty`. Trivial.

**Endpoint.lean:726** (the line-723 guard subsumption — the hard case):
```lean
-- BEFORE: explicit ipcState guard at line 723 + cons at line 728
match lookupTcb st waiter with
| none => .error .objectNotFound
| some tcb =>
    if tcb.ipcState = .blockedOnNotification notificationId then
      .error .alreadyWaiting
    else
      let ntfn' : Notification := {
        state := .waiting
        waitingThreads := waiter :: ntfn.waitingThreads     -- raw List cons
        pendingBadge := none
      }
      …

-- AFTER: typed smart constructor folds both
match ntfn.waitingThreads.consWithGuard? waiter with
| none => .error .alreadyWaiting
| some wt' =>
    let ntfn' : Notification := {
      state := .waiting
      waitingThreads := wt'                                  -- NoDupList typed
      pendingBadge := none
    }
    …
```
The `lookupTcb` call may still be needed for downstream `storeTcbIpcState` operations; do not remove it. The runtime guard semantics are preserved: same error tag (`.alreadyWaiting`), same control flow.

**Endpoint.lean:1134** — same pattern as 726.

**Endpoint.lean:649** (signal pop):
```lean
-- BEFORE
match ntfn.waitingThreads with
| waiter :: rest =>
    let ntfn' : Notification := {
      state := if rest.isEmpty then .idle else .waiting
      waitingThreads := rest
      …

-- AFTER
match ntfn.waitingThreads.tail? with
| some (waiter, rest) =>
    let ntfn' : Notification := {
      state := if rest.val.isEmpty then .idle else .waiting
      waitingThreads := rest
      …
| none => …  -- corresponds to the `[]` arm of the original match
```

**Cleanup.lean:155** (filter):
```lean
-- BEFORE: notif.waitingThreads.filter (· != tid)
-- AFTER:  notif.waitingThreads.filter (· != tid)   -- type-changes from List to NoDupList
```
No source change needed — `NoDupList.filter` has the same surface signature as `List.filter`. The result type lifts.

**FrozenOps/Operations.lean:222** — this is the FrozenOps copy of `notificationSignal`'s pop. The shape is identical to `Endpoint.lean:649` and the migration is identical (`tail?`).

**Verification:**
- `lake build SeLe4n.Kernel.IPC.Operations.Endpoint`
- `lake build SeLe4n.Kernel.Lifecycle.Operations.Cleanup`
- `lake build SeLe4n.Kernel.FrozenOps.Operations`
- `lake env lean --run tests/NegativeStateSuite.lean` (the `notificationWait` alreadyWaiting path)
- `lake env lean --run tests/InformationFlowSuite.lean`

**Failure mode:** the operational rewire forces proof-site downstream files to rebuild against the new types — those proofs are NOT updated in this PR; some of them may have stale `match … with | x :: rest =>` shapes that fail to elaborate. **Mitigation:** the proof-side migration is the entire scope of R4.C.4 below. Land R4.C.3 only after R4.C.4 is staged on the same branch (or interleave: R4.C.3 commits the operational change, R4.C.4 commits the proof-side fix immediately after, and the merge happens as a stack).

**Stack ordering note.** R4.C.3 and R4.C.4 should be developed as a stack on the same feature branch and merged together if the proof-side files in R4.C.4 are required for the build to be green. Practically: R4.C.3 lands first if the proof-side files build green via mechanical type-coercion (likely, given the read-only access patterns); otherwise R4.C.4 must be merged in the same PR.

---

### R4.C.4 — Rewire **proof-side** mutation sites in `NotificationPreservation` and `StoreObjectFrame`

**Scope:** ~150 LoC.

**Files (proof sites only):**
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Wait.lean` — `notificationWait` preservation proofs
- `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` — `notificationSignal` preservation proofs
- `SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` — frame lemmas with record literals at lines 1053, 1102, 1127, 1224, 1266, 1288
- `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv/ReplyRecv.lean` — any `Notification` literal in proof contexts
- `SeLe4n/Kernel/InformationFlow/Invariant/Helpers.lean:810` — `match` site in observability proof
- `SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean:352, 354` — observability proof
- `SeLe4n/Kernel/InformationFlow/Invariant/Composition.lean:105` — observability composition

**Three migration patterns** (per the §`Headline architectural decisions` accounting):

1. **Record literals in proof context** (StoreObjectFrame.lean lines 1053, 1102, 1127, 1224, 1266, 1288):
   ```lean
   -- BEFORE
   (.notification { state := …, waitingThreads := rest, pendingBadge := … })
   -- AFTER (where `rest : List ThreadId` was destructured from the original Nodup list)
   (.notification { state := …, waitingThreads := ⟨rest, hRestNodup⟩, pendingBadge := … })
   -- where hRestNodup is constructed from the surrounding hypothesis hOldNodup via Nodup.of_cons
   ```
   For each such site, prepend a `have hRestNodup : rest.Nodup := …` line that derives the proof from the surrounding `hOldNodup`. Most cases: `:= hOldNodup.of_cons` (when `rest` is the tail of a cons) or `:= hOldNodup.filter _` (when `rest` is a filter result).

2. **`match … waitingThreads with | x :: rest =>` patterns in proof context** (NotificationPreservation/Signal.lean has multiple, Helpers.lean:810):
   ```lean
   -- BEFORE
   match ntfn.waitingThreads with
   | x :: rest => …
   | []        => …
   -- AFTER (proof-side, retain explicit destructuring on the underlying List)
   match h : ntfn.waitingThreads.val with
   | x :: rest => -- can use ntfn.waitingThreads.hNodup with the new equation `h`
                  -- to derive `rest.Nodup` via `(h ▸ ntfn.waitingThreads.hNodup).of_cons`
                  …
   | []        => …
   ```
   Use the `match h : … with` form (with explicit equation) so the surviving `hNodup` can be transported.

3. **`tid ∈ ntfn.waitingThreads` membership** (Composition.lean:105, Helpers.lean:798/846/848, Operations.lean:352/354):
   ```lean
   -- BEFORE
   tid ∈ ntfn.waitingThreads
   -- AFTER (via the NoDupList Membership instance from R4.C.1, which is definitionally tid ∈ ntfn.waitingThreads.val)
   tid ∈ ntfn.waitingThreads
   -- ↑ no source change required — the Membership instance lifts
   ```
   This is the easiest migration class. The `Membership α (NoDupList α)` instance from R4.C.1 is definitionally equal to `α ∈ NoDupList.val`, so source code keeps working.

**Verification:**
- `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation` (this is the canary; if it builds green, the proof migration is correct)
- `lake build SeLe4n.Kernel.IPC.Invariant.Structural.StoreObjectFrame`
- `lake build SeLe4n.Kernel.IPC.Invariant.CallReplyRecv`
- `lake build SeLe4n.Kernel.InformationFlow.Invariant`
- `./scripts/test_smoke.sh`

**Failure mode:** proof elaboration time grows >2x in `NotificationPreservation/Wait.lean` (1.5k+ LoC) because every record literal re-elaborates against the typed field. **Mitigation:** add `@[reducible]` to `NoDupList.val` and the `CoeHead` instance in R4.C.1 (cheap rebase). If still too slow, split proof bodies into named `private` lemmas to reduce per-block elaboration cost.

**Failure mode:** a `match … with` site in a proof context may have multiple branches that internally rebuild the `Notification` with a new `waitingThreads`. Each rebuild now requires a fresh `Nodup` proof. **Mitigation:** the surrounding `hUnique : uniqueWaiters st` (or its post-deprecation equivalent) provides the precondition; chain via `Nodup.of_cons` / `Nodup.filter` from the destructured equation.

---

### R4.C.5 — Migrate Notification test fixtures and `MainTraceHarness`

**Scope:** ~50 LoC.

**Files:**
- `SeLe4n/Testing/MainTraceHarness.lean:105, 1763, 2037, 3013` — every `waitingThreads := []` → `waitingThreads := NoDupList.empty`
- `tests/ModelIntegritySuite.lean`, `tests/InformationFlowSuite.lean`, etc., wherever `Notification` literals appear with `waitingThreads := …`
- `SeLe4n/Testing/InvariantChecks.lean:74-76` — `ntfn.waitingThreads.isEmpty` lifts via `CoeHead`; no migration needed unless the surrounding theorem typing forces it

**Migration recipes:**
- `waitingThreads := []` → `waitingThreads := NoDupList.empty`
- `waitingThreads := [t1, t2]` (no duplicates) → `waitingThreads := ⟨[t1, t2], by decide⟩` (this is the **only** place `:= by decide` works because `t1.val ≠ t2.val` is decidable on concrete numeric literals)

**Verification:**
- `lake build SeLe4n.Testing.MainTraceHarness`
- `./scripts/test_full.sh`

**Failure mode:** `by decide` timeout on long literal lists. **Mitigation:** none of the existing fixtures are long; if encountered, fall back to `by simp [List.Nodup]` or explicit cons-by-cons proof.

---

### R4.C.6 — Deprecate `uniqueWaiters` to `True` (state-level invariant becomes trivial)

**Scope:** ~80 LoC; parallel to R4.A.5 strategy.

**Files:**
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean:584` — deprecate `uniqueWaiters` to `True`:
  ```lean
  @[deprecated "WS-RC R4.C: uniqueWaiters is now structural via NoDupList.hNodup. \
  This alias is retained for downstream callers and removed in R4.C.7's bundle cleanup."]
  def uniqueWaiters (st : SystemState) : Prop := True

  theorem uniqueWaiters_trivial (st : SystemState) : uniqueWaiters st := trivial
  ```
- All `_preserves_uniqueWaiters` theorem bodies collapse to `uniqueWaiters_trivial st'` via the alias.

**Why this PR is small.** It changes one definition and the proof bodies of its preservation chain. No bundle changes, no caller-site signature changes — those are deferred to R4.C.7.

**Verification:**
- `lake build SeLe4n.Kernel.IPC.Invariant.Defs`
- full `lake build SeLe4n`
- `./scripts/test_smoke.sh`

**Failure mode:** A downstream proof body destructures `hUnique : uniqueWaiters st` (which is now `True`) and fails. **Mitigation:** locally rewrite each `obtain ⟨…⟩ := hUnique` to `obtain _ := hUnique` and use `uniqueWaiters_trivial`. The reorganisation is mechanical; defer caller-side cleanup to R4.C.7.

---

### R4.C.7 — Bundle cleanup: remove `uniqueWaiters` from `ipcInvariantFull` and downstream

**Scope:** ~150 LoC.

**Files:**
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean` — remove `uniqueWaiters` conjunct from `ipcInvariantFull` (line ~1250) and any other bundle that includes it
- `SeLe4n/Kernel/Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean:220` — `coreIpcInvariantBundle_to_uniqueWaiters` becomes vacuous; either delete the theorem or rewrite its body to `uniqueWaiters_trivial _`
- Every `_preserves_ipcInvariantFull` theorem — drop the `uniqueWaiters` clause from the proof body's tuple construction
- Every caller of `_preserves_ipcInvariantFull` — drop the `uniqueWaiters` extraction
- `SeLe4n/Kernel/Architecture/Invariant.lean:434` (`default_uniqueWaiters`) — delete or trivialise

**Strategy.** Use the in-tree `@[deprecated]` alias from R4.C.6 to drive a phased deletion:
1. First commit in this PR: drop `uniqueWaiters` from each bundle definition; bundle clients now do not extract this conjunct.
2. Second commit: update each `_preserves_ipcInvariantFull` to no longer prove this conjunct (the proof-tuple loses one slot).
3. Third commit: update each caller of `_preserves_ipcInvariantFull` to match the new tuple shape.
4. Final commit: delete the `uniqueWaiters` definition itself; delete the `uniqueWaiters_trivial` helper.

**Why split into 4 in-PR commits.** Each commit is `lake build`-green end-to-end (mandatory per CLAUDE.md). A single squashed commit risks an intermediate non-buildable state; the staged approach lets the pre-commit hook gate every step.

**Verification:**
- After each in-PR commit: full `lake build SeLe4n`
- After final commit: `./scripts/test_full.sh` and `bash scripts/check_website_links.sh`

**Failure mode:** the `coreIpcInvariantBundle_to_uniqueWaiters` theorem at `EndpointReplyAndLifecycle.lean:220` may have callers in `tests/` that elaborate against the old shape. **Mitigation:** grep `coreIpcInvariantBundle_to_uniqueWaiters` in tests/ — if hits, update them in the same PR.

---

### R4.C.8 — Witness theorem, discharge index, marker theorem (workstream close)

**Scope:** ~50 LoC, all-additive.

**Files:**
- `SeLe4n/Model/Object/NoDupList.lean` — append the canonical witness theorem:
  ```lean
  /-- WS-RC R4.C / DEEP-IPC-05: every `Notification` has Nodup waiters
      structurally; the witness theorem codifies the §3.D D.3 closure. -/
  theorem SeLe4n.notification_waiters_nodup (n : Notification) :
      n.waitingThreads.val.Nodup :=
    n.waitingThreads.hNodup
  ```
- `SeLe4n/Kernel/IPC/Invariant/QueueNoDup.lean:671` — strengthen the docstring of the existing `notification_waitingThreads_nodup_witness` to cite the discharge index entry now that R4.C has fully landed
- `docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md` — populate §3.D row D.3 + §3.E row E.1 (full rows in §`Discharge index entries` below)
- `SeLe4n/Kernel/CrossSubsystem.lean` — append the marker theorem:
  ```lean
  /-- WS-RC R4.C landing: uniqueWaiters state-level invariant promoted to
      structural via NoDupList.hNodup. Marker theorem for the discharge-index
      reachability gate (`#check`-able by future audits). -/
  theorem uniqueWaiters_promoted_to_structural : True := trivial
  ```
- `CHANGELOG.md` — add a v0.31.0 line for "WS-RC R4.C: Notification.waitingThreads type-level uniqueness via NoDupList ThreadId"
- `docs/WORKSTREAM_HISTORY.md` — append the R4.C closure summary

**Verification:** full `lake build SeLe4n` + `./scripts/test_full.sh` + `bash scripts/check_website_links.sh`.

**Failure mode:** the discharge-index file path may be renamed if the v0.31.0 cut moves it. **Mitigation:** verify `scripts/website_link_manifest.txt` is consistent with the path before merging; the Tier 0 hygiene gate enforces this.

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
| R4.C.7 | Deprecation churn breaks `coreIpcInvariantBundle_to_uniqueWaiters` (`Capability/Invariant/Preservation/EndpointReplyAndLifecycle.lean:220`) | The 4-commit in-PR cleanup explicitly handles this caller; trivial alias keeps build green between commits |
| R4.C.7 | A bundle includes `uniqueWaiters` as a non-final conjunct, breaking tuple-extraction in callers | Update bundle definition first (commit 1), then preservation theorems (commit 2), then callers (commit 3); pre-commit hook gates each |
| R4.C.8 | Marker theorem name conflict with R4.A.7 in `CrossSubsystem.lean` | Use distinct names: `cspaceSlotUnique_promoted_to_structural` and `uniqueWaiters_promoted_to_structural` |

## Discharge index entries (`docs/audits/AUDIT_v0.30.11_DISCHARGE_INDEX.md`)

The current placeholder rows in §3.D (lines 134, 136), §3.E (line 153), and §3.F (line 171) are populated by these full-shape rows when the workstream lands.

### §3.D — Type-level promotion entries

**D.1 — R4.A landing (DEEP-MODEL-01):**

| Field | Value |
|-------|-------|
| Theorem name | `SeLe4n.UniqueSlotMap.keys_unique` |
| File:Line | `SeLe4n/Model/Object/UniqueSlotMap.lean:<line>` |
| Promoted invariant | `cspaceSlotUnique` (formerly `Builder.lean:291` runtime obligation, now structural) |
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
| Subsumed finding | DEEP-IPC-01 (`notificationWait` runtime NoDup at `IPC/Operations/Endpoint.lean:723`) |
| Subsuming structural promotion | R4.C (§3.D D.3); the line-723 guard is replaced by `NoDupList.consWithGuard?`'s `none` return |
| Equivalence theorem | `SeLe4n.Kernel.notificationWait_runtime_check_implied_by_nodup` (already in tree at `IPC/Invariant/QueueNoDup.lean:691`; survives R4.C unchanged) |
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
- `/home/user/seLe4n/SeLe4n/Model/Object/Types.lean` — CNode field declaration (~line 904)
- `/home/user/seLe4n/SeLe4n/Model/Object/Structures.lean` — `CNode.empty`, `CNode.mk'`, `CNode.insert`, `CNode.remove`, `slotsUnique`, `BEq CNode` instance (~lines 530–960)
- `/home/user/seLe4n/SeLe4n/Kernel/RobinHood/Bridge.lean` — existing `invExtK` preservation lemmas (lines 980–1095)
- `/home/user/seLe4n/SeLe4n/Kernel/RobinHood/Set.lean` — `RHSet` precedent template (the closest in-tree shape match)
- `/home/user/seLe4n/SeLe4n/Model/Builder.lean` — proof discharge at line 287/291
- `/home/user/seLe4n/SeLe4n/Kernel/InformationFlow/Projection.lean` — filter site at line 207
- `/home/user/seLe4n/SeLe4n/Kernel/FrozenOps/Operations.lean` — verify FrozenCNode independence
- `/home/user/seLe4n/SeLe4n/Kernel/Capability/Invariant/Defs.lean` — `cspaceSlotUnique` definition (line 27) and bundle composition

**For R4.C:**
- `/home/user/seLe4n/SeLe4n/Model/Object/Types.lean` — Notification field declaration (~line 884) and `deriving DecidableEq` (line 886)
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Operations/Endpoint.lean` — `notificationWait` (line 703), `notificationSignal` (line 640), the line-723 runtime guard, the cons sites at 726 and 1134
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Invariant/Defs.lean` — `uniqueWaiters` (line 584), `notificationWaiterConsistent` (line 558), bridge theorem `not_mem_waitingThreads_of_ipcState_ne` (line 567)
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Invariant/QueueNoDup.lean` — existing `notification_waitingThreads_nodup_witness` and `notificationWait_runtime_check_implied_by_nodup` (the §3.E equivalence theorem; survives R4.C unchanged)
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Wait.lean` — preservation proofs that adapt mechanically
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/Signal.lean` — preservation proofs that adapt mechanically
- `/home/user/seLe4n/SeLe4n/Kernel/IPC/Invariant/Structural/StoreObjectFrame.lean` — frame-lemma record literals (lines 1053, 1102, 1127, 1224, 1266, 1288)
- `/home/user/seLe4n/SeLe4n/Kernel/Lifecycle/Operations/Cleanup.lean` — `removeFromAllNotificationWaitLists` filter site (line 155)
- `/home/user/seLe4n/SeLe4n/Testing/MainTraceHarness.lean` — fixture sites (lines 105, 1763, 2037, 3013)

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
6. `docs/WORKSTREAM_HISTORY.md` — record R4.A.1..A.6 and R4.C.1..C.5 landing
7. `CHANGELOG.md` — add a v0.31.0 line for "WS-RC R4.A: CNode.slots type-level uniqueness via UniqueSlotMap" and similar for R4.C
8. `docs/codebase_map.json` — regenerate via `python3 scripts/regenerate_codebase_map.py` (or whatever the existing script is)

The `CLAUDE.md` source-layout block must also gain entries:
- `SeLe4n/Model/Object/UniqueSlotMap.lean` — UniqueSlotMap smart-constructor wrapper around RHTable
- `SeLe4n/Model/Object/NoDupList.lean` — NoDupList smart-constructor wrapper around List

## Open questions for the implementer (resolve before R4.A.2 / R4.C.2)

1. **`RHTable.ofList_invExtK`** — does Lean's existing `Bridge.lean` define this lemma? If yes, `UniqueSlotMap.ofListWF` becomes a 2-line lift; if no, `ofListWF` uses the fold-over-`insert` pattern (still 2 lines but slower at compile time).
2. **`FrozenOps/Operations.lean:540, 554`** — is `FrozenCNode.slots` typed as `RHTable Slot Capability` (in which case R4.A.4 rewires it) or `FrozenMap …` (in which case R4.A.4 is a no-op)? Reading `SeLe4n/Model/FrozenState.lean` answers this — recommended action is to confirm in the R4.A.4 first commit.
3. **`KernelObject.beq` (line 2578)** — does dropping `deriving DecidableEq` on `Notification` cascade into a `BEq Notification` requirement on the manual-`BEq KernelObject` instance? Verify by reading the instance body — it does `a == b` on each variant; the `Notification` arm needs `BEq Notification`. The manual `DecidableEq` provides this via Lean's standard `BEq`-from-`DecidableEq` derivation, but if not, R4.C.2 adds an explicit `instance : BEq Notification` immediately after.
4. **Lean 4 v4.28.0 lemma names** — `List.Nodup.of_cons` vs `List.nodup_cons.mp` vs `List.Nodup.cons` — verify the canonical name; if absent, the inline list-induction proof is ~10 LoC.

These four questions can be answered by direct code reads at the start of R4.A.2 / R4.C.2 in ~10 minutes; deferring them to plan-execution time keeps the plan tractable.

## Total scope summary

| Track | Sub-PRs | Estimated LoC | Files touched | Risk class |
|-------|---------|---------------|---------------|------------|
| R4.A | 7 | ~890 | ~30 | Medium (mechanical mostly; FrozenOps decision and bundle cleanup are the judgment calls) |
| R4.C | 8 | ~970 | ~38 | High (manual `DecidableEq Notification` is the canary; pattern-match migration is the second-largest risk) |
| **Total** | **15** | **~1860** | **~55 (with overlap on Types.lean and CrossSubsystem.lean only)** | — |

The earlier 11-sub-PR estimate (in a prior draft of this plan) under-counted by collapsing the **bundle cleanup** work (now A.6 and C.7) into the deprecation step, and by collapsing the **proof-side rewire** into the operational rewire (now C.3 + C.4). The 15-sub-PR breakdown surfaces those as their own coherent slices, each ≤200 LoC, each with its own pre-commit gate.

This plan converts two state-level invariants — `cspaceSlotUnique` (proven preserved by every CSpace operation) and `uniqueWaiters` (proven preserved by every notification operation) — into structural type-level invariants. The conversion is **redundant for correctness** (the state-level invariants are already proven), but is a true *faithfulness* improvement: it makes the property impossible to violate by construction rather than provable-but-bypassable. The runtime guard at `Endpoint.lean:723` becomes structurally subsumed by the typed `consWithGuard?` smart constructor, and the discharge index gains three reachability-gated witness theorems that future audits can re-derive from a single `#check` per closure.

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
- [ ] **Documentation sync.** If theorems / invariants / source layout changed, the relevant `docs/` files (`README.md` metrics, `docs/spec/SELE4N_SPEC.md`, `docs/gitbook/*.md`, `CHANGELOG.md`, `docs/WORKSTREAM_HISTORY.md`) are updated in the same commit.
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
- [x] **Documentation sync.** R4.A.7 and R4.C.8 explicitly synchronise `README.md`, `docs/spec/SELE4N_SPEC.md`, `docs/DEVELOPMENT.md`, `docs/gitbook/12-proof-and-invariant-map.md`, `docs/CLAIM_EVIDENCE_INDEX.md`, `docs/WORKSTREAM_HISTORY.md`, `CHANGELOG.md`, and `docs/codebase_map.json` per CLAUDE.md "Documentation rules".
- [x] **Website-linked-path protection.** No file in `scripts/website_link_manifest.txt` is renamed or deleted by this plan. The new files (`SeLe4n/Model/Object/UniqueSlotMap.lean`, `SeLe4n/Model/Object/NoDupList.lean`) are additions; if the manifest contains them post-landing, that is a website-update concern (out of scope for this plan).
- [x] **Background-agent file-change protection.** This plan is sequential per implementer track; no background agent overlapping file edits are proposed.
- [x] **Vulnerability reporting.** This plan introduces no security-sensitive code; it strengthens an existing structural invariant. No CVE-class findings are produced. If implementation surfaces one (e.g., a `DecidableEq` mistake yielding a silent miscompare), the implementer follows CLAUDE.md's "Vulnerability reporting" mandate to halt and surface immediately.
- [x] **`lake build` default target inadequate per CLAUDE.md.** The verification matrix explicitly enumerates module-specific build targets so the new `UniqueSlotMap` and `NoDupList` modules are exercised even before they're imported by `Main.lean` or any test harness.
- [x] **Tier-0 hygiene at workstream close.** R4.A.7 and R4.C.8 both run `bash scripts/check_website_links.sh` (the Tier-0 hygiene gate) per the protocol.
- [x] **No deep `do`-chain nesting in new tests.** Per CLAUDE.md's clang `-fbracket-depth=256` guidance, any new test helpers in R4.A.3 / R4.C.5 stay ≤150 Lean lines via the thin-dispatcher pattern (the canonical example being `tests/NegativeStateSuite.lean`'s `runNegativeChecks`).
- [x] **Reading large files in chunks.** Implementers reading `Notification`-touching files (e.g., `SeLe4n/Kernel/IPC/Invariant/NotificationPreservation/{Wait,Signal}.lean`, ~850/688 LoC) per CLAUDE.md's "Reading large files" guidance must use `Read(file_path, offset, limit)` rather than reading the whole file.
- [x] **Writing large files in chunks.** New file `SeLe4n/Model/Object/UniqueSlotMap.lean` is ~250 LoC; per CLAUDE.md's "Writing and editing large files" rule, this is built incrementally (skeleton ≤100 LoC + Edit appends ≤80 LoC each) or via Bash heredoc.
