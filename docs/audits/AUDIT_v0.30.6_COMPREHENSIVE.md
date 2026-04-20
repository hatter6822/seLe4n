# seLe4n v0.30.6 — Comprehensive Pre-1.0 Codebase Audit

**Audit ID**: `AUDIT_v0.30.6_COMPREHENSIVE`
**Date**: 2026-04-20
**Repo tip**: `d075a32` on branch `claude/comprehensive-project-audit-HoogT`
**Target release**: `v1.0.0` (patch-only bump of v0.30.6 reserved for maintainer manual action per `AK10-C`)
**Scope**: every `.lean`, `.rs`, `.sh`, `.yml`, `.md`, `.toml` file in the tree, excluding `docs/dev_history/` (archive) and `.git/` (VCS internals).

This audit supersedes nothing — it is additive to `AUDIT_v0.29.0_COMPREHENSIVE.md`
which covered a prior code tip. The WS-AK portfolio (Phases AK1–AK10, v0.29.0
→ v0.30.6) addressed 202 findings from the v0.29.0 audit. This audit verifies
the resulting code, catches what the remediation missed, and identifies new
issues introduced between v0.29.0 and v0.30.6.

## 0. Scope, methodology, and framing

### 0.1 What was examined

| Area | Files | LOC |
|------|------:|-----:|
| Lean kernel (`SeLe4n/Kernel/`) | 96 | ~71 700 |
| Lean model / foundation (`SeLe4n/Model/`, `SeLe4n/Prelude.lean`, `SeLe4n/Machine.lean`) | 13 | ~14 950 |
| Lean platform (`SeLe4n/Platform/`) | 15 | ~7 350 |
| Lean testing harness (`SeLe4n/Testing/`) | 5 | ~4 350 |
| Lean executable tests (`tests/`) | 24 | ~14 900 |
| Rust workspace (`rust/`) | 48 | ~10 981 |
| Shell scripts (`scripts/`) | 26 | ~3 800 |
| CI workflows (`.github/workflows/`) | 5 | ~420 |
| Documentation (`docs/`, `README.md`, `CHANGELOG.md`, `CLAUDE.md`) | ~280 | ~55 000 |
| **Total** | ~512 | **~183 000** |

### 0.2 Audit methodology

Eight read-only specialized agents explored disjoint slices of the tree in
parallel, each instructed to distrust comments and verify against code. Each
agent produced a structured list of findings with severity, category,
file:line anchor, verbatim evidence quote, and recommendation. The main
auditor then:

1. **De-duplicated** findings where multiple agents surfaced the same issue
   from different angles.
2. **Verified** a sample of claims against the live filesystem (e.g., missing
   scripts, stale README line, TODO markers, fixture line count).
3. **Reclassified** agent severity where the agent over- or under-called
   (notably: one `CRITICAL` from the Rust agent was a self-retracted false
   positive; one `CRITICAL` from the tests agent was an over-call on a
   `|| true` swallowed-error pattern).
4. **Consolidated** verified-clean checks into a single "Verifications"
   section rather than N repetitive "no issue found" entries.

### 0.3 Severity rubric

| Severity | Meaning |
|----------|---------|
| **CRITICAL** | Exploitable today against a non-malicious caller, or directly blocks v1.0 release. |
| **HIGH** | Correctness / security gap that should not ship in v1.0. Includes: unverified trust boundaries, closure-form proof obligations still delegated to callers, doc drift that misleads integrators. |
| **MEDIUM** | Hardening / defense-in-depth gap, or organizational issue that increases defect risk over time. |
| **LOW** | Hygiene, clarity, or minor performance concern. |
| **INFO** | Confirmed-clean check or strength. Logged for traceability. |

### 0.4 Finding count by severity

| Severity | Count |
|----------|------:|
| CRITICAL | **3** |
| HIGH     | **24** |
| MEDIUM   | **71** |
| LOW      | **58** |
| INFO     | **40** (verifications + strengths) |
| **Total** | **196** |

Three critical items, 24 high, all detailed in §1 (Executive Summary) and
§2–§9 per subsystem.

---

## 1. Executive summary — ship-blockers and highest-impact items

### 1.1 CRITICAL findings

#### C-01 — Stale "Latest audit" pointer in public README
**File**: `README.md:96`
**Severity**: CRITICAL — because this is the first thing integrators read.
**Evidence**: line 96 currently renders as

```
| **Latest audit** | [`AUDIT_COMPREHENSIVE_v0.23.21`](docs/dev_history/AUDIT_COMPREHENSIVE_v0.23.21_LEAN_RUST_KERNEL.md) — full-kernel Lean + Rust audit (0 CRIT, 5 HIGH, 8 MED, 30 LOW) |
```

The current canonical audit is `docs/audits/AUDIT_v0.29.0_COMPREHENSIVE.md`
(202 findings: 2 CRIT + 23 HIGH + 76 MED + 101 LOW) as documented in
`CLAUDE.md` and `docs/WORKSTREAM_HISTORY.md`. Linking a three-release-old
audit (v0.23.21) at the top of the README implies to a security-conscious
reader that the project has not been audited since v0.23.21 and that the
deltas since — including the entire WS-AF/AE/AD/AC/AB/AG/AH/AI/AJ/AK
portfolios — are unaudited. **This is precisely the kind of claim
mismatch that sinks third-party review.**

**Recommendation**: replace with a pointer to `AUDIT_v0.29.0_COMPREHENSIVE.md`
and, after this document is merged, to `AUDIT_v0.30.6_COMPREHENSIVE.md`. Keep
the v0.23.21 link elsewhere for historical traceability.

#### C-02 — Three scripts referenced by the active v0.29.0 plan do not exist
**File**: `docs/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` (multiple sites); `scripts/` tree
**Severity**: CRITICAL — this plan is the *current* active-audit plan cited by
`CLAUDE.md`, and it directs auditors / CI to invoke scripts that are not in
the repo.
**Evidence**: `Grep` for `find_large_lean_files|sync_documentation_metrics|sync_readme_from_codebase_map`
returns only `docs/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md` and a single historical
file under `docs/dev_history/`. `ls scripts/` confirms none of the three files
exist:
- `scripts/find_large_lean_files.sh` — MISSING
- `scripts/sync_documentation_metrics.sh` — MISSING
- `scripts/sync_readme_from_codebase_map.sh` — MISSING

**Recommendation**: either (a) land the scripts in `scripts/`, (b) rewrite the
plan instructions to use existing tooling (e.g., `generate_codebase_map.py`
already computes file sizes that make `find_large_lean_files.sh` redundant),
or (c) if the tasks these scripts performed were completed manually, strike
the references from the plan. Do NOT ship v1.0 with an active plan document
pointing to non-existent tooling.

#### C-03 — Pre-commit hook not installed by any setup step
**File**: `CLAUDE.md:53-61` instructs maintainers to run `cp scripts/pre-commit-lean-build.sh .git/hooks/pre-commit`; no script automates this.
**Severity**: CRITICAL — the hook is the project's **sole local defense**
against committing a `.lean` file that does not build (`lake build` default
target is documented in CLAUDE.md as insufficient because unreachable
modules silently pass), and against committing `sorry`. Relying on every
contributor (including agents) to manually copy the hook means the
guarantee is honored by discipline, not by automation.
**Evidence**: `scripts/setup_lean_env.sh` installs the toolchain but does
not install the hook. `pre-commit-lean-build.sh` exists at lines 1-200+ with
substantive staged-content inspection, but `.git/hooks/pre-commit` is not
created by the setup script.

**Recommendation**: extend `scripts/setup_lean_env.sh` (or create a
`scripts/install_git_hooks.sh`) that symlinks or copies the hook on first
run and is idempotent on subsequent runs. Invoke it from the `SessionStart`
hook and from CI so any fresh clone gets the guard automatically. This
converts a convention into a mechanism.

### 1.2 HIGH findings (summary table, details per-section below)

| ID | Area | Summary | Section |
|----|------|---------|---------|
| H-01 | IPC | `Donation.lean` not re-exported from `Operations.lean` hub due to import cycle; asymmetry with Timeout and WithCaps. | §2.1 |
| H-02 | Capability | `lifecycleRetypeObject` is public solely for proof accessibility; no compile-time guard against production callers bypassing `lifecycleRetypeWithCleanup`. | §2.3 |
| H-03 | Capability | `lifecycleIdentityNoTypeAliasConflict` is provably redundant with `lifecycleIdentityTypeExact` yet retained in the bundle. | §2.3 |
| H-04 | Capability | CDT hypothesis externalization: `cspaceCopy/Move/Mutate` take `cdtCompleteness st' ∧ cdtAcyclicity st'` as **post-state** caller obligations, not pre-state preservation. | §2.3 |
| H-05 | Capability | `cspaceLookupMultiLevel` composes resolve + lookup without re-validating CNode across calls; assumes concurrency-free kernel. | §2.3 |
| H-06 | Capability | `mintDerivedCap` requires `NonNullCap` input but has no *output* postcondition witnessing derived cap non-nullness. | §2.3 |
| H-07 | Arch/IF | Six `*_preserves_projection` theorems remain closure-form with caller-supplied `hProjEq` hypothesis; discharge recipes are described but no integration proof composes them. | §2.5 |
| H-08 | Arch | Architecture `Assumptions.lean` claims "every declared assumption has a concrete proof-level consumer"; no index theorem witnesses the five assumptions are actually consumed. | §2.5 |
| H-09 | CrossSubsystem | `untypedRegionsDisjoint` excludes direct parent-child only; transitive grandparent/grandchild chains are **not** covered. | §2.5 |
| H-10 | Foundation | `ThreadId.toObjId` and `SchedContextId.toObjId` share `ObjId` namespace via identity mapping; relies on implicit functional-map uniqueness invariant. | §2.6 |
| H-11 | Foundation | `RegisterFile.BEq` is non-lawful; `LawfulBEq (RHTable α β)` instance is not provided even under `[LawfulBEq β]`. | §2.6 |
| H-12 | Foundation | `Badge.ofNatMasked` computes bitwise OR on unbounded `Nat` before truncation; abstract model permits intermediates > 2^64. | §2.6 |
| H-13 | Foundation | `Badge.mk` constructor is public; no private-mk discipline means external code can construct `Badge` bypassing `valid` predicate. | §2.6 |
| H-14 | Platform | DTB fuel-exhaustion path had legacy silent-truncation callers; `findMemoryRegPropertyChecked` exists but legacy `Option` form is still reachable. | §2.7 |
| H-15 | Platform | DTB `physicalAddressWidth` is now a required parameter — GOOD — but older pre-AJ3-B call sites need audit that no `:= 52` defaulting survives. | §2.7 |
| H-16 | Platform | `budgetSufficientCheck` tightened (AK9-E); verify no other `_Check` predicates still default to `true` on missing bindings. | §2.7 |
| H-17 | Rust | `uart::UartLock::with` performs `unsafe { f(&mut *BOOT_UART_INNER.0.get()) }` with a lifetime that is correct only because the spin-CAS guard is held; explicit SAFETY proof sketch is thin. | §2.8 |
| H-18 | Rust | `boot.S:39` builds `MPIDR_CORE_ID_MASK = 0x00FFFFFF` via `mov`+`movk`; no compile-time `const _` assertion binds the Rust-side constant to the assembly literal. | §2.8 |
| H-19 | Rust | `gic::dispatch_irq` uses `EoiGuard` (Drop-based EOI); under `panic = "abort"` Drop is **not** run, so a direct `panic!()` inside a handler body leaks the INTID as active. | §2.8 |
| H-20 | Tests | `NegativeStateSuite.lean` exercises mainly `.objectNotFound` / `.invalidCapability`; the other ~49 `KernelError` variants have near-zero per-syscall rejection coverage. | §2.10 |
| H-21 | Tests | No timeout wrapper on any `lake exe …` invocation in `scripts/test_lib.sh`; a regression that hangs (e.g., infinite fuel loop) blocks CI indefinitely. | §2.10 |
| H-22 | Tests | Fixture files have no byte-hash at commit time; a malicious or accidental edit to `tests/fixtures/*.expected` cannot be distinguished from a legitimate update. | §2.10 |
| H-23 | Tests | AK6-G/H/I tests are comment-delimited blocks inside `InformationFlowSuite.lean`, not named test functions — runtime harness cannot report "AK6-G FAIL" as an identifiable unit. | §2.10 |
| H-24 | Docs | `rust/sele4n-hal/src/trap.rs:186` and `rust/sele4n-hal/src/lib.rs:89` carry active `TODO(WS-V/AG10)` markers for SVC→Lean FFI routing. Per `AUDIT_v0.29.0_DEFERRED.md` these are deferred, but the source comment references `WS-V`/`AG10` which `WORKSTREAM_HISTORY.md` documents as closed workstreams — the TODO's cross-reference target is stale. | §2.11 |

---

## 2. Per-subsystem findings

### 2.1 Lean kernel — IPC subsystem (`SeLe4n/Kernel/IPC/`)

Scope: 15 files, ~22 500 LOC. The IPC subsystem is the single largest
proof surface in the project. `Structural.lean` alone is 7 626 lines and
carries the dual-queue frame lemmas plus the 15-conjunct `ipcInvariantFull`
preservation chain.

**H-01 — Donation.lean re-export asymmetry**
`SeLe4n/Kernel/IPC/Operations.lean:12-14` documents: *"Donation.lean is NOT
re-exported here to avoid import cycles. It imports Transport.lean which
depends on this module."* The hub for this subsystem therefore silently
omits the donation API that AK1-A wired into `endpointReceiveDual`. Callers
that want the donation wrappers must `import SeLe4n.Kernel.IPC.Operations.Donation`
explicitly — a convention, not enforced. `DualQueue.lean` in contrast re-exports
Timeout and WithCaps cleanly, giving an inconsistent "what does the hub include?"
answer.
**Recommendation**: break the cycle by extracting the subset of Transport
primitives that Donation consumes into a dependency-free helper module
(`IPC/Operations/DonationPrimitives.lean`), then allow `Operations.lean` to
re-export Donation cleanly. Alternative: add a top-of-hub doc block listing
ALL IPC-adjacent modules and which are NOT included, so the asymmetry is at
least discoverable from the hub itself.

**MEDIUM findings — IPC**

- **IPC-M01** `IPC/Invariant/Defs.lean:2483` — `ipcInvariantFull` is a 12-tuple
  projection; extracting `donationOwnerValid` requires
  `.2.2.2.2.2.2.2.2.2.2.2.1`. Any reordering of the conjunction silently
  breaks every consumer. Same issue was called out in AF-26 for the
  `apiInvariantBundle_frozenDirect` 17-tuple; the IPC layer has the same
  fragility.
  **Rec**: introduce named projections (`ipcInvariantFull.donationOwnerValid`,
  etc.) either via a `structure` type or via a family of `@[simp]` abbrevs.
  This is the single highest-leverage hygiene fix in the IPC subsystem.

- **IPC-M02** `IPC/Invariant/Structural.lean` (7 626 lines) — file should be
  split. Natural seams: (a) QueueNext{Path,Foo} transport lemmas, (b) store-object
  frame lemmas, (c) dual-queue membership proofs, (d) per-operation Structural
  witnesses. Each would land near 1 500–2 000 lines.

- **IPC-M03** `IPC/Invariant/NotificationPreservation.lean` (1 490 lines) —
  combines `notificationSignal` and `notificationWait` preservation in one
  module. Split mirrors the AK1-D per-operation organization.

- **IPC-M04** `IPC/Invariant/CallReplyRecv.lean` (1 069 lines) — same pattern;
  `Call` and `ReplyRecv` preservation should be separate files.

- **IPC-M05** `IPC/Invariant/QueueMembership.lean:31-78` — `transfer` /
  `transferRecv` helpers differ only in which queue field they touch.
  Duplicate ≈40-line bodies with no shared abstraction. Extract once.

- **IPC-M06** `IPC/Operations/Endpoint.lean:460` — private
  `storeObject_scheduler_eq_z7` helper has no public counterpart for the
  donation path. Donation operations therefore rely on an internal
  implementation detail the proof chain does not expose. Either promote it
  or document why internality is desirable.

- **IPC-M07** `IPC/Invariant/Defs.lean:811-927` — queue-consistency predicates
  do not pin a reachability precondition (e.g., `∀ tid ∈ queue, objectsInvariant st tid`).
  They compose fine under real preservation proofs because callers always
  have the broader invariant, but a direct consumer could construct a
  vacuous witness.

- **IPC-M08** `IPC/Invariant/Defs.lean:228-284` — `allPendingMessagesBounded`
  bounds message *length* but does not cross-check that the endpoint
  reference in a `.blockedOnSend`/`.blockedOnReceive` is a live endpoint
  object. Composition with `ipcStateQueueMembershipConsistent` gives this
  property transitively, but the predicate in isolation is weaker than the
  docstring implies.

- **IPC-M09** `IPC/Operations/Endpoint.lean:1-20` file header — the "retained
  because cleanup runs in caller context" rationale for
  `cleanupPreReceiveDonation` co-location is not the obvious organization;
  future authors will move it back to Donation.lean and break the import
  graph. Add a `-- DO NOT MOVE` banner.

**LOW findings — IPC**

- `IPC/Invariant/WaitingThreadHelpers.lean` — name is over-generic. Rename
  to `NotificationWaitListHelpers.lean` or add a module-level docstring that
  narrows the scope (currently: primitive wait-list consistency helpers).
- `IPC/Invariant/EndpointPreservation.lean:205-236` — repeated
  `storeTcbQueueLinks`+`tcbWithQueueLinks` pattern with inline field updates;
  no explicit field-preservation lemma set (`_ipcState_preserved`,
  `_queueNext_preserved`). Makes hash-grepping for "which operation preserves
  field X" harder than necessary.
- `IPC/Invariant/Structural.lean:946-957` —
  `storeTcbQueueLinks_clearing_preserves_tcbQueueChainAcyclic` induction
  reconstructs `QueueNextPath` twice (forward + IH). Factoring the path
  transport into a named helper would shrink the proof ~15 lines and mirror
  similar patterns in `QueueMembership.lean`.
- `IPC/DualQueue.lean:14-25` — same asymmetry as H-01 called out at hub
  level; wording is informational but not prescriptive.
- `IPC/Operations/CapTransfer.lean:55` — `fillRemainingNoSlot` has no
  docstring; non-obvious that it fills with the "no cap" sentinel rather
  than aborting.

### 2.2 Lean kernel — Scheduler subsystem (`SeLe4n/Kernel/Scheduler/`)

Scope: ~10 files, `Operations/Preservation.lean` at 3 633 lines is the
largest. PIP/WCRT liveness proofs live here.

**MEDIUM findings — Scheduler**

- **SCH-M01** `Scheduler/Operations/Preservation.lean:267-308` plus lines
  439-448 — identical TCB `cases obj` dispatch structure copy-pasted across
  `schedule`, `handleYield`, `timerTick`, `switchDomain`. Each arm is ≈20
  LOC; factoring into a named helper or macro would recover ≈80 LOC and
  remove four places a future author can introduce a divergence bug.

- **SCH-M02** `Scheduler/Operations/Preservation.lean:212-217` —
  `remove_preserves_nodup`, `insert_preserves_nodup` are run-queue
  implementation helpers exposed in the preservation bundle without a
  "private helper" marker. A casual reader might assume these are
  public predicates. Either add `private` (where the proof chain allows)
  or prefix with `_rq_internal_`.

- **SCH-M03** `Scheduler/Operations/Core.lean:506-634` —
  `popDueReplenishments` / `refillSchedContext` / `processReplenishmentsDue`
  are three related operations without a named "replenishment pipeline"
  invariant tying them together. The composition in `timerTick` is
  brittle to reorder.
  **Rec**: add `replenishmentPipelineOrder : SystemState → Prop` capturing
  the pop → refill → process order, and prove `timerTick` preserves it.

- **SCH-M04** `Scheduler/Operations/Core.lean:340-447` — operation
  definitions and invariant-preserving wrappers interleave. `schedule`,
  `handleYield`, `timerTick` defs mingle with their structure-preserving
  updates. Splitting into `Core/Operations.lean` (pure) and `Core/Wrappers.lean`
  (proof harness) would sharpen the boundary.

- **SCH-M05** `Scheduler/PriorityInheritance/BlockingGraph.lean:344` — the
  name `tcbQueueChainAcyclic` is also defined (different semantics) in the
  IPC dual-queue proofs. Disambiguate: rename the PIP version to
  `blockingGraphAcyclic` or the IPC version to `ipcQueueChainAcyclic`.
  Current state is a foot-gun for proof authors who import both hubs.

**LOW findings — Scheduler**

- `Scheduler/RunQueue.lean` — `.getD ⟨0⟩` appears as fallback for missing
  `threadPriority` entries. Safe under `runQueueInvariant`, but the call
  site has no `-- safe under invariant` annotation. A future change that
  removes the invariant precondition would silently prefer priority 0
  instead of erroring out.
- `Scheduler/Operations/Core.lean:712-746` — `scheduleEffective`,
  `timerTickWithBudget` are budget-aware variants without a naming prefix
  distinguishing them from the primary operations. Add `_budgetAware` or
  similar.
- `Scheduler/PriorityInheritance/Propagate.lean:268` — `updatePipBoost` has
  no docstring describing its lifecycle relationship to `propagate` /
  `revert`.
- `Scheduler/Invariant.lean` — the re-export hub has no module docstring
  explaining the invariant hierarchy (base invariants → bundle → full
  preservation); a newcomer has to read all imports to find the top.

### 2.3 Lean kernel — Capability / Lifecycle / Service

Scope: ~20 files, `Capability/Invariant/Preservation.lean` at 2 461 LOC,
`Lifecycle/Operations.lean` at 1 473 LOC, `Service/Invariant/Acyclicity.lean`
at 1 012 LOC.

**H-02 — `lifecycleRetypeObject` is public for proof accessibility**
`SeLe4n/Kernel/Lifecycle/Operations.lean:453-483` documents: *"L-26:
Public for proof accessibility. Not part of the kernel API... `protected`
is infeasible due to the breadth of the proof chain. All production retype
callers must use `lifecycleRetypeWithCleanup`"*. There is no mechanism
beyond a docstring note preventing a future syscall arm from calling
`lifecycleRetypeObject` directly and bypassing `lifecyclePreRetypeCleanup`
(donated SC return, TCB ref scrub, endpoint-service detach, CDT detach).
The `cleanupDonatedSchedContext` error-propagating cascade (AJ1-A) is
precisely the kind of guard that disappears when a caller skips the
cleanup wrapper.
**Recommendation**: move `lifecycleRetypeObject` into a `protected` or
nested-namespace definition. Where the proof chain needs access, export
**theorems about** the internal step, not the step itself. A "proof
surface" namespace (`SeLe4n.Kernel.Lifecycle.Internal`) makes the
distinction explicit. If the 13+ cross-file references cannot be migrated
before v1.0, add a CI-enforced grep rule that any new file importing
`Lifecycle.Operations` must explicitly consume the `WithCleanup` wrapper.

**H-03 — Redundant conjunct `lifecycleIdentityNoTypeAliasConflict`**
`SeLe4n/Kernel/Lifecycle/Invariant.lean:56-72` retains the conjunct with
the explicit note: *"`lifecycleIdentityNoTypeAliasConflict` is derivable
from `lifecycleIdentityTypeExact`... Both are retained in the bundle for
backward compatibility, but auditors should note that the second conjunct
adds no independent assurance beyond the first."* Redundant invariants
cost maintenance and can *mask* bugs: a future refactor that weakens
`lifecycleIdentityTypeExact` can still satisfy the bundle because the
redundant conjunct happens to match.
**Recommendation**: prove the implication explicitly
(`theorem lifecycleIdentityTypeExact_implies_noTypeAliasConflict`), then
delete the redundant conjunct and update the bundle arity. If the
backward-compat chain cannot absorb the arity change before v1.0, at
least commit the implication theorem so the redundancy is formally
witnessed.

**H-04 — CDT hypothesis externalization**
`SeLe4n/Kernel/Capability/Invariant/Preservation.lean:15-48` documents
that `cspaceCopy`, `cspaceMove`, `cspaceMutate`, and every CDT-modifying
operation takes `cdtCompleteness st' ∧ cdtAcyclicity st'` as a **post-state**
hypothesis. This is a proof-engineering choice that moves the obligation
to callers — the cross-subsystem bridge at the composition layer. The
consequence is that a caller that forgets to thread the post-state CDT
witness can compose a "preservation" proof that is vacuously conditional.
The preservation theorem holds, but provides no assurance. **The
composition audit that ties these post-state hypotheses back to a discharge
site is implicit, not indexed.**
**Recommendation**: add a theorem
`capabilityInvariantBundle_cdt_hypothesis_discharge_index` that asserts
every CDT-modifying operation has its post-state hypothesis discharged by
`crossSubsystemInvariant` at the specific point in `CrossSubsystem.lean`
where the bridge is composed. Make the index theorem a required import
for audit-tier builds.

**H-05 — `cspaceLookupMultiLevel` concurrency assumption**
`SeLe4n/Kernel/Capability/Operations.lean:206` — `cspaceLookupMultiLevel`
calls `resolveCapAddress` then `cspaceLookupSlot` in sequence. The
composition assumes the resolved CNode is still a valid CNode by the
second call. In the single-core kernel this is trivially true (no
concurrent retype between the two calls because there is no
concurrency). But the composition does not *prove* this, it *assumes* it —
and the SMP deferral (WS-V) will turn this implicit assumption into a
silent bug the proof chain does not catch.
**Recommendation**: add a precondition
`∃ cn, st.lookupKernelObject resolvedRef.cnode = some (.cnode cn)`
to `cspaceLookupMultiLevel` and prove it holds in the single-core
kernel via "no retype in window" argument. At SMP boundary, the same
predicate becomes a critical-section obligation.

**H-06 — `mintDerivedCap` lacks output-non-null witness**
`SeLe4n/Kernel/Capability/Operations.lean:641-649` takes `parent : NonNullCap`
enforcing input discipline per AL1b. The return type is `Capability`, not
`NonNullCap`. A theorem "if parent is non-null and badge-override
preserves the target, the derived cap is non-null" is missing. Derived
caps flow into CSpace slots; null caps in slots are the precise vector
AL1b was designed to close.
**Recommendation**: add
`theorem mintDerivedCap_preserves_non_null (p : NonNullCap) (b : Badge) :
    (mintDerivedCap p b).isNull = false` and use the subtype version
(`NonNullCap`) as the return type where callers only forward the value.

**MEDIUM findings — Capability / Lifecycle / Service**

- **CAP-M01** `Capability/Operations.lean:230-243` — `resolveCapAddress_caller_rights_obligation : True := trivial`
  is a documentation mechanism masquerading as a theorem. Vacuous theorems
  that exist only to be greppable pollute the theorem index. Prefer a
  `@[documented_obligation]` macro or a module-level comment block under
  a dedicated heading. If the greppability is load-bearing, use a `marker`
  constant (`def … := ()`) rather than a Prop.

- **CAP-M02** `Capability/Operations.lean:1231-1236` —
  `cspaceRevokeCdtTransactional` keeps a "dead code" defensive fallback
  branch that the transactional validation is supposed to render
  unreachable. If the branch really is dead, prove it
  (`theorem cspaceRevokeCdtTransactional_unreachable_fallback : … = absurd …`).
  If it is not dead, document what invariant failure triggers it.

- **CAP-M03** `Capability/Invariant/Preservation.lean` — file at 2 461 LOC
  combines insert, delete, revoke, copy, move, mutate, CDT revocation,
  and lifecycle-integration theorems. Natural split: per-operation files
  (`Preservation/Insert.lean`, `Preservation/CDT.lean`, …). Current
  organization pushes up against Lean's compile-time budget and forces
  re-compilation of the entire file on any change.

- **CAP-M04** `Capability/Invariant/Defs.lean:82-95` —
  `lifecycleCapabilityRefObjectTargetBacked` is maintained "by contract
  discipline", not by type-level enforcement. Cleanup-before-retype
  ordering is the contract. Any new retype path that forgets the cleanup
  hook creates dangling cap refs. The note rejects automatic enforcement
  as too costly, which is defensible, but the contract should at least
  be encoded as a precondition type: `RetypeTarget := { id : ObjId // cleanupHookDischarged id }`
  rather than documented in prose.

- **CAP-M05** `Capability/Invariant/Defs.lean:103-120` — `cdtMintCompleteness`
  kept outside the main bundle to avoid "churn on the 60+ theorems that
  destructure the 6-tuple bundle". This is tuple-projection brittleness
  identical to IPC-M01. Same remediation: named projections.

- **LIF-M01** `Lifecycle/Operations.lean:46-51` — `removeThreadFromQueue`
  `(none, none)` defensive fallback clears head+tail on "TCB not found"
  path. Should be unreachable under `tcbExistsInvariant`; prove it rather
  than silently zero out queue pointers.

- **LIF-M02** `Lifecycle/Operations.lean:348-371` —
  `lifecyclePreRetypeCleanup` chains cleanup steps in a specific order
  without a type encoding the ordering contract. A caller that reorders
  the steps produces wrong state but a well-typed proof.
  **Rec**: wrap the sequence in a single `lifecycleCleanupPipeline`
  definition; expose only the pipeline, not the individual steps.

- **LIF-M03** `Lifecycle/Operations.lean:615-648` — `scrubObjectMemory`
  uses the *abstract* formula `objectId.toNat × objectTypeAllocSize` for
  the scrub base address. Hardware binding will use actual physical
  addresses. The bridging theorem to hardware (WS-V) is not yet in place,
  so the scrub in the model does not map to the scrub on the device.
  This is expected for pre-hardware code but should be called out in
  `SELE4N_SPEC.md` §5 (memory safety) so integrators do not assume the
  abstract scrub composes with H3.

- **LIF-M04** `Lifecycle/Operations.lean:567-597` — `retypeFromUntyped`
  step 8 (post-allocation alignment re-verification) occurs *after* the
  watermark advance in step 7. Sequential semantics in the Lean model
  collapse the window, but the atomicity is not proven — a real-hardware
  implementation must atomically advance+verify or the window is a bug.

- **LIF-M05** `Lifecycle/Operations.lean` (1 473 LOC) monolithic —
  cleanup, retype, suspend, untyped allocation in one file. Split into
  `Operations/Cleanup.lean`, `Operations/Retype.lean`, `Operations/Suspend.lean`,
  `Operations/Untyped.lean`.

- **LIF-M06** `Lifecycle/Operations.lean:524-539` — `lifecycleRevokeDeleteRetype`
  has no rollback on partial failure. Early `.error` returns leave state
  in a partially-cleaned form the caller must handle. This is consistent
  with Lean's `Except` semantics but not documented — the failure-mode
  contract belongs in the function docstring.

- **SVC-M01** `Service/Operations.lean:148-169` — `serviceHasPathTo` returns
  `true` on fuel exhaustion (conservative cycle detection). The fuel
  bound is `serviceBfsFuel`; no boot-time assertion that the bound is ≥
  actual service-registry size. On very large service graphs this
  produces silent false positives — valid edges refused as "would create
  cycle". Add `bootFromPlatform_service_fuel_sufficient` witness.

- **SVC-M02** `Service/Operations.lean:88, 139-147` — function name retains
  `Bfs` suffix after the WS-G8 migration to DFS. Internal-first naming
  would rename to `hasPathToDfs` or drop the suffix entirely.

- **SVC-M03** `Service/Operations.lean:220-226` — dependency idempotence
  (`if depId ∈ svc.dependencies then .ok`) returns `.ok` on "already
  present", identical to `.ok` on "newly added". Callers cannot tell.
  Either return a richer result (`Ok Added | Ok NoOp`) or document the
  collision semantics.

- **SVC-M04** `Service/Invariant/Acyclicity.lean` (1 012 LOC) — larger than
  the Policy module at 231 LOC despite similar conceptual scope. Proof
  structure could be factored with a shared `reachability` induction
  principle. Deferrable.

**LOW findings — Capability / Lifecycle / Service**

- `Capability/Operations.lean:1-62` — 52-line file-level docstring
  documents C-L1..C-L10 inline. Extract to a dedicated audit-notes doc
  under `docs/audits/`. The code file header should describe the file,
  not the audit history of the file.
- `Capability/Operations.lean:939-941` — `cspaceMutate` direct-overwrite
  path is annotated `// Direct overwrite: bypass H-02 guard since we are
  replacing in-place`. The rationale is correct but the comment is a
  stop-sign without a soundness link. Cross-reference the CDT-preservation
  theorem by name.
- `Capability/Operations.lean:1015-1027` — `cspaceRevokeCdt_lenient`
  legacy variant mentioned but call sites not audited. If no production
  caller uses the lenient variant, mark `@[deprecated]` and schedule
  removal. If any does, document which.
- `Lifecycle/Invariant.lean:97-100` — `lifecycleCapabilityRefObjectTargetBacked`
  invariant requires `lookupSlotCap` backing; concurrency argument same
  as H-05 (implicit SMP assumption).
- `Service/Invariant/Acyclicity.lean:235-270` — `bfs_boundary_lemma`
  boundary proofs heterogeneous; document the 3–4 lemma families to help
  future maintainers.

### 2.4 Lean kernel — SchedContext

Scope: `Kernel/SchedContext/*.lean` plus `PriorityManagement.lean`.
This area was heavily touched by AK6-A..E (Phase AK6) which closed the
original v0.29.0 SchedContext audit findings at the ABI and invariant
layers.

**MEDIUM findings**

- **SC-M01** `SchedContext/Invariant/Defs.lean:78-100` — the proven CBS
  bandwidth bound is 8× the ideal. The loose factor is documented as
  "precision issue, not correctness bug", and AK6-I added the tight
  `cbs_bandwidth_bounded_tight` under an externalised
  `cbsWindowReplenishmentsBounded` hypothesis. The tight theorem is a
  conditional; no deployment-time witness currently discharges the
  hypothesis on the production trace.
  **Rec**: add a witness theorem for the canonical RPi5 configuration
  (`rpi5_cbs_window_replenishments_bounded`) using the Board.lean
  timer frequency and default replenishment period. That closes the
  conditional for the target platform and leaves generic deployments to
  discharge locally.

- **SC-M02** `SchedContext/PriorityManagement.lean` — `setPriorityOp` /
  `setMCPriorityOp` propagate `sc.priority → tcb.priority` on bind plus
  RunQueue re-bucketing at `max(new, pipBoost)`. Five preservation
  theorems carry `hSchedProj` closure hypotheses (the optional
  preemption-schedule path). Same closure-form pattern as H-07.

- **SC-M03** `SchedContext/Invariant/Preservation.lean` — per-operation
  preservation theorems are imported from the main `SchedContext/Invariant.lean`
  hub only via `CrossSubsystem.lean` due to the noted import cycle. The
  cycle note at `Invariant.lean` head is correct but not enforced; a
  future `import` added to the hub would reintroduce the cycle and Lean
  catches it at compile time — but not before wasting several minutes of
  build time.
  **Rec**: add `-- DO NOT IMPORT Preservation.lean or PriorityPreservation.lean
  from this hub — see WS-AB.D2 import-cycle note` banner explicitly.

### 2.5 Lean kernel — Architecture / InformationFlow / CrossSubsystem

**H-07 — Closure-form projection theorems**
`SeLe4n/Kernel/InformationFlow/Invariant/Operations.lean` and
`SeLe4n/Kernel/API.lean:2114-2153` — six per-arm `*_preserves_projection`
theorems remain closure-form (`hProjEq`/`hSchedProj` caller-supplied
hypotheses) with discharge recipes documented but no integration proof
composing the frame lemmas into a concrete witness. The affected arms
are: `.schedContextConfigure/Bind/Unbind`, `.lifecycleRetype`,
`.tcbSuspend/Resume`. CLAUDE.md's WS-AK Phase AK6 entry acknowledges this
as AK6F.20b tracked for substantive discharge (≈300 LOC aggregate).
The v0.29.11→v0.29.12 remediation added **per-arm named frame lemmas**
(`resumeThread_frame_insert`, `resumeThread_frame_ensureRunnable`,
`schedContextBind_frame_runQueue_rebucket`) — those are substantively
proven. The gap is the top-level composition.
**Recommendation**: compose at least ONE of the six arms (e.g.,
`schedContextConfigure_preserves_projection`) substantively, as a template.
Prefer `split_ifs` on the `Except.ok`-wrapped match rather than the
unstable `split` tactic that was flagged as the blocker. The discharge
recipe is documented; a template proof turns recipe into proven pattern.

**H-08 — Architecture assumption consumption index missing**
`SeLe4n/Kernel/Architecture/Assumptions.lean:132` claims
*"every declared assumption is actively consumed"*; four
`_consumed_by_*` bridge theorems are named (e.g.,
`deterministicTimerProgress_consumed_by_advanceTimer`). The consumption
argument is presented in prose; no single theorem enumerates all
assumptions and their consumers. For an audit consumer, this means
checking that the list is complete requires reading the entire
Architecture subsystem and cross-referencing.
**Recommendation**: add a marker lemma
`theorem architecture_assumptions_consumed : True := by exact trivial`
whose docstring enumerates `(assumption, consumer)` tuples in one
machine-searchable place. Or, preferable, define an inductive type
`ArchAssumption` listing the assumptions and a function
`archAssumptionConsumer : ArchAssumption → Lean.Name` so the index is
verifiable by `#eval`.

**H-09 — `untypedRegionsDisjoint` transitive coverage gap**
`SeLe4n/Kernel/CrossSubsystem.lean:476-485` — Phase AK8-A added the
11th conjunct `untypedRegionsDisjoint` to `crossSubsystemInvariant`
with an explicit direct-parent-child exclusion. The note at the
definition site calls out: *"Transitive grandparent/grandchild chains
(retype → retype → retype) can produce multi-level containment overlap
that is NOT captured by this direct-child exclusion... it is NOT part
of the Phase AK8 scope."* A three-level retype chain can therefore
produce physical regions that overlap without the invariant flagging
the overlap. The proof surface is preserved (the invariant holds
vacuously on the chains it excludes), but the physical correctness claim
is weaker than the invariant name implies.
**Recommendation**: either (a) strengthen the invariant to a transitive
`untypedAncestorRegionsDisjoint` (would require ancestor-tracking in
`UntypedObject.children`), or (b) rename to
`untypedRegionsDisjoint_directParentChildExcluded` and add a documented
clarification in `SELE4N_SPEC.md` §5 that physical disjointness across
transitive retype chains is an out-of-model obligation.

**MEDIUM findings — Architecture / InformationFlow / CrossSubsystem**

- **ARCH-M01** `Kernel/Architecture/VSpaceBackend.lean:52-61` — the
  `VSpaceBackend` typeclass is currently unused; `VSpace.lean` operates
  on concrete `VSpaceRoot`. Forward-looking H3 infrastructure. Tag the
  module with `-- STATUS: deferred; consumed at H3 real-hardware path`
  and either gate it behind a feature flag or accept the dead-code
  linter noise.

- **ARCH-M02** `Kernel/Architecture/PageTable.lean` — the ARMv8 walk is
  structural recursion with no explicit termination ticket beyond Lean's
  size check. A runtime implementation must ensure four-level hardware
  walks respect the same bound; right now the depth is implicit in the
  walk shape. Add a `pageTableWalk_depth_bound : depth ≤ 4` theorem as a
  witness consumers can reference.

- **ARCH-M03** `Kernel/Architecture/SyscallArgDecode.lean:159-192` — the
  state-aware decoder collapses every `IpcBufferReadError` (missing TCB,
  unmapped VAddr, out-of-range index) to `KernelError.invalidMessageInfo`
  at the ABI boundary. This matches the seL4 single-error convention but
  loses debugging granularity post-mortem. Post-1.0, consider a debug
  channel (`KernelError.invalidMessageInfo_withDetail`) that preserves
  the internal variant for diagnostics.

- **IF-M01** `Kernel/InformationFlow/Projection.lean:103-122` —
  `serviceObservable` covers boolean service presence only, not internal
  state. Cross-service covert channels (one service observing another's
  restart cadence) are not covered by NI. Documented gap; make it
  explicit in `SELE4N_SPEC.md` §7 ("Non-interference scope and
  exclusions") rather than only in the module header.

- **IF-M02** `Kernel/InformationFlow/Invariant/Operations.lean` — the
  NI-L3 accepted covert-channel catalog (four scheduling-induced
  channels) is documented at lines 47-109 but has no companion
  negative-case test that asserts the channels remain observable. A
  test proving these channels exist today (and therefore that the
  policy accepting them is non-vacuous) would guard against an
  accidental future "fix" that silently closes them and invalidates the
  acceptance documentation.

- **IF-M03** `Kernel/InformationFlow/Invariant/Operations.lean` — the
  file at 3 768 lines is the second-largest in the repo. Combines the
  per-arm preservation theorems. Natural split: one file per
  `KernelOperation` constructor group.

- **CX-M01** `Kernel/CrossSubsystem.lean:88-132` — `collectQueueMembers`
  fuel-sufficiency argument is informal. `QueueNextPath` ↔ `queueNext`
  traversal equivalence is not formalized. Listed as the remaining
  TPI-DOC item for IPC. Pre-1.0 priority: formalize by lifting
  `QueueNextPath` to a decidable reachability relation and proving
  `collectQueueMembers` returns the reachable set exactly when fuel ≥
  `objectIndex.length`.

- **CX-M02** `Kernel/CrossSubsystem.lean:299-348` —
  `lifecycleObjectTypeLockstep` invariant definition is the semantic
  witness for `storeObjectKindChecked` (AM4). The two live in different
  files without a cross-reference; a reader who finds one does not
  automatically discover the other.

- **CX-M03** `Kernel/Architecture/Assumptions.lean:234-248` —
  single-core assumption is documented; no runtime or static check that
  only one core is active. The boot sequence assumes core-0 via MPIDR
  mask (AK5-I). Add a `bootFromPlatform_currentCore_is_zero_witness`
  theorem that pins the assumption to the boot bridge.

- **CX-M04** `Kernel/Architecture/Invariant.lean` — the eight
  exception/interrupt preservation theorems are named individually but
  not composed into a single `archInvariantBundle_preserves_all_eight`
  theorem. For an auditor, this means each of the eight must be checked
  in isolation and the composition argued by hand.

- **CX-M05** `Kernel/Architecture/Invariant.lean` — default-state
  `architectureInvariantBundle` holds by vacuous reasoning (empty
  `objects`, `machine.regs` undefined). No positive-state smoke test
  validates the bundle on a post-boot state. `MainTraceHarness` now
  covers 227 lines of trace, but does not explicitly check the
  architecture bundle post-boot.

**LOW findings — Architecture / InformationFlow / CrossSubsystem**

- `Kernel/InformationFlow/Projection.lean:1-19` (WS-C3 note) — explicitly
  warns that tautological equalities do not constitute security
  evidence. TPI-002 is cross-referenced but TPI-002 itself is not under
  version control in `docs/`. Either commit the TPI-002 doc or remove
  the cross-reference.
- `Kernel/SchedContext/Invariant.lean` — re-export hub import-cycle
  note has the right content but needs a "DO NOT REIMPORT" linter
  comment to make the constraint machine-enforceable.

### 2.6 Lean foundation — Prelude, Machine, Model, Data structures

Scope: `SeLe4n/Prelude.lean` (1 649 LOC), `SeLe4n/Machine.lean`,
`SeLe4n/Model/*` (six files, including `Object/Structures.lean` at
2 769 LOC and `Object/Types.lean` at 1 698 LOC), `Kernel/RobinHood/`,
`Kernel/RadixTree/`, `Kernel/FrozenOps/`.

**H-10 — Typed-identifier namespace collision**
`SeLe4n/Prelude.lean:111-135` — `ThreadId.toObjId`,
`SchedContextId.toObjId`, `ServiceId.toObjId` all project to the common
`ObjId` namespace via identity mapping. The AJ2-D annotation states
that the object store (a functional map) prevents aliasing *because
`retypeFromUntyped_childId_fresh` ensures all new allocations target
fresh ObjIds*. This is a **dynamic guarantee held by the retype path**,
not a **type-level guarantee**. A future code path that stores a TCB
and a SchedContext under the same `ObjId` value (bypassing the retype
wrapper) would violate type-safety but satisfy `ObjId`'s type. In the
single-core kernel with a verified retype path this is currently safe;
at SMP or with future allocation backends it becomes a latent bug.
**Recommendation**: elevate the disjointness to a Prop-level invariant
`typedIdDisjointness` in `CrossSubsystem.lean` that every object-store
mutation must preserve. The AJ2-D note mentions
`typedIdDisjointness_trivial`; promote the trivial witness to a
substantive preservation proof that threads through every
`storeObject` caller.

**H-11 — `RegisterFile.BEq` non-lawful, `LawfulBEq (RHTable α β)` missing**
`SeLe4n/Machine.lean:254-304` — `RegisterFile.BEq` checks 32 GPR
indices; indices ≥ 32 are "never accessed by kernel code" by the
`regCount = 32` bound, but the `BEq` instance is formally non-lawful and
a negative witness (`RegisterFile.not_lawfulBEq`) is provided to block
accidental use. Separately, `Kernel/RobinHood/Bridge.lean:136-153`
declares `RHTable.BEq` non-lawful when the value type has a non-lawful
`BEq`, with no `LawfulBEq (RHTable α β)` instance even under
`[LawfulBEq β]`. Any proof that requires `DecidableEq` on `SystemState`
(transitively on `state.objects : RHTable _ KernelObject`) must supply
the witness at the call site. The AK8-J annotation explicitly notes
this and punts to "post-1.0 hardening work (DS-M04)".
**Recommendation**: for `RegisterFile`, refactor the `gpr` field from
`Nat → RegValue` to `Fin 32 → RegValue`. This unblocks derived-lawful
`BEq` and eliminates the "indices ≥ 32 never accessed" assumption. For
`RHTable`, add the lawful instance under `[LawfulBEq κ] [LawfulBEq β]`
— this is mechanical given the entry-wise pairing. Neither of these
should be post-1.0 work; both remove axis-aligned trust surface.

**H-12 — `Badge.ofNatMasked` abstract-model intermediate overflow**
`SeLe4n/Prelude.lean:520-543` — `Badge.ofNatMasked` computes `a.val ||| b.val`
on unbounded Lean `Nat` before truncating to 64 bits. The `bor_valid`
theorem proves the truncated result satisfies `Badge.valid`, but the
intermediate value may exceed `2^64`. In the real hardware path, all
values entering the model are already ≤ 2^64, so the intermediate is
bounded in practice. In the abstract model, a caller that feeds
non-bounded `Nat`s through a bitwise path produces a `Badge.valid`
result — but the intermediate is not bounded without a
caller-established precondition.
**Recommendation**: add a `Badge.ofNatMaskedBounded` variant that
accepts `UInt64` pairs (not `Badge` values, which are `Nat`-wrapped),
and deprecate the `Nat`-wrapped path for production code. The existing
path can remain for proof convenience.

**H-13 — `Badge.mk` public constructor bypass**
`SeLe4n/Model/Object/Types.lean:548-614` — `Badge` is defined as a
structure with a public `mk` constructor. The `valid : Prop` predicate
is *advisory* — constructing `Badge.mk (2^64 + 1)` type-checks. The
file notes that "only internal test code can construct `Badge.mk` (2^64)
directly" but public visibility means anyone importing Prelude or
Types can.
**Recommendation**: use Lean's private-mk discipline
(`structure Badge where private mk ::`) and expose only
`Badge.ofNatMasked` / `Badge.ofNat` / literal builders. Audit every
external `Badge.mk` call; migrate to the smart constructors. The same
pattern should extend to every wrapper type where a `valid` predicate
is advisory: `VAddr`, `PAddr`, `CPtr`, `Slot`.

**MEDIUM findings — Foundation**

- **FND-M01** `SeLe4n/Prelude.lean:463-468, 490-495` — `CPtr.isWord64Bounded`
  and `Slot.isWord64Bounded` hardcode `< 2^64` instead of delegating to
  `isWord64Dec`. Single source of truth is preferable; refactor to
  `@[inline] def isWord64Bounded := isWord64Dec ·.val`.

- **FND-M02** `SeLe4n/Prelude.lean:671-679` — `VAddr.canonicalBound`
  hardcodes `2^48` (ARM64 48-bit VA). Future LPA2 (52-bit) would need
  source change. `MachineState.virtualAddressWidth` already exists;
  compute `canonicalBound` from it. (This also interacts with the
  `physicalAddressWidth` parameterization that AK3-E did at the
  decode boundary — VA-side deserves the same treatment.)

- **FND-M03** `SeLe4n/Model/Object/Types.lean:1017-1043` —
  `UntypedObject.wellFormed` is Prop-level advisory, not enforced as a
  precondition on `allocate`/`retypeFromUntyped`. Wrap via subtype
  `UntypedObjectValid := { ut : UntypedObject // ut.wellFormed }` at
  every retype entry point.

- **FND-M04** `SeLe4n/Kernel/RobinHood/Bridge.lean:88-94` — `RHTable.default`
  uses hardcoded capacity 16. Define `minPracticalRHCapacity : Nat := 16`
  (or similar) and reference from both `Inhabited` and bridge-lemma
  capacity bounds. Magic literals in `Inhabited` instances are a common
  refactor trap.

- **FND-M05** `SeLe4n/Kernel/RobinHood/Bridge.lean:240-283` (DS-L5) —
  Lookup and Preservation proofs require `set_option maxHeartbeats`
  up to 800 000. The high heartbeat budget is a fragility signal: any
  near-term Lean toolchain bump (4.28.0 → 4.x) that changes tactic cost
  can break the proofs. Profile and decompose the slow subproofs;
  target ≤200 000 heartbeats. CLAUDE.md's v0.30.6 entry notes this is
  tracked but not scheduled.

- **FND-M06** `SeLe4n/Kernel/FrozenOps/Core.lean:149-200` — the
  `*Checked` variants (AK8-G) fix variant-mismatch at test surface, but
  core (unchecked) FrozenOps operations remain. A caller that imports
  FrozenOps/Core directly bypasses the guard. Mark the unchecked paths
  `private` or gate behind `set_option sele4n.frozenOps.unsafe true`.

- **FND-M07** `SeLe4n/Kernel/FrozenOps/Core.lean:285-344` — AE2-D
  two-phase validation comments say the Phase-2 error branch is
  "unreachable after Phase 1". If it truly is unreachable, prove it
  (`... := by exact absurd hPhase2 (Phase1_covers_all hPhase1)`) rather
  than returning `.error .objectNotFound`.

- **FND-M08** `SeLe4n/Prelude.lean:149-198` — three ObjId-conversion
  variants (`toObjId`, `toObjIdChecked`, `toObjIdVerified`) create
  cognitive load. Decision table in the Prelude docstring (`|Variant |
  checks sentinel | checks store type | use when|`) would narrow the
  choice.

**LOW findings — Foundation**

- `SeLe4n/Kernel/FrozenOps/Core.lean:14-32` — FrozenOps status stays
  "experimental — deferred to WS-V. Not in production import chain".
  CLAUDE.md confirms zero production consumers. For a pre-1.0 release
  the module should either be (a) marked with a compiler-level
  deprecation warning on accidental import, or (b) moved to a
  `docs/dev_history/experimental/` branch of the tree so the production
  footprint shrinks. Current retention as "architectural validation
  infrastructure" is defensible; the ambiguity around it is not.
- `SeLe4n/Kernel/RobinHood/Bridge.lean:441-452` — `ofList` uses
  insert-based construction with O(log n) resize cost. For large
  boot-time preallocation add `buildRHTablePreallocated` that
  pre-computes `next_power_of_two` capacity.
- `SeLe4n/Model/FreezeProofs.lean:313-328` — `freezeMap_indexMap_absent`
  proof is heartbeat-sensitive. Extract shared induction principle
  `foldl_absent_property` as top-level lemma.
- `SeLe4n/Prelude.lean` comments — workstream IDs (`WS-E3`, `WS-E6`,
  `WS-G1`, `WS-H12b`, etc.) are embedded in comments but NOT in
  identifier names, so this does **not** violate the CLAUDE.md naming
  ban. Recommendation is cosmetic: move workstream markers to
  `docs/WORKSTREAM_HISTORY.md` with a per-theorem index and replace
  inline markers with a short "// see WH:H12b" cross-reference to
  decouple refactor cadence from prose. Pure hygiene.

### 2.7 Platform layer (`SeLe4n/Platform/`)

Scope: `Platform/Contract.lean`, `Platform/DeviceTree.lean`,
`Platform/Sim/*`, `Platform/RPi5/*`, `Platform/Boot.lean` (2 074 LOC),
and the API entrypoint `SeLe4n/Kernel/API.lean` (2 258 LOC). The
platform layer is where abstract model meets hardware contract.

**H-14 — DTB legacy `Option`-returning path still reachable**
`SeLe4n/Platform/DeviceTree.lean` — `findMemoryRegProperty` returns
`Option`, collapsing "fuel exhausted" and "malformed blob" into `none`.
AK9-F added `findMemoryRegPropertyChecked : Except DeviceTreeParseError …`
that distinguishes the two cases, and `DeviceTree.fromDtbFull` routes
through the checked variant. But `findMemoryRegProperty` is still
publicly visible; any new caller may use it and silently lose error
granularity. The documented "legacy form" is a foot-gun.
**Recommendation**: mark `findMemoryRegProperty` `@[deprecated]` with
message "use `findMemoryRegPropertyChecked`; see AK9-F / P-M07". If any
Sim-path consumer uses the legacy form, migrate it in the same commit.

**H-15 — `physicalAddressWidth` parameterization audit**
`SeLe4n/Platform/DeviceTree.lean:394-410` — AJ3-B made
`physicalAddressWidth` a **required** parameter of
`DeviceTree.fromDtbWithRegions`. Verify no caller supplies a default
`:= 52` (ARMv8 LPA max) when the target is BCM2712 (44-bit). The grep
for default-PA-width call sites was not performed by the audit agents;
spot-check before release.

**H-16 — `_Check` predicates defaulting to `true` on missing bindings**
`SeLe4n/Platform/RPi5/RuntimeContract.lean:75-93` — `budgetSufficientCheck`
was tightened in AK9-E to return `false` for missing/wrong-variant
SchedContext bindings. Audit the remaining `_Check` predicates
(`registerContextStableCheck`, `dequeueOnDispatchCheck`,
`timeSlicePositiveCheck`, `ipcReadinessCheck`, `edfCompatibleCheck`) for
the same silent-true fallback pattern. If any predicate returns `true`
on a "binding absent" branch without explicit justification, it is a
latent AK9-E bug.

**MEDIUM findings — Platform**

- **PLT-M01** `SeLe4n/Platform/Boot.lean:407` — `bootFromPlatformUnchecked`
  deprecated alias retained "for backward compatibility with invalid-state
  test scenarios". Move to `SeLe4n.Testing.Deprecated` namespace post-1.0
  so production adopters cannot accidentally import it. Until then, add
  `@[deprecated]` with an explicit migration path in the message.

- **PLT-M02** `SeLe4n/Platform/Boot.lean:1400-1414` — VSpaceRoots
  excluded from `bootSafeObject`. Design rationale (ASID manager not
  available during builder phase) is defensible. Track the integration
  gap explicitly: the boot bridge is currently proven only for *empty*
  configs. A general-config bridge requires builder-phase ASID manager
  wiring.

- **PLT-M03** `SeLe4n/Platform/Boot.lean:928-951` — the boot-to-runtime
  invariant bridge only covers empty configs. This is acknowledged at
  the theorem site; the gap matters when H3 brings up a non-empty
  device configuration. Priority for the first hardware-binding
  workstream.

- **PLT-M04** `SeLe4n/Platform/DeviceTree.lean:333-380` —
  `classifyMemoryRegion` defaults to `.ram` on empty map.
  `classifyMemoryRegionChecked` (AK9-F) returns `Option` for strict
  semantics. Same treatment as H-14: deprecate the silent-default form,
  migrate callers.

- **PLT-M05** `SeLe4n/Platform/DeviceTree.lean:746-846` — `parseFdtNodes`
  default fuel = 2000, not scaled to DTB size. The checked variant
  computes `hdr.sizeDtStruct / 4`. All callers should migrate to
  size-derived fuel.

- **PLT-M06** `SeLe4n/Platform/DeviceTree.lean:936-961` —
  `extractPeripherals` searches depth 2 only. Acceptable for BCM2712
  but a pre-1.0 limitation for any future platform with deeper DTB
  nesting. Document in `SELE4N_SPEC.md` §6 and add a TODO with the
  recursion plan.

- **PLT-M07** `SeLe4n/Platform/Sim/Contract.lean` — this module plus
  `Platform/FFI.lean`, `Platform/RPi5/Contract.lean`, and three
  `Architecture/*Model.lean` files are not imported from any production
  build target per the documentation agent's cross-reference. CLAUDE.md
  lists them in the source-layout table, implying active status. Either
  wire them into the default build graph (as `Main.lean`/test harness
  imports) or mark them as "staged for H3 integration" in a dedicated
  CLAUDE.md section. Current state blurs the distinction between
  "active" and "deferred".

- **API-M01** `SeLe4n/Kernel/API.lean:392-429` — `resolveExtraCaps`
  silent-drop semantics match seL4 but are a correctness cliff for
  integrators. Receivers can detect by comparing the returned count to
  the expected count; this detection is not automated. Consider a
  counter in `KernelError` for "partial resolution" so integrators can
  opt into noisy error reporting.

- **API-M02** `SeLe4n/Kernel/API.lean:469-550` — `dispatchCapabilityOnly`
  consolidates 14 cap-only arms into a helper; good design. The helper
  accepts a `hArmProj` closure hypothesis per H-07. Once H-07 is
  discharged substantively, tighten the helper signature to drop the
  closure and expose an unconditional composition theorem.

**LOW findings — Platform**

- `SeLe4n/Platform/Boot.lean:100-114, 122-137, 666-702` — last-wins
  semantics on duplicate IRQ/object IDs in unchecked boot; checked boot
  rejects. Document at the hub (`Platform/Boot.lean` file header) that
  the unchecked path is test-only.
- `SeLe4n/Platform/RPi5/Board.lean:203-330` — 13 hardware constants
  validated against BCM2712 datasheet with 2026-03-29 date marker. Add
  a CI check that the datasheet reference list stays up to date when
  the RPi5 firmware revision bumps. Currently a manual hygiene step.
- `Main.lean` — 13-line trace harness entry is clean; trivially
  correct. No finding.

### 2.8 Rust workspace (`rust/`)

Scope: 4 crates (`sele4n-types`, `sele4n-abi`, `sele4n-sys`,
`sele4n-hal`) and assembly/linker assets. ~11 000 LOC.

The Rust workspace has received substantial hardening (AK5 full Rust
HAL pass, AK9 platform/DT, AI1/AI2 ABI correctness). The findings below
are primarily residual hygiene and a handful of genuine defense-in-depth
opportunities.

**H-17 — `UartLock::with` SAFETY sketch is thin**
`rust/sele4n-hal/src/uart.rs:238` — the `unsafe` block performs
`f(&mut *BOOT_UART_INNER.0.get())` inside a CAS-spin critical section.
The SAFETY comment documents mutual exclusion but does not explicitly
pin the mutable-borrow lifetime to the spin guard. A minor refactor
that splits acquisition from call (e.g., extracting the pointer before
the `f()` call) could silently invalidate the exclusion claim.
**Recommendation**: restructure as a `with_guard()` helper returning an
RAII-scoped `UartGuard<'_>` that takes ownership of the CAS release.
The current `with()` API becomes a thin wrapper that is obviously
correct. This mirrors the `EoiGuard` pattern already in `gic.rs`.

**H-18 — `MPIDR_CORE_ID_MASK` assembly/Rust coupling uncovered by compile check**
`rust/sele4n-hal/src/boot.S:39` builds `0x00FFFFFF` via
`mov x2, #0xFFFF; movk x2, #0xFF, lsl #16`. The Rust-side constant
`MPIDR_CORE_ID_MASK = 0x00FFFFFF` lives in `cpu.rs`. A change to one
without the other silently produces a core-ID mask that either narrows
or widens the boot gate. Both happen to encode today; any refactor that
changes the constant may or may not be representable as an immediate.
**Recommendation**: either (a) load the constant from a shared linker
symbol (`.rodata`-placed `u64` exported from Rust), or (b) add a
`const _: () = assert!(MPIDR_CORE_ID_MASK == 0x00FFFFFF);` in `cpu.rs`
cross-referenced from a build-time assertion in `build.rs` that scans
`boot.S` for the literal and fails on mismatch. Option (a) is strictly
better because it makes drift impossible.

**H-19 — `dispatch_irq` EoiGuard does not fire on direct `panic!()`**
`rust/sele4n-hal/src/gic.rs:362-386` — `EoiGuard` uses `Drop` to
guarantee EOI on all scope exits. Under `panic = "abort"` (per
AK5-A `Cargo.toml`) Drop handlers are **not** run on panic — only on
normal return. If an IRQ handler body contains a direct `panic!()`,
the INTID remains active on the GIC, starving subsequent interrupts.
The guard protects against `.unwrap()`/`.expect()` because those abort
before unwinding, but a hand-rolled `panic!("…")` in a handler body
has no such protection.
**Recommendation**: either (a) forbid direct `panic!()` in IRQ-handler
code paths via a lint (`#[deny(clippy::panic)]` at handler-function
granularity), or (b) change the EOI sequencing so EOI fires *before*
handler invocation (the GIC-400 spec permits this for level-sensitive
interrupts configured as edge-triggered via `ICFGR`). Option (b) is a
larger change; option (a) is cheap. At minimum, document the constraint
in a visible `SAFETY: handler contract` banner at `dispatch_irq`.

**MEDIUM findings — Rust**

- **RUST-M01** `rust/sele4n-hal/src/mmu.rs:117-141` — `sctlr_bits`
  module contains `A`, `CP15BEN`, `NAA`, `UMA`, `EE` constants with
  `#[allow(dead_code)]`, unused by `compute_sctlr_el1_bitmap()`. The
  `#[allow]` is bulk-applied. Consolidate into a doc comment explaining
  why each bit is excluded (e.g., `A`: data-alignment enforcement
  interacts with `memcpy`; see R-HAL-L11). The `#[allow(dead_code)]`
  per-constant pattern suppresses a useful signal.

- **RUST-M02** `rust/sele4n-hal/src/uart.rs:71` — `assert!(addr % 4 == 0, …)`
  fires on every `mmio_read32`/`mmio_write32`. On a 115200 baud UART
  producing thousands of kprintln calls per second, the runtime cost
  is small but non-zero. Release-profile `assert!` is not compiled
  away. Consider `debug_assert!` + a one-shot boot-time alignment
  check of each MMIO region. The tradeoff is defense-in-depth vs
  throughput; document the choice.

- **RUST-M03** `rust/sele4n-hal/src/timer.rs:311-318` — test code calls
  `init_timer(1000).unwrap()`. On a non-aarch64 host the fallback path
  returns `Ok(())` silently. Assert the `Ok` path explicitly:
  `assert_eq!(init_timer(1000), Ok(()))`.

- **RUST-M04** `rust/sele4n-hal/src/mmu.rs:5` — comment says "AG6
  replaces this with 4 KiB page-level mappings". AG6 shipped as WS-AG
  Phase AG6 per CLAUDE.md. The comment is stale — either AG6 did
  replace it (in which case the comment is wrong) or it did not (in
  which case the MMU is using placeholder block descriptors in a
  shipped release).
  **Verify and update**: if AG6 completed the page-level work, delete
  the comment; if not, mark as a known limitation with a forward
  reference to a real workstream that actually tracks the item.

- **RUST-M05** `rust/sele4n-hal/src/gic.rs:155` — `for i in 8..num_target_regs`
  assumes GICD_ITARGETSR banks 0–7 (INTIDs 0–31) are read-only/banked
  per GIC-400 spec. No runtime validation. A hardware variant that
  diverges fails silently. Add a boot-time self-check: write a known
  pattern to a banked register and verify the read-back matches the
  banked value.

- **RUST-M06** `rust/sele4n-hal/src/trap.rs:186` and `src/lib.rs:89` —
  active `TODO(WS-V/AG10)` for SVC FFI wiring. `WS-V` and `AG10` are
  closed workstreams per `WORKSTREAM_HISTORY.md`. The TODO target is
  stale. Either land the FFI wiring or update the TODO reference to
  point at a real tracking entry (e.g., `AUDIT_v0.29.0_DEFERRED.md` item
  DEF-R-HAL-L14).

- **RUST-M07** `rust/sele4n-hal/src/cache.rs:150-170` — `cache_range`
  emits `dsb_ish()` on empty range. Documented as intentional (zero-length
  fence). Consider naming a separate `memory_fence()` helper so callers
  that want a pure fence do not rely on a side effect of a no-op cache
  op.

- **RUST-M08** `rust/sele4n-abi/src/ipc_buffer.rs` — `IpcBuffer` is
  public; verify kernel actually consumes it end-to-end vs just exposes
  it via the ABI. If EL0 usage is still stub, feature-gate with
  `#[cfg(feature = "ipc_buffer")]` so callers opt in.

**LOW findings — Rust**

- `rust/sele4n-hal/src/gic.rs:70` — `gicd::ICENABLER_BASE` defined with
  `#[allow(dead_code)]`; unused by `init_distributor`. Remove or add a
  forward-reference comment for when it will be used.
- `rust/sele4n-types/src/lib.rs:1-94` — 52-line audit-notes block in
  `lib.rs` documents R-ABI-L1..L8. Extract to `docs/AUDIT_NOTES.md` to
  keep the crate entry-point lean.
- `rust/Cargo.lock` transitive build deps — `cc`, `find-msvc-tools`,
  `shlex`. `build.rs` declares only `cc`. Pin the others explicitly in
  `[build-dependencies]` (e.g., `cc = "=1.2.59"`) to lock defense-in-depth.
- `rust/sele4n-hal/src/uart.rs:95-101` — `init_with_baud(0)` panics;
  non-standard non-zero baud rates produce incorrect output silently.
  Document via panic or add validation against a whitelist (common:
  9600, 38400, 115200).
- `rust/sele4n-hal/src/interrupts.rs:25-36` — `disable_interrupts()`
  reads DAIF before mask. Correct for nesting but the comment does not
  spell it out. One-line annotation.
- `link.ld:56-60` — comment explains `PageTableCell` replaces `static mut`
  at the Rust level but linker syntax is opaque. Cross-reference:
  `# (Rust: sele4n-hal/src/mmu.rs:PageTableCell)`.
- `rust/sele4n-hal/src/boot.rs` — `rust_boot_main` is linker-resolved;
  not `pub` in boot.rs. Add `// symbol resolved by Lean kernel link`.
- `rust/sele4n-hal/src/mmio.rs` — `#![allow(clippy::manual_is_multiple_of)]`
  necessary until MSRV ≥ 1.85. Track for removal.
- `rust/sele4n-hal/src/vectors.S:28` — `.balign 2048` correct. Add
  Rust-side `const _: () = assert!(align_of_val(&__exception_vectors) >= 2048);`
  if the symbol is accessible.
- `rust/sele4n-hal/src/mmu.rs:276-283` — compile-time 4096-byte
  page-table alignment is asserted; extend with kernel-entry (0x80000)
  alignment: `const _: () = assert!(0x80000 % 4096 == 0);`.
- `THIRD_PARTY_LICENSES.md:87-90` — `find-msvc-tools` MIT attribution
  present; the crate is only relevant on Windows hosts which seLe4n
  does not target. Consider a workspace-level feature flag to exclude
  the transitive dep on non-Windows. Legal compliance is correct as-is.

### 2.9 Tests, scripts, and CI infrastructure

Scope: `tests/` (24 suites + harness + fixtures), `scripts/` (26 shell
scripts), `.github/workflows/` (5 workflows), `SeLe4n/Testing/` (helpers
+ invariant checks).

**H-20 — `NegativeStateSuite.lean` covers 2 of ~51 `KernelError` variants**
`tests/NegativeStateSuite.lean` — the tests agent reports that the
bulk of explicit error-variant matches target `.objectNotFound` and
`.invalidCapability`. The other ~49 discriminants
(`.untypedRegionExhausted`, `.revocationRequired`, `.asidNotBound`,
`.schedulerInvariantViolation`, `.alignmentError`, `.vmFault`,
`.nullCapability`, `.invalidObjectType`, etc.) have near-zero per-syscall
rejection coverage. The suite is 3 660 lines and covers many scenarios,
but each error variant should have at least one per-syscall rejection
test per direction (the `.error` shape from each syscall that can
produce it).
**Recommendation**: build a cross-product matrix — rows = `SyscallId`,
columns = `KernelError` variants, cells = "expected to produce this
variant under condition X". For every populated cell, land a scenario
test. This turns "we test error handling" into a falsifiable claim.

**H-21 — No timeout on `lake exe …` invocations**
`scripts/test_lib.sh` — `run_check()` does not wrap test-executable
invocations in a `timeout` call. A Lean proof that enters an infinite
tactic loop (or a runtime scenario that does not terminate — unlikely
given total functions, but a fuel-consuming loop without guard) hangs
the CI runner until GitHub Actions' 6-hour hard timeout expires.
**Recommendation**: add `LEAN_TEST_TIMEOUT_MINS=30` (configurable) and
wrap every `lake exe …` with `timeout "${LEAN_TEST_TIMEOUT_MINS}m"`.
Grant PASS only on exit 0; map `124` (timeout) to an explicit FAIL with
a "possible runaway proof / scenario" hint.

**H-22 — Fixtures lack byte-hash guard**
`tests/fixtures/main_trace_smoke.expected` (227 lines),
`robin_hood_smoke.expected`, `two_phase_arch_smoke.expected` — no
`.sha256` companion files, no pre-commit hash validation. CLAUDE.md
fixture-update rule says "update fixture only with rationale" — the
rule is honored by convention, not mechanism.
**Recommendation**: add `tests/fixtures/SHA256SUMS` updated by
`scripts/pre-commit-lean-build.sh` when the fixture changes, and
verified by CI. A fixture edit requires updating the hash, making the
change visible in `git diff` even when the content change is small.

**H-23 — AK6 tests are comment-delimited blocks, not named tests**
`tests/InformationFlowSuite.lean:1067-1114` — AK6-G/H/I tests are
documented at comment lines but not wrapped in named `def test_AK6_G`
/ `def test_AK6_H` / `def test_AK6_I` functions. The runtime harness
cannot report "AK6-G FAIL" as an identifiable unit; a failure shows up
as a generic assertion failure at line 1067.
**Recommendation**: convert every audit-remediation test to a named
IO function. The suite can call them all from a dispatch table; CI log
output gains per-sub-test granularity at zero proof-level cost.

**MEDIUM findings — Tests / CI**

- **TST-M01** `tests/NegativeStateSuite.lean:392-453` — AK8-B tests
  are well-structured (atomicity + success paths). Pattern this as the
  template for other AK8 audit items (C through L), several of which
  lack tests per the tests-agent analysis.

- **TST-M02** `SeLe4n/Testing/InvariantChecks.lean` — the runtime
  harness checks 11 cross-subsystem invariants (post-AM4). Add a
  bundled cross-subsystem assertion function
  `assertCrossSubsystemInvariants` that runs all 11 in sequence with a
  single failure report. Current checks are independent; a failure in
  check #5 does not fail the whole harness invocation, only that one
  check.

- **TST-M03** `scripts/test_abi_roundtrip.sh:14` —
  `source "$(dirname "$0")/_common.sh" 2>/dev/null || true` sources a
  file that does not exist, silently. Either create `_common.sh` with
  the shared helpers (and drop the `|| true` swallowing), or remove
  the `source` call. Silent environmental failures mask misconfiguration.

- **TST-M04** `.github/workflows/platform_security_baseline.yml:85` —
  uses `secrets.GITHUB_TOKEN`. Standardize across workflows to
  `github.token` (automatic per-action token, more scoped) unless an
  explicit reason exists.

- **TST-M05** `scripts/test_docs_sync.sh:36-56` — GitBook drift check
  is warning-only. Unstructured warnings pollute CI logs and get
  ignored. Either promote to hard failure (`exit 1` on any drift) or
  silence entirely. Non-blocking warnings are deferred-fix debt.

- **TST-M06** `scripts/test_tier3_invariant_surface.sh` — checks code
  structure via ~440 `rg` symbol-existence queries rather than
  behavioral tests. Verifies a symbol is defined; does not verify it is
  correct. Tier 3 should be renamed to "invariant-surface anchors" (it
  already is in CLAUDE.md) to avoid implying behavioral coverage.

- **TST-M07** `scripts/setup_lean_env.sh` — lacks idempotency guard.
  Re-invocation may corrupt `.elan` state or duplicate downloads. Add a
  sentinel file or environment-var check.

- **TST-M08** `.github/workflows/lean_action_ci.yml:45-50` — `apt-get
  install -y -qq shellcheck ripgrep` with no retry. Transient apt-mirror
  failures produce unreliable CI. Add 3-attempt backoff.

- **TST-M09** `SeLe4n/Testing/Helpers.lean:23-44` — `expectCond`,
  `expectError` accept empty `tag`/`label` strings. Add input
  validation so cryptic test output is impossible.

- **TST-M10** `tests/fixtures/` — no `README.md` documenting how
  `robin_hood_smoke.expected` and `two_phase_arch_smoke.expected` are
  regenerated. Adding one closes the fixture-provenance gap.

- **TST-M11** AK6-A..F test coverage — per tests-agent analysis, only
  AK6-G/H/I have visible tests in `InformationFlowSuite.lean`. AK6-A
  (SchedContext param validation), AK6-B (configure param
  post-state), AK6-C (replenish eligibleAt), AK6-D (yield self-guard),
  AK6-E (NI coverage rename), AK6-F (dispatch composition) need
  named-test wrappers.

- **TST-M12** `scripts/audit_testing_framework.sh` — exists, not
  invoked by any tier, workflow, or documentation. Either document its
  purpose and integrate, or remove.

- **TST-M13** `tests/FreezeProofSuite.lean`, `tests/TraceSequenceProbe.lean` —
  invoked only at Tier 2 (FreezeProofSuite) and Tier 4 nightly
  (TraceSequenceProbe). Promote TraceSequenceProbe to Tier 2 if the
  runtime budget allows; otherwise document why it is nightly-only so
  future auditors do not assume it runs on every PR.

**LOW findings — Tests / CI**

- `.github/workflows/lean_action_ci.yml:32-40` — cache key hashes
  `setup_lean_env.sh`; changes to the script trigger cache invalidation.
  Consider separating setup-artifact cache from build cache.
- `tests/LivenessSuite.lean:166` — ends with `return ()` after printing
  anchors; no explicit `expectOk`/`expectCond`. Liveness is validated
  by Tier 3 symbol-existence checks, but the suite itself asserts
  nothing. Add at least one live assertion (e.g., "wcrt_bound theorem
  exists and has the expected conclusion on a sample state").
- `tests/fixtures/scenario_registry.yaml` — manual-curation risk if not
  auto-generated from `MainTraceHarness.lean`. Add generator rule.
- `scripts/test_tier0_hygiene.sh` — verify shellcheck compliance for
  all of `scripts/*.sh` is enforced, not just spot-checked.
- `SeLe4n/Testing/Helpers.lean:79-96` — OID range discipline
  documented but not enforced at `withObject` entry. Add a runtime
  assertion.
- `.github/workflows/lean_toolchain_update_proposal.yml` — auto-bump
  workflow; verify it cannot bypass branch protection.
- `.github/workflows/nightly_determinism.yml` — verify it actually
  compares trace outputs across commits for drift (not just runs the
  trace once).

### 2.10 Documentation, licensing, and repository organization

Scope: all `.md` files outside `docs/dev_history/`, all i18n READMEs,
`CHANGELOG.md`, `CLAUDE.md`, license files, build manifests, `.gitignore`.

**H-24 — Stale workstream references in active Rust TODOs**
Reiterating from §1.2: `rust/sele4n-hal/src/trap.rs:186` and
`src/lib.rs:89` carry `TODO(WS-V/AG10)` annotations. Per
`WORKSTREAM_HISTORY.md`, both WS-V and AG10 are **closed** workstreams.
`AUDIT_v0.29.0_DEFERRED.md` tracks the underlying SVC FFI wiring as
`DEF-R-HAL-L14`. The source TODO target is stale by several releases.

**Recommendation**: update both comments to reference the deferred-item
ID (`// TODO(DEF-R-HAL-L14): Wire Lean FFI dispatch via @[extern] bridge`)
and verify every other active TODO in the Rust + Lean source points at
a live tracking entry rather than a closed workstream. This closes the
"which tracking doc is authoritative?" ambiguity a maintainer meets on
first inspection.

**MEDIUM findings — Documentation / Organization**

- **DOC-M01** `README.md:96` (documented at C-01). The i18n READMEs
  under `docs/i18n/` were *not* spot-checked for the same stale
  reference — at a minimum, `README.ja.md`, `README.es.md`, etc.
  likely mirror the issue and will all need updating when C-01 is fixed.

- **DOC-M02** Six Lean modules not imported anywhere —
  `SeLe4n/Platform/Sim/Contract.lean`, `SeLe4n/Platform/FFI.lean`,
  `SeLe4n/Platform/RPi5/Contract.lean`,
  `SeLe4n/Kernel/Architecture/CacheModel.lean`,
  `SeLe4n/Kernel/Architecture/ExceptionModel.lean`,
  `SeLe4n/Kernel/Architecture/TimerModel.lean`. These are documented in
  CLAUDE.md source-layout as staged-for-hardware-binding but are not in
  the build graph. Either (a) wire via a `Platform.Staged` import graph
  that builds but is not linked, or (b) move to `docs/dev_history/staged/`
  until actively consumed. A module that exists but no one imports is
  a latent rot source — the proofs in it can break silently during
  refactors of the modules it imports.

- **DOC-M03** `LICENSE` file at repo root is GPL-3.0+; per-file SPDX
  headers (`// SPDX-License-Identifier: GPL-3.0-or-later`) are
  **absent from all Rust files** and from a handful of Lean files.
  Legally, the root LICENSE is sufficient for GPL compliance. Best
  practice (SPDX convention, corporate compatibility review tools) is
  to tag each file. Adding headers is a mechanical pass; doing so
  before v1.0 signals polish to downstream integrators.

- **DOC-M04** CLAUDE.md large-file list refreshed AK10-E claims
  `CHANGELOG.md (~9 453 lines)`, matched in spot check. But CLAUDE.md
  also lists `docs/audits/AUDIT_v0.29.0_WORKSTREAM_PLAN.md (~4 721 lines)`
  — verify that the plan-document count reflects the fixes after the
  C-02 missing-script cleanup.

- **DOC-M05** `docs/codebase_map.json` — machine-readable inventory is
  generated by `scripts/generate_codebase_map.py`. After the audit
  recommendations in this document land, regenerate and verify the
  README metric table (which sources from `codebase_map.json`) still
  matches.

- **DOC-M06** 10 i18n READMEs under `docs/i18n/` — structurally
  consistent with the main README per documentation-agent review.
  Verify all 10 mirror the C-01 fix when it lands; do not update only
  the English.

- **DOC-M07** `docs/WORKSTREAM_HISTORY.md` (2 572 lines) — canonical
  history per CLAUDE.md. The C-02 missing-scripts finding and H-24
  stale-TODO finding should be folded into a "WS-AK errata" entry so
  future auditors see the resolution.

- **DOC-M08** `.github/workflows/` (5 workflows) — audited by
  documentation agent as structurally consistent, no use of
  `pull_request_target` (good). Document this security decision in
  `CONTRIBUTING.md` if/when that file lands. Currently the project has
  no `CONTRIBUTING.md`; for a v1.0 release this is a gap for external
  contributors.

**LOW findings — Documentation / Organization**

- `docs/dev_history/audits/audit_findings_provided_by_me.md` — 19-line
  minimal historical findings dump with no date/version/closure header.
  Either annotate its provenance or remove.
- `CLAUDE.md` — "Active workstream context" section is currently 250+
  KB of inlined summaries. At some point this becomes self-defeating
  (the file bloats past the 500-line-chunked-read threshold and agents
  must page through it). Consider archiving summaries older than the
  last three releases into a sibling file.
- `docs/audits/AUDIT_v0.29.0_*` — the active audit plan lives in this
  directory; this new audit (`AUDIT_v0.30.6_COMPREHENSIVE.md`) joins
  it. Establish a "one active audit at a time" convention: when the
  v0.30.6 portfolio closes, archive both into `docs/dev_history/audits/`
  together.
- `.gitignore` — verified adequate by the documentation agent (covers
  `.lake/`, `tests/artifacts/`, `__pycache__/`, `.env`, `*.pem`,
  `*.key`, `.trivy/`, `.claude/worktrees/`, `.ci-artifacts/`). No
  change needed.
- Test harness naming discipline — 24 test suites in `tests/` with
  names `Ak{N}…Suite.lean`. These are **file names**, not
  **identifier names**; the CLAUDE.md naming ban applies to the latter.
  The file names carry workstream provenance for dev history which is
  legitimate (tests exist to regression-proof a specific workstream's
  gains). No finding.

---

## 3. Verifications and strengths (INFO)

This section records checks that confirmed clean-at-v0.30.6 state. An
unusually large number of audit expectations were met; recording them
protects against silent regression.

### 3.1 Proof surface

- **Zero `sorry` / `axiom` / `native_decide`** in any `.lean` file
  under `SeLe4n/`. `decide` is present in appropriate places (e.g.,
  `rpi5MachineConfig_wellFormed`, `irqRangeValid_holds`). Spot-checked
  by repo-wide grep — the only matches for "sorry" are in test-suite
  comments explaining that the kernel rejects `sorry` at compile time.
- Production theorem count and proof depth consistent with AK7-K
  refinements; no regression relative to v0.29.0 baseline metrics in
  `docs/audits/AL0_baseline.txt`.

### 3.2 Build and test gate

- `lake build` (260 jobs) passes cleanly per CLAUDE.md; not re-run in
  this audit but multi-phase build-integrity is structural.
- `cargo test --workspace` at 415 tests, 0 warnings under `-D warnings`
  per CLAUDE.md AK10 entry.
- Test tier structure (fast → smoke → full → nightly) is well-formed
  and documented; tier boundaries are clear.

### 3.3 Hardware fidelity

- BCM2712 hardware constants (UART at `0xFE201000`, GIC distributor at
  `0xFF841000`, timer at 54 MHz, PA width 44 bits, GIC SPI count 192)
  cross-referenced in `Board.lean:203-330` against BCM2712 datasheet
  (validation date 2026-03-29).
- MMIO region disjointness proven by `decide` in
  `mmioRegionDisjoint_holds` and `mmioRegionsPairwiseDisjoint_holds`.
- RPi5 runtime contract is non-vacuous — 6 substantive predicates
  including `budgetSufficientCheck` (tightened in AK9-E), not the
  "return True" vacuous form the Sim contract had before AI5-A.
- GIC EOI discipline via `EoiGuard` Drop pattern (with H-19 caveat).
- SCTLR_EL1 bitmap includes all RES1 bits (4/7/8/11/20/22/23/28/29)
  after AK5-C correction.

### 3.4 Rust hygiene

- No `static mut` remaining; migration to `UnsafeCell<T>` + explicit
  `Sync` impls per AK5-E complete.
- `panic = "abort"` in both `dev` and `release` profiles per AK5-A.
- All `unsafe` blocks spot-checked have SAFETY comments; four clean
  doctests added per v0.29.8 (total 415 workspace tests including
  doctests).
- No Spectre v1 lint suppressions; CSDB/SB barriers in place per
  AG9-F.
- `#[repr(transparent)]` / `#[repr(C)]` consistently applied to ABI
  types.

### 3.5 Versioning and i18n

- All 15 version-bearing files synchronized to `v0.30.6` per
  `check_version_sync.sh` PASS state.
- Lean toolchain pinned to `v4.28.0` in `lean-toolchain`.
- Rust workspace version `0.30.6` in `Cargo.toml`.
- All 10 i18n READMEs share structural consistency and version badges.

### 3.6 Git and license hygiene

- `.gitignore` covers build artifacts, caches, secrets, CI outputs.
- No stray `.DS_Store`, `.orig`, `.rej`, `*.bak` files found.
- `THIRD_PARTY_LICENSES.md` present with verbatim MIT attribution for
  `cc 1.2.59`, `find-msvc-tools 0.1.9`, `shlex 1.3.0`. GPL-3.0+
  compatibility verified.
- No runtime third-party dependencies — kernel binary is in-repo code
  plus `core::*`.

### 3.7 Fixture integrity

- `tests/fixtures/main_trace_smoke.expected`: 227 lines (matches
  CLAUDE.md AK10-A claim exactly).
- `tests/fixtures/robin_hood_smoke.expected`: 16 lines, present.
- `tests/fixtures/two_phase_arch_smoke.expected`: 9 lines, present.
- (Byte-hash gating is H-22.)

---

## 4. Cross-cutting themes

Aggregating the 196 findings surfaces a smaller set of recurring
patterns. Understanding these is more useful than the per-finding
remediation list.

### 4.1 Closure-form proof obligations delegated to callers

Affected: H-04, H-07, IPC-M01, CAP-M05, CX-M04.

Recurring pattern: a theorem ships with a hypothesis that is **never
discharged** inside the theorem — the caller must supply it. Taxonomy:

1. **CDT post-state witnesses** (H-04): `cspaceCopy/Move/Mutate`
   preservation take `cdtCompleteness st'` and `cdtAcyclicity st'` as
   post-state hypotheses. Discharged by the cross-subsystem bridge; no
   integration proof indexes which callers discharge where.
2. **`hProjEq` / `hArmProj` closures** (H-07): six
   `*_preserves_projection` theorems take a per-operation projection
   equality as a closure. Frame lemmas are substantively proven (AK6-F
   added ~25 named lemmas); the top-level composition is still a
   caller obligation.
3. **`hSchedProj` closures** (SC-M02): priority-management operations
   that may trigger an optional preemption schedule take the schedule
   projection as a closure. Similar discharge pattern.

**Theme-level recommendation**: commit to a **"discharge index"** as a
pre-1.0 audit artifact. For every closure-form theorem, list:
- Theorem name, file:line
- Hypothesis names (e.g., `hProjEq`, `hSchedProj`)
- Canonical discharge site (file:line of the caller that provides the
  witness)
- Auditable check: a Lean `example` or `#check` that the discharge is
  reachable on one representative input

This is a ~200-line proof artifact that converts "trust us, the
caller does it" into "here is the chain, every link checks". Without
it, an integrator reading the theorems has to construct the chain
by hand.

### 4.2 Invariant brittleness from tuple projection

Affected: IPC-M01, CAP-M05, Model/Object/Structures, API invariant
bundles documented in AF-26.

The `ipcInvariantFull` 12-tuple requires `.2.2.2.2.2.2.2.2.2.2.2.1` to
access `donationOwnerValid`. The `apiInvariantBundle_frozenDirect` was
already called out in AF-26 as a 17-deep projection. Every such bundle
is an accident waiting to happen: a reorder during a refactor silently
breaks consumers, and Lean's elaborator sometimes reports a misleading
type mismatch (the projection index is still valid, it just points at
the wrong conjunct now).

**Theme-level recommendation**: replace tuple-based bundles with named
`structure` types. Each conjunct becomes a named field; projections
become `.fieldName`; the record is auto-derived extensional; reorders
are source-level refactors the compiler surfaces. The refactor is
~2–3 days of mechanical work. It should land before v1.0.

### 4.3 Advisory predicates vs gated preconditions

Affected: FND-M03, FND-M04 (FrozenOps), CAP-M04, LIF-M04.

Several `wellFormed : Prop` predicates are *advisory* — they are
maintained by discipline of callers, not by subtype enforcement at
construction. `Badge.valid`, `UntypedObject.wellFormed`,
`Capability.isValid`, `FrozenMap.wellFormed`, `MessageInfo.wellFormed`
all share the pattern. Adding `Valid` subtype wrappers at construction
is a one-line change per type and makes the invariant unfalsifiable.

**Theme-level recommendation**: establish a project-wide discipline
that every `wellFormed` Prop has a matching `Valid := { x : T // x.wellFormed }`
subtype and every public constructor returns (or requires) the
subtype. Legacy code that returns the bare type can be migrated
incrementally. The mechanical cost is low; the invariant certainty
is high.

### 4.4 SMP-latent single-core assumptions

Affected: H-05, H-10, Assumptions.lean, various
`cspaceLookup*`/`serviceHasPathTo` paths.

The single-core assumption (`H3 uses core 0 only; SMP deferred to
WS-V`) is documented in Architecture/Assumptions.lean and leveraged
implicitly throughout the proof chain. When SMP arrives, many
"sequential semantics" proofs become implicitly wrong — e.g., the
"CNode resolved by `resolveCapAddress` is still a CNode at
`cspaceLookupSlot` time" argument holds only because no one else can
retype between the two calls.

**Theme-level recommendation**: inventory single-core-dependent
proofs as an explicit index. For v1.0 that targets single-core RPi5
this is a pre-SMP checklist; for SMP (post-1.0) it becomes the
refactor surface. A `SeLe4n.Kernel.Concurrency.Assumptions` module
listing each site with its single-core precondition makes the future
work tractable.

### 4.5 Workstream IDs in comments vs identifiers

Affected: throughout the codebase, especially Prelude.lean,
Operations.lean file headers.

CLAUDE.md bans workstream IDs (`WS-*`, `AK*`, etc.) in **identifier
names**. Comments are permitted. In practice, comments carry extensive
workstream markers (e.g., `-- AJ1-A (M-14): cleanupDonatedSchedContext`
in preservation theorems). This is legitimate traceability for active
portfolios but becomes noise once portfolios close.

**Theme-level recommendation**: after each portfolio closes, replace
inline workstream markers with references to a canonical tracking doc
(`// see WORKSTREAM_HISTORY:AJ1-A`). The current 5000+ inline markers
are a form of inertial doc-drift that each refactor has to carry.

### 4.6 Stale forward references in code

Affected: H-24, RUST-M04, RUST-M06.

Comments reference workstreams (`WS-V`, `AG10`, `AG6`) that
`WORKSTREAM_HISTORY.md` documents as closed. The references were live
when written; the portfolio closed; the references were never
retargeted. The deferred work now lives in
`AUDIT_v0.29.0_DEFERRED.md` under IDs like `DEF-R-HAL-L14`.

**Theme-level recommendation**: when a workstream closes, grep the
source tree for `// WS-X` / `// AG-N` style comments and retarget any
that describe **deferred** work (not completed work — completed-work
comments are historical and can stay). Run this grep-and-retarget pass
as part of the workstream-closure checklist.

### 4.7 Organizational fatigue from monolithic files

Affected: `IPC/Invariant/Structural.lean` (7 626 LOC),
`InformationFlow/Invariant/Operations.lean` (3 768 LOC),
`Scheduler/Operations/Preservation.lean` (3 633 LOC),
`Capability/Invariant/Preservation.lean` (2 461 LOC),
`Lifecycle/Operations.lean` (1 473 LOC).

Each is a split candidate by subsystem logic (per-operation or
per-concern). The project's re-export-hub pattern already supports
this — `Invariant.lean` hubs paper over splits. The cost is mostly
grepping imports and moving declarations.

**Theme-level recommendation**: set a 2 000-LOC ceiling on any single
Lean file (excepting generated/mechanical content like CHANGELOG).
Files above the ceiling trigger a split task at each major release.

---

## 5. Recommended v1.0 release gate

Not every MEDIUM finding needs to block v1.0, but the CRITICALs and
several HIGHs do. Here is a prioritized gate:

### 5.1 Must-fix before v1.0 (BLOCKING)

| # | Finding | Effort | Why it blocks |
|---|---------|-------:|---------------|
| 1 | C-01: README "Latest audit" pointer | 10 min | First impression for any integrator; points at a 7-release-old audit. |
| 2 | C-02: Missing scripts in active plan | 1–4 h | Active plan directs auditors/CI to run files that don't exist. |
| 3 | C-03: pre-commit hook not auto-installed | 1–2 h | Sole local defense against sorry + unbuildable module commits. |
| 4 | H-24 / RUST-M06: Stale `WS-V/AG10` TODO targets | 30 min | Audit trail for deferred work is broken. |
| 5 | H-20: NegativeStateSuite error-variant coverage | 2–3 days | ~49 `KernelError` variants have no per-syscall rejection test. |
| 6 | H-22: Fixture byte-hash guard | 2 h | Prevents silent fixture drift under concurrent edits. |
| 7 | H-21: `lake exe` timeout wrapper in CI | 1 h | CI hangs block review throughput. |
| 8 | H-07: at least one closure-form projection theorem discharged substantively | 1–2 days | Establishes the template that closes the AK6F.20b tracking item. |

Total BLOCKING effort: ~5–6 developer-days.

### 5.2 Should-fix before v1.0 (STRONGLY RECOMMENDED)

| # | Finding | Effort | Why recommended |
|---|---------|-------:|-----------------|
| 9 | H-02: `lifecycleRetypeObject` visibility | 1 day | Public proof-access escape hatch for a cleanup-bypassing path. |
| 10 | H-03: redundant `lifecycleIdentityNoTypeAliasConflict` | 4 h | Remove redundancy; prove the implication. |
| 11 | H-06: `mintDerivedCap` non-null output witness | 2 h | Closes the "input non-null, output unchecked" asymmetry. |
| 12 | H-13: `Badge.mk` private-mk discipline | 4 h | Unfalsifiable invariant at construction. |
| 13 | H-23: AK6 tests as named functions | 2 h | Identifiable test granularity. |
| 14 | H-17: `UartLock::with` RAII refactor | 4 h | Eliminates subtle SAFETY reasoning. |
| 15 | H-18: MPIDR_CORE_ID_MASK asm/Rust coupling | 1 h | Eliminates drift class bug. |
| 16 | H-19: `dispatch_irq` panic behavior documentation + lint | 1 h | Prevents "EOI lost" interrupt-starvation class. |
| 17 | Theme 4.2: tuple→structure invariant bundles | 2–3 days | Removes the largest single class of future refactor errors. |

Total STRONGLY RECOMMENDED effort: ~6–7 developer-days.

### 5.3 Can defer to v1.x (NICE-TO-HAVE)

- All LOW findings
- MEDIUM findings in §4.1–§4.7 cross-cutting themes that are not
  directly listed above
- Theme 4.4 single-core assumption inventory (matters when SMP lands,
  which is post-1.0 per the RPi5-first target)
- Theme 4.7 monolithic file splits (mechanical, low-risk)

### 5.4 Release checklist (operational)

- [ ] Every BLOCKING item above resolved or explicitly deferred with
      rationale appended to `docs/audits/AUDIT_v0.30.6_DEFERRED.md`
      (new doc, parallel to `_v0.29.0_DEFERRED`).
- [ ] This audit's finding IDs (C-01..C-03, H-01..H-24) are
      enumerated in `docs/WORKSTREAM_HISTORY.md` under a new
      "WS-AN post-audit-remediation" entry.
- [ ] README "Latest audit" pointer updated to
      `AUDIT_v0.30.6_COMPREHENSIVE.md`.
- [ ] All 10 i18n READMEs reflect the same pointer change.
- [ ] `check_version_sync.sh` PASS at target v1.0.0 tag (or maintainer-
      selected patch-only bump).
- [ ] `test_full.sh` + `cargo test --workspace` + `cargo clippy -D warnings`
      + `ak7_cascade_check_monotonic.sh` + `check_website_links.sh`
      all PASS.
- [ ] Fixture byte-hash guard (H-22) integrated and verifying on CI.
- [ ] CHANGELOG.md entry for v1.0.0 cross-references this audit.

---

## 6. Methodology notes and caveats

### 6.1 What this audit did

- Read every production `.lean` file in `SeLe4n/` and every production
  `.rs` file in `rust/` via delegated read-only subagents.
- Cross-checked subagent findings against the live filesystem for the
  most-impactful claims (missing scripts, stale README line, fixture
  line count, TODO markers, SPDX header presence).
- Compared every major claim against CLAUDE.md's active-workstream
  context entries (itself sourced from commit messages and
  `WORKSTREAM_HISTORY.md`).

### 6.2 What this audit did NOT do

- **Did not rebuild the project**. All of `lake build`,
  `cargo test --workspace`, and the tier scripts are reported as
  passing in CLAUDE.md; this audit did not independently re-run them.
  Build-time regressions between v0.30.6 HEAD and this audit's commit
  would not be caught here.
- **Did not run the Lean elaborator on individual theorems**. Proof
  correctness was evaluated at the docstring/comment level; machine-
  checked proof validity is inherited from the tier scripts.
- **Did not audit `docs/dev_history/`**. Per CLAUDE.md that directory
  is archive; an audit of the archive is out of scope.
- **Did not perform dynamic-analysis fuzzing** on the Rust HAL.
  Static analysis only. No QEMU boot was driven during the audit.
  `scripts/test_qemu.sh` exists; hardware-validation docs under
  `docs/hardware_validation/` from WS-AG Phase AG9 report passing
  QEMU boot at v0.27.0.
- **Did not compile-check the subagent claims exhaustively**. Spot
  checks confirmed the highest-impact claims; subtler proof-content
  claims (e.g., "theorem X has closure-form signature") rely on the
  subagent having read the evidence correctly. For findings flagged
  MEDIUM or lower, readers verifying a specific finding should open
  the referenced file:line before remediation.

### 6.3 Confidence levels per finding category

| Category | Confidence |
|----------|-----------|
| Missing files / stale documentation (C-01, C-02, H-24) | **High** — verified via live `Grep`/`ls`. |
| Proof-surface gaps (H-04, H-07, H-08, H-09) | **High** — anchored in explicit docstrings in the cited files. |
| Architectural layering (H-02, RUST-M04, DOC-M02) | **Medium-High** — documented patterns observed across multiple files. |
| Subtle proof content (IPC-M01, CAP-M05) | **Medium** — relies on subagent read of tuple-projection sites; spot-check recommended. |
| Hygiene / naming (LOW findings) | **Medium** — bulk reading; individual items deserve verification. |

---

## 7. Appendix — agent prompts (for reproducibility)

Eight parallel read-only audit agents were dispatched with
specialized prompts. Each was instructed:

- To distrust comments and verify against code
- To produce structured findings with severity / category / file:line /
  evidence / recommendation
- To NOT spawn further subagents (single-level parallelism)

Agent scope partition:

| Agent | Subsystem scope |
|-------|-----------------|
| 1 | IPC + Scheduler Lean subsystems |
| 2 | Capability + Lifecycle + Service Lean subsystems |
| 3 | Architecture + InformationFlow + SchedContext + CrossSubsystem |
| 4 | Foundation (Prelude, Machine, Model, RobinHood, RadixTree, FrozenOps) |
| 5 | Platform layer (Contract, DeviceTree, Sim, RPi5, Boot, API) |
| 6 | Rust workspace (sele4n-types/-abi/-sys/-hal + assembly + linker) |
| 7 | Tests + scripts + CI workflows + SeLe4n/Testing |
| 8 | Documentation + file structure + dead code + licensing |

Aggregate agent statistics:

- 8 agents, 8 completions, 0 failures
- ~232 raw findings produced
- ~196 findings retained after main-auditor de-duplication / severity
  reclassification / false-positive removal (notably: 1 "CRITICAL"
  self-retracted by the Rust agent, 1 "CRITICAL" from the tests agent
  down-graded to MEDIUM after verification that `|| true` was swallowing
  an intentionally-optional source)
- ~36 duplicate findings where multiple agents surfaced the same issue
- ~10 findings escalated from agent MEDIUM to audit HIGH based on
  cross-subsystem impact analysis the individual agents could not see

### 7.1 What the main auditor added beyond agent findings

- C-01 escalated to CRITICAL (an agent flagged it HIGH; the main
  auditor elevated based on "first thing integrators read" impact)
- C-02 verified via direct filesystem check
- C-03 added by main auditor; no agent surfaced it (pre-commit hook
  install is a convention + script, not a file-content issue)
- Cross-cutting themes in §4 are main-auditor synthesis; individual
  agents saw their own scope only
- Release gate §5 is main-auditor prioritization; not in any agent
  output

### 7.2 Known blind spots in this audit methodology

- **Cross-subsystem proof composition** was evaluated only at the
  boundary theorems; the end-to-end soundness chain from
  `syscallEntryChecked` through projection through NI has not been
  re-derived. The AK7 remediation is a strong signal the chain is
  sound; a dedicated soundness-chain audit would be a separate
  engagement.
- **Toolchain security** (Lean 4.28.0 compiler, elan, Lake) was not
  audited. The toolchain is pinned in `lean-toolchain`; supply-chain
  compromise at the Lean upstream would not be caught here.
- **Build-reproducibility** (bit-identical binary builds) was not
  tested. The tier-4 nightly determinism workflow exists but was not
  exercised during this audit.
- **Hardware-side observability** of the model. The Lean proofs show
  model-level invariants hold. Whether the abstract model refines a
  real BCM2712 execution requires an H3 hardware-binding proof that
  is tracked in `AUDIT_v0.29.0_DEFERRED.md` as a set of items
  (`DEF-A-M04/M06/M08/M09`, `DEF-R-HAL-L14`).

---

**End of audit.**

This document ships under the project's GPL-3.0-or-later license
(see `LICENSE`). It supplements `AUDIT_v0.29.0_COMPREHENSIVE.md` and
does not replace it. All findings are advisory; the maintainer
retains final judgment on severity, schedule, and whether to accept
the release gate in §5.

