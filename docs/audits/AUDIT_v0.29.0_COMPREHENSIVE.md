# Comprehensive Pre-Release Audit — seLe4n v0.29.0

**Date:** 2026-04-16
**Scope:** Full codebase — 140 Lean modules (~94,749 LOC) + 48 Rust sources (~9,739 LOC)
**Version:** 0.29.0
**Branch:** `claude/audit-kernel-modules-lWPDp`
**Auditor:** Claude Opus 4.7 (automated, 10 parallel specialized agents)

---

## Executive Summary

This audit is the most thorough line-by-line review of the seLe4n codebase performed
to date. It was conducted in preparation for the first major release (v1.0) and the
beginning of hardware-benchmarking on Raspberry Pi 5. Ten parallel specialized
agents each reviewed a disjoint subsystem at the source-line level. Findings were
then cross-validated against documentation claims (README, SELE4N_SPEC.md,
CHANGELOG, CLAUDE.md) — documentation was treated as a suspect artifact, not a
source of truth.

The codebase is in exceptionally strong shape. Zero `sorry`/`axiom` across the
production proof surface, comprehensive NI proofs, 360+ Rust conformance tests,
and a disciplined invariant/operations split. The previous audit cycles (WS-AH,
WS-AI, WS-AJ) have closed a large fraction of previously-observed gaps.

Nevertheless, several classes of residual issues remain that should be addressed
before v1.0, most of them documentation-level, plus a handful of correctness
concerns that warrant a new workstream. This report groups findings by severity
and by subsystem, and terminates with a prioritized remediation roadmap.

---

## Table of Contents

1. [Scope and Methodology](#1-scope-and-methodology)
2. [Finding Summary](#2-finding-summary)
3. [HIGH Findings](#3-high-findings)
4. [MEDIUM Findings](#4-medium-findings)
5. [LOW Findings](#5-low-findings)
6. [INFO / Observations](#6-info--observations)
7. [Subsystem Notes](#7-subsystem-notes)
8. [Rust Implementation Notes](#8-rust-implementation-notes)
9. [Cross-Cutting Analysis](#9-cross-cutting-analysis)
10. [Recommendations and Roadmap](#10-recommendations-and-roadmap)

---

## 1. Scope and Methodology

### 1.1 Files Audited

| Layer | Files | LOC (approx) |
|-------|-------|--------------|
| Lean Prelude/Machine | 2 | ~2,200 |
| Lean Model (Object, State, Builder, Frozen, Freeze) | 8 | ~9,500 |
| Lean Kernel Scheduler + PIP + Liveness + RunQueue | 16 | ~11,000 |
| Lean Kernel IPC (Ops, DualQueue, Invariant) | 18 | ~19,000 |
| Lean Kernel Capability + Lifecycle + Service | 12 | ~9,000 |
| Lean Kernel Architecture (VSpace, TLB, Cache, PT, ARMv8, exceptions) | 17 | ~8,500 |
| Lean Kernel InformationFlow + SchedContext | 13 | ~9,500 |
| Lean Kernel API + CrossSubsystem | 2 | ~4,100 |
| Lean Kernel Data Structures (RobinHood, RadixTree, FrozenOps) | 14 | ~9,000 |
| Lean Platform (Boot, DTB, Sim, RPi5, Contract) | 14 | ~4,800 |
| Lean Testing + Test Suites | 24 | ~19,000 |
| Rust sele4n-types | 5 | ~750 |
| Rust sele4n-abi | 16 | ~3,700 |
| Rust sele4n-hal | 19 | ~3,900 |
| Rust sele4n-sys | 8 | ~1,400 |
| **Total** | **188** | **~115,350** |

### 1.2 Methodology

Each agent:
- Read the source files in its scope directly (no trust in documentation).
- Compared the Lean specification against the Rust implementation where both exist.
- Looked for: sorry/axiom, `native_decide`, deterministic violations, hidden panics,
  proof gaps (vacuous quantifiers, trivial theorems), unreachable code,
  capability-check bypasses, invariant-preservation gaps, IPC deadlock
  opportunities, scheduler priority inversions, Rust unsafe correctness,
  MMIO alignment/ordering, ASID/TLB maintenance bugs, cache coherency gaps,
  decode truncation, and NI leakage.
- Reported findings with severity and `file:line` anchors.

### 1.3 Top-Level Sanity Checks

- `Grep` for `\b(sorry|axiom|native_decide)\b` across `SeLe4n/` returned 8 matches — all 8 are explanatory comments documenting prior removal of `native_decide`. **Zero actual `sorry`/`axiom`/`native_decide` in production proof surface** (confirmed at line level).
- Lake version = `0.29.0`; Rust workspace version = `0.29.0`; Rust package version = `0.29.0`. Version sync is consistent.

---

## 7. Subsystem Notes

### 7.1 Foundational Modules (Prelude, Machine, Model)

Scope: `SeLe4n/Prelude.lean`, `SeLe4n/Machine.lean`, `SeLe4n/Model/*`.

**HIGH:**

- **[F-H01] `FrozenMap.indexMap` unbounded growth without capacity witness** — `FrozenState.lean:294–299, 363–369`. `freezeMap` seeds `indexMap` with a 16-capacity `RHTable` and relies on the auto-grow contract. The returned `FrozenMap` carries no `invExtK` witness. For `maxObjects = 65536` entries this relies on an undocumented invariant transfer. *Remediation:* prove `freezeMap_indexMap_invExtK` and an explicit `freezeMap_capacity_sufficient` lemma.
- **[F-H02] `apiInvariantBundle_frozenDirect` observationally weak** — `FreezeProofs.lean:1103–1106`. Only `objects.get?` agreement is required; scheduler, machine, TLB, services, IRQs, CDT, lifecycle metadata are unconstrained. Any non-`objects` mutation vacuously preserves the predicate. *Remediation:* rename to `apiInvariantBundle_frozenDirectObjectsOnly` or extend field-agreement conjuncts.

**MEDIUM:**

- **[F-M01] `Memory` is total `PAddr → UInt8` without bounds** — `Machine.lean:144`. `readMem`/`writeMem` never consult `memoryMap`/`physicalAddressWidth`; out-of-range accesses silently succeed. *Remediation:* route through `RuntimeBoundaryContract.memoryAccessAllowed`.
- **[F-M02] `MessageInfo.encode` no label-bound saturation** — `Types.lean:1178`. `MessageInfo.mk` bypasses `maxLabel` check (only `decode` enforces it); constructed messages can overflow into the caps field. *Remediation:* make `MessageInfo.mk` private, expose `mkChecked`.
- **[F-M03] Typed IDs derive `Inhabited ⟨0⟩` — sentinel-zero is convention-only** — `Prelude.lean:60–497`. Any `default : ObjId`/`ThreadId`/`SchedContextId`/`CPtr`/`Slot`/`Badge` silently produces the sentinel. Nothing prevents downstream proofs from instantiating defaults where a valid ID is expected. *Remediation:* drop `Inhabited` on ID types or switch to a `Valid` subtype carrying explicit sentinel witness.
- **[F-M04] `ThreadId.toObjId`/`SchedContextId.toObjId` alias via identity mapping** — `Prelude.lean:137, 384`. `ThreadId ⟨5⟩.toObjId = SchedContextId ⟨5⟩.toObjId = ObjId ⟨5⟩`. Disjointness relies on pattern-match discipline downstream. *Remediation:* phantom-tag `ObjId` with `kind : ObjectKind` or assign disjoint sub-ranges.
- **[F-M05] Non-lawful `BEq RegisterFile`/`BEq TCB` publicly exported** — `Machine.lean:278–281; Types.lean:581`. Acknowledged in comments but any downstream `LawfulBEq` search or `decide` over TCB equality is silently unsound outside GPR indices 0–31. *Remediation:* restrict the non-lawful instances to a test-only newtype; expose canonical `TCB.ext` for proofs.
- **[F-M06] `FrozenSystemState` drops `FrozenMap` invariant proofs** — `FrozenState.lean:76`. No proof that `indexMap` entries are in-bounds of `data.size`; out-of-bounds `get?` returns `none` silently. *Remediation:* carry `well_formed : ∀ k idx, indexMap.get? k = some idx → idx < data.size`.
- **[F-M07] `Capability` has no `isNull`-style invariant guard** — `Types.lean:110`. `default : AccessRightSet` is `empty`; combined with sentinel `ObjId ⟨0⟩` this mirrors `seL4_CapNull` only by convention. *Remediation:* add `Capability.isNull` predicate and check at sensitive entry points.
- **[F-M08] `PagePermissions.ofNat` silently masks bits ≥ 5** — `Structures.lean:66–71`. `ofNat (2^10) = empty-rights` with no execute/read — but callers that use `ofNat` (not `ofNat?`) get surprising downgrades on reserved-bit input. *Remediation:* route `ofNat` through `ofNat?` at its single call sites, or document masked-to-5-bits semantics.
- **[F-M09] `ensureCdtNodeForSlot` increments `cdtNextNode` unbounded** — `State.lean:1326–1338`. Unbounded `Nat` model is fine, but a hardware mapping to fixed-width CDT node IDs reuses IDs silently. *Remediation:* gate by `cdtNextNode.val < maxCdtDepth` invariant.
- **[F-M10] `noVirtualOverlap_trivial` is a tautology** — `Structures.lean:184`. The predicate collapses trivially on functional maps; it does not assert physical-frame uniqueness. *Remediation:* redefine to `∀ v₁ v₂, lookup v₁ = some(p,_) → lookup v₂ = some(p,_) → v₁ = v₂`.
- **[F-M11] `TlbEntry` lacks ASID generation/age field** — `State.lean:168`. Stale entries against re-mapped VSpaceRoot cannot be detected from the entry alone. *Remediation:* mirror `AsidManager` generation in each `TlbEntry`.

**LOW:** 15 findings covering predicate naming inconsistency (L-01), Badge truncation cross-ref (L-02), TCB permissive MCP default (L-03), boot interrupt-enable window (L-04), one-sided permission round-trip (L-05), TCB Queue recovery coverage (L-06), depth-1 descendantsOf fuel (L-07), bool-valued CDT predicates (L-08), 17-deep tuple projections in `allTablesInvExtK` (L-09), missing `DecidableEq KernelObject` (L-10), hardcoded register-index counterexample (L-11), default zero `RegisterContext` (L-12), `IpcMessage.mk` non-private (L-13), zero-offset allocate (L-14), `CdtNodeId`/`InterfaceId` without sentinel convention (L-15).

**INFO:** `ToString` fallback priority, UInt64 system-register fields, TLB freeze-verbatim, `maxObjects = 65536`.

**Health notes:** Very high proof hygiene; zero `sorry`/`axiom`/`native_decide`/`unsafe`/`partial`; no `get!`/`head!`/`panic`; lawful BEq/Hashable on all typed IDs; full extensionality + round-trip coverage. Recurring structural themes are (1) unbounded-`Nat` ID wrappers with `Inhabited ⟨0⟩` relying on pattern-match discipline, (2) observationally weak `FrozenSystemState` invariants post-freeze, (3) maintenance-fragile 17-deep tuple projections. W^X layered correctly (decode + builder + runtime). No CVE-worthy defects.

### 7.2 Scheduler, Priority Inheritance, Liveness (WCRT)

Scope: `SeLe4n/Kernel/Scheduler/*`, `SeLe4n/Kernel/PriorityInheritance/*`, `SeLe4n/Kernel/Liveness/*`, `SeLe4n/Kernel/Scheduler/RunQueue.lean`.

**HIGH:**

- **[S-H01] WCRT theorem is a proof schema, not a closed liveness proof** — `Liveness/WCRT.lean:181–226`. `bounded_scheduling_latency_exists` is a trivial arithmetic composition whose two load-bearing hypotheses `hDomainActiveRunnable` (lines 187–193) and `hBandProgress` (lines 196–201) are externalized and expected from callers. `eventuallyExits` (`BandExhaustion.lean:52–56`) is similarly an externalized predicate. The advertised release-grade "WCRT = D·L + N·(B+P)" is effectively delegated to the deployer. *Remediation:* derive `hBandProgress` from CBS budget finiteness + `consumeBudget_budgetRemaining_le`, derive `hDomainActiveRunnable` from `scheduleDomain` + `domainScheduleEntriesPositive`.
- **[S-H02] `pip_bounded_inversion` bounds depth by fuel, not by structural blocking-chain** — `PriorityInheritance/BoundedInversion.lean:39–43`. `chainDepth × wcrt` is upper-bounded by `objectIndex.length`. Under the cyclic blocking graph that `BlockingGraph.lean:82–85` explicitly tolerates ("conservative" behavior), the bound is vacuously correct but operationally useless. *Remediation:* bind `chainDepth` to an invariant-derived structural bound (distinct reply-blocked TCBs under `blockingAcyclic`) and prove each link's completion time via scheduler progress.
- **[S-H03] Bound-thread re-enqueue uses TCB base priority on production paths — concrete priority inversion vector** — `Scheduler/Operations/Core.lean:337` (`handleYield`), `:390, 546` (`timerTick`, `timerTickBudget` unbound branch), `:776` (`switchDomain`). Each uses `effectiveRunQueuePriority tcb` (base TCB + PIP) rather than `resolveInsertPriority` which uses SchedContext priority. Selection (`Selection.lean:370–394`) uses SC priority via `resolveEffectivePrioDeadline`, so a SC-bound thread with `sc.priority ≠ tcb.priority` is scheduled at SC priority but lives in the TCB-priority bucket — `chooseBestInBucketEffective` misses it. *Remediation:* replace with `resolveInsertPriority` in all three entry points (already used by the `-WithBudget` variants).
- **[S-H04] `schedulerPriorityMatch` and `effectiveParamsMatchRunQueue` are jointly over-constraining** — `Scheduler/Invariant.lean:291–296` vs `:560–572`. Both are conjuncts of `schedulerInvariantBundleExtended`. For any SC-bound thread with `pipBoost = none`, one demands `threadPriority[tid] = some tcb.priority`, the other demands `threadPriority[tid] = some sc.priority`. Simultaneous satisfaction *forces* `tcb.priority = sc.priority`, but neither `schedContextBind` nor `schedContextConfigure` enforces this equality. *Remediation:* fuse into a single SC-aware predicate or enforce the equality at bind/configure.

**MEDIUM:**

- **[S-M01] `blockingChain` silently truncates on fuel exhaustion** — `PriorityInheritance/BlockingGraph.lean:86–96, 128`. Returns `[]` rather than an error tag; under invariant violation, PIP stops mid-chain and stale `pipBoost` persists. *Remediation:* return `Sum`/`Option` error on fuel exhaustion.
- **[S-M02] `timeoutBlockedThreads` swallows per-thread error list** — `Scheduler/Operations/Core.lean:580`. `_timeoutErrors` is discarded by name; a non-empty list signals invariant violation and is never surfaced. *Remediation:* propagate or at least `debug_assert`.
- **[S-M03] CBS admission-check truncates utilization downward** — `SchedContext/Budget.lean:208–228`. Aggregate over-admission up to ~6.4% for 64 contexts. For a safety-critical RT kernel this can violate `cbs_bandwidth_bounded`. *Remediation:* ceiling-round or boot-parameterize rounding direction and prove a tight bound.
- **[S-M04] `ReplenishQueue.insertSorted` uses non-strict `≤` → LIFO on equal eligibility times** — `SchedContext/ReplenishQueue.lean:67`. Duplicates processed out-of-order. *Remediation:* use strict `<` and document FIFO-within-tie.
- **[S-M05] `schedContextConfigure` does not remove stale `replenishQueue` entries** — `SchedContext/Operations.lean:90–113`. `processReplenishmentsDue` (`Core.lean:447–455`) may redundantly enqueue already-runnable thread. *Remediation:* call `ReplenishQueue.remove scId` at configure entry.
- **[S-M06] Production `schedule`/`switchDomain` use unchecked save/restore variants** — `Scheduler/Operations/Selection.lean:487–495, 560–564`. Under `currentThreadValid` the branch is provably unreachable, but production routes through non-`Checked` variants — any invariant drift silently drops register state. *Remediation:* route production callers through `*Checked`.
- **[S-M07] `switchDomain` unreachable fallback returns `.ok ((), st)`** — `Operations/Core.lean:756–764`. `switchDomain_index_in_bounds` proves the branch dead, but a boot-config bug violating `domainScheduleEntriesPositive` silently stops rotation. *Remediation:* return `.error .schedulerInvariantViolation`.
- **[S-M08] `migrateRunQueueBucket` fallback uses raw `newPriority`** — `SchedContext/PriorityManagement.lean:109–122`. Could erase a legitimate PIP boost on partially-constructed state. *Remediation:* error or assert `currentThreadValid`.

**LOW:** `handleYield` error code semantics (L-13), `getCurrentPriority` silent fallback (L-14), `oid.toNat→ThreadId` direct cast (L-15), brittle `isBetterCandidate_transitive` proof (L-16), `⟨Nat.max …⟩` bypasses Priority validity (L-17), `runQueueUnique` on flat list only not per-bucket (L-18).

**INFO:** `effectiveRunQueuePriority` reads only TCB fields (clean framing); `Machine.tick` uses unbounded `Nat` (no rollover concern in model — Rust side separate); no sorry/axiom/native_decide/partial in scope.

**Health notes:** Scheduler core (selection, EDF tie-break, dequeue-on-dispatch, RH backing) is internally consistent at the invariant level. Principal risks before GA: (a) WCRT theorem is a schema whose hypotheses come from callers; (b) PIP bounded inversion bounds by fuel not by structure; (c) three production entry points (yield/timerTick/switchDomain) re-enqueue SC-bound threads at the wrong bucket — this is a concrete production priority-inversion vector; (d) the two priority-match invariants silently require `tcb.priority = sc.priority`.

### 7.3 IPC (Operations, DualQueue, Invariant)

Scope: `SeLe4n/Kernel/IPC/*`.

**HIGH:**

- **[I-H01] `cleanupPreReceiveDonation` silently swallows donation-return errors** — `IPC/Operations/Endpoint.lean:296–298`. The `.error _ ⇒ st` branch drops every `returnDonatedSchedContext` failure and proceeds to block the receiver. Under ordinary IPC invariants this cannot fire, but this is not formally proven at the call site, contradicting the AJ1-A/AI4-A error-propagation policy elsewhere. Any invariant drift becomes a silent SchedContext leak just before receiver blocks. *Remediation:* change return to `Except KernelError SystemState` and propagate, or prove unreachability.
- **[I-H02] `endpointReply`/`endpointReplyRecv` fail-open when `blockedOnReply _ none`** — `IPC/DualQueue/Transport.lean:1777–1785, 1809–1815`. Any thread can deliver the reply when the target is `none`; soundness depends entirely on `blockedOnReplyHasTarget` (16th conjunct of `ipcInvariantFull`) holding at every use. This is not gated by a proof-carrying wrapper. *Remediation:* make the `none` branch return `.error .replyCapInvalid` (fail-closed); convert `blockedOnReplyHasTarget` to a soundness lemma.

**MEDIUM:**

- **[I-M01] `endpointCall` leaves caller with stale `pendingMessage`** — `Transport.lean:1728–1739`. On handshake, caller's `pendingMessage` is never cleared after rendezvous; caller transitions to `.blockedOnReply` retaining its outbound message — can leak on self-call or protocol regression. *Remediation:* clear via `storeTcbIpcStateAndMessage ... none`.
- **[I-M02] `endpointReceiveDual` rendezvous path does not update receiver `ipcState`** — `Transport.lean:1639–1671`. When a waiting sender is dequeued, `senderMsg` is written into receiver's `pendingMessage` but `ipcState` is untouched, silently violating `waitingThreadsPendingMessageNone` (5th conjunct). *Remediation:* add `storeTcbIpcState ... .ready`.
- **[I-M03] `notificationSignal` wake does not use PIP-effective priority** — `Endpoint.lean:385–388`. Uses base `tcb.priority`; PIP-boosted server placed into wrong RunQueue bucket until next scheduler tick. Contradicts AI3-A fix pattern (yield/timer/switch). *Remediation:* use `effectiveRunQueuePriority` in wake path.
- **[I-M04] `timeoutThread` PIP revert only covers `.blockedOnReply`** — `Operations/Timeout.lean:76–100`. Correct today but fragile to future PIP-on-call integration. *Remediation:* document the call-state gap formally.
- **[I-M05] `ipcUnwrapCapsLoop` is publicly callable with mis-sized fuel argument** — `CapTransfer.lean:95–97, 132–134`. When invoked at `idx > 0`, produces off-by-one padding → silently drops one cap with no `.noSlot` placeholder. *Remediation:* mark `private` or pass explicit `remaining := caps.size - idx`.
- **[I-M06] `endpointQueueRemove` defensive fallback arms** — `DualQueue/Core.lean:482–494`. Unreachability lemmas exist (`queueRemove_predecessor_exists`, `queueRemove_successor_exists`) but are not composed at call sites. Corrupt queue silently breaks linkage. *Remediation:* add `endpointQueueRemove_fallback_unreachable` composition theorem.
- **[I-M07] Send/receive asymmetric cap-root error handling — covert channel** — `DualQueue/WithCaps.lean:110–121, 152–153`. Missing receiver CSpace root on send returns `.ok (empty)`; missing sender CSpace root on receive returns `.error .invalidCapability`. The asymmetry is a per-pair information-flow distinguisher. *Remediation:* align both paths.

**LOW:** `donateSchedContext` unproven-unreachable defensive branch (L-1); `timeoutAwareReceive` stale `.timedOut` flag reachability (L-2); `endpointCallWithDonation` relies on external `popHead_returns_head` (L-3); reply-path badge handling TODO (L-4); unbounded `Nat` arithmetic in `notificationSignal.Badge.bor` (L-5); `returnDonatedSchedContext` leaves client in replenish queue (L-6).

**INFO:** `ipcInvariant` is narrow (notifications only) — rename to `notificationInvariantSystem`; `.endpointQueueEmpty` error code misused for missing `pendingMessage` (AH2-G); self-call deadlock not proscribed; no "reply target runnable" invariant; reply-cap badge handling matches seL4.

**Health notes:** Strong shape overall; zero `sorry`/`axiom`; 16-conjunct `ipcInvariantFull` with explicit donation/uniqueness/reply-target conjuncts; preservation chains thorough and layered. Key risks before release: fail-open defaults in reply/replyRecv (I-H02) and silent error-swallow in `cleanupPreReceiveDonation` (I-H01) — both benign today but one invariant regression away from a real confused-deputy defect. Secondary concerns: receiver-side state gap at rendezvous (I-M01/I-M02), PIP coverage on notification wake (I-M03), public fuel-footgun `ipcUnwrapCapsLoop` (I-M05).

### 7.4 Capability, Lifecycle, Service

Scope: `SeLe4n/Kernel/Capability/*`, `SeLe4n/Kernel/Lifecycle/*`, `SeLe4n/Kernel/Service/*`.

**HIGH:** None.

**MEDIUM:**

- **[C-M01] Cross-untyped physical-overlap not enforced** — `Lifecycle/Operations.lean:667`. `ut.children.any` check rejects child ID collisions only within the *same* untyped. Two untypeds with overlapping `[regionBase, regionBase+regionSize)` can both allocate at the same PA with different child IDs. *Remediation:* add `untypedRegionsDisjoint` invariant.
- **[C-M02] `cspaceRevokeCdtStrict` retains partial state on first failure** — `Operations.lean:1011–1012`. Not transactional. *Remediation:* rename `cspaceRevokeCdtBestEffort` or provide transactional wrapper.
- **[C-M03] `resolveCapAddress` recurses without intermediate-level rights check** — `Operations.lean:118–125`. Documented design choice. Any future cap-forwarding operation would leak authority through un-attenuated traversal. *Remediation:* annotate with proof obligation that all callers enforce rights.
- **[C-M04] `suspendThread` non-atomic across G2→G7** — `Suspend.lean:162–205`. Documents H3-ATOMICITY; relies on Rust HAL's `with_interrupts_disabled`. Lean model cannot verify that wrapping. *Remediation:* require `interruptsDisabled st.machine` precondition on hardware paths.
- **[C-M05] `validatePriorityAuthority` uses unbounded `Nat` MCP comparison** — `PriorityManagement.lean:50–53`. A thread with `maxControlledPriority = ∞` (root task) can escalate arbitrarily. Standard seL4 behavior but should be explicitly annotated as root-task-only. *Remediation:* document; add hardware-width bound constant.
- **[C-M06] `getCurrentPriority` silent fallback to `tcb.priority` on missing SC** — `PriorityManagement.lean:68–75`. Documented "dead code under invariants" but neither `setPriorityOp`/`setMCPriorityOp` establish `schedContextBindingConsistent` before call. *Remediation:* return `Except` and propagate.
- **[C-M07] `findFirstEmptySlot` without radix-width upper bound** — `Structures.lean:538–545`. Can exceed `2^radixWidth`. *Remediation:* cap `scanLimit` at `2^radixWidth - base.toNat`.

**LOW:** `cspaceMove` no self-move early-reject (L-1); `cspaceMutate` bypasses occupied-slot guard (L-2); `ipcTransferSingleCap` CDT edge without sender-rights record (L-3); `cleanupDonatedSchedContext` asymmetric cleanup between `.bound` vs `.donated` (L-4); IPC buffer canonical upper-bound not checked (L-5); `registerService` O(n) duplicate scan before authority check — timing side-channel (L-6); `lookupServiceByCap` not stable across RH rehash (L-7); `serviceCountBounded` boot-time establishment not exposed (L-8); abstract object sizes differ from seL4 RPi5 (L-9); `cspaceDeleteSlotCore` leaves dangling CDT edges (L-10).

**INFO:** Zero `sorry`/`axiom`/`native_decide`/`partial`; sentinel conventions in `objectOfTypeTag`; CPtr masking to `machineWordMax`; Badge overriding in mint machine-checked safe; `cspaceRevokeCdt` fuel-sufficiency deferred to WS-V.

**Health notes:** Mature and well-structured. Core security properties (authority reduction, CDT-based revocation, fresh-child uniqueness, capacity gating, MCP authority, IPC buffer 7-step validation) all machine-checked. Main gaps are behavioral (atomicity window C-M04, cross-untyped disjointness C-M01, strict-revoke partial state C-M02) rather than proof-layer. D2 `getCurrentPriority` silent fallback (C-M06) worth hardening before production.

### 7.5 Architecture Layer (VSpace, TLB, Cache, PageTable, ARMv8, ASID, Exceptions, Interrupts, Timer, Decode)

Scope: `SeLe4n/Kernel/Architecture/*`.

**CRITICAL:**

- **[A-C01] `AsidPool.allocate` rollover blindly returns ASID 1, potentially reusing an active one** — `AsidManager.lean:116–122`. When `nextAsid = maxAsidValue` and free list empty, `allocate` unconditionally returns `ASID.mk 1`; the generation counter is never consulted. `asidPoolUnique` is deferred to the "caller's integration layer" — `allocate` itself can return a duplicate ASID, breaking TLB isolation. *Remediation:* track active ASID set inside the pool; rollover must fail until all ASIDs are released via `free`, or flip generation + full-TLB flush assertion atomically.

**HIGH:**

- **[A-H01] `ARMv8VSpace.mapPage` does not enforce W^X** — `VSpaceARMv8.lean:169–189`. The ARMv8 backend delegates to `VSpaceRoot.mapPage` (no `wxCompliant` check either) and encodes via `fromPagePermissions` without gating. Only the `vspaceMapPage` wrapper (`VSpace.lean:101`) enforces W^X. A direct `VSpaceBackend.mapPage` call on the production instance can install W+X, silently breaking `wxExclusiveInvariant`. *Remediation:* add `if !perms.wxCompliant then none` at the top of `ARMv8VSpace.mapPage` and mirror in `VSpaceRoot.mapPage`.
- **[A-H02] `interruptDispatchSequence` suppresses EOI for 224–1019 INTIDs** — `InterruptDispatch.lean:127–137`. Every `acknowledgeInterrupt = none` (including out-of-range 224–1019) is treated as spurious and skips EOI. On hardware erratum or SMP path returning such IAR, GIC locks up — the exact condition AI2-A set out to prevent. *Remediation:* differentiate spurious (`≥ 1020`) from out-of-range and emit EOI on the latter.
- **[A-H03] `AsidPool.allocate` does not bump `generation` on free-list reuse** — `AsidManager.lean:99–103`. Reuse sets `requiresFlush := true` but `generation` is untouched; downstream stale-entry tracking via generation is broken. *Remediation:* bump `generation` on reuse or drop the field and rely purely on `requiresFlush`.

**MEDIUM:**

- **[A-M01] `decodeVSpaceMapArgs` missing PA bounds check** — `SyscallArgDecode.lean:201–225`. `paddr := PAddr.ofNat r2.val` without `< 2^physicalAddressWidth` check; dispatch-level enforcement is inconsistent. *Remediation:* parameterize decode by `maxPA = 2^physicalAddressWidth`.
- **[A-M02] `validateIpcBufferAddress` only checks starting PA bound** — `IpcBufferValidation.lean:74–82`. 512-byte buffer at `[2^width−512, 2^width)` passes validation but extends beyond PA window. *Remediation:* strengthen to `paddr.toNat + ipcBufferAlignment ≤ 2^width`.
- **[A-M03] `fromPagePermissions` lacks W^X precondition** — `VSpaceARMv8.lean:137–149`. Under `execute=true, write=true, user=true` produces `ap=.rwAll, uxn=false` → W+X user page on hardware. *Remediation:* return `Option` and reject W+X.
- **[A-M04] Cache model does not enforce D-cache→I-cache ordering** — `CacheModel.lean:294–296`. `pageTableUpdate_icache_coherent` uses `icInvalidateAll` only; required DSB between DC CIVAC and IC IALLU is not modeled (L:286–292). `dcZeroByVA` creates dirty lines without mandatory clean. *Remediation:* add `BarrierKind`-indexed sequencing predicate requiring DC+IC pairing with barrier token for executable-remap.
- **[A-M05] `HardwareTimerConfig` permits `countsPerTick = 0`** — `TimerModel.lean:55–65`. If DT-provided freq × interval < 10⁹, timer never advances. Only sanity check is `rpi5TimerConfig_countsPerTick = 54000`. *Remediation:* add `positive` field or refutation theorem; fail boot via `configTimeSlicePositive`-style guard.
- **[A-M06] `tlbBarrierComplete := True` — barrier completeness is trivially True** — `TlbModel.lean:398–407`. Every `*_barrier_complete` theorem proven by `trivial`. *Remediation:* bind to a `tlb.lastBarrierCompleted : Bool` field toggled by Rust HAL.
- **[A-M07] `decodeSchedContextConfigureArgs` has no validation** — `SyscallArgDecode.lean:958–966`. Raw `r4.val` assigned to `domain` with no `< 16` check; priority/budget/period unconstrained. *Remediation:* mirror `decodeSetPriorityArgs` bounds.
- **[A-M08] `writeUInt64`/`readUInt64` don't model MMU/Device-memory ordering** — `VSpaceARMv8.lean:95–103; PageTable.lean:349–359`. `simulationRelation` assumes hardware walker sees same memory as `pageTableMemory` — false without DSB ISHST after descriptor writes. *Remediation:* pair with `BarrierKind.ishst` token; emit `dsb ishst` in FFI.
- **[A-M09] `ensureTable` zero-page coherency** — `VSpaceARMv8.lean:152–165`. Allocated page linked without cache-cleaning; walker may see stale D-cache lines. *Remediation:* `dcCleanInvalidate` of zeroed range before `.table` descriptor publication.
- **[A-M10] `endOfInterrupt` is identity — no audit trail for missing EOI** — `InterruptDispatch.lean:81–82`. No way to detect missing EOI at proof layer. *Remediation:* add `eoiPending : HashSet InterruptId` to `SystemState`, prove empty at kernel-exit.

**LOW:** `exceptionLevelFromSpsr` collapses EL2/EL3 → EL1 (L-1); `memoryMap.find?` returns first match — overlapping regions defeat device-vs-RAM check (L-2); hardcoded MAIR indices (L-3); `acknowledgeInterrupt` silent truncation (L-4); `decodeCapPtr.isWord64Dec` proof-level invariant (L-5); timer 64-bit wrap horizon unmodeled (L-6); `contextSwitchState` doesn't touch TLB/ASID (L-7); `BumpAllocator` off-by-one at end (L-8); `validateIpcBufferAddress` page-granularity dependency (L-9).

**INFO:** No `sorry`/`axiom`/`native_decide`/`partial` in any of 17 Architecture files; round-trip theorems for all decoders; `AdapterProofHooks.preserveReadMemory` is no-op.

**Health notes:** Biggest RPi5 bring-up exposures: (1) ASID correctness (A-C01 rollover + A-H03 generation); (2) W^X only enforced at `vspaceMapPage` wrapper, not typeclass level (A-H01 + A-M03); (3) GIC EOI suppression (A-H02) — easy fix, material risk reduction. TLB/cache composition gaps (A-M04/A-M06/A-M08/A-M09) deferred to WS-V but worth upgrading `tlbBarrierComplete` to substantive state before end-to-end trust. SyscallArgDecode otherwise thorough; `decodeSchedContextConfigureArgs` and PA bounds (A-M07/A-M01) are unfinished.

### 7.6 Information Flow & SchedContext (CBS)

Scope: `SeLe4n/Kernel/InformationFlow/*`, `SeLe4n/Kernel/SchedContext/*`.

**HIGH:**

- **[NI-H01] `niStepCoverage` witness uses state-identity NI constructor — discoverability-only, not semantic coverage** — `InformationFlow/Invariant/Composition.lean:884–900`. The "coverage" theorem witnesses an NI step for each `KernelOperation` using `syscallDecodeError rfl`; it does NOT prove each op's real semantics preserve projection. *Remediation:* replace stub witness with operational mapping, or rename theorem to clarify discoverability-only scope.
- **[NI-H02] `syscallDispatchHigh` discharges projection preservation via unproven hypothesis for `dispatchCapabilityOnly` arms** — `InformationFlow/Invariant/Composition.lean:295–299` + `API.lean:1886–1898`. The `hProj` caller hypothesis is required for `suspendThread`, `resumeThread`, `setPriorityOp`, `setMCPriorityOp`, `setIPCBufferOp`, `schedContextConfigure`, `schedContextBind`, `schedContextUnbind`, `vspaceMapPage`/`Unmap`, `revokeService` — no in-kernel `*_preserves_projection` theorem discharges it. The advertised 11/11 enforcement bridge does not cover these. *Remediation:* prove `dispatchCapabilityOnly_preserves_projection` end-to-end for each arm.
- **[SC-H01] `validateSchedContextParams` does not enforce `budget > 0`** — `SchedContext/Operations.lean:51–57, 90–114`. When `budget = 0`, `schedContextConfigure` stores `replenishments := [{amount := ⟨0⟩, ...}]`, VIOLATING `replenishmentListWellFormed` (`Invariant/Defs.lean:54–56`: `∀ r, r.amount.val > 0`). Breaks `schedContextWellFormed`. *Remediation:* reject `budget == 0` with `.invalidArgument`.

**MEDIUM:**

- **[NI-M01] `projectKernelObject` does not strip `pendingMessage`/`timedOut` from TCBs** — `InformationFlow/Projection.lean:185–228` + `Model/Object/Types.lean:570`. Both fields survive projection and can differ after cross-domain IPC/timeout — open covert channel. AH5-A acknowledged `pendingMessage` as "unreachable under invariants" and deferred proof; `timedOut` (AG8-A) has no justification. *Remediation:* strip both in `.tcb` arm of `projectKernelObject`.
- **[NI-M02] `defaultLabelingContext_valid` discharges coherence trivially — default context is deployable** — `Policy.lean:220–226` + `Composition.lean:740–751`. The `publicLabel`-everything default labeling satisfies `LabelingContextValid`. The `isInsecureDefaultContext` multi-probe (AJ2-C) can be evaded by overriding one of `[0,1,42]`. *Remediation:* strengthen `LabelingContextValid` to require ≥2 distinct labels actually used; compile-time rejection in production.
- **[SC-M01] `schedContextConfigure` preservation uses diverging helper** — `SchedContext/Invariant/Preservation.lean:60–82` + `Operations.lean:109`. `applyConfigureParams` leaves `replenishments` untouched; the real op REPLACES with `[{amount := ⟨budget⟩, eligibleAt := st.machine.timer}]`. End-to-end `schedContextWellFormed` preservation is never proven for the concrete transition. *Remediation:* prove `schedContextConfigure_preserves_schedContextWellFormed` against the real post-state.
- **[SC-M02] `schedContextConfigure` sets `eligibleAt := st.machine.timer` — double-budget window** — `Operations.lean:109`. The new replenishment is eligible at the CURRENT tick, so the reconfigured SC gets `budgetRemaining := budget` PLUS an immediately-eligible replenishment of size `budget`. *Remediation:* use `eligibleAt := st.machine.timer + period.val`.
- **[SC-M03] `schedContextYieldTo` has no self-yield guard** — `Operations.lean:261–290`. `yieldTo st id id` zeros source then writes target; HashMap ordering decides the final state. *Remediation:* early return on `fromScId == targetScId`.
- **[SC-M04] CBS bandwidth bound is 8× loose** — `SchedContext/Invariant/Defs.lean:78–100`. `cbs_bandwidth_bounded` proves `totalConsumed ≤ 8 × budget`; tight bound is `budget × ⌈window / period⌉`. Acknowledged AF-08 but marketing-grade CBS isolation is weaker than expected. *Remediation:* prove the tight bound or add prominent admission-time caveat.

**LOW:** `endpointReplyChecked` flow check assumes `target == caller` without invariant (NI-L1); `endpointReplyRecvChecked` non-atomicity comment (NI-L2); four accepted U6-K covert channels require production warning (NI-L3); `processReplenishments` lump-sum cap discards over-cap refills (SC-L1); `ReplenishQueue.insert` no idempotence for duplicate `scId` (SC-L2); `getCurrentPriority` silent fallback subtle invariant dependency (SC-L3); `cspaceMint` NI does not hypothesize on `badge` (NI-L4).

**INFO:** 11-wrapper enforcement coverage complete; `ReplenishQueue` sort-/length-/consistency-preservation tight; `cbs_single_period_bound` sound; no `sorry`/`axiom`/`native_decide`/`partial`.

**Health notes:** Enforcement layer (11 checked wrappers) is rigorous, but NI layer has two structural gaps — vacuous `niStepCoverage` witness + unproven `hProj` for all `dispatchCapabilityOnly`-routed arms — plus the `pendingMessage`/`timedOut` projection leakage. The default labeling is trivially valid, a latent production risk. CBS engine is solid per-object but has a zero-budget hole, a divergent preservation helper, and a mis-computed `eligibleAt` window on reconfigure.

### 7.7 Data Structures (RobinHood, RadixTree, FrozenOps) & Top-Level (API, CrossSubsystem)

Scope: `SeLe4n/Kernel/RobinHood/*`, `SeLe4n/Kernel/RadixTree/*`, `SeLe4n/Kernel/FrozenOps/*`, `SeLe4n/Kernel/API.lean`, `SeLe4n/Kernel/CrossSubsystem.lean`.

**HIGH:** None.

**MEDIUM:**

- **[DS-M01] FrozenOps `frozenStoreTcb` bypass typing gap** — `FrozenOps/Core.lean:135–157` + `Operations.lean:333, 358, 369, 398, 405, 415, 445, 453, 465, 490`. `frozenStoreObject` uses `FrozenMap.set` which checks only key membership, not variant tag. A caller with a `ThreadId` whose `.toObjId` aliases an endpoint slot silently overwrites. `typedIdDisjointness` (`CrossSubsystem.lean:283`) is trivial by function-injectivity and does NOT prevent wrapper collisions on the same ObjId. Not reachable from production. *Remediation:* pre-check via `frozenLookupTcb` before storing, or use a type-indexed primitive.
- **[DS-M02] FrozenOps `frozenSchedContextUnbind` partial mutation** — `Operations.lean:683–699`. On failed bound-thread lookup, SC side is written (`boundThread := none, isActive := false`) but TCB binding never cleared. Contradicts AE2-D two-phase validate-then-write pattern. Not in production. *Remediation:* hoist validation into pre-check phase.
- **[DS-M03] `CNodeRadix` silent aliasing via unchecked build path** — `RadixTree/Core.lean:100–131` + `Bridge.lean:44–54`. `extractBits slot.toNat 0 radixWidth = slot.toNat % (2^radixWidth)` — distinct slots sharing low bits map to same array entry. `buildCNodeRadix_lookup_equiv` requires `UniqueRadixIndices` + `hNoPhantom` preconditions not enforced by the public `buildCNodeRadix`. `freezeCNodeSlots` uses the unchecked variant. *Remediation:* redirect to `buildCNodeRadixChecked`.
- **[DS-M04] `RHTable.BEq` not `LawfulBEq`-proven; propagates non-lawful value BEq** — `RobinHood/Bridge.lean:43–53`. Downstream callers requiring `LawfulBEq` would silently lose reflexivity proof; `BEq β` without `LawfulBEq β` can return `false` on structural equality. *Remediation:* document non-lawful assumption or gate on `[LawfulBEq β]`.

**LOW:** `extractBits` public `offset` parameter (L-1); `insertNoResize` fuel-exhaustion silent failure (L-2); `RHTable.erase` `Nat` size saturation (L-3); RH `Inhabited` default allocates 16 slots (L-4); multiple 400K–800K heartbeat proofs (L-5); `resolveExtraCaps` silent drop (documented seL4-compatible) (L-6); wildcard unreachability theorem manually enumerates 25 variants (L-7); `ofList` uses resizing `insert` (L-8); FrozenOps hardcoded `priority > 255`/`domain ≥ 16` (L-9); `typedIdDisjointness` trivially true — documents rather than asserts injectivity across wrapper types (L-10); `RHTable.BEq` dual-fold (L-11).

**INFO:** `RHTable.empty_wf` etc. structurally sound on empty; `hCapGe4` structurally enforced; FrozenOps confirmed NOT in production import chain (only 5 test suites); wildcard unreachability theorems cover all 25 `SyscallId` variants for both `dispatchWithCap` and `dispatchWithCapChecked`; hashing is deterministic (all `Hashable` instances go through `.val : Nat`); 10-predicate `crossSubsystemInvariant` 45-pair composition complete.

**Health notes:** RobinHood mature and proof-expensive (2500-line preservation suite); `4 ≤ capacity` closes U-28. Weakest spot: `insertNoResize` silent drop on fuel exhaustion under non-invariant states. RadixTree has 24 proofs; `extractBits` mod-reduction is main hazard. FrozenOps is test-only and correctly isolated. API.lean dispatch wiring tight with machine-checked wildcard unreachability. CrossSubsystem 10-predicate bundle structurally complete.

### 7.8 Platform (Boot, DTB, Sim, RPi5, FFI) & Testing

Scope: `SeLe4n/Platform/*`, `SeLe4n/Testing/*`, `Main.lean`, `SeLe4n.lean`.

**HIGH:**

- **[P-H01] MMIO adapter missing width-specific reads with alignment check** — `RPi5/MmioAdapter.lean:358`. Only 8-bit `mmioRead` exists; no `mmioRead32`/`mmioRead64` with `isAligned` guards. GIC-400 / BCM2712 device registers require word-aligned word-sized reads on ARM64; byte-read of GIC register is hardware-undefined. Write-side has alignment guards; reads do not. *Remediation:* add `mmioRead32`/`mmioRead64` with `isAligned` checks; restrict byte-`mmioRead` to debug/UART.
- **[P-H02] `objectStoreNonEmpty` field name inverted vs semantics** — `Sim/BootContract.lean:70` + `RPi5/BootContract.lean:57`. Both define `objectStoreNonEmpty := (default : SystemState).objects.size = 0` — the field asserts the OPPOSITE of its name. Compiles cleanly; downstream consumers will misread the specification. *Remediation:* rename to `objectStoreEmptyAtBoot` (or flip predicate and rename consistently).

**MEDIUM:**

- **[P-M01] `bootFromPlatformChecked` does not validate IRQ→handler references** — `Boot.lean:493–503`. Checked boot validates `wellFormed` + `bootSafeObjectCheck` but not that each `IrqEntry.handler` ObjId refers to a notification present in `initialObjects` (StateBuilder's check #5 covers this at runtime only). *Remediation:* add handler-existence check.
- **[P-M02] MMIO multi-byte write range check not region-local** — `MmioAdapter.lean:406, 434, 508`. `isDeviceAddress addr && isDeviceAddress (addr+N)` validates endpoints individually; adjacent device regions could be spliced at boundary by aligned 4/8-byte write. Currently unreachable on RPi5 layout, but not structurally sound. *Remediation:* use `findMmioRegion addr`, require `addr+N ≤ region.endAddr` in a single region.
- **[P-M03] `registerContextStableCheck` budget branch fails-open** — `RPi5/RuntimeContract.lean:78–84`. `budgetSufficientCheck` returns `true` for `schedContextBinding = .bound scId` when store has wrong variant or `none` → context switch into missing/corrupted SC passes stability check. *Remediation:* return `false` for non-`schedContext`/`none` lookups when bound.
- **[P-M04] `classifyMemoryRegion` defaults to `.ram` with empty platform map** — `DeviceTree.lean:326–330`. Firmware-declared reserved region could silently be admitted as RAM. *Remediation:* require non-empty map or default to `.reserved`.
- **[P-M05] `applyMachineConfig` copies fields blindly without validation** — `Boot.lean:159–169`. No `pageSize` power-of-two check; no `physicalAddressWidth ≤ 52` cap; no machine-config `wellFormed` gate. *Remediation:* reject on `wellFormed = false`.
- **[P-M06] Interrupts default-disabled post-boot; Lean model never re-enables** — `Boot.lean:1049` + AJ3-E. Rust HAL AG5 re-enables at Phase 3, but Lean model stays disabled — Lean-vs-HAL state divergence. *Remediation:* add an `enableInterrupts` builder step mirroring Phase 3.
- **[P-M07] `findMemoryRegProperty` fuel 1000 — silent failure on large DTBs** — `DeviceTree.lean:513–515`. Fuel unvalidated vs `blob.size`. *Remediation:* compute fuel from `hdr.sizeDtStruct / 4` and propagate explicit `fuelExhausted`.

**LOW:** `StateBuilder.buildChecked` uses `panic!` (L-1); `readCString` fuel 256 silent truncation (L-2); `physicalAddressWidth` unbounded (L-3); `extractPeripherals` 2-level silent skip (L-4); MMIO ops lack interrupts-disabled guard (L-5); `buildValidated` returns unstructured strings (L-6); `mmioRegionDisjointCheck` only RAM vs MMIO (L-7); O(n²) boot IRQ scan (L-8); `bootSafeObject` excludes VSpaceRoots tracked WS-V (L-9); `registerContextStableCheck` ignores pre-state (L-10); FFI `opaque BaseIO` has no contract bridging (L-11); `mmioWrite` unchecked against W1C region kind (L-12); touching-regions fragility (L-13).

**INFO:** `MainTraceHarness` emits deterministic 225-line fixture trace via 252 `IO.println`; no `reprStr`/pointer-address leaks; no `sorry`/`axiom`/`native_decide`/`partial`/`unsafe`; BCM2712 constants cross-checked to TRM; RPi5 runtime contract substantive (6-conjunct), Sim permissive all-True; AI5-A/B substantive Sim boot contracts; boot pipeline preserves all four invariant witnesses.

**Health notes:** Platform layer is structurally sound; production contracts substantive; MMIO writes enforce alignment. Main release-blockers are asymmetry in MMIO read vs write alignment (P-H01), the inverted-semantics `objectStoreNonEmpty` field (P-H02), and `registerContextStableCheck` fallthrough (P-M03). FFI boundary (L-11) and VSpaceRoot boot exclusion (L-9) are known deferrals to WS-V/AG10.

---

## 8. Rust Implementation Notes

### 8.1 `sele4n-hal` (Hardware Abstraction Layer)

Scope: `rust/sele4n-hal/src/*` (~3,900 LOC — boot, UART, MMIO, MMU, GIC, timer, interrupts, barriers, CPU, FFI, profiling, TLB, cache, trap, vectors).

**HIGH:**

- **[R-HAL-H01] `BOOT_L1_TABLE` is still `static mut` after AJ5-B** — `mmu.rs:110`. UART was migrated to `UnsafeCell`+spinlock but `BOOT_L1_TABLE` remains raw `static mut` with `&raw mut` access. Same soundness class eliminated for UART; warns under future Rust editions. The dedicated `.bss.page_tables` link-section is unused. *Remediation:* wrap in `PageTableCell(UnsafeCell<PageTable>); unsafe impl Sync` mirroring `UartInner`, or use `#[link_section]`.
- **[R-HAL-H02] MMU enable sequence lacks TLB flush + D-cache clean of page tables** — `mmu.rs:162–181`. `enable_mmu` writes TTBR then DSB ISH + ISB + SCTLR without (a) `tlbi vmalle1` to invalidate stale translations (D8.11 requires before enable if TLB not known clean), (b) `dc cvac`/`dc civac` of page-table pages (required on boot where D-cache was disabled). On warm reset stale entries persist. *Remediation:* `cache::clean_range(&BOOT_L1_TABLE, +size)` + `tlb::tlbi_vmalle1()` before DSB ISH + ISB + SCTLR.
- **[R-HAL-H03] SCTLR_EL1 write does not set WXN/SA/EOS** — `mmu.rs:175–177`. Only M/C/I are OR'd in. WXN=0 means HW does not enforce W^X; Lean model proves it but defense-in-depth should set WXN=1. Alignment checking (SA) state is reset-dependent. *Remediation:* write full SCTLR_EL1 bitmap (WXN=1, SA=1, SA0=1, M=1, C=1, I=1, EOS=1, EIS=1) rather than OR-accumulating.
- **[R-HAL-H04] `TrapFrame` does not save ESR_EL1 / FAR_EL1** — `trap.S:154–157, 162–166`. `save_context` saves only ELR/SPSR/SP_EL0 + GPRs (272 bytes). `handle_synchronous_exception` reads ESR_EL1 live from system register — correct for outer exception, stale on nested. FAR_EL1 never preserved. CLAUDE.md scope list calls these out explicitly. *Remediation:* extend TrapFrame to 288 bytes + adjust asm, or enforce no-nested with debug check.
- **[R-HAL-H05] IRQ handler panic skips EOI → GIC lockup** — `trap.rs:220–233` + `gic.rs:305`. `dispatch_irq` sends EOI only after handler returns; if `reprogram_timer()`/`kprintln!` panics, unwind skips EOI → GIC deadlock on that INTID forever. AI2-A addressed error paths but not panic. *Remediation:* scope-exit guard ensuring EOI always fires; confirm workspace `panic = "abort"`.

**MEDIUM:**

- **[R-HAL-M01] Cargo profile `panic = "abort"` unverified** — workspace-root profiles not confirmed. `no_std` + unwinding = UB. *Remediation:* verify / add.
- **[R-HAL-M02] `boot.S:22–25` core affinity check uses only Aff0** — on BCM2712 multi-cluster, Aff1 distinguishes clusters; core (Aff1=1, Aff0=0) would pass. *Remediation:* mask `(mpidr & 0xFF00FF)` or full MPIDR Aff{3,2,1,0}.
- **[R-HAL-M03] `BOOT_L1_TABLE` → TTBR conversion via `&raw const` cast** — `mmu.rs:165`. VA==PA under identity map; if image relocated, TTBR gets VA not PA. No BAADDR mask applied. *Remediation:* mask `& 0xFFFF_FFFF_FFFE` + boot-time assert.
- **[R-HAL-M04] GIC driver shadows `mmio_read32`/`mmio_write32` bypassing AJ5-A alignment assert** — `gic.rs:102–133`. *Remediation:* use `crate::mmio::*`.
- **[R-HAL-M05] PL011 UART MMIO bypasses alignment assert** — `uart.rs:66–82`. *Remediation:* route through `crate::mmio::*` or add `debug_assert!`.
- **[R-HAL-M06] `dispatch_irq` Spectre v1 — handler indexing under attacker-influenced INTID** — `gic.rs:291–307`. Current handler only compares `intid == TIMER_PPI_ID`; safe. Future table-lookup handlers must re-apply CSDB. *Remediation:* document invariant in closure docstring.
- **[R-HAL-M07] `init_timer` silently falls back when CNTFRQ_EL0 == 0** — `timer.rs:158–160`. Wrong tick rate corrupts WCRT bound. *Remediation:* return `TimerError::CntfrqNotProgrammed` on aarch64.
- **[R-HAL-M08] `cache_range` empty-range early return skips DSB ISH** — `cache.rs:150–164`. *Remediation:* drop early return or document empty=no-op.
- **[R-HAL-M09] `current_core_id` only masks Aff0** — `cpu.rs:79–89`. Same as M-02. *Remediation:* full MPIDR or cluster+core mask.
- **[R-HAL-M10] `init_with_baud(0)` divide-by-zero reachable** — `uart.rs:101–109`. *Remediation:* `assert!(baud > 0)` or `pub(crate)`.
- **[R-HAL-M11] FFI functions lack `catch_unwind` — panic over ABI boundary is UB** — `ffi.rs:30–49, 66–86`. Lean → Rust crossing a panic is UB; AJ5-A runtime `assert!` in MMIO can panic. *Remediation:* catch panics at boundary (requires `panic = "abort"` workspace-wide as minimum).
- **[R-HAL-M12] SError handler has `-> ()` but body loops — fall-through emits dead `eret`** — `trap.S:125–148` + `trap.rs:239`. *Remediation:* make signature `-> !` and `b .` after `bl` in asm.

**LOW:** SError signature not `-> !` (L-1); `__exception_vectors` declared as `u8` (L-2); non-`const` `div_ceil` (L-3); GIC SPI banks range comment (L-4); spinlock backoff absent (L-5); DAIF reserved-bit write (L-6); MAIR comment fragile (L-7); `dc_zva` missing `preserves_flags` (L-8); `TICK_COUNT` re-init on dual `init_timer` (L-9); misleading saturated-mean docstring (L-10); hard-coded `GICC_BASE` (L-11); `Ordering::Relaxed` tick (SMP-unready) (L-12); SB-encoded SB confirmation (L-13); SVC `_syscall_id` bindings unused TODO (L-14); secondary-core wake-storm risk (L-15); SP0 vector stub silently hangs (L-16).

**INFO:** `KERNEL_VERSION = "0.29.0"` (AH4-A); `const _: () = assert!(TRAP_FRAME_SIZE == 272)` enforces layout invariant; no `todo!`/`unimplemented!` in production; all `unsafe` blocks have ARM-ARM SAFETY comments; AJ5-A/B/C/D, AI1-A/B/C/D, AI2-A, AH4-A all verified in place.

**Health notes:** Well-structured, disciplined SAFETY annotations, recent remediation phases AI1/AJ5 solid. Main release-blockers: TLB flush + D-cache clean before MMU enable (R-HAL-H02), WXN not set (R-HAL-H03), `BOOT_L1_TABLE` `static mut` (R-HAL-H01), missing ESR/FAR in `TrapFrame` vs docs (R-HAL-H04), panic-before-EOI (R-HAL-H05). Multi-core affinity check too narrow. FFI panic discipline (M-11) must be locked in before hardware boot.

### 8.2 `sele4n-types` / `sele4n-abi` / `sele4n-sys` (ABI Crates)

Scope: `rust/sele4n-types/*`, `rust/sele4n-abi/*`, `rust/sele4n-sys/*` (~5,850 LOC).

**CRITICAL:**

- **[R-ABI-C01] `service_register` and `sched_context_configure` encode MR[4] into IPC buffer overflow slot, but the Lean kernel model only decodes 4 inline msgRegs — both syscalls fail decoding** — `rust/sele4n-sys/src/service.rs:40` + `sched_context.rs:49` vs `SeLe4n/Machine.lean:848` (`arm64DefaultLayout.msgRegs := #[⟨2⟩, ⟨3⟩, ⟨4⟩, ⟨5⟩]`) and `SeLe4n/Kernel/Architecture/RegisterDecode.lean:109–125` (`decodeSyscallArgs` populates `msgRegs` from `layout.msgRegs` only — no IPC-buffer merge). Meanwhile `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean:958–966` (`decodeSchedContextConfigureArgs`) and `:775–786` (`decodeServiceRegisterArgs`) BOTH require `requireMsgReg decoded.msgRegs 4` — i.e. 5 entries. `decodeServiceRegisterArgs_error_iff` theorem proves decode fails iff `msgRegs.size < 5`. `arm64DefaultLayout` produces `msgRegs.size = 4`. **Both syscalls will return `.error .invalidMessageInfo` on every invocation against the production Lean kernel.** The Rust wrapper comments (`service.rs:16–20`, `sched_context.rs:22–25`) claim the Lean side reads MR[4] from the IPC buffer, but no such merge exists. *Remediation:* add a `decodeSyscallArgs` step that merges IPC-buffer overflow slots into `msgRegs` when `msgInfo.length > layout.msgRegs.size`, OR shrink both affected syscalls to ≤4 inline args, OR extend `arm64DefaultLayout.msgRegs` to include x6/x7. Update affected round-trip theorems.

**HIGH:**

- **[R-ABI-H01] `SchedContextId` absent from Rust type layer** — `sele4n-types/src/identifiers.rs`. Lean has `SchedContextId` (`Prelude.lean:412`) with `.sentinel` + `ofObjIdChecked` (AF-22) but Rust uses raw `u64`. `SchedContextBindArgs.thread_id` and `sched_context_bind(thread_id: u64)` all use raw `u64` where a typed ID should exist. *Remediation:* add `SchedContextId(pub(crate) u64)` mirroring the Lean newtype.
- **[R-ABI-H02] Lean vs Rust decode validation divergence — `service_register`** — `sele4n-abi/src/args/service.rs:48–71` vs Lean `decodeServiceRegisterArgs` (`SyscallArgDecode.lean:775–786`). Lean uses `requiresGrant := r4.val != 0` (any-nonzero) and does NOT bound `methodCount`/`maxMessageSize`/`maxResponseSize`; Rust rejects non-bool (2..u64::MAX) with `InvalidMessageInfo` and rejects overflows with `InvalidArgument`. Divergent acceptance surfaces in both directions. *Remediation:* align Lean to reject out-of-range (authoritative direction).

**MEDIUM:**

- **[R-ABI-M01] `SchedContextConfigureArgs::decode` tighter than Lean** — `sele4n-abi/src/args/sched_context.rs:39–44` validates `priority ≤ 255`, `domain ≤ 15`; Lean (`SyscallArgDecode.lean:958–966`) accepts any `u64`. *Remediation:* lift validation into Lean decode.
- **[R-ABI-M02] `CSpaceMintArgs::decode` rejects rights > 0x1F; Lean silently masks** — `cspace.rs:32–45` vs `SyscallArgDecode.lean:140–149`. Same pattern in `PagePerms`/`VSpaceMapArgs`. *Remediation:* align Lean to reject out-of-range.
- **[R-ABI-M03] `VSpaceMapArgs::decode` weaker than Lean** — `vspace.rs:35–44`. Lean checks ASID-in-config, VAddr canonicity, W^X; Rust only PagePerms 5-bit. *Remediation:* add matching checks or document.
- **[R-ABI-M04] `IpcBuffer::set_mr(0..3)` returns `Ok(false)` while `get_mr(0..3)` returns `Err`** — `ipc_buffer.rs:82–92`. Asymmetry documented (W6-H) but surprising and easy to misuse in `?`-propagating callers. *Remediation:* rename or add `set_mr_overflow`.

**LOW:** `lifecycle.rs:14` docstring missing `6=SchedContext` (L-1); `sele4n-types/src/lib.rs:6` says "14 newtype identifiers" but actually 15 (L-2); `RegisterFile` exported but effectively unused (L-3); `ServiceQueryArgs` empty struct defined but never used (L-4); `trap.rs:49` `lateout("x6") _` redundant with `clobber_abi("C")` (L-5); constants duplicated across 3 crates (L-6); `ThreadId::SENTINEL` vs `CPtr::NULL` naming inconsistency (L-7); `Hash` derive on 0-sentinel-overlapping typed IDs (documented AJ2-D) (L-8).

**INFO:** `KernelError` verified 1:1 against Lean (49 variants + `UnknownKernelError = 255` AF-20 sentinel); `SyscallId` 1:1 across 25 variants; `TypeTag` 1:1 across 7; single `unsafe` block in `trap.rs` (AAPCS64-gated, SAFETY-commented); `IpcBuffer` compile-time layout asserts (960 bytes, 8-byte aligned); all 25 syscall wrappers present; `Cap<Obj, Rts>` sealed traits; `#![deny(unsafe_code)]` across all three crates; Cargo workspace + lock all at 0.29.0.

**Health notes:** Type-level ABI (discriminants, bit layouts, constants, enum ordering) is tightly synchronized with the Lean model via compile-time asserts and cross-validation tests. Primary concern is **semantic drift at the decode boundary**: Rust decoders systematically tighten input validation while Lean decoders silently mask or accept wider ranges. The R-ABI-C01 finding — `service_register`/`sched_context_configure` write MR[4] into IPC-buffer but Lean model only decodes 4 inline msgRegs — appears to render both syscalls non-functional against the production Lean kernel and should be verified by adding an integration test that encodes via the sys wrapper and decodes via the Lean kernel. Missing `SchedContextId` newtype is a defense-in-depth gap. Otherwise rigorously audited.

---

## 2. Finding Summary

**Aggregate counts across the entire codebase (10 subsystems):**

| Severity | Count |
|----------|-------|
| CRITICAL | 2 |
| HIGH | 23 |
| MEDIUM | 68 |
| LOW | 108 |
| INFO | Many (contextual) |

### CRITICAL:

1. **A-C01** — `AsidPool.allocate` rollover blindly returns ASID 1, potentially reusing active ASID; `asidPoolUnique` not preserved by `allocate`. Breaks TLB isolation on hardware. *(Architecture)*
2. **R-ABI-C01** — `service_register` and `sched_context_configure` Rust wrappers write their 5th argument to IPC buffer MR[4], but the Lean kernel's `arm64DefaultLayout` only decodes 4 inline msgRegs and `decodeSyscallArgs` has no IPC-buffer merge step. Both syscalls will fail decoding with `.invalidMessageInfo` against the production Lean kernel. *(Rust ABI vs Lean decode)*

### HIGH (23):

- Foundational (2): F-H01 FrozenMap indexMap unbounded growth; F-H02 apiInvariantBundle_frozenDirect observationally weak.
- Scheduler (4): S-H01 WCRT theorem schema; S-H02 PIP bound by fuel; S-H03 bound-thread re-enqueue at TCB priority; S-H04 schedulerPriorityMatch / effectiveParamsMatchRunQueue over-constrain.
- IPC (2): I-H01 cleanupPreReceiveDonation swallows errors; I-H02 endpointReply `blockedOnReply _ none` fail-open.
- Capability/Lifecycle/Service (0).
- Architecture (3): A-H01 ARMv8VSpace.mapPage no W^X; A-H02 EOI suppressed for 224–1019 INTIDs; A-H03 AsidPool.allocate no generation bump.
- InformationFlow/SchedContext (3): NI-H01 niStepCoverage vacuous; NI-H02 syscallDispatchHigh hProj unproven for dispatchCapabilityOnly arms; SC-H01 validateSchedContextParams no budget>0 check.
- Data Structures (0).
- Platform/Testing (2): P-H01 MMIO read no alignment check; P-H02 objectStoreNonEmpty field name inverted.
- Rust HAL (5): R-HAL-H01 static mut BOOT_L1_TABLE; R-HAL-H02 MMU enable lacks TLB+cache maintenance; R-HAL-H03 SCTLR WXN not set; R-HAL-H04 TrapFrame missing ESR/FAR; R-HAL-H05 IRQ panic skips EOI.
- Rust ABI (2): R-ABI-H01 SchedContextId absent; R-ABI-H02 Lean vs Rust service_register validation divergence.

### MEDIUM (68):

Distributed across all 10 subsystems. Highlights:

- Architecture TLB+cache+pagetable composition gaps (A-M04, A-M06, A-M08, A-M09).
- NI projection leakage of `pendingMessage`/`timedOut` (NI-M01) and trivially-valid `defaultLabelingContext` (NI-M02).
- SchedContext configure diverging preservation helper (SC-M01) and double-budget window (SC-M02).
- IPC receiver-state gap on rendezvous (I-M01, I-M02), PIP-wake coverage (I-M03), public fuel footgun in `ipcUnwrapCapsLoop` (I-M05).
- Boot-pipeline validation gaps: IRQ-handler existence (P-M01), MachineConfig unchecked fields (P-M05), fuel-unvalidated DTB (P-M07).
- Rust HAL boot/MMU/GIC/UART alignment and safety hardening items (12 total).
- Rust ABI decode validation divergence (R-ABI-M01..M04).

### LOW (108):

Documentation, naming, defensive code, fragile predicates, hardcoded constants — mostly deferrable to post-release hardening.

---

## 9. Cross-Cutting Analysis

### 9.1 sorry / axiom / native_decide hygiene

Verified via `Grep` across `SeLe4n/`: 8 matches for `\b(sorry|axiom|native_decide)\b` — **all 8 are explanatory comments** documenting prior removal of `native_decide` in favor of `decide`. **Zero actual `sorry`/`axiom`/`native_decide` in the production proof surface** (confirmed at line level across all 140 Lean modules).

### 9.2 Version synchronization

- `lakefile.toml` version: 0.29.0 ✓
- `rust/Cargo.toml` workspace version: 0.29.0 ✓
- `rust/sele4n-hal/src/boot.rs` `KERNEL_VERSION`: "0.29.0" ✓
- `scripts/check_version_sync.sh` (AH4-E) enforces this at CI.

### 9.3 Recurring structural themes

1. **Unbounded-`Nat` typed ID wrappers with `Inhabited ⟨0⟩`** — `ObjId`, `ThreadId`, `SchedContextId`, `CPtr`, `Slot`, `Badge` all share this pattern. Sentinel-zero is a convention-only defense; no type-level disjointness across wrapper types (see F-M03, F-M04, DS-M01, `typedIdDisjointness_trivial`).
2. **Fail-open defaults vs fail-closed discipline** — IPC reply `none` target (I-H02), AsidPool rollover (A-C01), budget-sufficient-check on missing SC (P-M03), `cleanupPreReceiveDonation` swallow (I-H01).
3. **Lean ↔ Rust validation drift** — Rust ABI systematically tighter than Lean decode (R-ABI-H02, R-ABI-M01, R-ABI-M02, R-ABI-M03). Both directions produce acceptance-surface drift; no cross-check test.
4. **Trivially-true predicates masking real obligations** — `tlbBarrierComplete := True` (A-M06); `typedIdDisjointness_trivial` (DS-L10); `noVirtualOverlap_trivial` (F-M10); `niStepCoverage` witness via `syscallDecodeError rfl` (NI-H01); `defaultLabelingContext_valid` (NI-M02).
5. **WCRT / PIP bounded-inversion are proof schemas, not closed liveness proofs** — S-H01 + S-H02. The release-grade claim "WCRT = D·L + N·(B+P)" is delegated to callers for two load-bearing hypotheses.
6. **Projection leaks post-freeze / post-projection** — F-H02 weak frozen-state invariant + NI-M01 `pendingMessage`/`timedOut` survive NI projection.

### 9.4 Hardware-binding readiness (RPi5)

**Not ready for first silicon bring-up without remediating:**

- **A-C01 ASID rollover** — without fix, TLB isolation can silently break.
- **A-H01/A-H02/A-H03** — W^X not enforced at backend; GIC EOI suppressed; ASID generation not bumped.
- **R-HAL-H01..H05** — MMU enable TLB/cache discipline; SCTLR WXN; trap frame missing ESR/FAR; panic-before-EOI.
- **R-ABI-C01** — two syscalls non-functional in current ABI encoding.

All five Architecture + HAL issues are pre-bring-up blockers.

### 9.5 Defense-in-depth observations

- W^X is enforced only at `vspaceMapPage` (Lean model) — Rust HAL does not set SCTLR.WXN, backend typeclass does not gate (A-H01, A-M03, R-HAL-H03). Three independent defenses should be layered.
- `private` constructor discipline is uneven — `MessageInfo.mk`, `AccessRightSet.mk` (now private), `IpcMessage.mk` all bypass validated constructors in some paths (F-M02, F-L13).
- Badge/CPtr `ofNatMasked` vs ABI-decode discrepancy — truncation in Lean, rejection in Rust (F-L02, R-ABI-M02).

### 9.6 Test coverage observations

- Fixture-backed evidence via `MainTraceHarness` is stable and deterministic (225-line expected).
- FrozenOps is confirmed test-only via import analysis — not in production chain.
- `DecodingSuite` / `BadgeOverflowSuite` / `LivenessSuite` cover AG9-E / T-03 decoders / liveness surface anchors.
- **Gap:** No end-to-end test encoding via `sele4n-sys` wrappers and decoding via the Lean kernel — would have caught R-ABI-C01 immediately.

---

## 10. Recommendations and Roadmap

### 10.1 Must-fix before v1.0 / hardware bring-up (CRITICAL + HIGH)

**Proposed WS-AK — Pre-1.0 Release Hardening**, 7 phases:

1. **AK1 — IPC fail-closed discipline.** Fix I-H01 (cleanupPreReceiveDonation) and I-H02 (reply `none` target), add unit test coverage.
2. **AK2 — Scheduler priority-bucket alignment.** Fix S-H03 (use `resolveInsertPriority` in yield/timerTick/switchDomain) and S-H04 (fuse priority-match predicates or enforce tcb=sc equality at bind/configure).
3. **AK3 — Architecture ASID + W^X + EOI.** Fix A-C01 (ASID rollover), A-H01 (ARMv8 W^X), A-H02 (EOI for 224–1019 INTIDs), A-H03 (generation bump on reuse).
4. **AK4 — ABI bridge.** Fix R-ABI-C01 (IPC buffer merge into `msgRegs` for `service_register`/`sched_context_configure`, or redesign signatures); fix R-ABI-H01 (typed `SchedContextId`), R-ABI-H02 (align Lean/Rust validation).
5. **AK5 — Rust HAL boot hardening.** Fix R-HAL-H01 through R-HAL-H05 (MMU enable TLB/cache, SCTLR WXN, BOOT_L1_TABLE soundness, TrapFrame ESR/FAR, panic-before-EOI).
6. **AK6 — NI projection + coverage.** Fix NI-H01 (niStepCoverage), NI-H02 (syscallDispatchHigh proof-carrying for dispatchCapabilityOnly arms), NI-M01 (project `pendingMessage`/`timedOut`).
7. **AK7 — SchedContext validation + preservation.** Fix SC-H01 (budget>0), SC-M01 (end-to-end configure preservation), SC-M02 (eligibleAt window).

### 10.2 Should-fix before v1.0 (selected MEDIUM)

- Platform: P-H01 MMIO read alignment, P-H02 field-name inversion (breaks spec readability), P-M03 budgetSufficientCheck fail-open.
- SchedContext: CBS bandwidth tight bound (SC-M04) or admission caveat.
- Architecture: A-M01 decodeVSpaceMap PA bounds; A-M02 IPC buffer upper PA bound.
- Data Structures: DS-M03 route `freezeCNodeSlots` through `buildCNodeRadixChecked`.

### 10.3 Post-release hardening roadmap

- **WS-V / AG10 (existing plan):** H3 hardware binding, TLB/cache composition, FFI contract bridging, VSpaceRoot boot support, CDT fuel sufficiency.
- **Proof hygiene pass:** Replace 17-deep tuple projections with named record (F-L09); reduce 400K-800K heartbeat proofs (DS-L5).
- **Sentinel-zero discipline:** Phantom-tag `ObjId` with `kind : ObjectKind`, disjoint sub-ranges per wrapper (F-M03, F-M04, DS-M01).
- **End-to-end encode/decode integration test** spanning `sele4n-sys` → Lean kernel (would have caught R-ABI-C01).

### 10.4 Assurance summary

The codebase is in a strong state, materially closer to release-grade than the v0.28.0 audit baseline. The WS-AJ remediation phases have closed a substantial fraction of prior findings, and the Lean proof surface remains free of `sorry`/`axiom`/`native_decide`. The principal gaps are localized and fixable:

- Two CRITICAL issues that are both correctness-bug-class (one silent ASID reuse, one silent syscall non-functionality) — remediable within a focused workstream.
- 23 HIGH findings concentrated around three categories: ABI bridge, proof-schema closure (WCRT/PIP/NI), and hardware binding (ASID/W^X/MMU/GIC).
- No evidence of systemic design flaws, no CVE-worthy exploit chains, and no evidence that documentation claims have been made in bad faith — most observed drift is the natural result of rapid iteration ahead of formal release.

The project is well-positioned for a tightly-scoped **WS-AK Pre-1.0 Hardening** workstream, after which v1.0 and RPi5 bring-up can proceed with high confidence.

---

*End of audit.*









