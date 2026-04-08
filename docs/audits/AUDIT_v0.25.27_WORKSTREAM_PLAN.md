# WS-AG Workstream Plan — v0.25.27 Release Audit Remediation

**Created**: 2026-04-08
**Baseline version**: v0.25.27
**Baseline audit**: `docs/audits/AUDIT_v0.25.27_RELEASE_COMPREHENSIVE.md`
**Prior portfolio**: WS-AF (v0.25.22–v0.25.27, 6 phases, 49 sub-tasks — COMPLETE)
**Workstream ID**: WS-AG
**Target version**: v0.26.x (pre-hardware-binding remediation)

---

## 1. Executive Summary

### 1.1 Audit Overview

The v0.25.27 Release Comprehensive Audit reviewed all 132 Lean modules and
30 Rust files across 10 parallel audit streams. It found **0 CRITICAL**,
**0 HIGH**, **19 MEDIUM**, and **25 LOW** findings. This workstream plan
addresses all actionable findings through a phased remediation strategy.

### 1.2 Finding Triage Summary

| Category | Count | Description |
|----------|-------|-------------|
| Actionable (code change required) | **7** | S-04, R-01, R-05, T-01, F-T02, S-05, F-F04 |
| Pre-Hardware deferred (H3 blocked) | **7** | F-S05, P-01, P-02, P-03, P-04, P-05, P-07 |
| Intentional design (no action) | **8** | C-03, C-07, A-01, IF-02, IF-03, SA-01, SA-02, S-06 |
| Already documented (no action) | **18** | F-ST02, F-B04, F-FP05, RT-05, FO-03, S-01–S-03, SA-03–SA-04, I-01, C-08, C-14, L-09, L-11, L-15, T-02, T-03 |
| Informational (no action) | **12** | A-02, A-07, IF-11, RH-02, RH-06, RT-03, FO-05, P-06, P-08, R-02, R-03, R-04 |
| Partially erroneous | **1** | F-T02 (see §2.2) |

### 1.3 Erroneous Finding Analysis

**F-T02 (LOW) — PARTIALLY ERRONEOUS.**
The audit states: "`Notification.waitingThreads : List ThreadId` has no `Nodup`
invariant. Duplicate entries would cause double-wakeup. The IPC invariant
`endpointQueueNoDup` covers endpoint queues but not notification wait lists
directly."

**Actual state:** The `uniqueWaiters` invariant at
`SeLe4n/Kernel/IPC/Invariant/Defs.lean:551` already enforces
`ntfn.waitingThreads.Nodup` for all notifications. Preservation proofs exist
for `notificationWait` (line 557) and `notificationSignal` (referenced at
line 689). The audit is correct that `endpointQueueNoDup` covers only endpoint
queues, but incorrect that no `Nodup` invariant exists for notification wait
lists.

**Remaining gap:** `uniqueWaiters` is NOT included in the 14-conjunct
`ipcInvariantFull` bundle (line 1084). It exists as a standalone invariant
with preservation proofs but is not composed into the main invariant hierarchy.
This is the actual actionable finding: **promote `uniqueWaiters` to
`ipcInvariantFull`** (making it a 15-conjunct bundle).

### 1.4 Plan Structure

| Phase | Name | Sub-tasks | Scope |
|-------|------|-----------|-------|
| AG1 | Scheduler Correctness | 7 | S-04 effective priority fix (4 call sites + helper + proofs), S-05 error handling |
| AG2 | Rust ABI Completion | 4 | R-01 sched_context wrappers, R-05 MAX_DOMAIN fix |
| AG3 | Invariant Bundle Hardening | 4 | F-T02 uniqueWaiters promotion, T-01 runtime checks |
| AG4 | Pre-Hardware Preparation | 3 | F-F04 frozen replenishQueue, documentation sync |
| AG5 | Documentation & Closure | 3 | Doc sync, fixture update, workstream history |

**Total sub-tasks**: 21
**Estimated scope**: ~800–1200 lines changed across ~25 files

---

## 2. Consolidated Finding Registry

### 2.1 Actionable Findings (Code Changes Required)

| Unified ID | Audit ID | Severity | Subsystem | Summary | Phase |
|------------|----------|----------|-----------|---------|-------|
| AG-01 | S-04 | MEDIUM | Scheduler | 4 RunQueue insert sites use base `sc.priority` instead of effective priority (base + PIP boost) | AG1 |
| AG-02 | S-05 | MEDIUM | Scheduler | `timeoutBlockedThreads` silently swallows `timeoutThread` errors | AG1 |
| AG-03 | R-01 | MEDIUM | Rust ABI | Missing `sele4n-sys/src/sched_context.rs` — 3 SchedContext syscalls (17–19) have no typed wrapper | AG2 |
| AG-04 | R-05 | MEDIUM | Rust ABI | `MAX_DOMAIN = 255` diverges from Lean `numDomainsVal = 16` — accepts invalid domain values 16–255 | AG2 |
| AG-05 | F-T02 | LOW | IPC Invariant | `uniqueWaiters` (Nodup on notification wait lists) exists but is not bundled into `ipcInvariantFull` | AG3 |
| AG-06 | T-01 | MEDIUM | Testing | `crossSubsystemInvariant` (10 predicates), PIP, InfoFlow, SchedContext invariants lack runtime checks | AG3 |
| AG-07 | F-F04 | MEDIUM | Frozen State | `FrozenSchedulerState` omits `replenishQueue` — CBS data lost during freeze | AG4 |

### 2.2 Pre-Hardware Deferred (H3-Blocked, Not Remediated)

These findings require hardware-binding context (RPi5 bring-up) and are
explicitly deferred to the H3 workstream. They are documented here for
traceability but receive no sub-tasks in this plan.

| Audit ID | Severity | Summary | Blocking Reason |
|----------|----------|---------|-----------------|
| F-S05 | MEDIUM | `descendantsOf` fuel sufficiency deferred (AF-34) | CDT depth bounds require hardware memory layout |
| P-01 | MEDIUM | `classifyMemoryRegion` always returns `.ram` (AF-41) | Requires DTB memory node parsing from real hardware |
| P-02 | MEDIUM | `bootFromPlatform` accepts empty `PlatformConfig` (AF-44) | Minimum-config validation requires H3 boot spec |
| P-03 | MEDIUM | Last-wins semantics on duplicate IRQs/objects | Dedup requires H3 platform config schema |
| P-04 | MEDIUM | `applyMachineConfig` partial copy (AF-45) | Full field propagation requires H3 register model |
| P-05 | MEDIUM | MMIO read returns stale value for volatile registers | Inherent pure-functional modeling limitation |
| P-07 | LOW | Production `rpi5RuntimeContract` lacks `AdapterProofHooks` | Register context stability requires H3 context-switch model |

### 2.3 Intentional Design (No Action Required)

These findings describe deliberate architectural decisions that have been
verified correct. Each is documented in the codebase with rationale.

| Audit ID | Severity | Summary | Rationale |
|----------|----------|---------|-----------|
| C-03 | MEDIUM | seL4 traversal rights divergence — operation-level enforcement | Documented U-M25: simpler to prove, covers all paths since capabilities immutable during resolution |
| C-07 | MEDIUM | CDT acyclicity externalized as `hCdtPost` hypothesis | Lines 15–48 of Preservation.lean: fresh children cannot create cycles; externalization is compositionally sound |
| A-01 | MEDIUM | `setIPCBufferOp` no W^X check | Only writes TCB `ipcBuffer : VAddr` field — W^X enforced at `mapPage` time |
| IF-02 | MEDIUM | Default `LabelingContext` all-permissive | `labelingContextValid_is_deployment_requirement` witness theorem warns; deployment must override |
| IF-03 | MEDIUM | Service orchestration outside NI boundary | `serviceOrchestrationOutsideNiBoundary` theorem; `registerServiceChecked` has full NI proofs |
| SA-01 | MEDIUM | CBS 8× bandwidth bound precision gap (AF-08) | `budgetWithinBounds` per-object guard prevents actual overrun; `maxReplenishments=8` is structural |
| SA-02 | MEDIUM | `schedContextYieldTo` no capability check (AF-30/AF-47) | Kernel-internal helper below capability layer; callers validate access rights |
| S-06 | MEDIUM | WCRT hypotheses externalized (AF-14) | `hDomainActiveRunnable`/`hBandProgress` documented for future derivation from CBS finiteness |

### 2.4 Already Documented / Previously Tracked (No Action Required)

| Audit ID | Severity | Summary | Prior Tracking |
|----------|----------|---------|----------------|
| F-ST02 | MEDIUM | `storeObject` capacity precondition | AF2-B: `storeObject_capacity_safe_of_existing`, `retypeFromUntyped_capacity_gated` |
| F-B04 | LOW | Deep tuple projections (16-deep `.2` chains) | Tracked for WS-V named-structure migration (AF-26) |
| F-FP05 | LOW | `UniqueRadixIndices` hypothesis in freeze proofs | Q4 bridge: satisfied by well-formed CNodes via `buildCNodeRadixChecked` |
| RT-05 | MEDIUM | Radix `extractBits` modular arithmetic for OOB keys | `buildCNodeRadixChecked` provides runtime defense; `UniqueRadixIndices` for proof correctness |
| FO-03 | MEDIUM | FrozenOps Phase 2 unreachability unproved | Experimental code (U-02); not in production chain |
| S-01 | LOW | RunQueue `flat` O(n) membership | Performance acceptable for <100 threads |
| S-02 | LOW | `syncThreadStates` O(n) in total objects | Idempotent post-op synchronization, not hot path |
| S-03 | LOW | `handleYield` re-selects when no peer runnable (AF-29) | Semantically correct: yield forfeits quantum, not time |
| SA-03 | LOW | `dispatchWithCap` wildcard returns `.illegalState` | Provably unreachable (theorems at API.lean:1222–1249) |
| SA-04 | LOW | `serviceHasPathTo` returns `true` on fuel exhaustion (AF-18) | Conservative: prevents cycle creation on ambiguity |
| I-01 | LOW | Timeout sentinel ordering fragility | Documented H3 migration plan |
| C-08 | LOW | `cdtAcyclic` uses `WellFounded` — no fuel needed | Structural correctness |
| C-14 | LOW | `revokeFromSlot` fuel-bounded BFS (AF-07) | Returns `resourceExhausted` on fuel depletion |
| L-09 | LOW | Untyped overlap checking linear scan | Acceptable for small child counts |
| L-11 | LOW | Suspend/resume invariant externalized to transport lemmas | Architecturally standard |
| L-15 | LOW | `objectOfTypeTag` creates TCBs with zeroed fields | `lifecycleRetypeWithCleanup` enforces well-formedness |
| T-02 | LOW | Test states use empty CDTs/replenishment queues | Test simplification; multi-step chains tested separately |
| T-03 | LOW | `lake build` only builds main target; isolated modules need explicit build | Pre-commit hook mitigates (scripts/pre-commit-lean-build.sh) |

### 2.5 Informational (Positive Observations, No Action)

The audit recorded ~80 informational observations confirming correctness.
Notable highlights: zero `sorry`/`axiom`/`native_decide`/`partial` in
production code, verified Lean-Rust ABI boundary (all 25 syscalls, 44+1
errors, register layouts match), zero external dependencies, SHA-pinned CI,
`shellcheck` enforcement, and complete NI step coverage (34/34 operations).

---

## 3. Phase AG1 — Scheduler Correctness

**Scope**: Fix 4 RunQueue insert sites to use effective priority; improve
error visibility in `timeoutBlockedThreads`.
**Files modified**: `Scheduler/Operations/Core.lean`, `SchedContext/Operations.lean`,
`Scheduler/Operations/Preservation.lean`
**Estimated lines changed**: ~120

### AG1-A: Extract `resolveInsertPriority` helper

**Finding**: AG-01 (S-04)
**File**: `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`

The existing `resolveEffectivePrioDeadline` (Selection.lean:323) computes
effective priority from a TCB by resolving SchedContext binding and applying
PIP boost. However, the 4 buggy call sites have a SchedContext in hand but
not always a TCB. We need a lightweight helper that, given a state, thread ID,
and fallback SchedContext priority, looks up the TCB and applies `pipBoost`.

**Task**: Add `resolveInsertPriority` to `Selection.lean`:

```
def resolveInsertPriority (st : SystemState) (tid : ThreadId)
    (scPriority : Priority) : Priority :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
    match tcb.pipBoost with
    | none => scPriority
    | some boostPrio => ⟨Nat.max scPriority.val boostPrio.val⟩
  | _ => scPriority
```

This returns `max(sc.priority, pipBoost)` when the TCB has a PIP boost,
or the SchedContext priority as fallback. It is consistent with
`resolveEffectivePrioDeadline`'s PIP application logic (line 332–334).

**Verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Selection`

### AG1-B: Fix `processReplenishmentsDue` (Core.lean:460)

**Finding**: AG-01 (S-04), call site 1
**File**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean:460`

**Current code**:
```lean
runQueue := refilled.scheduler.runQueue.insert tid sc.priority
```

**Fix**: Replace `sc.priority` with `resolveInsertPriority refilled tid sc.priority`.

The state `refilled` already contains the updated objects after
`refillSchedContext`, so TCB lookup will return the correct current TCB.

**Verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`

### AG1-C: Fix `timerTickBudget` (Core.lean:586)

**Finding**: AG-01 (S-04), call site 2
**File**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean:586`

**Current code** (note the misleading comment on line 583):
```lean
-- Re-enqueue current thread at its effective priority
runQueue := st'.scheduler.runQueue.insert tid sc.priority
```

**Fix**: Replace `sc.priority` with `resolveInsertPriority st' tid sc.priority`.
Also fix the comment — it currently says "effective priority" but uses base
priority. After the fix, the comment will be accurate.

The `tcb : TCB` parameter is available at this scope (line 545), so
alternatively we could inline the computation as:
```lean
let effectivePrio := match tcb.pipBoost with
  | none => sc.priority
  | some bp => ⟨Nat.max sc.priority.val bp.val⟩
```
However, using `resolveInsertPriority` is preferred for consistency across
all 4 sites. Note: `st'` has already written the updated SchedContext but
the TCB is unchanged (only `sc` was modified), so looking up `tid` in `st'`
returns the same TCB as `tcb`.

**Verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`

### AG1-D: Fix `handleYieldWithBudget` (Core.lean:710)

**Finding**: AG-01 (S-04), call site 3
**File**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean:710`

**Current code**:
```lean
let rq' := st'.scheduler.runQueue.insert tid sc.priority
```

**Fix**: Replace `sc.priority` with `resolveInsertPriority st' tid sc.priority`.

The TCB `tcb` is in scope from line 688's pattern match. The state `st'`
contains the updated SchedContext but the TCB at `tid` is unchanged.

**Verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`

### AG1-E: Fix `schedContextYieldTo` (SchedContext/Operations.lean:268)

**Finding**: AG-01 (S-04), call site 4
**File**: `SeLe4n/Kernel/SchedContext/Operations.lean:268`

**Current code**:
```lean
runQueue := st2.scheduler.runQueue.insert tid targetSc.priority
```

**Fix**: Replace `targetSc.priority` with
`resolveInsertPriority st2 tid targetSc.priority`.

Here `tid` comes from `targetSc.boundThread` (line 264). The TCB is not
directly in scope, so the helper's state lookup is essential. The state
`st2` has both SchedContexts updated but TCBs are unchanged.

**Verification**: `lake build SeLe4n.Kernel.SchedContext.Operations`

### AG1-F: Update scheduler preservation proofs

**Finding**: AG-01 (S-04), proof impact
**File**: `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean`

The 4 code changes alter the priority argument to `RunQueue.insert`. Existing
preservation theorems for `schedulerInvariantBundleFull` reference the insert
call. Each proof that pattern-matches on the RunQueue insert priority will
need to account for the `resolveInsertPriority` lookup.

**Sub-steps**:
1. Update `processReplenishmentsDue` preservation lemmas
2. Update `timerTickBudget` / `timerTick` preservation chain
3. Update `handleYieldWithBudget` preservation lemmas
4. Update `schedContextYieldTo` cross-subsystem bridge lemma
   (`schedContextYieldTo_crossSubsystemInvariant_bridge` in CrossSubsystem.lean)

Each proof update is a mechanical adjustment: the priority value changes from
a direct field access to a function application, but the RunQueue structural
invariants are priority-agnostic (they hold for any `Priority` value).

**Verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation`,
`lake build SeLe4n.Kernel.CrossSubsystem`

### AG1-G: Improve `timeoutBlockedThreads` error visibility

**Finding**: AG-02 (S-05)
**File**: `SeLe4n/Kernel/Scheduler/Operations/Core.lean:525`

**Current code**:
```lean
| .error _ => acc  -- defensive: skip if queue removal fails
```

The function silently swallows errors from `timeoutThread`. Under well-formed
invariants, `timeoutThread` should never fail (the thread is verified blocked
on an endpoint before calling). The defensive fallback masks potential
invariant violations.

**Fix**: Add a diagnostic comment documenting the unreachability argument,
and add a `-- AUDIT:AG-02` annotation so future audits can track this site.
The error swallowing is retained (changing it would alter the function's
return type from `SystemState` to `Except KernelError SystemState`, which
would cascade through `timerTickBudget` and `timerTick` callers). Instead,
we document the invariant argument:

```lean
| .error _ => acc  -- AG-02: Unreachable under ipcInvariantFull ∧
                    -- ipcStateQueueMembershipConsistent. The fold
                    -- only enters this branch for threads where
                    -- tcbBlockingInfo returns `some (epId, isReceiveQ)`,
                    -- meaning the thread is blocked on an endpoint.
                    -- timeoutThread fails only if the thread is not
                    -- in the endpoint's queue, contradicting
                    -- ipcStateQueueMembershipConsistent.
```

**Alternative (not recommended for this phase)**: Refactor
`timeoutBlockedThreads` to return `Except KernelError SystemState` and
propagate errors. This would require changing `timerTickBudget` (line 589),
`timerTick`, and all callers. Deferred to WS-V if the unreachability
argument proves insufficient.

**Verification**: `lake build SeLe4n.Kernel.Scheduler.Operations.Core`

---

## 4. Phase AG2 — Rust ABI Completion

**Scope**: Add missing SchedContext syscall wrappers; fix MAX_DOMAIN mismatch.
**Files modified**: `rust/sele4n-sys/src/sched_context.rs` (new),
`rust/sele4n-sys/src/lib.rs`, `rust/sele4n-abi/src/args/sched_context.rs`
**Estimated lines changed**: ~130 (new file) + ~15 (fixes)

### AG2-A: Create `sele4n-sys/src/sched_context.rs`

**Finding**: AG-03 (R-01)
**File**: `rust/sele4n-sys/src/sched_context.rs` (new)

`sele4n-sys` provides typed wrappers for 22 of 25 syscalls. The 3 missing
SchedContext syscalls (configure=17, bind=18, unbind=19) have ABI encoding
in `sele4n-abi/src/args/sched_context.rs` but no high-level entry points.

**Task**: Create `sched_context.rs` following the established pattern from
`tcb.rs` (which provides the closest analogue — capability-controlled
operations with register arguments):

```rust
//! SchedContext operations — configure, bind, unbind.
//!
//! Lean: `SeLe4n/Kernel/API.lean` — Z5 (SchedContext operations).
//! All require appropriate rights on the target SchedContext capability.

use sele4n_types::{CPtr, KernelResult, SyscallId};
use sele4n_abi::{MessageInfo, SyscallRequest, SyscallResponse, invoke_syscall};
use sele4n_abi::args::sched_context::*;

pub fn sched_context_configure(
    sc_cap: CPtr,
    budget: u64,
    period: u64,
    priority: u64,
    deadline: u64,
    domain: u64,
) -> KernelResult<SyscallResponse> { ... }

pub fn sched_context_bind(
    sc_cap: CPtr,
    thread_id: u64,
) -> KernelResult<SyscallResponse> { ... }

pub fn sched_context_unbind(
    sc_cap: CPtr,
) -> KernelResult<SyscallResponse> { ... }
```

Each function creates the corresponding `*Args` struct, calls `.encode()`,
constructs a `SyscallRequest` with the correct `SyscallId`, and delegates
to `invoke_syscall`. Follow the patterns established in `tcb.rs` for:
- `MessageInfo::new_const(reg_count, 0, 0)` with correct register count
- `msg_regs` array with encoded values (pad unused slots with 0)
- `#[inline]` attribute
- Doc comments referencing Lean source locations

**Register counts** (from `SyscallArgDecode.lean`):
- `SchedContextConfigure`: 5 registers (budget, period, priority, deadline, domain)
- `SchedContextBind`: 1 register (thread_id)
- `SchedContextUnbind`: 0 registers (capability-only)

### AG2-B: Register module in `sele4n-sys/src/lib.rs`

**Finding**: AG-03 (R-01)
**File**: `rust/sele4n-sys/src/lib.rs`

**Task**: Add `pub mod sched_context;` to the module declarations (after
existing `pub mod cap;` at line 35). This follows the alphabetical ordering
pattern used for existing modules.

### AG2-C: Fix `MAX_DOMAIN` to match Lean `numDomainsVal`

**Finding**: AG-04 (R-05)
**File**: `rust/sele4n-abi/src/args/sched_context.rs:13`

**Current code**:
```rust
/// Maximum configurable domain value (matching Lean DomainId range).
pub const MAX_DOMAIN: u64 = 255;
```

**Lean reference** (`SchedContext/Operations.lean:43,56`):
```lean
def numDomainsVal : Nat := 16
-- ...
else if domain ≥ numDomainsVal then .error .invalidArgument
```

Valid domains are 0–15. The Rust validation (`regs[4] > MAX_DOMAIN`) should
reject values >= 16.

**Fix**:
```rust
/// Maximum configurable domain value (matching Lean numDomainsVal = 16, 0-indexed).
pub const MAX_DOMAIN: u64 = 15;
```

**Comment update**: Fix the existing comment "matching Lean DomainId range"
to accurately reference `numDomainsVal`.

### AG2-D: Update `MAX_DOMAIN` tests

**Finding**: AG-04 (R-05)
**File**: `rust/sele4n-abi/src/args/sched_context.rs:118-131`

Two tests must be updated:

1. `configure_domain_out_of_range` (line 118): Currently tests `domain=256`
   rejection. Should also test that `domain=16` is rejected (new boundary).

2. `configure_max_valid_priority_and_domain` (line 126): Currently asserts
   `domain=255` is accepted. Must change to `domain=15`:
   ```rust
   let args = SchedContextConfigureArgs::decode(
       &[1000, 5000, 255, 10000, 15]
   ).unwrap();
   assert_eq!(args.domain, 15);
   ```

3. Add boundary test: `domain=16` should return `InvalidSyscallArgument`.

**Verification**: `cd rust && cargo test --workspace`

---

## 5. Phase AG3 — Invariant Bundle Hardening

**Scope**: Promote `uniqueWaiters` into IPC invariant bundle; add runtime
checks for `crossSubsystemInvariant` predicates.
**Files modified**: `IPC/Invariant/Defs.lean`, `IPC/Invariant/Structural.lean`,
`IPC/Invariant/NotificationPreservation.lean`, `Testing/InvariantChecks.lean`,
`Kernel/CrossSubsystem.lean`
**Estimated lines changed**: ~200

### AG3-A: Promote `uniqueWaiters` to `ipcInvariantFull`

**Finding**: AG-05 (F-T02)
**File**: `SeLe4n/Kernel/IPC/Invariant/Defs.lean:1084-1091`

**Context**: The `uniqueWaiters` invariant (`Defs.lean:551`) already enforces
`ntfn.waitingThreads.Nodup` for all notifications, with preservation proofs
for `notificationWait` (line 557) and `notificationSignal` (line 689).
However, it is NOT included in the 14-conjunct `ipcInvariantFull` bundle.

**Task**: Add `uniqueWaiters st` as the 15th conjunct of `ipcInvariantFull`:

```lean
def ipcInvariantFull (st : SystemState) : Prop :=
  ipcInvariant st ∧ dualQueueSystemInvariant st ∧ allPendingMessagesBounded st ∧
  badgeWellFormed st ∧ waitingThreadsPendingMessageNone st ∧
  endpointQueueNoDup st ∧ ipcStateQueueMembershipConsistent st ∧
  queueNextBlockingConsistent st ∧ queueHeadBlockedConsistent st ∧
  blockedThreadTimeoutConsistent st ∧
  donationChainAcyclic st ∧ donationOwnerValid st ∧
  passiveServerIdle st ∧ donationBudgetTransfer st ∧
  uniqueWaiters st
```

Update the docstring to reference "fifteen IPC sub-invariants" and add
`uniqueWaiters` to the bullet list.

### AG3-B: Update `ipcInvariantFull` preservation proofs

**Finding**: AG-05 (F-T02), proof cascading
**Files**: `IPC/Invariant/Structural.lean`, `IPC/Invariant/NotificationPreservation.lean`,
`IPC/Invariant/EndpointPreservation.lean`, `IPC/Invariant/CallReplyRecv.lean`

Adding a 15th conjunct to `ipcInvariantFull` means every preservation theorem
that concludes `ipcInvariantFull st'` must also prove `uniqueWaiters st'`.

**Strategy**: Since `uniqueWaiters` preservation proofs already exist as
standalone theorems (`notificationWait_preserves_uniqueWaiters` at Defs.lean:557),
the proof updates are mechanical — extract `uniqueWaiters` from the pre-state
`ipcInvariantFull` hypothesis and apply the existing preservation theorem.

**Sub-steps**:
1. For each preservation theorem in `Structural.lean` that proves
   `ipcInvariantFull st'`, add a `uniqueWaiters st'` conjunct using the
   matching standalone preservation theorem.
2. For operations that don't touch notification objects (e.g., pure endpoint
   operations), `uniqueWaiters` is preserved by frame reasoning: if the
   operation only modifies endpoints/TCBs but not notification objects,
   `uniqueWaiters` is trivially preserved.
3. Verify that `notificationWaiterConsistent` (which `uniqueWaiters`
   preservation requires) is available at all call sites — it is, since it's
   threaded through the notification preservation proofs.

**Risk**: This is the highest-risk sub-task in Phase AG3. The `Structural.lean`
file is ~7591 lines and contains many preservation theorems. Each must be
updated. However, the updates are mechanical (add one more conjunct) and can
be tested incrementally by building after each theorem update.

**Verification**: `lake build SeLe4n.Kernel.IPC.Invariant.Structural`

### AG3-C: Add runtime checks for `crossSubsystemInvariant`

**Finding**: AG-06 (T-01)
**File**: `SeLe4n/Testing/InvariantChecks.lean`

**Context**: The `crossSubsystemInvariant` 10-predicate bundle
(`CrossSubsystem.lean:295-305`) is only verified via formal proofs.
`InvariantChecks.lean` performs ~20 runtime checks but excludes
`crossSubsystemInvariant`, PIP invariants, InfoFlow invariants, and
SchedContext budget invariants.

**Task**: Add runtime check functions for the most impactful
`crossSubsystemInvariant` predicates:

1. `checkNoStaleEndpointQueueReferences` — Verify all endpoint queue members
   reference live TCBs (predicate 4: `noStaleEndpointQueueReferences`)
2. `checkNoStaleNotificationWaitReferences` — Verify notification waitlists
   reference live TCBs (predicate 5: `noStaleNotificationWaitReferences`)
3. `checkSchedContextNotDualBound` — Verify no thread bound to two
   SchedContexts (predicate 8: `schedContextNotDualBound`)
4. `checkBlockingAcyclic` — Verify PIP blocking graph has no cycles
   (predicate 10: `blockingAcyclic`) — fuel-bounded cycle detection

**Excluded from runtime checks** (justification):
- Predicates 1–3 (registry invariants): Covered by existing service graph
  acyclicity check
- Predicate 6 (`serviceGraphInvariant`): Already checked
- Predicate 7 (`schedContextStoreConsistent`): Would require deep
  structure comparison — low cost/benefit ratio
- Predicate 9 (`schedContextRunQueueConsistent`): Covered indirectly by
  existing RunQueue/threadPriority checks

**Implementation pattern**: Follow the established `Bool`-returning check
function convention in `InvariantChecks.lean`. Each check iterates over
`st.objects.toList` and validates the predicate for each relevant object.

### AG3-D: Wire runtime checks into test harness

**Finding**: AG-06 (T-01)
**Files**: `SeLe4n/Testing/MainTraceHarness.lean`, `tests/NegativeStateSuite.lean`

**Task**: Call the new cross-subsystem check functions after multi-step
operation chains in the trace harness and negative-state suite. Add Tier-3
surface anchors for each new check.

**Verification**: `./scripts/test_full.sh`

---

## 6. Phase AG4 — Pre-Hardware Preparation

**Scope**: Add `replenishQueue` to `FrozenSchedulerState`; document H3-blocked
findings.
**Files modified**: `Model/FrozenState.lean`, `Model/FreezeProofs.lean`,
`Kernel/FrozenOps/Core.lean`
**Estimated lines changed**: ~80

### AG4-A: Add `replenishQueue` to `FrozenSchedulerState`

**Finding**: AG-07 (F-F04)
**File**: `SeLe4n/Model/FrozenState.lean:207-216`

**Current state**: `FrozenSchedulerState` has 9 fields mirroring
`SchedulerState`, but omits `replenishQueue` (which is field 10 of
`SchedulerState` at `State.lean:120`).

**Task**: Add `replenishQueue : SeLe4n.Kernel.ReplenishQueue` to
`FrozenSchedulerState`:

```lean
structure FrozenSchedulerState where
  byPriority          : FrozenMap SeLe4n.Priority (List SeLe4n.ThreadId)
  threadPriority      : FrozenMap SeLe4n.ThreadId SeLe4n.Priority
  membership          : FrozenSet SeLe4n.ThreadId
  current             : Option SeLe4n.ThreadId
  activeDomain        : SeLe4n.DomainId
  domainTimeRemaining : Nat
  domainSchedule      : List DomainScheduleEntry
  domainScheduleIndex : Nat
  configDefaultTimeSlice : Nat
  replenishQueue      : SeLe4n.Kernel.ReplenishQueue
```

`ReplenishQueue` is already a pure functional sorted list
(`SchedContext/ReplenishQueue.lean`), so no freezing conversion is needed —
it can be carried directly from `SchedulerState` to `FrozenSchedulerState`.

### AG4-B: Update `freezeScheduler` to include `replenishQueue`

**Finding**: AG-07 (F-F04)
**File**: `SeLe4n/Model/FrozenState.lean` (search for `freezeScheduler`)

**Task**: Update the `freezeScheduler` function to copy the `replenishQueue`
field from the source `SchedulerState` to the target `FrozenSchedulerState`.

### AG4-C: Update freeze proofs for `replenishQueue`

**Finding**: AG-07 (F-F04)
**File**: `SeLe4n/Model/FreezeProofs.lean`

**Task**: Add a roundtrip lemma proving that `replenishQueue` is preserved
through the freeze operation:

```lean
theorem freezeScheduler_replenishQueue_eq (sched : SchedulerState) :
    (freezeScheduler sched).replenishQueue = sched.replenishQueue := rfl
```

This is trivially `rfl` since `ReplenishQueue` is not converted (no
`FrozenMap` transformation needed).

**Verification**: `lake build SeLe4n.Model.FrozenState`,
`lake build SeLe4n.Model.FreezeProofs`

---

## 7. Phase AG5 — Documentation & Closure

**Scope**: Synchronize documentation, update workstream history, verify
fixtures.
**Files modified**: `docs/WORKSTREAM_HISTORY.md`, `CHANGELOG.md`, `README.md`,
`docs/gitbook/12-proof-and-invariant-map.md`
**Estimated lines changed**: ~100

### AG5-A: Update `WORKSTREAM_HISTORY.md`

**Task**: Add WS-AG entry to the workstream history with:
- Phase summaries (AG1–AG5)
- Sub-task completion records
- Version number for each phase
- Cross-references to audit finding IDs

### AG5-B: Synchronize documentation

**Task**: Update the following documents for any behavioral changes:
1. `docs/spec/SELE4N_SPEC.md` — Update IPC invariant count (14 → 15),
   update scheduler priority semantics if specification mentions
   RunQueue insertion priority
2. `docs/gitbook/12-proof-and-invariant-map.md` — Add `uniqueWaiters` to
   IPC invariant listing, update `ipcInvariantFull` conjunct count
3. `README.md` — Sync metrics from `docs/codebase_map.json` if Lean
   module count changes
4. `CLAUDE.md` — Update active workstream context section to reflect
   WS-AG status

### AG5-C: Verify fixtures and CI

**Task**: Run the full validation pipeline and update fixtures if outputs
change due to scheduler priority fixes:
1. Run `./scripts/test_smoke.sh` — minimum validation
2. Run `./scripts/test_full.sh` — full invariant surface
3. If `tests/fixtures/main_trace_smoke.expected` hash changes (possible
   if the trace harness exercises scheduler paths that now use effective
   priority), update the fixture with documented rationale
4. Run `cd rust && cargo test --workspace` — Rust ABI tests

---

## 8. Scope Estimates

| Phase | Sub-tasks | New Lines | Changed Lines | Files Touched | Risk |
|-------|-----------|-----------|---------------|---------------|------|
| AG1 | 7 | ~30 | ~90 | 4 Lean | HIGH (proof cascading) |
| AG2 | 4 | ~130 | ~15 | 3 Rust | LOW |
| AG3 | 4 | ~150 | ~50 | 6 Lean | HIGH (Structural.lean 7.5k) |
| AG4 | 3 | ~20 | ~10 | 3 Lean | LOW |
| AG5 | 3 | ~60 | ~40 | 5 docs | LOW |
| **Total** | **21** | **~390** | **~205** | **~21** | — |

**Worst-case estimate**: If AG1-F (proof updates) or AG3-B (Structural.lean)
require extensive proof refactoring beyond mechanical adjustments, scope could
expand by 200–400 lines. The contingency budget is ~400 lines above the
base estimate.

---

## 9. Dependency Graph

```
AG1-A (helper)
  ├── AG1-B (site 1) ──┐
  ├── AG1-C (site 2) ──┤
  ├── AG1-D (site 3) ──┼── AG1-F (proof updates) ──┐
  └── AG1-E (site 4) ──┘                           │
                                                    │
AG1-G (error docs) ─ [independent] ─────────────────┤
                                                    │
AG2-C (MAX_DOMAIN) ──── AG2-D (tests) ──┐           │
AG2-A (wrappers) ──── AG2-B (lib.rs) ───┤           │
                                        │           │
AG3-A (uniqueWaiters) ── AG3-B (proofs) │           │
AG3-C (runtime checks) ─ AG3-D (wire) ──┤           │
                                        │           │
AG4-A (frozen field) ── AG4-B (freeze) ─┤           │
AG4-C (freeze proof)  ──────────────────┤           │
                                        │           │
                                 AG5-A (history) ───┤
                                 AG5-B (docs) ──────┤
                                 AG5-C (verify) ────┘
```

**Critical path**: AG1-A → AG1-{B,C,D,E} → AG1-F → AG5-C

**Parallel opportunities**:
- AG1 and AG2 are fully independent (Lean vs Rust, disjoint files)
- AG3-{A,B} and AG3-{C,D} are independent of each other
- AG4 is independent of AG1, AG2, AG3
- AG5 depends on all prior phases completing

---

## 10. Phase Ordering

| Order | Phase | Rationale |
|-------|-------|-----------|
| 1 | AG1 + AG2 (parallel) | AG1 is the highest-risk phase (proof cascading); AG2 is independent and low-risk. Running in parallel maximizes throughput. |
| 2 | AG3 | Depends on nothing in AG1/AG2 but is the second-highest risk (Structural.lean). Starting after AG1 ensures proof methodology is validated before tackling another large proof file. |
| 3 | AG4 | Low-risk, small scope. Independent but sequenced here to maintain focus on one subsystem at a time. |
| 4 | AG5 | Documentation sync requires all code changes to be final. Must run last. |

**Alternative ordering** (if AG1-F proof updates prove difficult):

Pivot AG3 ahead of AG1 to gain confidence on proof methodology before
tackling the scheduler preservation proofs. AG3's proof updates are
mechanically simpler (adding one more conjunct vs changing a function argument).

---

## 11. Risk Register

| Risk | Probability | Impact | Mitigation |
|------|-------------|--------|------------|
| AG1-F proof cascading | MEDIUM | HIGH | RunQueue invariants are priority-agnostic — most proofs should only need trivial adjustments. If a proof requires priority-specific reasoning, fall back to inlining the effective priority computation at each call site instead of using the helper. |
| AG3-B Structural.lean scope | MEDIUM | HIGH | Edit in ≤500-line chunks per CLAUDE.md. Build incrementally after each theorem update. If total proof delta exceeds ~300 lines, split into AG3-B1 (notification operations) and AG3-B2 (endpoint operations). |
| AG2-A register count mismatch | LOW | MEDIUM | Cross-reference `SyscallArgDecode.lean` (lines 894–911) for exact register layouts. Use `MessageInfo::new_const` with correct counts (5, 1, 0). |
| AG4-A cascading field additions | LOW | LOW | `ReplenishQueue` is a direct copy (not frozen). Only `freezeScheduler` and its immediate callers are affected. FrozenOps is experimental and not in the production chain. |
| Trace fixture changes from AG1 | LOW | MEDIUM | The trace harness creates test states with `pipBoost = none` (default). With no PIP boost active, `resolveInsertPriority` returns `sc.priority` unchanged, so trace output should be identical. If it changes, update fixture with rationale. |
| `uniqueWaiters` requires `notificationWaiterConsistent` | LOW | MEDIUM | `notificationWaiterConsistent` is already threaded through all notification preservation proofs. If it's not available at some `ipcInvariantFull` preservation site, add it as an additional hypothesis (this is safe since `notificationWaiterConsistent` is already proved for all operations). |

---

## 12. Verification Protocol

### Per-Phase Verification

| Phase | Required Checks |
|-------|-----------------|
| AG1 | `lake build SeLe4n.Kernel.Scheduler.Operations.Selection`, `lake build SeLe4n.Kernel.Scheduler.Operations.Core`, `lake build SeLe4n.Kernel.SchedContext.Operations`, `lake build SeLe4n.Kernel.Scheduler.Operations.Preservation`, `lake build SeLe4n.Kernel.CrossSubsystem` |
| AG2 | `cd rust && cargo test --workspace`, `cd rust && cargo clippy --workspace` |
| AG3 | `lake build SeLe4n.Kernel.IPC.Invariant.Defs`, `lake build SeLe4n.Kernel.IPC.Invariant.Structural`, `lake build SeLe4n.Kernel.IPC.Invariant.NotificationPreservation`, `lake build SeLe4n.Testing.InvariantChecks` |
| AG4 | `lake build SeLe4n.Model.FrozenState`, `lake build SeLe4n.Model.FreezeProofs` |
| AG5 | `./scripts/test_smoke.sh`, `./scripts/test_full.sh` |

### Pre-Commit Checklist (each phase)

- [ ] `lake build <Module.Path>` for every modified `.lean` file
- [ ] `grep -rn 'sorry' SeLe4n/` returns 0 matches in production code
- [ ] `grep -rn 'axiom' SeLe4n/` returns 0 matches
- [ ] No `native_decide` introduced
- [ ] Pre-commit hook passes (builds all staged modules, checks for sorry)
- [ ] `cargo test --workspace` passes (if Rust files changed)

### Portfolio-Level Validation

After all 5 phases:
1. `./scripts/test_full.sh` — Tier 0–3 complete validation
2. `cd rust && cargo test --workspace` — Rust ABI tests
3. `./scripts/check_website_links.sh` — Website link integrity
4. Manual review of `WORKSTREAM_HISTORY.md` entry
5. Verify `docs/codebase_map.json` regenerated if Lean sources changed

---

## 13. Conclusion

WS-AG addresses 7 actionable findings from the v0.25.27 Release Comprehensive
Audit through 5 phases and 21 sub-tasks. The plan prioritizes:

1. **Scheduler correctness** (AG1): Fixing the 4 RunQueue insert sites to
   use effective priority is the most semantically significant change — it
   ensures threads with PIP boosts are enqueued at their correct elevated
   priority rather than relying on schedule-time compensation.

2. **Rust ABI completeness** (AG2): Adding the missing SchedContext wrappers
   and fixing the MAX_DOMAIN mismatch ensures the Lean-Rust ABI contract is
   complete and correct for all 25 syscalls.

3. **Invariant bundle hardening** (AG3): Promoting `uniqueWaiters` into
   `ipcInvariantFull` and adding runtime cross-subsystem checks strengthens
   both the formal proof hierarchy and the runtime regression detection
   surface.

4. **Pre-hardware preparation** (AG4): Adding `replenishQueue` to
   `FrozenSchedulerState` closes the last known data-loss gap in the freeze
   pipeline before H3 hardware binding.

The remaining findings are correctly triaged as: pre-hardware deferred (7),
intentional design (8), already documented (18), or informational/observational
(12). One finding (F-T02) was identified as partially erroneous — the
`uniqueWaiters` invariant already exists but needs bundle promotion.

**Zero sorry/axiom policy** is maintained throughout. All code changes are
accompanied by proof updates. No security invariants are weakened.

---

*Plan created 2026-04-08 for seLe4n v0.25.27. Baseline audit:
`docs/audits/AUDIT_v0.25.27_RELEASE_COMPREHENSIVE.md`.*

