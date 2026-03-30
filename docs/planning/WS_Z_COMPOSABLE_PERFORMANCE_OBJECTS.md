# WS-Z: Composable Performance Objects — EDF+CBS, Scheduling Contexts, Capability-Controlled Thread Creation

**Status**: PLANNED
**Created**: 2026-03-30
**Baseline version**: 0.22.25
**Prior portfolios**: WS-B through WS-Y (all COMPLETE or IN PROGRESS)
**Constraint**: Zero `sorry`/`axiom` in production proof surface
**Hardware target**: Raspberry Pi 5 (ARM64)
**Sub-task count**: 213 atomic units across 10 phases
**Axiom budget**: 0 (all proofs machine-checked)

---

## 1. Motivation

### 1.1 The Problem: Monolithic Scheduling State

seLe4n's current scheduler embeds all scheduling parameters directly in the TCB:

```lean
-- Current TCB (Object/Types.lean)
structure TCB where
  priority : Priority          -- Fixed at creation
  domain : DomainId            -- Fixed at creation
  timeSlice : Nat := 5         -- Hardcoded quantum
  deadline : Deadline := ⟨0⟩   -- EDF tie-breaking only
  ...
```

This design has five fundamental limitations:

| ID | Limitation | Impact |
|----|-----------|--------|
| L-1 | **No CPU budget accounting** | Threads consume unbounded CPU within their priority band. No mechanism to limit a thread to X microseconds per Y-millisecond period. The `timeSlice` field is a fixed round-robin quantum (5 ticks), not a replenishable budget. |
| L-2 | **No scheduling context separation** | Priority, budget, and period are fused into the TCB. Cannot share scheduling parameters across threads (e.g., a thread group with a collective budget). Cannot dynamically rebind a thread to different scheduling parameters. |
| L-3 | **No passive server support** | Servers must own scheduling resources even when idle. A server blocked on `endpointReceiveDual` still occupies a priority slot and time-slice allocation. In seL4 MCS, passive servers borrow the client's scheduling context during IPC, consuming zero CPU when idle. |
| L-4 | **No capability-controlled resource binding** | Thread creation via `retypeFromUntyped` produces a TCB with default scheduling parameters. No capability gate controls which scheduling resources a thread may use. Any thread with retype authority can create threads at any priority. |
| L-5 | **No timeout-bounded IPC** | Threads blocked on IPC (`blockedOnSend`, `blockedOnReceive`, `blockedOnReply`) have no timeout mechanism. Unblocking is purely event-driven. A malicious or buggy server can hold a client's reply indefinitely. |

### 1.2 The seL4 MCS Model

seL4's Mixed-Criticality System (MCS) extensions solve these problems through
three composable abstractions:

1. **Scheduling Context (SchedContext)**: A first-class kernel object containing
   CPU budget, period, and replenishment parameters. Threads are bound to
   scheduling contexts via capabilities. Multiple threads can share a context
   (but only one runs at a time per context).

2. **CBS (Constant Bandwidth Server)**: Each scheduling context acts as a
   sporadic server with bandwidth reservation `budget/period`. The CBS algorithm
   ensures that a thread cannot exceed its allocated bandwidth, preventing
   priority inversion through resource exhaustion.

3. **Timeout Endpoints**: IPC operations are bounded by the caller's scheduling
   context budget. When the budget expires during a blocking IPC, the thread is
   unblocked with a timeout error, preventing indefinite blocking.

### 1.3 Design Principles for seLe4n

This workstream adapts seL4 MCS concepts to seLe4n's verified model with these
principles:

- **Execution as a first-class object**: CPU time is a capability-controlled
  resource, not an implicit property of threads.
- **Time as a verifiable quantity**: Budget consumption and replenishment are
  pure functions with machine-checked invariants.
- **Memory as a composable object**: Scheduling contexts are kernel objects
  allocated from untyped memory, subject to the same lifecycle and capability
  controls as all other objects.
- **Composability over monolithism**: Scheduling parameters are separated from
  threads, enabling dynamic rebinding, passive servers, and budget sharing.
- **Backward compatibility**: Existing scheduler invariants
  (`schedulerInvariantBundleFull`) are preserved and extended, not replaced.

---

## 2. Current State Analysis

### 2.1 Scheduling Infrastructure (What Exists)

| Component | File | Status | Reusable? |
|-----------|------|--------|-----------|
| EDF within priority | `Selection.lean:38` (`isBetterCandidate`) | Complete | **Yes** — CBS uses EDF; existing 3-level comparison extends naturally |
| Priority-bucketed RunQueue | `RunQueue.lean` | Complete | **Yes** — bucket structure accommodates CBS priority adjustment |
| Dequeue-on-dispatch | `Core.lean:schedule` | Complete | **Extend** — must check SchedContext budget before dispatch |
| Time-slice decrement | `Core.lean:timerTick` | Complete | **Replace** — CBS budget decrement replaces fixed quantum |
| Domain scheduling | `Core.lean:switchDomain` | Complete | **Preserve** — orthogonal to CBS (temporal partitioning layer above CBS) |
| Context save/restore | `Selection.lean` | Complete | **Preserve** — unchanged by scheduling context separation |
| 9 scheduler invariants | `Invariant.lean` | Complete | **Extend** — 6 new invariants added; `timeSlicePositive`/`currentTimeSlicePositive` gain SchedContext-aware branches; `schedulerPriorityMatch` complemented by `effectiveParamsMatchRunQueue` |

### 2.2 Object Model (What Exists)

| Component | File | Status | Change Required |
|-----------|------|--------|----------------|
| `KernelObject` inductive | `Structures.lean` | 6 variants | **Add** `.schedContext` variant |
| `KernelObjectType` | `Structures.lean` | 6 types | **Add** `.schedContext` type |
| `retypeFromUntyped` | `Lifecycle/Operations.lean` | Complete | **Extend** — handle SchedContext allocation |
| CDT integration | `Structures.lean` | Complete | **Extend** — SchedContext caps tracked in CDT |
| `storeObject` | `State.lean` | Complete | **Extend** — ASID-like index for SchedContext |

### 2.3 IPC Infrastructure (What Exists)

| Component | File | Status | Change Required |
|-----------|------|--------|----------------|
| `ThreadIpcState` | `Types.lean` | 6 variants | **Add** timeout metadata to blocking states |
| `endpointSendDual` | `DualQueue/Transport.lean` | Complete | **Extend** — budget check before blocking |
| `endpointReceiveDual` | `DualQueue/Transport.lean` | Complete | **Extend** — passive server SchedContext donation |
| `endpointCall` | `DualQueue/Transport.lean` | Complete | **Extend** — timeout + SchedContext lending |
| Dual-queue operations | `DualQueue/Core.lean` | Complete | **Preserve** — queue structure unchanged |

### 2.4 Capability Infrastructure (What Exists)

| Component | File | Status | Change Required |
|-----------|------|--------|----------------|
| `AccessRight` enum | `Types.lean` | 5 rights | **Preserve** — existing rights sufficient |
| `Capability` structure | `Types.lean` | Complete | **Preserve** — `CapTarget.object` covers SchedContext |
| `syscallRequiredRight` | `API.lean` | 17 mappings | **Add** 3 new syscalls |
| `SyscallId` enum | `Types.lean` | 17 variants | **Add** 3 new variants |

---

## 3. Architecture Overview

```
┌─────────────────────────────────────────────────────────────────┐
│  User Space                                                      │
│  ┌──────────┐  ┌──────────┐  ┌──────────┐  ┌──────────────────┐ │
│  │ Thread A │  │ Thread B │  │ Thread C │  │ Passive Server D │ │
│  │ (active) │  │ (active) │  │ (active) │  │ (no SchedCtx)    │ │
│  └────┬─────┘  └────┬─────┘  └────┬─────┘  └────────┬─────────┘ │
│       │cap          │cap          │cap               │cap        │
│       ▼             ▼             ▼                   ▼          │
│  ┌─────────┐  ┌─────────────────────┐         ┌───────────┐     │
│  │ SchedCtx│  │ SchedCtx (shared)   │         │ Endpoint  │     │
│  │   α     │  │   β                 │         │ (server)  │     │
│  │ B:1000  │  │ B:500               │         └───────────┘     │
│  │ P:10000 │  │ P:5000              │               ▲           │
│  │ Pri:200 │  │ Pri:150             │               │           │
│  └─────────┘  └─────────────────────┘               │           │
│       │              │                    Client Call│+ donate   │
│       ▼              ▼                    SchedCtx α │           │
├───────────────────────────────────────────────────────┼──────────┤
│  Kernel (CBS Scheduler)                               │          │
│                                                       │          │
│  ┌─────────────────────────────────────────────────┐  │          │
│  │  CBS Budget Manager                             │  │          │
│  │  ┌─────────────────────────┐                    │  │          │
│  │  │ Replenishment Queue     │                    │  │          │
│  │  │ (deadline-sorted)       │                    │  │          │
│  │  │ α: next_replenish=T+10k│                    │  │          │
│  │  │ β: next_replenish=T+5k │                    │  │          │
│  │  └─────────────────────────┘                    │  │          │
│  │  On timer tick:                                 │  │          │
│  │   1. Decrement active SchedCtx budget           │  │          │
│  │   2. If budget=0: preempt, charge, reschedule   │  │          │
│  │   3. If replenishment due: refill budget         │  │          │
│  └─────────────────────────────────────────────────┘  │          │
│                                                       │          │
│  ┌─────────────────────────────────────────────────┐  │          │
│  │  EDF Selection (extended)                       │  │          │
│  │  isBetterCandidate now uses SchedCtx deadline   │  │          │
│  │  Budget > 0 required for eligibility            │  │          │
│  └─────────────────────────────────────────────────┘  │          │
│                                                       │          │
│  ┌─────────────────────────────────────────────────┐  │          │
│  │  SchedContext Donation (IPC)                     │  │          │
│  │  Client Call: lend SchedCtx to server            │◄─┘          │
│  │  Server Reply: return SchedCtx to client         │             │
│  │  Server idle: no SchedCtx = passive (not in RQ)  │             │
│  └──────────────────────────────────────────────────┘             │
└───────────────────────────────────────────────────────────────────┘
```

---

## 4. Phase Dependency Graph

```
Z1 (SchedContext Type Foundation)
 │
 ├──→ Z2 (CBS Budget Engine)
 │     │
 │     ├──→ Z4 (Scheduler Integration) ───────────────┐
 │     │     │                                         │
 │     │     ├──→ Z6 (Timeout Endpoints) ──────────┐   │
 │     │     │     │                               │   │
 │     │     │     └──→ Z8 (API Surface)           │   │
 │     │     │           │                         │   │
 │     │     │           └──→ Z10 (Docs/Closure)   │   │
 │     │     │                  ▲                   │   │
 │     │     └──→ Z7 (Donation/Passive Servers) ┐  │   │
 │     │           │                            │  │   │
 │     │           └──→ Z8                      │  │   │
 │     │                                        │  │   │
 │     └──→ Z5 (Capability Binding) ──────────┐ │  │   │
 │           │                                │ │  │   │
 │           └──→ Z8                          │ │  │   │
 │                                            ▼ ▼  ▼   ▼
 ├──→ Z3 (Replenishment Queue)         Z9 (Invariant Composition)
 │     │                                      │
 │     └──→ Z4                                └──→ Z10
```

**Critical path**: Z1 → Z2 → Z4 → Z6 → Z8 → Z10 (6 sequential phases)
**Parallelizable**: Z3 ∥ Z2 (after Z1); Z5 ∥ Z4 (after Z2); Z7 ∥ Z6 (after Z4, with care — both touch Transport.lean but different functions)

---

## 5. Detailed Phase Specifications

### Phase Z1: SchedContext Type Foundation (18 sub-tasks)

**Goal**: Introduce the `SchedContext` kernel object type and all supporting
data structures. Pure type definitions and default instances — no behavioral
changes, no proof obligations beyond structural well-formedness.

**New files**:
- `SeLe4n/Kernel/SchedContext/Types.lean`
- `SeLe4n/Kernel/SchedContext.lean` (re-export hub)

**Modified files**:
- `SeLe4n/Model/Object/Types.lean` (ThreadIpcState extension)
- `SeLe4n/Model/Object/Structures.lean` (KernelObject + KernelObjectType variants)
- `SeLe4n/Prelude.lean` (SchedContextId typed wrapper)

| ID | Description | Files | Est. |
|----|-------------|-------|------|
| Z1-A | **Define `SchedContextId` typed wrapper in Prelude.lean.** Follow existing pattern: `structure SchedContextId where val : Nat deriving DecidableEq, Repr, Inhabited`. Add `Hashable`, `LawfulHashable`, `EquivBEq`, `LawfulBEq` instances (required for RHTable keys). Add `toObjId`/`ofObjId` conversions mirroring `ThreadId.toObjId`. Add `sentinel`, `isReserved`, `valid` predicates matching Prelude conventions. ~40 lines | `Prelude.lean` | Small |
| Z1-B | **Define `Budget` typed wrapper.** `structure Budget where val : Nat deriving DecidableEq, Repr, Inhabited`. Represents CPU time in ticks. Add `isZero`, `isPositive` predicates. Add `decrement : Budget → Budget` (saturating at 0). Add `refill : Budget → Budget → Budget` (set to min of value and ceiling). `Budget.zero := ⟨0⟩`. ~25 lines | `Types.lean` | Trivial |
| Z1-C | **Define `Period` typed wrapper.** `structure Period where val : Nat deriving DecidableEq, Repr, Inhabited`. Represents replenishment period in ticks. Add `isPositive` predicate (period must be > 0 for well-formedness). Add `Period.default := ⟨10000⟩` (default 10k ticks). ~15 lines | `Types.lean` | Trivial |
| Z1-D | **Define `Bandwidth` computed type.** `structure Bandwidth where budget : Nat, period : Nat`. Add `isValid : Bandwidth → Bool := period > 0`. Add `utilization : Bandwidth → Nat := budget * 1000 / period` (per-mille). Add `exceeds : Bandwidth → Bandwidth → Bool` for admission control. ~20 lines | `Types.lean` | Trivial |
| Z1-E | **Define `ReplenishmentEntry` structure.** Models a single CBS replenishment event: `structure ReplenishmentEntry where amount : Budget, eligibleAt : Nat` where `eligibleAt` is the absolute tick at which this replenishment becomes available. Add `isEligible : ReplenishmentEntry → Nat → Bool := entry.eligibleAt ≤ currentTime`. ~15 lines | `Types.lean` | Trivial |
| Z1-F | **Define `SchedContext` structure (core).** The first-class scheduling context object: `structure SchedContext where scId : SchedContextId, budget : Budget` (configured CBS budget — the amount replenished each period)`, period : Period, priority : Priority, deadline : Deadline, domain : DomainId, budgetRemaining : Budget` (current remaining ticks — decremented each tick, refilled up to `budget` on replenishment)`, periodStart : Nat, replenishments : List ReplenishmentEntry := [], boundThread : Option ThreadId := none, isActive : Bool := false`. Note: seL4 uses `scBudget` for the configured value and tracks consumption separately; we use `budget` (configured ceiling) and `budgetRemaining` (current). There is no separate `maxBudget` — the configured `budget` IS the replenishment cap. ~35 lines | `Types.lean` | Small |
| Z1-G | **Define `SchedContext.wellFormed` predicate.** Structural well-formedness: `period.isPositive ∧ budget.val ≤ period.val ∧ budgetRemaining.val ≤ budget.val ∧ replenishments.length ≤ maxReplenishments`. Add `maxReplenishments : Nat := 8` constant (seL4 uses `MIN_REFILLS = 2`, `MAX_REFILLS` varies). The key CBS constraint is `budget ≤ period` (utilization ≤ 1.0 per-context). ~20 lines | `Types.lean` | Small |
| Z1-H | **Define `SchedContext.bandwidth` accessor.** `def bandwidth (sc : SchedContext) : Bandwidth := { budget := sc.budget.val, period := sc.period.val }`. Add `SchedContext.utilizationPerMille`. ~10 lines | `Types.lean` | Trivial |
| Z1-I | **Define `SchedContextBinding` enum.** Models the thread ↔ SchedContext relationship: `inductive SchedContextBinding where \| unbound \| bound (scId : SchedContextId) \| donated (scId : SchedContextId, originalOwner : ThreadId)`. The `donated` variant tracks IPC-based SchedContext lending for passive servers. ~15 lines | `Types.lean` | Trivial |
| Z1-J | **Add `schedContextBinding` field to TCB.** Extend TCB structure: `schedContextBinding : SchedContextBinding := .unbound`. This replaces the monolithic `priority`/`deadline`/`timeSlice`/`domain` fields as the primary scheduling parameter source for threads with bound SchedContexts. The legacy fields are retained for backward compatibility during migration. ~5 lines (field addition) | `Object/Types.lean` | Trivial |
| Z1-K | **Add `.schedContext` variant to `KernelObject`.** Extend the `KernelObject` inductive: `\| schedContext (sc : SchedContext)`. Add corresponding `KernelObjectType.schedContext` variant. Update `KernelObject.objectType` match. Update `KernelObjectType.ofNat?`/`toNat` codec (assign value 6). ~15 lines across matches | `Object/Structures.lean` | Small |
| Z1-L | **Add `objectTypeAllocSize` entry for SchedContext.** In `Lifecycle/Operations.lean`: `\| .schedContext => 256`. SchedContext is smaller than CNode/VSpaceRoot but larger than Endpoint (holds replenishment list). Add `requiresPageAlignment` entry: `\| .schedContext => false`. ~4 lines | `Lifecycle/Operations.lean` | Trivial |
| Z1-M | **Define `SchedContext.default` and `empty` constructors.** Default SchedContext with zero budget, default period, no bound thread. Used by `retypeFromUntyped` when creating a new SchedContext object. Add `SchedContext.mk_with_params` convenience constructor that validates well-formedness. ~20 lines | `Types.lean` | Small |
| Z1-N | **Define `ThreadSchedulingParams` accessor.** `def threadSchedulingParams (tcb : TCB) (objects : RHTable ObjId KernelObject) : Priority × Deadline × DomainId × Budget`. Resolves effective scheduling parameters: if `schedContextBinding = .bound scId` or `.donated scId _`, look up SchedContext from objects and return its params; otherwise fall back to TCB's legacy fields. This is the migration bridge. ~25 lines | `Types.lean` | Small |
| Z1-O | **Add `SchedContext` to frozen object representation.** Extend `FrozenKernelObject` inductive in `FrozenState.lean`: `\| schedContext (sc : SchedContext)`. SchedContext has no internal RHTables, so freezing is identity (passthrough like TCB/Endpoint/Notification). Update `freezeObject` match. ~5 lines | `Model/FrozenState.lean` | Trivial |
| Z1-P | **Update `BEq` instances.** Add `BEq SchedContext` (field-wise), `BEq SchedContextBinding`, `BEq ReplenishmentEntry`, `BEq Budget`, `BEq Period`. Follow existing non-lawful convention (V7-F warning). ~30 lines | `Types.lean` | Small |
| Z1-Q | **Create re-export hub.** Write `SeLe4n/Kernel/SchedContext.lean`: `import SeLe4n.Kernel.SchedContext.Types`. Follows re-export hub pattern. ~5 lines | `SchedContext.lean` | Trivial |
| Z1-R | **Build verification.** Run `source ~/.elan/env && lake build SeLe4n.Kernel.SchedContext.Types && lake build SeLe4n.Kernel.SchedContext && lake build SeLe4n.Model.Object.Structures && lake build SeLe4n.Model.FrozenState` to verify all modified modules compile. Run `./scripts/test_fast.sh`. ~0 lines (verification only) | — | Small |

**Intra-phase ordering**: Z1-A must precede Z1-F (SchedContextId used in SchedContext).
Z1-B,C,D,E are independent of each other. Z1-F depends on Z1-A through Z1-E.
Z1-J depends on Z1-I. Z1-K depends on Z1-F. Z1-N depends on Z1-J and Z1-K.
Z1-O depends on Z1-K. Z1-R is terminal.

**Backward compatibility**: All existing code continues to compile. The new
`schedContextBinding` TCB field defaults to `.unbound`, so all existing TCBs
behave identically. The `threadSchedulingParams` accessor falls back to legacy
fields when unbound.

---

### Phase Z2: CBS Budget Engine (24 sub-tasks)

**Goal**: Implement the Constant Bandwidth Server budget management algorithm
as pure functions with machine-checked invariants. No scheduler integration
yet — this phase builds the budget engine in isolation.

**New files**:
- `SeLe4n/Kernel/SchedContext/Budget.lean`
- `SeLe4n/Kernel/SchedContext/Invariant/Defs.lean`
- `SeLe4n/Kernel/SchedContext/Invariant.lean` (re-export hub)

**Prerequisite**: Z1 complete.

| ID | Description | Files | Est. |
|----|-------------|-------|------|
| Z2-A | **Define `consumeBudget` operation.** `def consumeBudget (sc : SchedContext) (ticks : Nat) : SchedContext`. Decrements `budgetRemaining` by `ticks`, saturating at 0. Sets `isActive := budgetRemaining.val > 0` after decrement. Pure function, no state monad. Theorem: `consumeBudget_budgetRemaining_le` (result ≤ input). ~15 lines | `Budget.lean` | Small |
| Z2-B | **Define `isBudgetExhausted` predicate.** `def isBudgetExhausted (sc : SchedContext) : Bool := sc.budgetRemaining.isZero`. Determines whether a thread's scheduling context has run out of CPU budget. Used by `timerTick` to decide preemption. ~5 lines | `Budget.lean` | Trivial |
| Z2-C1 | **Define `mkReplenishmentEntry` constructor.** `def mkReplenishmentEntry (consumed : Budget) (currentTime : Nat) (period : Period) : ReplenishmentEntry`. Creates a single replenishment entry: `{ amount := consumed, eligibleAt := currentTime + period.val }`. Pure helper used by Z2-C2. Theorem: `mkReplenishmentEntry_amount_eq`. ~8 lines | `Budget.lean` | Trivial |
| Z2-C2 | **Define `truncateReplenishments` helper.** `def truncateReplenishments (rs : List ReplenishmentEntry) : List ReplenishmentEntry`. If `rs.length > maxReplenishments`, drop the oldest (head) entry. Returns a list of length ≤ `maxReplenishments`. Theorem: `truncateReplenishments_length_le`. ~10 lines | `Budget.lean` | Trivial |
| Z2-C3 | **Define `scheduleReplenishment` (compose C1+C2).** `def scheduleReplenishment (sc : SchedContext) (currentTime : Nat) (consumed : Budget) : SchedContext`. Creates entry via `mkReplenishmentEntry`, appends to `sc.replenishments`, truncates via `truncateReplenishments`. ~10 lines | `Budget.lean` | Small |
| Z2-D1 | **Define `partitionEligible` helper.** `def partitionEligible (rs : List ReplenishmentEntry) (currentTime : Nat) : List ReplenishmentEntry × List ReplenishmentEntry`. Splits replenishment list into (eligible, not-yet-eligible) based on `eligibleAt ≤ currentTime`. Returns `(due, remaining)`. Theorem: `partitionEligible_disjoint`. ~12 lines | `Budget.lean` | Small |
| Z2-D2 | **Define `sumReplenishments` helper.** `def sumReplenishments (entries : List ReplenishmentEntry) : Nat`. Sums the `amount.val` of all entries. Theorem: `sumReplenishments_nil`, `sumReplenishments_cons`. ~8 lines | `Budget.lean` | Trivial |
| Z2-D3 | **Define `applyRefill` helper.** `def applyRefill (sc : SchedContext) (refillAmount : Nat) : SchedContext`. Adds `refillAmount` to `budgetRemaining`, capped at configured `budget`: `budgetRemaining := ⟨min (sc.budgetRemaining.val + refillAmount) sc.budget.val⟩`. Theorem: `applyRefill_le_budget`. ~8 lines | `Budget.lean` | Trivial |
| Z2-D4 | **Define `processReplenishments` (compose D1+D2+D3).** `def processReplenishments (sc : SchedContext) (currentTime : Nat) : SchedContext`. Calls `partitionEligible`, sums eligible via `sumReplenishments`, applies via `applyRefill`, stores remaining list. ~10 lines | `Budget.lean` | Small |
| Z2-E | **Define `cbsUpdateDeadline` operation.** `def cbsUpdateDeadline (sc : SchedContext) (currentTime : Nat) : SchedContext`. CBS deadline assignment rule: when a SchedContext is replenished and becomes eligible, set `deadline := currentTime + sc.period.val`. If budget was not exhausted (continuing execution), deadline is unchanged. This maintains the CBS invariant that `deadline` reflects the current server period. ~15 lines | `Budget.lean` | Small |
| Z2-F | **Define `cbsBudgetCheck` combined operation.** `def cbsBudgetCheck (sc : SchedContext) (currentTime : Nat) (ticksConsumed : Nat) : SchedContext × Bool`. Combines consume + exhaustion check + replenishment scheduling into a single atomic step. Returns `(updatedSc, wasPreempted)`. This is the per-tick budget accounting entry point. ~20 lines | `Budget.lean` | Small |
| Z2-G | **Define `admissionCheck` predicate.** `def admissionCheck (existing : List SchedContext) (candidate : SchedContext) : Bool`. CBS admission control: total utilization must not exceed 1.0 (or configurable threshold). Computes `Σ(budget_i/period_i) + candidate.budget/candidate.period ≤ threshold`. Uses integer arithmetic (per-mille) to avoid rationals. ~20 lines | `Budget.lean` | Small |
| Z2-H | **Define `SchedContext` invariant: `budgetWithinBounds`.** `def budgetWithinBounds (sc : SchedContext) : Prop := sc.budgetRemaining.val ≤ sc.budget.val ∧ sc.budget.val ≤ sc.period.val`. The fundamental CBS bandwidth constraint: remaining ≤ configured ≤ period. ~8 lines | `Invariant/Defs.lean` | Trivial |
| Z2-I | **Define `replenishmentListWellFormed` invariant.** `def replenishmentListWellFormed (sc : SchedContext) : Prop := sc.replenishments.length ≤ maxReplenishments ∧ ∀ r ∈ sc.replenishments, r.amount.val > 0`. No zero-amount entries, bounded list length. ~10 lines | `Invariant/Defs.lean` | Trivial |
| Z2-J | **Define `schedContextWellFormed` bundle.** Conjunction: `sc.wellFormed ∧ budgetWithinBounds sc ∧ replenishmentListWellFormed sc`. This is the per-object invariant for SchedContext, analogous to `CNode.wellFormed`. ~8 lines | `Invariant/Defs.lean` | Trivial |
| Z2-K | **Prove `consumeBudget_preserves_budgetWithinBounds`.** If `budgetWithinBounds sc`, then `budgetWithinBounds (consumeBudget sc ticks)`. Core preservation theorem. Proof by `Nat.sub_le` and transitivity. ~15 lines | `Invariant/Defs.lean` | Small |
| Z2-L | **Prove `processReplenishments_preserves_budgetWithinBounds`.** Refill is capped at `budget` (configured ceiling), so `budgetRemaining ≤ budget` is maintained. Proof by `Nat.min_le_left`. ~20 lines | `Invariant/Defs.lean` | Small |
| Z2-M | **Prove `scheduleReplenishment_preserves_replenishmentListWellFormed`.** New entry has `consumed > 0` (only called when budget was actually consumed), and list is truncated to `maxReplenishments`. ~15 lines | `Invariant/Defs.lean` | Small |
| Z2-N | **Prove `cbsBudgetCheck_preserves_schedContextWellFormed`.** Composition of Z2-K through Z2-M. The combined operation preserves the full invariant bundle. ~15 lines | `Invariant/Defs.lean` | Small |
| Z2-O1 | **Define `totalConsumed` accumulator.** `def totalConsumed (sc : SchedContext) (window : Nat) : Nat`. Computes the total ticks consumed by a SchedContext over a time window by summing replenishment amounts within the window. Helper for the bandwidth theorem. ~10 lines | `Invariant/Defs.lean` | Trivial |
| Z2-O2 | **Prove single-period bandwidth bound.** `theorem cbs_single_period_bound : ∀ sc, totalConsumed sc sc.period.val ≤ sc.budget.val`. Within one period, consumption is at most `budget` (from `budgetWithinBounds`). Base case for induction. ~10 lines | `Invariant/Defs.lean` | Small |
| Z2-O3 | **Prove CBS bandwidth isolation theorem (multi-period).** `theorem cbs_bandwidth_bounded : ∀ sc window, totalConsumed sc window ≤ sc.budget.val * (window / sc.period.val + 1)`. Induction on `window / period` using Z2-O2 as base case. Each period adds at most `budget` consumption. ~15 lines | `Invariant/Defs.lean` | Small |
| Z2-P | **Create re-export hub.** `SeLe4n/Kernel/SchedContext/Invariant.lean`: `import SeLe4n.Kernel.SchedContext.Invariant.Defs`. ~5 lines | `Invariant.lean` | Trivial |
| Z2-Q | **Build verification.** `lake build SeLe4n.Kernel.SchedContext.Budget && lake build SeLe4n.Kernel.SchedContext.Invariant`. Run `./scripts/test_fast.sh`. | — | Small |

**Intra-phase ordering**: Z2-A,B independent. Z2-C depends on Z2-A (consumes budget
before scheduling replenishment). Z2-D independent of Z2-C. Z2-E depends on Z2-D.
Z2-F depends on Z2-A,B,C. Z2-G independent. Z2-H through Z2-J are invariant defs
(independent of operations). Z2-K through Z2-N are proofs (depend on both ops and defs).
Z2-O depends on Z2-N.

**Key design decisions**:
- **Integer arithmetic only**: No rationals, no floating point. Utilization computed
  as per-mille (`budget * 1000 / period`) for admission control.
- **Bounded replenishment list**: seL4 uses `MIN_REFILLS=2, MAX_REFILLS` varies.
  We use `maxReplenishments=8` as a balance between precision and proof complexity.
- **Saturating decrement**: Budget cannot go negative. Simplifies invariant proofs.

---

### Phase Z3: Replenishment Queue (12 sub-tasks)

**Goal**: Implement a system-wide replenishment queue that tracks when each
SchedContext's budget becomes eligible for refill. This is the timer-driven
backbone of CBS — on each tick, the queue is checked for due replenishments.

**New file**: `SeLe4n/Kernel/SchedContext/ReplenishQueue.lean`

**Prerequisite**: Z1 complete. **Parallelizable with Z2.**

| ID | Description | Files | Est. |
|----|-------------|-------|------|
| Z3-A | **Define `ReplenishQueue` structure.** `structure ReplenishQueue where entries : List (SchedContextId × Nat), size : Nat`. Sorted by eligibility time (ascending). The `Nat` is the absolute tick at which the SchedContext becomes eligible for replenishment. Maintains sorted invariant for O(1) peek at earliest due entry. ~15 lines | `ReplenishQueue.lean` | Small |
| Z3-B | **Define `ReplenishQueue.empty`.** Constructor for empty queue. ~5 lines | `ReplenishQueue.lean` | Trivial |
| Z3-C | **Define `ReplenishQueue.insert` (sorted insertion).** `def insert (rq : ReplenishQueue) (scId : SchedContextId) (eligibleAt : Nat) : ReplenishQueue`. Inserts maintaining sorted order by `eligibleAt`. O(n) insertion but n is bounded by number of active SchedContexts (typically < 64). ~20 lines | `ReplenishQueue.lean` | Small |
| Z3-D | **Define `ReplenishQueue.popDue` (collect eligible entries).** `def popDue (rq : ReplenishQueue) (currentTime : Nat) : ReplenishQueue × List SchedContextId`. Returns all entries with `eligibleAt ≤ currentTime` and the remaining queue. Since entries are sorted, this is a prefix split — O(k) where k = number of due entries. ~15 lines | `ReplenishQueue.lean` | Small |
| Z3-E | **Define `ReplenishQueue.remove` (cancel replenishment).** `def remove (rq : ReplenishQueue) (scId : SchedContextId) : ReplenishQueue`. Removes all entries for a SchedContext (used when SchedContext is unbound or destroyed). O(n) filter. ~10 lines | `ReplenishQueue.lean` | Small |
| Z3-F | **Define `ReplenishQueue.peek` (next due time).** `def peek (rq : ReplenishQueue) : Option Nat`. Returns the eligibility time of the earliest entry, or `none` if empty. O(1) via sorted invariant. ~5 lines | `ReplenishQueue.lean` | Trivial |
| Z3-G | **Define `replenishQueueSorted` invariant.** `def replenishQueueSorted (rq : ReplenishQueue) : Prop := List.Pairwise (· ≤ ·) (rq.entries.map Prod.snd)`. Entries are sorted by eligibility time. ~8 lines | `ReplenishQueue.lean` | Trivial |
| Z3-H | **Prove `insert_preserves_sorted`.** Sorted insertion maintains the sorted invariant. Proof by induction on the entries list with `Nat.le` transitivity. ~20 lines | `ReplenishQueue.lean` | Small |
| Z3-I | **Prove `popDue_preserves_sorted`.** Prefix removal from a sorted list yields a sorted suffix. Proof by `List.Pairwise` suffix lemma. ~10 lines | `ReplenishQueue.lean` | Small |
| Z3-J | **Prove `remove_preserves_sorted`.** Filtering from a sorted list yields a sorted sublist. Proof by `List.Pairwise` filter lemma. ~10 lines | `ReplenishQueue.lean` | Small |
| Z3-K | **Define `replenishQueueConsistent` invariant.** Every `SchedContextId` in the queue corresponds to an active SchedContext in the object store with `isActive = true`. Connects queue membership to kernel object state. ~12 lines | `ReplenishQueue.lean` | Small |
| Z3-L | **Build verification.** `lake build SeLe4n.Kernel.SchedContext.ReplenishQueue`. Run `./scripts/test_fast.sh`. | — | Small |

**Intra-phase ordering**: Z3-A,B first. Z3-C through Z3-F depend on Z3-A.
Z3-G depends on Z3-A. Z3-H through Z3-J depend on Z3-G and their respective
operations. Z3-K depends on Z3-A. Z3-L terminal.

---

### Phase Z4: Scheduler Integration (33 sub-tasks)

**Goal**: Wire the CBS budget engine and replenishment queue into the existing
scheduler. Replace the fixed `timeSlice` decrement with SchedContext-aware
budget accounting. Extend `isBetterCandidate` to use SchedContext deadlines.
Preserve all 9 existing scheduler invariants (`schedulerInvariantBundleFull`)
and add 6 new ones.

**Modified files**:
- `SeLe4n/Kernel/Scheduler/Operations/Selection.lean`
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean`
- `SeLe4n/Kernel/Scheduler/Invariant.lean`
- `SeLe4n/Kernel/Scheduler/Operations/Preservation.lean`
- `SeLe4n/Model/State.lean` (add `replenishQueue` to `SchedulerState`)

**Prerequisites**: Z2 and Z3 complete.

| ID | Description | Files | Est. |
|----|-------------|-------|------|
| Z4-A | **Add `replenishQueue` field to `SchedulerState`.** `replenishQueue : ReplenishQueue := ReplenishQueue.empty`. This tracks system-wide CBS replenishment events. Update `SchedulerState` default. ~5 lines | `State.lean` | Trivial |
| Z4-B | **Define `effectivePriority` accessor.** `def effectivePriority (st : SystemState) (tid : ThreadId) : Option (Priority × Deadline × DomainId)`. Resolves scheduling params from SchedContext if bound, else falls back to TCB legacy fields. Central resolution point used by all scheduler operations. ~20 lines | `Selection.lean` | Small |
| Z4-C | **Define `hasSufficientBudget` eligibility predicate.** `def hasSufficientBudget (st : SystemState) (tid : ThreadId) : Bool`. Returns `true` if the thread's SchedContext has `budgetRemaining > 0`, or if the thread is unbound (legacy mode — always eligible). Unbound threads use the existing `timeSlice` mechanism unchanged. ~15 lines | `Selection.lean` | Small |
| Z4-D | **Compose budget eligibility into `chooseBestRunnableBy`.** `chooseBestRunnableBy` already accepts an `eligible : TCB → Bool` parameter (line 137). Modify the call site to compose `hasSufficientBudget` with the existing eligibility predicate: `eligible := fun tcb => existingEligible tcb && hasSufficientBudget st tcb.tid`. Threads with exhausted budgets are skipped even if they have higher priority. This is the core CBS enforcement point. ~5 lines (call-site modification only) | `Selection.lean` | Trivial |
| Z4-E | **Extend `isBetterCandidate` to use SchedContext deadlines.** The existing 3-level comparison already handles `Priority × Deadline`. Modify the call site to pass SchedContext-derived deadlines via `effectivePriority` instead of raw TCB fields. The comparison logic itself is unchanged — only the input source changes. ~10 lines (modification) | `Selection.lean` | Small |
| Z4-F1 | **Define `timerTickBudget` — unbound branch.** `def timerTickBudget (st : SystemState) : SystemState`. Match on current thread's `schedContextBinding`: if `.unbound`, delegate to existing `timeSlice` decrement logic (reuses existing `timerTick` path which already uses `configDefaultTimeSlice` from `SchedulerState`). ~12 lines | `Core.lean` | Small |
| Z4-F2 | **Define `timerTickBudget` — bound decrement branch.** Extend `timerTickBudget` for `.bound scId` case when `budgetRemaining > 1`: call `consumeBudget sc 1`, write updated SchedContext back to store. ~12 lines | `Core.lean` | Small |
| Z4-F3 | **Define `timerTickBudget` — bound exhaustion branch.** Extend `timerTickBudget` for `.bound scId` case when `budgetRemaining ≤ 1`: call `scheduleReplenishment`, update deadline via `updateDeadline`, preempt current thread (re-enqueue + reschedule). ~18 lines | `Core.lean` | Small |
| Z4-G1 | **Define `popDueReplenishments` helper.** `def popDueReplenishments (rq : ReplenishQueue) (now : Nat) : List SchedContextId × ReplenishQueue`. Wraps `ReplenishQueue.popDue` (Z3-D) at the system level, converting SchedContextIds for use in `refillSchedContext`. Returns due SchedContextIds and remaining queue. ~12 lines | `Core.lean` | Small |
| Z4-G2 | **Define per-SchedContext refill logic.** `def refillSchedContext (st : SystemState) (scId : SchedContextId) : SystemState`. Looks up SchedContext by `scId.toObjId`, calls `processReplenishments` (Z2-D4) with current timer, calls `cbsUpdateDeadline` (Z2-E), writes updated SchedContext back to store. ~10 lines | `Core.lean` | Small |
| Z4-G3 | **Define `processReplenishmentsDue` — compose and re-enqueue.** `def processReplenishmentsDue (st : SystemState) : SystemState`. Calls `popDueReplenishments`, folds `refillSchedContext` over results, re-enqueues bound threads whose budget was restored (was 0, now > 0). ~15 lines | `Core.lean` | Small |
| Z4-H | **Integrate replenishment into `timerTick`.** Modify `timerTick` to: (1) call `processReplenishmentsDue` first, (2) then `timerTickBudget` for current thread, (3) then existing domain scheduling logic. The replenishment check must happen before budget decrement so newly-eligible threads can preempt. ~15 lines (modification) | `Core.lean` | Small |
| Z4-I | **Integrate budget into `schedule`.** Modify `schedule` to verify the chosen thread has sufficient budget before dispatch. If `chooseThread` selects a thread with exhausted budget (race between replenishment and selection), skip it and re-select. In practice this is unreachable because `chooseBestRunnableBy` already filters by budget (Z4-D), but the guard is defense-in-depth. ~10 lines (modification) | `Core.lean` | Small |
| Z4-J | **Integrate budget into `handleYield`.** When a SchedContext-bound thread yields: (1) charge remaining budget as consumed, (2) schedule replenishment for the consumed amount, (3) re-enqueue at updated deadline. This ensures yielding threads don't "bank" unused budget across periods. ~15 lines (modification) | `Core.lean` | Small |
| Z4-K | **Define `budgetPositive` invariant.** `def budgetPositive (st : SystemState) : Prop`. For every SchedContext-bound runnable thread, the SchedContext's `budgetRemaining > 0`. Analogous to `timeSlicePositive` but for the new budget system. ~12 lines | `Invariant.lean` | Small |
| Z4-L | **Define `currentBudgetPositive` invariant.** `def currentBudgetPositive (st : SystemState) : Prop`. If current thread is SchedContext-bound, its SchedContext `budgetRemaining > 0`. Companion to `budgetPositive` (same pattern as `currentTimeSlicePositive`). ~12 lines | `Invariant.lean` | Small |
| Z4-M | **Define `schedContextsWellFormed` invariant.** `def schedContextsWellFormed (st : SystemState) : Prop`. Every SchedContext object in the store satisfies `schedContextWellFormed`. System-wide per-object well-formedness. ~10 lines | `Invariant.lean` | Small |
| Z4-N | **Define `replenishQueueValid` invariant.** `def replenishQueueValid (st : SystemState) : Prop`. The replenish queue is sorted and every entry references an active SchedContext. Connects Z3's queue invariants to system state. ~10 lines | `Invariant.lean` | Small |
| Z4-O | **Define `schedContextBindingConsistent` invariant.** `def schedContextBindingConsistent (st : SystemState) : Prop`. For every TCB with `schedContextBinding = .bound scId`, the SchedContext object exists and `sc.boundThread = some tid`. Bidirectional consistency between TCB and SchedContext. ~15 lines | `Invariant.lean` | Small |
| Z4-P | **Define `effectiveParamsMatchRunQueue` invariant.** For every runnable thread, `runQueue.threadPriority[tid]` matches the effective priority from `effectivePriority` (which may come from SchedContext). Extends `schedulerPriorityMatch` to the SchedContext world. ~12 lines | `Invariant.lean` | Small |
| Z4-Q1 | **Prove `timerTickBudget_exhaustion_removes_runnable`.** When `budgetRemaining ≤ 1`, the thread is preempted and removed from runnable set. `budgetPositive` holds vacuously for the removed thread. ~12 lines | `Preservation.lean` | Small |
| Z4-Q2 | **Prove `timerTickBudget_decrement_positive`.** When `budgetRemaining > 1`, decrement yields `budgetRemaining - 1 > 0`. Proof by `Nat.sub_pos_of_lt` and transitivity. ~12 lines | `Preservation.lean` | Small |
| Z4-R1 | **Prove `popDueReplenishments_preserves_sortedness`.** Removing head elements from a sorted queue preserves sortedness of the remainder. ~10 lines | `Preservation.lean` | Small |
| Z4-R2 | **Prove `refillSchedContext_preserves_active_references`.** Refilling a SchedContext doesn't destroy it; remaining queue entries still reference active objects. ~10 lines | `Preservation.lean` | Small |
| Z4-S1 | **Prove legacy branch preserves 6 new SchedContext invariants.** For unbound threads, the new invariants hold by frame (no SchedContext state modified) or vacuity (no bound threads affected). Prove each of `budgetPositive`, `currentBudgetPositive`, `schedContextsWellFormed`, `replenishQueueValid`, `schedContextBindingConsistent`, `effectiveParamsMatchRunQueue` for the unbound path. ~15 lines | `Preservation.lean` | Small |
| Z4-S2 | **Prove SchedContext branch preserves original 9 invariants.** Budget decrement/exhaustion modifies SchedContext objects and may re-enqueue. Prove each of the original 9 `schedulerInvariantBundleFull` conjuncts is preserved, using field-disjointness where SchedContext fields don't overlap scheduler RunQueue structure. ~15 lines | `Preservation.lean` | Small |
| Z4-S3 | **Prove SchedContext branch preserves 6 new invariants.** Budget decrement preserves `budgetPositive` (Z4-Q1/Q2), exhaustion preserves `replenishQueueValid` (Z4-R1/R2), compose with Z2's `cbsBudgetCheck_preserves_schedContextWellFormed`. ~12 lines | `Preservation.lean` | Small |
| Z4-S4 | **Compose `timerTick_preserves_schedulerInvariantBundleFull` (extended).** Final composition: `rcases hInv` into 15 components, branch on bound/unbound, use Z4-S1/S2/S3 to construct the 15-tuple. ~10 lines | `Preservation.lean` | Small |
| Z4-T1 | **Prove selected thread budget positive.** `chooseThread` selects from `chooseBestRunnableBy` which filters by `hasSufficientBudget` (Z4-D). Selected thread therefore has `budgetRemaining > 0`. ~10 lines | `Preservation.lean` | Small |
| Z4-T2 | **Prove dequeue preserves budgetPositive.** Dequeued thread removed from runnable set. `budgetPositive` universal quantifier domain shrinks. Preservation is vacuous for the removed thread. ~10 lines | `Preservation.lean` | Small |
| Z4-U | **Prove `handleYield_preserves_schedContextWellFormed`.** Yield charges and schedules replenishment; both operations preserve SchedContext well-formedness (Z2-N). ~15 lines | `Preservation.lean` | Small |
| Z4-V1 | **Build scheduler modules.** `lake build SeLe4n.Kernel.Scheduler.Operations && lake build SeLe4n.Kernel.Scheduler.Invariant`. Verify zero `sorry`/`axiom` in new code. ~2 min | — | Small |
| Z4-V2 | **Run smoke test and verify backward compatibility.** `./scripts/test_smoke.sh`. Verify existing tests pass unchanged with unbound (legacy) threads. Check that `timerTick` behavior for unbound threads is identical to pre-Z4. ~3 min | — | Small |

**Intra-phase ordering**: Z4-A first. Z4-B,C independent of each other but
depend on Z4-A. Z4-D,E depend on Z4-B,C. Z4-F1/F2/F3 sequential (build up
`timerTickBudget`). Z4-G1/G2/G3 sequential (build up `processReplenishmentsDue`).
Z4-F and Z4-G independent of each other but depend on Z4-B. Z4-H depends on
Z4-F3,G3. Z4-I depends on Z4-D. Z4-J depends on Z4-F3. Z4-K through Z4-P
are invariant defs (depend on Z4-A,B). Z4-Q1/Q2 depend on Z4-F,K,L. Z4-R1/R2
depend on Z4-G,N. Z4-S1/S2/S3/S4 depend on all Q/R sub-tasks. Z4-T1/T2
depend on Z4-D,K,L. Z4-U depends on Z4-J,M. Z4-V1/V2 terminal.

**Migration strategy**: Threads with `schedContextBinding = .unbound` use
the existing `timeSlice` path unchanged. This means all existing tests pass
without modification. The new SchedContext path activates only when a thread
is explicitly bound to a SchedContext via capability operations (Phase Z5).

---

### Phase Z5: Capability-Controlled Thread Binding (25 sub-tasks)

**Goal**: Implement capability-gated operations to bind threads to scheduling
contexts, configure scheduling parameters, and enforce admission control.
This is where execution becomes a capability-controlled resource.

**New files**:
- `SeLe4n/Kernel/SchedContext/Operations.lean`
- `SeLe4n/Kernel/SchedContext/Invariant/Preservation.lean`

**Modified files**:
- `SeLe4n/Model/Object/Types.lean` (new SyscallId variants)
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean` (new decode structs)
- `SeLe4n/Kernel/API.lean` (new dispatch arms)

**Prerequisites**: Z2 complete. **Parallelizable with Z4** (after Z2).

| ID | Description | Files | Est. |
|----|-------------|-------|------|
| Z5-A | **Define `SchedContextConfigure` syscall arguments.** `structure SchedContextConfigureArgs where budget : Nat, period : Nat, priority : Nat, deadline : Nat, domain : Nat`. Add decode/encode functions following `SyscallArgDecode.lean` patterns. Requires 5 message registers. ~35 lines | `SyscallArgDecode.lean` | Small |
| Z5-B | **Define `SchedContextBind` syscall arguments.** `structure SchedContextBindArgs where threadId : Nat`. Thread to bind. Requires 1 message register. Add decode/encode. ~15 lines | `SyscallArgDecode.lean` | Trivial |
| Z5-C | **Define `SchedContextUnbind` syscall arguments.** No additional args (SchedContext from capability target). Add decode (trivial). ~10 lines | `SyscallArgDecode.lean` | Trivial |
| Z5-D | **Add `SyscallId` variants.** Add `.schedContextConfigure` (17), `.schedContextBind` (18), `.schedContextUnbind` (19) to `SyscallId` enum. Update `ofNat?`/`toNat` codec. Update `toNat_injective` proof. ~15 lines | `Object/Types.lean` | Small |
| Z5-E | **Add `syscallRequiredRight` entries.** `.schedContextConfigure => .write`, `.schedContextBind => .write`, `.schedContextUnbind => .write`. ~3 lines | `API.lean` | Trivial |
| Z5-F1 | **Define parameter validation for `schedContextConfigure`.** `def validateSchedContextParams (args : SchedContextConfigureArgs) : Except KernelError Unit`. Checks: `period > 0`, `budget ≤ period`, `priority ≤ maxPriority`, `domain < numDomains`. Returns descriptive error on failure. ~15 lines | `Operations.lean` | Small |
| Z5-F2 | **Define admission control check.** Collect all existing SchedContexts from the object store, call `admissionCheck` (Z2-G) with the candidate parameters. Reject if total utilization would exceed threshold. ~10 lines | `Operations.lean` | Small |
| Z5-F3 | **Define `schedContextConfigure` — compose and store.** `def schedContextConfigure (scId : ObjId) (args : SchedContextConfigureArgs) : Kernel Unit`. Calls Z5-F1 validation, Z5-F2 admission check, then updates SchedContext object fields in the store. ~15 lines | `Operations.lean` | Small |
| Z5-G1 | **Define `schedContextBind` — precondition checks.** Lookup SchedContext and TCB. Verify `sc.boundThread = none` and `tcb.schedContextBinding = .unbound`. Return error if either precondition fails. ~12 lines | `Operations.lean` | Small |
| Z5-G2 | **Define `schedContextBind` — bidirectional binding.** Set `sc.boundThread := some tid` and `tcb.schedContextBinding := .bound scId`. Write both updated objects to store. ~10 lines | `Operations.lean` | Small |
| Z5-G3 | **Define `schedContextBind` — RunQueue priority update.** If thread is in RunQueue, remove and re-insert with SchedContext-derived priority. Ensures `effectiveParamsMatchRunQueue` invariant. ~12 lines | `Operations.lean` | Small |
| Z5-H1 | **Define `schedContextUnbind` — preemption guard.** If bound thread is current, trigger preemption first (save context, clear current). Prevents unbinding the running thread without rescheduling. ~10 lines | `Operations.lean` | Small |
| Z5-H2 | **Define `schedContextUnbind` — RunQueue removal and unbinding.** If thread is runnable, remove from RunQueue. Clear `sc.boundThread` and `tcb.schedContextBinding := .unbound`. Write both objects. ~12 lines | `Operations.lean` | Small |
| Z5-H3 | **Define `schedContextUnbind` — replenish queue cleanup.** Remove SchedContext from replenish queue (pending replenishments no longer relevant after unbind). ~8 lines | `Operations.lean` | Trivial |
| Z5-I1 | **Define `schedContextYieldTo` — budget transfer (kernel-internal).** `def schedContextYieldTo (st : SystemState) (fromScId targetScId : SchedContextId) : SystemState`. Transfer `budgetRemaining` from source to target SchedContext. Cap at target's configured `budget`. This is a kernel-internal helper for hierarchical scheduling, **not a userspace syscall** — no SyscallId or decode is defined in this workstream. A future workstream may expose it as a 4th SchedContext syscall if needed. ~12 lines | `Operations.lean` | Small |
| Z5-I2 | **Define `schedContextYieldTo` — re-enqueue target.** If target SchedContext's bound thread was waiting for budget (budget was 0, now > 0), enqueue it in RunQueue. ~12 lines | `Operations.lean` | Small |
| Z5-J | **Wire dispatch for new syscalls.** Add arms to `dispatchWithCap` and `dispatchWithCapChecked` in `API.lean`. Route `.schedContextConfigure`, `.schedContextBind`, `.schedContextUnbind` through `syscallInvoke` with capability gate. ~20 lines | `API.lean` | Small |
| Z5-K | **Prove `schedContextBind_preserves_schedContextBindingConsistent`.** After bind, the bidirectional TCB ↔ SchedContext references are consistent. ~20 lines | `Preservation.lean` | Small |
| Z5-L | **Prove `schedContextUnbind_preserves_schedContextBindingConsistent`.** After unbind, both sides cleared. Thread reverts to unbound state. ~15 lines | `Preservation.lean` | Small |
| Z5-M | **Prove `schedContextConfigure_preserves_schedContextsWellFormed`.** Validated parameters satisfy well-formedness. Admission control prevents over-commitment. ~20 lines | `Preservation.lean` | Small |
| Z5-N1 | **Prove `schedContextBind_preserves_schedulerPriorityMatch`.** RunQueue re-insert (Z5-G3) uses SchedContext priority, which matches `threadPriority` map entry. ~12 lines | `Preservation.lean` | Small |
| Z5-N2 | **Prove `schedContextBind_preserves_effectiveParamsMatchRunQueue`.** After bind, `effectivePriority` resolves from SchedContext (not legacy TCB fields). The re-inserted priority matches this effective priority. ~12 lines | `Preservation.lean` | Small |
| Z5-O | **Add information-flow wrappers.** `schedContextConfigureChecked`, `schedContextBindChecked`, `schedContextUnbindChecked` with `securityFlowsTo` gates. Thread binding crosses security domains when thread and SchedContext are in different domains. ~25 lines | `Enforcement/Wrappers.lean` | Small |
| Z5-P1 | **Build SchedContext and API modules.** `lake build SeLe4n.Kernel.SchedContext.Operations && lake build SeLe4n.Kernel.API`. Verify zero `sorry`/`axiom`. ~2 min | — | Small |
| Z5-P2 | **Run smoke test.** `./scripts/test_smoke.sh`. Verify new syscall IDs don't break existing dispatch paths. ~3 min | — | Small |

**Intra-phase ordering**: Z5-A through Z5-D are independent type definitions.
Z5-E depends on Z5-D. Z5-F1/F2/F3 sequential. Z5-G1/G2/G3 sequential.
Z5-H1/H2/H3 sequential. Z5-I1/I2 sequential. All F/G/H/I depend on Z5-A
through Z5-D. Z5-J depends on Z5-D,E,F3,G3,H3. Z5-K through Z5-M depend on
Z5-F3,G3,H3. Z5-N1/N2 depend on Z5-G3. Z5-O depends on Z5-F3,G3,H3.
Z5-P1/P2 terminal.

**Security model**: SchedContext operations require capabilities with `.write`
rights targeting the SchedContext object. A thread can only be bound to a
SchedContext if the caller holds capabilities to both the thread's TCB and
the SchedContext. This means:

- **Resource isolation**: A domain cannot consume CPU budget it doesn't own.
- **Admission control**: System-wide bandwidth is bounded.
- **Dynamic rebinding**: Threads can be unbound and rebound at runtime via
  capability operations (e.g., migrating a thread between CPU allocations).

---

### Phase Z6: Timeout Endpoints (26 sub-tasks)

**Goal**: Add budget-driven timeout to all blocking IPC operations. When a
thread's SchedContext budget expires while the thread is blocked on IPC, the
thread is unblocked with a timeout error. This eliminates unbounded IPC
blocking (limitation L-5) and closes starvation vector SV-3 from WS-V.

**Modified files**:
- `SeLe4n/Model/Object/Types.lean` (timeout metadata in ThreadIpcState)
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (endpointSendDual/ReceiveDual/Call timeout metadata)
- `SeLe4n/Kernel/IPC/DualQueue/Core.lean` (new endpointQueueRemove)
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (timeoutThread, timeoutAwareReceive)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean`
- `SeLe4n/Kernel/Scheduler/Operations/Core.lean`

**Prerequisites**: Z4 complete.

| ID | Description | Files | Est. |
|----|-------------|-------|------|
| Z6-A | **Add timeout metadata to blocking IPC states.** Extend `ThreadIpcState` variants to carry optional timeout info: `blockedOnSend (endpoint : ObjId) (timeoutBudget : Option SchedContextId := none)`, `blockedOnReceive (endpoint : ObjId) (timeoutBudget : Option SchedContextId := none)`, `blockedOnCall (endpoint : ObjId) (timeoutBudget : Option SchedContextId := none)`, `blockedOnReply (endpoint : ObjId) (replyTarget : Option ThreadId) (timeoutBudget : Option SchedContextId := none)`. The `timeoutBudget` field records which SchedContext's budget bounds this blocking operation. `none` = no timeout (legacy/unbound). ~15 lines (field additions) | `Object/Types.lean` | Small |
| Z6-B1 | **Update IPC operation pattern matches.** Add `timeoutBudget` field to `blockedOnSend`/`blockedOnReceive`/`blockedOnCall`/`blockedOnReply` matches in `DualQueue/Transport.lean` and `DualQueue/Core.lean`. Use `..` syntax where the field is irrelevant. ~20 lines across 2 files | `DualQueue/Transport.lean`, `DualQueue/Core.lean` | Small |
| Z6-B2 | **Update IPC invariant proof pattern matches.** Add `timeoutBudget` field handling in `EndpointPreservation.lean`, `CallReplyRecv.lean`, `NotificationPreservation.lean`. Since field defaults to `none`, existing proofs need only the additional wildcard. ~20 lines across 3 files | `Invariant/*.lean` | Small |
| Z6-B3 | **Update scheduler/lifecycle IPC state matches.** Add `timeoutBudget` field to pattern matches in `Lifecycle/Operations.lean` (`cleanupTcbReferences`) and scheduler code that inspects IPC state. ~10 lines across 2 files | `Lifecycle/Operations.lean`, `Core.lean` | Trivial |
| Z6-C1 | **Define `timeoutThread` — IPC state reset.** Set `tcb.ipcState := .ready`, clear `tcb.pendingMessage := none`. Write updated TCB to store. ~10 lines | `Endpoint.lean` | Small |
| Z6-C2 | **Define `timeoutThread` — endpoint queue removal.** Call `endpointQueueRemove` (Z6-D) to dequeue the timed-out thread from the endpoint's sendQ or recvQ. ~8 lines | `Endpoint.lean` | Trivial |
| Z6-C3 | **Define `timeoutThread` — scheduler re-enqueue.** Set timeout error code in register context (`tcb.regs.gpr 0 := timeoutErrorCode`). Re-enqueue thread in RunQueue with current effective priority. ~12 lines | `Endpoint.lean` | Small |
| Z6-D1 | **Define `endpointQueueRemove` — queue location lookup.** Determine whether thread is in sendQ or recvQ (from `isReceiveQ` parameter). Look up the endpoint and verify thread is actually in the specified queue. ~10 lines | `DualQueue/Core.lean` | Small |
| Z6-D2 | **Define `endpointQueueRemove` — mid-queue splice-out.** Adapt `spliceOutMidQueueNode` pattern (from `Lifecycle/Operations.lean:60`): patch predecessor's `queueNext` to successor, patch successor's `queuePrev` to predecessor. Handle head/tail edge cases. Write updated TCBs and endpoint. ~15 lines | `DualQueue/Core.lean` | Small |
| Z6-E | **Integrate timeout into `timerTickBudget` — blocked thread scan.** In the budget exhaustion branch of `timerTickBudget` (Z4-F3): after preempting the running thread, scan all blocked threads whose `timeoutBudget = some scId` references the now-exhausted SchedContext. For each such thread, call `timeoutThread`. Rationale: the running thread consumed the last tick of the SC's budget; any blocked thread whose IPC was bounded by that SC must now be timed out. In the donation case, the client blocked on reply with `timeoutBudget = some clientScId` is timed out when the server (running on the donated SC) exhausts the budget. ~18 lines (modification) | `Core.lean` | Small |
| Z6-F | **Integrate timeout into `processReplenishmentsDue`.** After processing replenishments, no timeout action is needed — replenishment *restores* budget, which is the opposite of timeout. However, verify that replenished SchedContexts whose bound threads are blocked do NOT get incorrectly timed out (guard: only timeout when `budgetRemaining = 0`). Add defensive assertion. ~8 lines (modification) | `Core.lean` | Trivial |
| Z6-G | **Set timeout metadata on IPC blocking.** Modify `endpointSendDual` to set `timeoutBudget := tcb.schedContextBinding.scId?` when blocking. Same for `endpointReceiveDual`, `endpointCall`. The timeout is tied to the caller's own SchedContext budget: when the budget expires, the IPC times out. ~15 lines across Transport.lean | `DualQueue/Transport.lean` | Small |
| Z6-H | **Define `IpcTimeoutResult` type.** `inductive IpcTimeoutResult where \| completed (msg : IpcMessage) \| timedOut`. Returned by timeout-aware IPC operations to distinguish successful delivery from timeout. ~8 lines | `Object/Types.lean` | Trivial |
| Z6-I | **Define `timeoutAwareReceive` wrapper.** `def timeoutAwareReceive (endpointId : ObjId) (receiver : ThreadId) : Kernel IpcTimeoutResult`. Wraps `endpointReceiveDual` with timeout semantics. If the receive completes before budget expiry, returns `.completed`. If budget expires during blocking, `timeoutThread` is called by the timer tick path and the thread observes `.timedOut` when it resumes. ~20 lines | `Endpoint.lean` | Small |
| Z6-J | **Define `blockedThreadTimeoutConsistent` invariant.** `def blockedThreadTimeoutConsistent (st : SystemState) : Prop`. For every blocked thread with `timeoutBudget = some scId`: (1) the SchedContext exists, (2) the thread's TCB references the correct endpoint. Prevents dangling timeout references. ~15 lines | `Invariant/Defs.lean` | Small |
| Z6-K1 | **Prove queue removal preserves well-formedness.** `endpointQueueRemove` reduces queue size by 1, removed thread no longer in queue. Follows from `spliceOutMidQueueNode` correctness already proven in `Transport.lean`. ~12 lines | `Invariant/EndpointPreservation.lean` | Small |
| Z6-K2 | **Prove queue removal preserves link integrity and acyclicity.** Predecessor/successor patching maintains bidirectional link chain. No cycles introduced (chain shortened). ~12 lines | `Invariant/EndpointPreservation.lean` | Small |
| Z6-L1 | **Prove timeout unblock preserves blocking/runnable consistency.** Thread transitions from blocked to ready. `blockedOn*NotRunnable` no longer applies (thread is runnable). `runnableThreadIpcReady` now includes the thread (ipcState = .ready). ~12 lines | `Invariant/EndpointPreservation.lean` | Small |
| Z6-L2 | **Prove timeout preserves remaining 8 IPC conjuncts.** Clear pending message preserves `waitingThreadsPendingMessageNone`. Re-enqueue preserves queue membership consistency. Compose with Z6-K for queue invariants. ~15 lines | `Invariant/EndpointPreservation.lean` | Small |
| Z6-M1 | **Prove predecessor link patching correctness.** After removal, predecessor's `queueNext` points to removed thread's successor. If removed thread was head, endpoint head pointer updated. ~10 lines | `DualQueue/Transport.lean` | Small |
| Z6-M2 | **Prove successor link patching correctness.** After removal, successor's `queuePrev` points to removed thread's predecessor. If removed thread was tail, endpoint tail pointer updated. Bidirectional consistency maintained. ~10 lines | `DualQueue/Transport.lean` | Small |
| Z6-N | **Update `ipcStateQueueMembershipConsistent` for timeout.** Timed-out threads are removed from queues and set to `.ready`, so membership must be updated. Prove preservation through `timeoutThread`. ~15 lines | `Invariant/QueueMembership.lean` | Small |
| Z6-O1 | **Update EndpointPreservation.lean proofs for `timeoutBudget` field.** Add `none` case handling to preservation theorems that destructure `ThreadIpcState`. Most need only a wildcard or `rfl` addition. ~15 lines | `Invariant/EndpointPreservation.lean` | Small |
| Z6-O2 | **Update CallReplyRecv.lean and NotificationPreservation.lean proofs.** Same pattern as Z6-O1 for the remaining IPC preservation files. ~15 lines across 2 files | `CallReplyRecv.lean`, `NotificationPreservation.lean` | Small |
| Z6-P1 | **Build IPC and scheduler modules.** `lake build SeLe4n.Kernel.IPC.Operations && lake build SeLe4n.Kernel.IPC.Invariant && lake build SeLe4n.Kernel.Scheduler.Operations`. Verify zero `sorry`/`axiom`. ~2 min | — | Small |
| Z6-P2 | **Run smoke test.** `./scripts/test_smoke.sh`. Verify timeout-related changes don't break existing IPC tests. ~3 min | — | Small |

**Intra-phase ordering**: Z6-A first (type changes). Z6-B1/B2/B3 depend on
Z6-A (match updates, can be parallelized across files). Z6-C1/C2/C3 sequential.
Z6-D1/D2 sequential. Z6-C and Z6-D independent but both depend on Z6-A.
Z6-E,F depend on Z6-C3. Z6-G depends on Z6-A. Z6-H independent. Z6-I depends
on Z6-C3,G,H. Z6-J depends on Z6-A. Z6-K1/K2 depend on Z6-D2,J. Z6-L1/L2
depend on Z6-C3,K. Z6-M1/M2 depend on Z6-D2. Z6-N depends on Z6-C3.
Z6-O1/O2 depend on Z6-A (can parallelize with B tasks). Z6-P1/P2 terminal.

**seL4 MCS correspondence**: In seL4 MCS, timeout is handled via "timeout
endpoints" — special notification objects that signal when a SchedContext's
budget expires. Our design is simpler: the timeout is implicit in the budget
system. When a thread's SchedContext budget expires while the thread is
blocked, the timer tick handler unblocks the thread directly. This avoids
the complexity of timeout endpoint objects while providing the same guarantee:
no IPC blocks indefinitely if the caller has a finite budget.

**Cross-cutting concern — timeout + donation**: When a client's SchedContext is
donated to a passive server (Z7), the server runs on the client's budget. The
client is blocked on reply with `timeoutBudget = some clientScId`. If the server
consumes all of the donated budget, `timerTickBudget` exhausts the SchedContext
and Z6-E fires: the server is preempted (budget exhaustion), AND the client is
timed out (budget-bounded IPC). The client observes a timeout error; the server
becomes passive (unbound, removed from RunQueue). The SchedContext returns to the
client via the timeout cleanup path, not the normal reply path. This interaction
between Z6 and Z7 is safe because: (1) the SchedContext has exactly one `boundThread`
at any time (the server during donation), (2) the client's `timeoutBudget` references
the same SchedContext, (3) timeout cleanup and donation return are mutually exclusive
(timeout fires only when budget = 0, at which point normal reply has not occurred).
Z6-E's blocked-thread scan and Z7-P's lifecycle cleanup together guarantee no
dangling donation references after timeout.

---

### Phase Z7: SchedContext Donation / Passive Servers (26 sub-tasks)

**Goal**: Implement SchedContext lending during IPC Call/Reply, enabling passive
servers that consume zero CPU when idle. When a client calls a server, the
client's SchedContext is temporarily donated to the server. The server runs
on the client's budget and returns the SchedContext when it replies.

**Modified files**:
- `SeLe4n/Kernel/IPC/DualQueue/Transport.lean` (endpointCall donation, endpointReply return, endpointReplyRecv swap)
- `SeLe4n/Kernel/IPC/Operations/Endpoint.lean` (donation cleanup helpers)
- `SeLe4n/Kernel/IPC/Invariant/Defs.lean`
- `SeLe4n/Kernel/IPC/Invariant/CallReplyRecv.lean`
- `SeLe4n/Kernel/Lifecycle/Operations.lean` (donation cleanup on destroy)

**Prerequisites**: Z4 complete. **Partially parallelizable with Z6** (Z7 modifies
`endpointCall`/`endpointReply`/`endpointReplyRecv` in Transport.lean; Z6 modifies
`endpointSendDual`/`endpointReceiveDual` and adds `timeoutThread` — different
functions in the same file, so merge conflicts are possible but logic is independent).

| ID | Description | Files | Est. |
|----|-------------|-------|------|
| Z7-A | **Define donation semantics.** Document the SchedContext donation protocol: (1) Client calls server via `endpointCall`. (2) Client's SchedContext is "lent" to server: server's TCB gets `schedContextBinding := .donated(clientScId, clientTid)`. (3) Server runs on client's budget. (4) Server replies via `endpointReply`. (5) SchedContext returned to client: server's TCB reverts to previous binding. This is a design document within the code (module docstring). ~30 lines comment | `DualQueue/Transport.lean` | Small |
| Z7-B1 | **Detect passive server in `endpointCall`.** After blocking the client, check if the receiving server has `schedContextBinding = .unbound`. If server is active (already has SchedContext), skip donation — no changes needed. ~8 lines | `DualQueue/Transport.lean` | Trivial |
| Z7-B2 | **Perform donation transfer in `endpointCall`.** For passive servers: save client's `SchedContextId`, set `server.schedContextBinding := .donated(clientScId, clientTid)`, set `sc.boundThread := some serverTid`. Write both updated objects. ~12 lines | `DualQueue/Transport.lean` | Small |
| Z7-B3 | **Enqueue donated server in RunQueue.** After donation, enqueue server in RunQueue with the donated SchedContext's priority and deadline. Server becomes runnable on the client's budget. ~10 lines | `DualQueue/Transport.lean` | Small |
| Z7-C1 | **Detect donated binding in `endpointReply`.** Check if server's `schedContextBinding` is `.donated(scId, originalOwner)`. If `.bound` or `.unbound`, skip return logic — this is a normal reply. ~8 lines | `DualQueue/Transport.lean` | Trivial |
| Z7-C2 | **Return SchedContext to original client.** Rebind SchedContext: `sc.boundThread := some originalOwner`, `originalOwner.schedContextBinding := .bound scId`, `server.schedContextBinding := .unbound`. Write all three objects. ~12 lines | `DualQueue/Transport.lean` | Small |
| Z7-C3 | **Remove passive server from RunQueue.** If server has no own SchedContext after return (binding = `.unbound`), remove from RunQueue. Server returns to passive/idle state. ~8 lines | `DualQueue/Transport.lean` | Trivial |
| Z7-D1 | **Return SchedContext in `endpointReplyRecv`.** Reuse Z7-C1/C2/C3 logic: detect donated binding, return SchedContext to previous client, remove server from RunQueue if passive. ~8 lines (reuse helper) | `DualQueue/Transport.lean` | Small |
| Z7-D2 | **Accept new donation in `endpointReplyRecv`.** If a new client is waiting on send queue, accept its call. Reuse Z7-B1/B2/B3 logic: detect passive server, donate new client's SchedContext, enqueue server. Atomic transition from one client's budget to the next. ~12 lines | `DualQueue/Transport.lean` | Small |
| Z7-E | **Handle donation during `endpointReceiveDual`.** When a passive server receives (blocking case): if server has `.donated` binding from a previous call that was never replied to (abnormal path), the donation must be cleaned up before blocking. Set `schedContextBinding := .unbound` and return SchedContext to original owner. ~15 lines (modification) | `DualQueue/Transport.lean` | Small |
| Z7-F | **Define `donationChainAcyclic` invariant.** `def donationChainAcyclic (st : SystemState) : Prop`. No thread can transitively donate to itself: if A donates to B and B donates to C, C ≠ A. Prevents circular donation chains that would cause resource leaks. Formalized as well-foundedness on donation edges. ~15 lines | `Invariant/Defs.lean` | Small |
| Z7-G | **Define `donationOwnerValid` invariant.** `def donationOwnerValid (st : SystemState) : Prop`. For every TCB with `.donated(scId, originalOwner)`: (1) SchedContext exists, (2) `originalOwner` exists as a TCB, (3) `originalOwner` is blocked on reply (waiting for the server). Ensures donation can always be returned. ~15 lines | `Invariant/Defs.lean` | Small |
| Z7-H | **Define `passiveServerIdle` invariant.** `def passiveServerIdle (st : SystemState) : Prop`. A thread with `schedContextBinding = .unbound` that is not in the RunQueue and not current is considered a passive server. Such threads must be blocked on receive or inactive — not blocked on send/call (which requires a SchedContext for timeout). ~12 lines | `Invariant/Defs.lean` | Small |
| Z7-I | **Define `donationBudgetTransfer` invariant.** When a SchedContext is donated, the budget tracking must be consistent: the donated SchedContext's `boundThread` matches the server, and the client's TCB records the donation source. No SchedContext can be simultaneously bound to two threads. ~12 lines | `Invariant/Defs.lean` | Small |
| Z7-J1 | **Prove server binding → SchedContext consistency after donation.** After Z7-B2: `server.schedContextBinding = .donated(scId, _)` and `sc.boundThread = some serverTid`. Bidirectional reference from server side. ~12 lines | `CallReplyRecv.lean` | Small |
| Z7-J2 | **Prove client binding cleared during donation.** Client is blocked on reply with SchedContext lent away. Client's `schedContextBinding` is either `.bound` (SchedContext still exists but `boundThread` now points to server) or tracked via donation metadata. Consistency preserved. ~12 lines | `CallReplyRecv.lean` | Small |
| Z7-K1 | **Prove SchedContext rebound to client after reply.** After Z7-C2: `sc.boundThread = some originalOwner` and `originalOwner.schedContextBinding = .bound scId`. Bidirectional consistency restored. ~10 lines | `CallReplyRecv.lean` | Small |
| Z7-K2 | **Prove server reverts to unbound after reply.** After Z7-C2: `server.schedContextBinding = .unbound`. Server no longer references any SchedContext. `schedContextBindingConsistent` holds vacuously for server. ~10 lines | `CallReplyRecv.lean` | Small |
| Z7-L | **Prove `donationChainAcyclic_preserved_by_call`.** New donation edge cannot create a cycle: client is blocked (cannot donate further), so chain grows linearly. ~15 lines | `CallReplyRecv.lean` | Small |
| Z7-M | **Prove `donationChainAcyclic_preserved_by_reply`.** Donation edge removed on reply. Chain shrinks. ~10 lines | `CallReplyRecv.lean` | Small |
| Z7-N1 | **Prove old donation removed in ReplyRecv.** Return step (Z7-D1) removes server's `.donated` binding. `schedContextBindingConsistent` holds after removal (same as Z7-K1/K2). ~12 lines | `CallReplyRecv.lean` | Small |
| Z7-N2 | **Prove new donation added in ReplyRecv.** Accept step (Z7-D2) creates new `.donated` binding. `schedContextBindingConsistent` holds after creation (same as Z7-J1/J2). Compose return + accept for end-to-end consistency. ~12 lines | `CallReplyRecv.lean` | Small |
| Z7-O | **Update `ipcInvariantFull` with donation invariants.** Add `donationChainAcyclic`, `donationOwnerValid`, `passiveServerIdle`, `donationBudgetTransfer` to the IPC invariant bundle. Update projection theorems. ~15 lines | `Invariant/Defs.lean` | Small |
| Z7-P | **Handle donation cleanup in lifecycle.** When a thread with `.donated` binding is destroyed (retyped away), the SchedContext must be returned to the original owner first. Extend `cleanupTcbReferences` to handle donation return. ~15 lines | `Lifecycle/Operations.lean` | Small |
| Z7-Q1 | **Build IPC modules.** `lake build SeLe4n.Kernel.IPC.Operations && lake build SeLe4n.Kernel.IPC.Invariant`. Verify zero `sorry`/`axiom`. ~2 min | — | Small |
| Z7-Q2 | **Run smoke test.** `./scripts/test_smoke.sh`. Verify donation changes don't break existing IPC call/reply/replyrecv tests. ~3 min | — | Small |

**Intra-phase ordering**: Z7-A first (design). Z7-B1/B2/B3 sequential (build
`endpointCall` donation). Z7-C1/C2/C3 sequential (build `endpointReply` return).
Z7-D1/D2 depend on Z7-B3,C3 (reuse helpers). Z7-E depends on Z7-B3. Z7-F
through Z7-I are invariant defs (depend on Z7-A). Z7-J1/J2 depend on Z7-B3,F-I.
Z7-K1/K2 depend on Z7-C3,F-I. Z7-L,M depend on Z7-B3,C3. Z7-N1/N2 depend
on Z7-D2,J,K. Z7-O depends on Z7-F through Z7-I. Z7-P depends on Z7-B3.
Z7-Q1/Q2 terminal.

**Passive server example**: A file system server creates a TCB with no
SchedContext (passive). It blocks on `endpointReceiveDual`. When a client
calls via `endpointCall`, the client's SchedContext is donated to the server.
The server processes the request using the client's CPU budget. On
`endpointReply`, the SchedContext returns to the client. The server blocks
on receive again with zero CPU consumption. This eliminates L-3 (no passive
server support) and enables efficient server pooling.

---

### Phase Z8: API Surface & Syscall Wiring (17 sub-tasks)

**Goal**: Complete the public API surface for SchedContext operations. Wire
new syscalls through the register decode → dispatch → invoke pipeline. Add
frozen operation variants. Update test harness and fixtures.

**Modified files**:
- `SeLe4n/Kernel/API.lean`
- `SeLe4n/Kernel/Architecture/RegisterDecode.lean`
- `SeLe4n/Kernel/Architecture/SyscallArgDecode.lean`
- `SeLe4n/Kernel/FrozenOps/Operations.lean`
- `SeLe4n/Testing/MainTraceHarness.lean`
- `tests/fixtures/main_trace_smoke.expected`

**Prerequisites**: Z5, Z6, Z7 complete.

| ID | Description | Files | Est. |
|----|-------------|-------|------|
| Z8-A | **Add round-trip theorems for new syscall decode.** `decodeSyscallId_roundtrip` must cover new IDs 17-19. `decodeSchedContextConfigureArgs_roundtrip`, `decodeSchedContextBindArgs_roundtrip`. Follow existing patterns in `SyscallArgDecode.lean`. ~25 lines | `SyscallArgDecode.lean` | Small |
| Z8-B | **Add error-exclusivity theorems for new decode.** `decodeSchedContextConfigureArgs_error_iff : ... ↔ msgRegs.size < 5`. `decodeSchedContextBindArgs_error_iff : ... ↔ msgRegs.size < 1`. Follow existing patterns. ~20 lines | `SyscallArgDecode.lean` | Small |
| Z8-C | **Wire `dispatchWithCap` for `.schedContextConfigure`.** Decode args from message registers, invoke `schedContextConfigure` with resolved SchedContext ObjId from capability target. ~15 lines | `API.lean` | Small |
| Z8-D | **Wire `dispatchWithCap` for `.schedContextBind`.** Decode `threadId` from message registers, invoke `schedContextBind`. ~10 lines | `API.lean` | Small |
| Z8-E | **Wire `dispatchWithCap` for `.schedContextUnbind`.** No additional args, invoke `schedContextUnbind` with SchedContext ObjId. ~8 lines | `API.lean` | Trivial |
| Z8-F | **Wire `dispatchWithCapChecked` for all three.** Route through information-flow-checked wrappers (Z5-O). ~15 lines | `API.lean` | Small |
| Z8-G | **Update `dispatchWithCap_wildcard_unreachable` proof.** Extend to cover 20 `SyscallId` variants (was 17). ~5 lines | `API.lean` | Trivial |
| Z8-H | **Add frozen SchedContext operations.** `frozenSchedContextConfigure`, `frozenSchedContextBind`, `frozenSchedContextUnbind` in `FrozenOps/Operations.lean`. SchedContext is passthrough-frozen (no internal RHTables), so these are straightforward wrappers around `frozenStoreObject`. ~30 lines | `FrozenOps/Operations.lean` | Small |
| Z8-I | **Add frozen `timerTickBudget` variant.** `frozenTimerTickBudget` replaces `frozenTimerTick` budget path for SchedContext-bound threads. Mirrors Z4-F in frozen monad. ~25 lines | `FrozenOps/Operations.lean` | Small |
| Z8-J1 | **Add SchedContext creation and configure to trace harness.** Create a SchedContext object via `lifecycleRetype`, configure with budget=100/period=1000 via `schedContextConfigure`. Verify object exists in store. ~15 lines | `Testing/MainTraceHarness.lean` | Small |
| Z8-J2 | **Add bind-and-run scenario to trace harness.** Bind SchedContext to test thread via `schedContextBind`. Run thread, observe budget decrement via `timerTick`. Assert `budgetRemaining` decreases each tick. ~12 lines | `Testing/MainTraceHarness.lean` | Small |
| Z8-J3 | **Add exhaustion and replenishment scenario.** Continue running until budget exhausted. Assert thread is preempted. Advance timer past replenishment due time. Assert budget is replenished and thread becomes runnable again. ~15 lines | `Testing/MainTraceHarness.lean` | Small |
| Z8-K | **Update smoke test fixture.** Regenerate `tests/fixtures/main_trace_smoke.expected` to include the new SchedContext trace output. Document rationale for fixture update. ~10 lines | `tests/fixtures/` | Small |
| Z8-L | **Add negative-state tests.** Tests for error paths: bind to non-existent SchedContext, double-bind, configure with zero period, admission control rejection. ~30 lines | `tests/NegativeStateSuite.lean` | Small |
| Z8-M | **Update `enforcementBoundaryExtended` with new operations.** Add `schedContextConfigure`, `schedContextBind`, `schedContextUnbind` to the 22-entry enforcement boundary table. ~5 lines | `Enforcement/Wrappers.lean` | Trivial |
| Z8-N1 | **Full build.** `lake build` (all targets). Verify zero `sorry`/`axiom` in new and modified code. ~5 min | — | Small |
| Z8-N2 | **Run smoke and full test suites.** `./scripts/test_smoke.sh && ./scripts/test_full.sh`. Verify all tiers pass, including new SchedContext trace output. ~5 min | — | Small |

**Intra-phase ordering**: Z8-A,B independent (decode theorems). Z8-C through
Z8-F depend on Z5-D,E,J. Z8-G depends on Z8-C,D,E. Z8-H,I independent of
Z8-C through Z8-G. Z8-J depends on all operations being wired. Z8-K depends
on Z8-J. Z8-L independent of Z8-J. Z8-M depends on Z5-O. Z8-N terminal.

---

### Phase Z9: Invariant Composition & Cross-Subsystem (20 sub-tasks)

**Goal**: Prove that all new invariants compose correctly with existing
cross-subsystem invariants. Extend `proofLayerInvariantBundle` with
SchedContext invariants. Prove field-disjointness for new state fields.
Establish the full end-to-end invariant chain from boot through runtime.

**Modified files**:
- `SeLe4n/Kernel/CrossSubsystem.lean`
- `SeLe4n/Kernel/Architecture/Invariant.lean`
- `SeLe4n/Platform/Boot.lean`
- `SeLe4n/Model/FreezeProofs.lean`

**Prerequisites**: Z4, Z5, Z6, Z7 complete.

| ID | Description | Files | Est. |
|----|-------------|-------|------|
| Z9-A | **Define `schedContextStoreConsistent` cross-subsystem predicate.** Every SchedContext referenced by a TCB's `schedContextBinding` exists in the object store as a `.schedContext` object. Analogous to `noStaleEndpointQueueReferences` for SchedContexts. ~12 lines | `CrossSubsystem.lean` | Small |
| Z9-B | **Define `schedContextNotDualBound` predicate.** No SchedContext is simultaneously `.bound` by one thread and `.donated` to another. At most one thread references any given SchedContext at any time. Prevents resource aliasing. ~12 lines | `CrossSubsystem.lean` | Small |
| Z9-C | **Define `schedContextRunQueueConsistent` predicate.** Every runnable thread that is SchedContext-bound has a live SchedContext with positive budget. Combines `budgetPositive` with store consistency. ~12 lines | `CrossSubsystem.lean` | Small |
| Z9-D | **Extend `crossSubsystemInvariant` with SchedContext predicates.** Add Z9-A, Z9-B, Z9-C to the 5-predicate conjunction (now 8 predicates). Update projection theorems. ~10 lines | `CrossSubsystem.lean` | Small |
| Z9-E | **Analyze field-disjointness for new state fields.** `replenishQueue` is part of `scheduler`. SchedContext objects are in `objects`. TCB `schedContextBinding` is in `objects`. Document read-sets: `schedContextStoreConsistent` reads `objects`. `schedContextNotDualBound` reads `objects`. `replenishQueueValid` reads `scheduler.replenishQueue` + `objects`. Identify disjoint and sharing pairs. ~20 lines (documentation) | `CrossSubsystem.lean` | Small |
| Z9-F | **Prove frame lemmas for new predicates.** `schedContextStoreConsistent_frame`: preserved when `objects` unchanged. `schedContextNotDualBound_frame`: preserved when `objects` unchanged. `replenishQueueValid_frame`: preserved when `scheduler.replenishQueue` and `objects` unchanged. ~20 lines | `CrossSubsystem.lean` | Small |
| Z9-G | **Extend `proofLayerInvariantBundle` with SchedContext invariants.** Add `schedContextsWellFormed`, `schedContextBindingConsistent`, `budgetPositive`, `currentBudgetPositive`, `replenishQueueValid`, `effectiveParamsMatchRunQueue` to the composed bundle. ~15 lines | `Architecture/Invariant.lean` | Small |
| Z9-H | **Prove `default_system_state_proofLayerInvariantBundle` (extended).** The default state satisfies all new invariants vacuously: no SchedContexts, no bindings, empty replenish queue. ~15 lines | `Architecture/Invariant.lean` | Small |
| Z9-I | **Extend boot sequence for SchedContext initialization.** Add `Builder.createSchedContext` that creates a SchedContext object during boot. Update `bootFromPlatform` to accept SchedContext entries in `PlatformConfig`. ~25 lines | `Boot.lean` | Small |
| Z9-J | **Prove boot preserves SchedContext invariants.** `bootFromPlatform_schedContextsWellFormed`: all boot-created SchedContexts satisfy well-formedness. `bootFromPlatform_schedContextBindingConsistent`: no bindings at boot time (vacuous). ~15 lines | `Boot.lean` | Small |
| Z9-K | **Extend freeze proofs for SchedContext.** `freeze_preserves_schedContextsWellFormed`: SchedContext is passthrough-frozen, so well-formedness transfers directly. `freeze_preserves_schedContextBindingConsistent`: binding references are preserved by freeze (both objects and TCB fields unchanged by freeze). ~20 lines | `FreezeProofs.lean` | Small |
| Z9-L1 | **Prove timerTick preserves `schedContextStoreConsistent`.** Budget decrement modifies SchedContext fields but doesn't destroy the object. Replenishment refills but doesn't create/remove objects. Frame preservation. ~12 lines | `CrossSubsystem.lean` | Small |
| Z9-L2 | **Prove timerTick preserves `schedContextNotDualBound` and `schedContextRunQueueConsistent`.** Timer tick doesn't modify binding fields (only budget/deadline). Frame preservation for `NotDualBound`. Budget decrement preserves positive budget for non-exhausted threads; exhausted threads removed from runnable. ~12 lines | `CrossSubsystem.lean` | Small |
| Z9-M | **Prove `schedule_preserves_crossSubsystemInvariant` (extended).** Schedule doesn't modify SchedContexts (only reads budget for eligibility). Frame preservation for all new predicates. ~15 lines | `CrossSubsystem.lean` | Small |
| Z9-N1 | **Prove donation preserves `schedContextNotDualBound`.** Old client binding cleared (client blocked on reply) before server receives donation. At no point does the SchedContext have two active bindings. ~10 lines | `CrossSubsystem.lean` | Small |
| Z9-N2 | **Prove donation preserves `schedContextStoreConsistent`.** SchedContext object not created/destroyed during donation — only `boundThread` and TCB `schedContextBinding` fields modified. Store consistency is a frame property. ~10 lines | `CrossSubsystem.lean` | Small |
| Z9-O1 | **Prove SchedContext cleanup on destroy.** When a SchedContext is destroyed via `lifecycleRetypeWithCleanup`: any bound thread's `schedContextBinding` cleared, SchedContext removed from replenish queue. Binding consistency holds after cleanup. ~10 lines | `CrossSubsystem.lean` | Small |
| Z9-O2 | **Prove thread cleanup returns donated SchedContext.** When a thread with `.donated` binding is destroyed: return SchedContext to original owner (Z7-P logic). Cross-subsystem invariants preserved through return + destroy. ~10 lines | `CrossSubsystem.lean` | Small |
| Z9-P1 | **Build cross-subsystem and architecture modules.** `lake build SeLe4n.Kernel.CrossSubsystem && lake build SeLe4n.Kernel.Architecture.Invariant`. Verify zero `sorry`/`axiom`. ~2 min | — | Small |
| Z9-P2 | **Run full test suite.** `./scripts/test_full.sh` (theorem changes require full test). Verify all invariant surface anchors pass. ~5 min | — | Small |

**Intra-phase ordering**: Z9-A through Z9-C independent. Z9-D depends on
Z9-A,B,C. Z9-E,F depend on Z9-A,B,C. Z9-G depends on Z4 invariants and
Z9-D. Z9-H depends on Z9-G. Z9-I,J depend on Z1 types. Z9-K depends on
Z9-J. Z9-L through Z9-O depend on Z9-D,F,G. Z9-P terminal.

---

### Phase Z10: Documentation & Closure (12 sub-tasks)

**Goal**: Update all documentation to reflect the new composable performance
object architecture. Sync specification, development docs, codebase map, and
GitBook chapters. Close out the workstream.

**Modified files**:
- `docs/spec/SELE4N_SPEC.md`
- `docs/DEVELOPMENT.md`
- `docs/WORKSTREAM_HISTORY.md`
- `docs/CLAIM_EVIDENCE_INDEX.md`
- `docs/codebase_map.json`
- `docs/gitbook/12-proof-and-invariant-map.md`
- `README.md`
- `CLAUDE.md`
- `scripts/website_link_manifest.txt`

**Prerequisites**: Z8, Z9 complete.

| ID | Description | Files | Est. |
|----|-------------|-------|------|
| Z10-A1 | **Add SchedContext data model and CBS algorithm to spec.** Add section covering: `SchedContext` structure, CBS budget/period semantics, `consumeBudget`/`processReplenishments`/`scheduleReplenishment` operations, admission control. Reference `cbs_bandwidth_bounded` theorem. ~25 lines | `docs/spec/SELE4N_SPEC.md` | Small |
| Z10-A2 | **Add donation protocol and timeout semantics to spec.** Add section covering: passive server model, Call/Reply donation lifecycle, ReplyRecv atomic swap, timeout endpoints, budget-driven IPC timeout. Reference `donationChainAcyclic` and `timeoutThread` invariants. ~25 lines | `docs/spec/SELE4N_SPEC.md` | Small |
| Z10-B | **Update `DEVELOPMENT.md` with new build targets.** Document `lake build SeLe4n.Kernel.SchedContext.Types`, etc. Add development workflow for SchedContext changes. ~15 lines | `docs/DEVELOPMENT.md` | Small |
| Z10-C | **Update `WORKSTREAM_HISTORY.md`.** Add WS-Z entry: 10 phases, 213 sub-tasks, version range, key deliverables. Mark as COMPLETE. ~20 lines | `docs/WORKSTREAM_HISTORY.md` | Small |
| Z10-D | **Update `CLAIM_EVIDENCE_INDEX.md`.** Add claims for: CBS bandwidth isolation theorem, donation chain acyclicity, timeout termination, admission control soundness. Link to specific theorem names and file locations. ~25 lines | `docs/CLAIM_EVIDENCE_INDEX.md` | Small |
| Z10-E | **Regenerate `codebase_map.json`.** Add `SchedContext/Types.lean`, `SchedContext/Budget.lean`, `SchedContext/ReplenishQueue.lean`, `SchedContext/Operations.lean`, `SchedContext/Invariant/Defs.lean`, `SchedContext/Invariant/Preservation.lean` to the source layout. ~15 lines | `docs/codebase_map.json` | Small |
| Z10-F | **Update GitBook proof and invariant map.** Add SchedContext invariants to the chapter: `schedContextsWellFormed`, `budgetPositive`, `replenishQueueValid`, `schedContextBindingConsistent`, `donationChainAcyclic`, `donationOwnerValid`. ~20 lines | `docs/gitbook/12-proof-and-invariant-map.md` | Small |
| Z10-G | **Update `README.md` metrics.** Sync theorem counts, invariant counts, object type counts from `codebase_map.json`. ~10 lines | `README.md` | Small |
| Z10-H | **Update `CLAUDE.md` source layout.** Add `SchedContext/*` entries to the source layout section. Update active workstream context. ~15 lines | `CLAUDE.md` | Small |
| Z10-I | **Update `website_link_manifest.txt`.** Add new file paths that may be linked from the website. ~5 lines | `scripts/website_link_manifest.txt` | Trivial |
| Z10-J1 | **Run full test suite and sorry/axiom check.** `./scripts/test_full.sh`. `grep -r 'sorry\|axiom' SeLe4n/ --include='*.lean'` — verify zero hits in production code. ~5 min | — | Small |
| Z10-J2 | **Documentation sync verification and release tag.** Verify `README.md` metrics match `codebase_map.json`. Verify `WORKSTREAM_HISTORY.md` has WS-Z entry. Tag release version (e.g., `v0.23.0`). ~5 min | — | Small |

**Intra-phase ordering**: Z10-A1/A2 sequential. Z10-B through Z10-I are
independent documentation tasks (parallelizable). Z10-J1/J2 terminal
(depend on all above).

---

## 6. Migration Strategy

### 6.1 Backward Compatibility

The design ensures full backward compatibility throughout the migration:

1. **Phase Z1**: All existing TCBs default to `schedContextBinding = .unbound`.
   The `threadSchedulingParams` accessor falls back to legacy `priority`/
   `deadline`/`timeSlice`/`domain` fields when unbound.

2. **Phase Z4**: The scheduler checks `schedContextBinding` first. For unbound
   threads, the existing `timeSlice` decrement path is taken unchanged. Only
   SchedContext-bound threads use the new CBS budget path.

3. **Phase Z5**: Binding is opt-in via capability operations. No existing thread
   is automatically bound. Systems that don't create SchedContexts behave
   identically to the pre-WS-Z kernel.

4. **Phase Z6**: Timeout metadata defaults to `none` in all IPC blocking states.
   Unbound threads have no timeout (existing behavior). Only SchedContext-bound
   threads get budget-driven timeouts.

5. **Phase Z7**: Donation only occurs when the server is passive (unbound).
   Active servers with their own SchedContexts are unaffected.

### 6.2 Legacy Field Deprecation Path

The TCB's direct `priority`, `deadline`, `timeSlice`, and `domain` fields are
**not removed** in this workstream. They serve as the fallback for unbound
threads. A future workstream (post-WS-Z) may:

1. Require all threads to be SchedContext-bound (remove unbound path).
2. Remove legacy scheduling fields from TCB.
3. Simplify the dual-path scheduler logic.

This is intentionally deferred to minimize the blast radius of WS-Z.

### 6.3 Test Strategy

| Phase | Test Level | Verification |
|-------|-----------|-------------|
| Z1 | `test_fast.sh` | Type compilation only |
| Z2 | `test_fast.sh` | Budget engine unit proofs |
| Z3 | `test_fast.sh` | ReplenishQueue unit proofs |
| Z4 | `test_smoke.sh` | Scheduler integration + existing tests |
| Z5 | `test_smoke.sh` | Capability binding + existing tests |
| Z6 | `test_smoke.sh` | Timeout + IPC tests |
| Z7 | `test_smoke.sh` | Donation + IPC tests |
| Z8 | `test_full.sh` | Full API surface + trace harness |
| Z9 | `test_full.sh` | Cross-subsystem composition |
| Z10 | `test_full.sh` | Final validation |

---

## 7. Risk Assessment

| Risk | Severity | Mitigation |
|------|----------|------------|
| **Heartbeat pressure in CBS proofs** | HIGH | Budget isolation theorem (Z2-O) may require high `maxHeartbeats`. Mitigation: decompose into helper lemmas, use `Nat.sub`/`Nat.min` simp sets. |
| **RunQueue priority update on bind** | MEDIUM | Binding changes effective priority, requiring RunQueue remove + re-insert. Must preserve all 15 scheduler invariants (9 original + 6 new) through the update. Mitigation: factor into `updateRunQueuePriority` helper with bundled preservation. |
| **Donation chain complexity** | MEDIUM | Nested calls (A calls B calls C) create multi-hop donation chains. Each link must be tracked and returned in LIFO order. Mitigation: `SchedContextBinding.donated` tracks `(scId, originalOwner)` per-link; the `donationChainAcyclic` invariant (Z7-F) prevents cycles; LIFO ordering is enforced by the Call/Reply protocol (blocked clients cannot initiate further calls). |
| **Timeout + donation interaction** | MEDIUM | When a donated SchedContext's budget expires, both the running server (preemption) and the blocked client (timeout) must be handled atomically. Mitigation: Z6-E's blocked-thread scan handles the client; Z4-F3 handles the server; the `schedContextNotDualBound` invariant (Z9-B) ensures no aliasing. See Z6 "Cross-cutting concern" note. |
| **ThreadIpcState field additions** | LOW | Z6-B requires updating all pattern matches across the codebase. Mitigation: default `none` for new field, use `..` syntax where possible. |
| **Admission control arithmetic** | LOW | Integer per-mille arithmetic may have precision issues (e.g., 333/1000 vs 1/3). Mitigation: over-approximate (round up) for safety. |
| **Frozen ops divergence** | LOW | FrozenOps must mirror builder-phase operations. Mitigation: Z8-H,I added after builder ops are stable. |

---

## 8. Metrics Summary

| Metric | Value |
|--------|-------|
| Total phases | 10 |
| Total atomic sub-tasks | 213 |
| New files | 8 |
| Modified files | ~25 |
| New kernel object types | 1 (SchedContext) |
| New syscalls | 3 (configure, bind, unbind) |
| New invariants | ~14 |
| New preservation theorems | ~45 |
| Critical path length | 6 phases (Z1→Z2→Z4→Z6→Z8→Z10) |
| Parallelizable pairs | 3 (Z3∥Z2, Z5∥Z4, Z7∥Z6) |
| Estimated LOC (new) | ~1800 |
| Estimated LOC (modified) | ~600 |
| Axiom budget | 0 |

---

## 9. Relationship to Prior Workstreams

| Workstream | Relationship |
|-----------|-------------|
| **WS-V (Starvation Prevention)** | WS-Z closes starvation vectors SV-1 (via CBS bandwidth isolation), SV-3 (via timeout endpoints), SV-5 (via per-domain SchedContext budgets). WS-V's bounded latency theorem (V1) is strengthened by CBS WCRT bounds. |
| **WS-W (Hardware Partition)** | Orthogonal. WS-W addresses microarchitectural isolation (MPAM/CCA). WS-Z addresses CPU time isolation. They compose: a thread's SchedContext determines CPU budget, while its domain's partition determines cache/bandwidth allocation. |
| **WS-U (Deep-Dive Remediation)** | WS-Z builds on WS-U's `configDefaultTimeSlice` freeze preservation (Y1-B). The frozen `timerTick` now uses SchedContext budget when available, falling back to `configDefaultTimeSlice` for unbound threads. |
| **WS-Q (Kernel State Architecture)** | WS-Z adds a 7th kernel object type (SchedContext) to the Q-series state model. The builder/freeze/frozen pipeline (Q3/Q5/Q7) is extended to handle SchedContext objects. |

---

## 10. Success Criteria

WS-Z is complete when:

1. **Functional**: All 213 sub-tasks delivered with zero `sorry`/`axiom`.
2. **Correct**: `test_full.sh` passes. All existing tests pass unchanged.
3. **CBS**: `cbs_bandwidth_bounded` theorem machine-checked.
4. **Timeout**: No IPC blocks indefinitely for SchedContext-bound threads.
5. **Donation**: Passive servers consume zero CPU when idle.
6. **Admission**: System-wide bandwidth cannot exceed configured threshold.
7. **Compatible**: Unbound threads behave identically to pre-WS-Z kernel.
8. **Documented**: All documentation synced per section 10 checklist.
