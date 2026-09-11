-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
-- WS-SM SM3.A.6: per-SchedContext lock field requires the abstract
-- operational RwLock specification from SM2.C.  This import does not
-- introduce a cycle: `Concurrency.Locks.RwLock` depends transitively
-- only on `Prelude` (via `Concurrency.Types` and `Concurrency.MemoryModel`).
import SeLe4n.Kernel.Concurrency.Locks.RwLock

/-! # SchedContext Types — WS-Z Phase Z1

First-class scheduling context types for CBS (Constant Bandwidth Server)
scheduling. A `SchedContext` is a kernel object containing CPU budget, period,
and replenishment parameters. Threads are bound to SchedContexts via capabilities.

## Key types:
- `Budget`: CPU time allocation in ticks (saturating decrement)
- `Period`: Replenishment period in ticks (must be > 0)
- `Bandwidth`: Computed budget/period pair for admission control
- `ReplenishmentEntry`: Single CBS replenishment event
- `SchedContext`: The first-class scheduling context object
- `SchedContextBinding`: Thread ↔ SchedContext relationship enum
-/

namespace SeLe4n.Kernel

-- ============================================================================
-- Z1-B: Budget typed wrapper
-- ============================================================================

/-- CPU time budget in ticks. Represents the amount of CPU time a scheduling
context is allowed to consume per period. -/
structure Budget where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace Budget

@[inline] def zero : Budget := ⟨0⟩
@[inline] def isZero (b : Budget) : Bool := b.val == 0
@[inline] def isPositive (b : Budget) : Bool := b.val > 0

/-- Saturating decrement — budget cannot go negative. -/
@[inline] def decrement (b : Budget) (ticks : Nat := 1) : Budget :=
  ⟨b.val - ticks⟩

-- AE3-H/SC-06: `Budget.refill` deleted — had inverted semantics (capped down
-- to ceiling instead of refilling up). Unused by CBS engine; `applyRefill`
-- in Budget.lean handles actual replenishment.

end Budget

instance : BEq Budget where
  beq a b := a.val == b.val

-- ============================================================================
-- Z1-C: Period typed wrapper
-- ============================================================================

/-- Replenishment period in ticks. Must be > 0 for well-formedness.
The CBS algorithm replenishes a SchedContext's budget every `period` ticks. -/
structure Period where
  val : Nat
deriving DecidableEq, Repr, Inhabited

namespace Period

/-- Default period: 10000 ticks. -/
@[inline] def default : Period := ⟨10000⟩
@[inline] def isPositive (p : Period) : Bool := p.val > 0

end Period

instance : BEq Period where
  beq a b := a.val == b.val

-- ============================================================================
-- Z1-D: Bandwidth computed type
-- ============================================================================

/-- Computed bandwidth pair for admission control.
Utilization = budget/period. Integer arithmetic only (per-mille). -/
structure Bandwidth where
  budget : Nat
  period : Nat
deriving DecidableEq, Repr, Inhabited

namespace Bandwidth

@[inline] def isValid (bw : Bandwidth) : Bool := bw.period > 0
/-- Utilization in per-mille (parts per thousand).

AK2-E (S-M03): Uses CEILING-ROUND division to guarantee over-admission is
impossible. For any positive `period`, `(budget * 1000 + period - 1) / period`
equals `⌈budget * 1000 / period⌉`. Each context's utilization is now upper-
bounded, not lower-bounded, so the admission sum also upper-bounds the true
bandwidth. Admission acceptance (`sum ≤ 1000`) therefore strictly implies the
real bandwidth fraction is ≤ 1, eliminating the prior aggregate 6.4% over-
admission window on 64-context deployments. -/
@[inline] def utilization (bw : Bandwidth) : Nat :=
  if bw.period > 0 then (bw.budget * 1000 + bw.period - 1) / bw.period else 0
/-- Check if this bandwidth exceeds another. -/
@[inline] def exceeds (a b : Bandwidth) : Bool :=
  a.utilization > b.utilization

end Bandwidth

instance : BEq Bandwidth where
  beq a b := a.budget == b.budget && a.period == b.period

-- ============================================================================
-- Z1-E: ReplenishmentEntry structure
-- ============================================================================

/-- Maximum number of replenishment entries per SchedContext.
seL4 uses MIN_REFILLS=2, MAX_REFILLS varies. We use 8 as a balance
between precision and proof complexity. -/
def maxReplenishments : Nat := 8

/-- A single CBS replenishment event. When `eligibleAt ≤ currentTime`,
the `amount` is added back to the SchedContext's `budgetRemaining`. -/
structure ReplenishmentEntry where
  amount : Budget
  eligibleAt : Nat
deriving DecidableEq, Repr, Inhabited

namespace ReplenishmentEntry

@[inline] def isEligible (entry : ReplenishmentEntry) (currentTime : Nat) : Bool :=
  entry.eligibleAt ≤ currentTime

end ReplenishmentEntry

instance : BEq ReplenishmentEntry where
  beq a b := a.amount == b.amount && a.eligibleAt == b.eligibleAt

-- ============================================================================
-- Z1-F: SchedContext structure (core)
-- ============================================================================

/-- First-class scheduling context object for CBS scheduling.

- `budget`: configured CBS budget — the amount replenished each period.
- `budgetRemaining`: current remaining ticks — decremented each tick,
  refilled up to `budget` on replenishment.
- `period`: replenishment period in ticks.
- `priority`: effective scheduling priority for bound thread.
- `deadline`: CBS deadline for EDF tie-breaking.
- `domain`: scheduling domain for temporal partitioning.
- `periodStart`: absolute tick at which the current period started.
- `replenishments`: pending replenishment events (bounded list).
- `boundThread`: the thread currently bound to this SchedContext (at most one).
- `scReply`: the head of this SchedContext's MCS reply stack — the innermost
  Reply object through which the context has been donated (seL4-MCS's
  `sc->scReply`).  `none` when the context has not been donated through any
  Call.  See `donationChainWellFormed`.
- `isActive`: whether this SchedContext is actively scheduling a thread. -/
structure SchedContext where
  scId : SeLe4n.SchedContextId
  budget : Budget
  period : Period
  priority : SeLe4n.Priority
  deadline : SeLe4n.Deadline
  domain : SeLe4n.DomainId
  budgetRemaining : Budget
  periodStart : Nat := 0
  replenishments : List ReplenishmentEntry := []
  boundThread : Option SeLe4n.ThreadId := none
  /-- WS-OD OD2.1: the head of this SchedContext's MCS reply stack — seL4-MCS's
      `sc->scReply`.  A `Call` that donates this context pushes the donor's
      Reply object here (`Reply.next = some (.head scId)`, `Reply.prev` = the
      previous head, whose own `next` becomes `.frame` of the pushed Reply since
      `v0.35.4`), and the donation return pops it; the stack is what makes
      donation *transitive*, so a passive server can itself Call and pass the
      context on.  `Reply.wellFormed`'s docstring has named this field since
      SM6.D — it is built rather than designed around, and building it is also
      what keeps the call footprint inside `maxLockSetSize`: the push reads the
      previous head off an object the footprint already write-locks, instead of
      re-deriving it from the owner's TCB and the outer reply.

      The chain this field heads is constrained by `donationChainWellFormed`
      (`SeLe4n/Kernel/IPC/Invariant/Defs.lean`) and erased by
      `projectKernelObject`, in the same class as `boundThread`. -/
  scReply : Option SeLe4n.ReplyId := none
  isActive : Bool := false
  /-- WS-SM SM3.A.6: per-SchedContext reader-writer lock state.  Default
      `RwLockState.unheld` means a freshly-allocated SchedContext starts
      with its lock available.  CBS operations that mutate budget /
      replenishments (`timerTickBudget`, `applyRefill`,
      `schedContextBind`, `schedContextUnbind`, donation paths) acquire
      in write mode; observation paths (read-only budget queries) acquire
      in read mode.  See `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md`
      §5.1 (SM3.A.6). -/
  lock : SeLe4n.Kernel.Concurrency.RwLockState :=
    SeLe4n.Kernel.Concurrency.RwLockState.unheld
deriving Repr

-- ============================================================================
-- Z1-G: SchedContext.wellFormed predicate
-- ============================================================================

namespace SchedContext

/-- Structural well-formedness: period > 0, budget ≤ period,
budgetRemaining ≤ budget, bounded replenishment list. -/
def wellFormed (sc : SchedContext) : Prop :=
  sc.period.isPositive ∧
  sc.budget.val ≤ sc.period.val ∧
  sc.budgetRemaining.val ≤ sc.budget.val ∧
  sc.replenishments.length ≤ maxReplenishments

-- ============================================================================
-- Z1-H: SchedContext.bandwidth accessor
-- ============================================================================

/-- Compute the bandwidth pair for admission control. -/
@[inline] def bandwidth (sc : SchedContext) : Bandwidth :=
  { budget := sc.budget.val, period := sc.period.val }

/-- Utilization in per-mille (parts per thousand). -/
@[inline] def utilizationPerMille (sc : SchedContext) : Nat :=
  sc.bandwidth.utilization

-- ============================================================================
-- Z1-M: SchedContext.default and empty constructors
-- ============================================================================

/-- Default SchedContext with zero budget, default period, no bound thread.
Used by `retypeFromUntyped` when creating a new SchedContext object. -/
def empty (scId : SeLe4n.SchedContextId) : SchedContext :=
  { scId := scId
    budget := Budget.zero
    period := Period.default
    priority := ⟨0⟩
    deadline := ⟨0⟩
    domain := ⟨0⟩
    budgetRemaining := Budget.zero }

/-- Default instance uses sentinel ID and zero budget. -/
instance : Inhabited SchedContext where
  default := empty ⟨0⟩

/-- Convenience constructor with well-formedness validation. Returns `none` if
parameters violate well-formedness (period = 0 or budget > period). -/
def mkChecked (scId : SeLe4n.SchedContextId) (budget : Nat) (period : Nat)
    (priority : Nat) (deadline : Nat) (domain : Nat) : Option SchedContext :=
  if period == 0 then none
  else if budget > period then none
  else some {
    scId := scId
    budget := ⟨budget⟩
    period := ⟨period⟩
    priority := ⟨priority⟩
    deadline := ⟨deadline⟩
    domain := ⟨domain⟩
    budgetRemaining := ⟨budget⟩
  }

end SchedContext

-- ============================================================================
-- Z1-I: SchedContextBinding enum
-- ============================================================================

/-- Models the thread ↔ SchedContext relationship.

- `unbound`: Thread uses legacy TCB scheduling fields (priority/deadline/timeSlice).
- `bound`: Thread is bound to a SchedContext for CBS scheduling.
- `donated`: Thread temporarily holds a SchedContext lent during IPC Call.
  The `originalOwner` is the client thread that donated the SchedContext. -/
inductive SchedContextBinding where
  | unbound
  | bound (scId : SeLe4n.SchedContextId)
  | donated (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
deriving Repr, DecidableEq

namespace SchedContextBinding

/-- `v0.35.4`: is this binding a donation?  The one-word form of the question
`schedContextUnbind` asks (a donated holder is not unbound in place), so the
transition and every proof about it read one predicate. -/
def isDonated : SchedContextBinding → Bool
  | .donated _ _ => true
  | _ => false

@[simp] theorem isDonated_unbound : isDonated .unbound = false := rfl
@[simp] theorem isDonated_bound (scId : SeLe4n.SchedContextId) :
    isDonated (.bound scId) = false := rfl
@[simp] theorem isDonated_donated (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) :
    isDonated (.donated scId owner) = true := rfl

/-- Extract the SchedContextId if bound or donated, `none` if unbound. -/
@[inline] def scId? : SchedContextBinding → Option SeLe4n.SchedContextId
  | .unbound => none
  | .bound scId => some scId
  | .donated scId _ => some scId

/-- The SchedContext this binding **owns**, `none` when the thread owns none.

This is the counterpart to `scId?`, and the difference is the whole of
seL4-MCS's donation semantics: `scId?` is the reservation a thread **runs on**
(`.bound` *or* `.donated`), while `ownScId?` is the one it **owns** (`.bound`
alone).  The two govern different halves of a thread's scheduling parameters:

* **Reservation-owned** — budget, period and deadline — come from `scId?` at
  every binding.  A donee is charged to the donor's reservation and answers to
  its deadline; that is what a donation *is*.
* **Thread-owned** — base priority and domain — come from the thread's own
  `TCB` fields, mirrored onto `ownScId?`'s SchedContext by the AK2-B
  propagation convention and read back from it there.  A donee keeps its own
  scheduling band and its own domain, and rises to the client's band only
  through priority inheritance.  In seL4 these two live on the TCB
  (`tcb->tcbPriority`, `tcb->tcbDomain`) and the scheduling context carries
  budget and period; `schedContext_donate` moves the reservation and touches
  neither.

Reading the donor's SchedContext for a donee's thread-owned parameters is an
authority crossing in both directions, and both were live before WS-OD
(v0.35.3): `.tcbSetPriority` / `.tcbSetMCPriority` on a passive server rewrote
the **client's** reservation, and `schedContextConfigure` on the client's
reservation rewrote the **server's** own priority and domain.  Neither syscall's
authority says anything about the other principal.

Every reader and writer of a thread-owned parameter classifies through this
function rather than matching the binding itself, so a binding constructor added
later (WS-CB's hierarchical servers) must be classified here before it compiles
— the enumeration-standing-in-for-a-derivation shape `CLAUDE.md` forbids.
`SystemState.threadBasePriority` (`Model/State.lean`) is the state-level
resolver built on it. -/
@[inline] def ownScId? : SchedContextBinding → Option SeLe4n.SchedContextId
  | .unbound => none
  | .bound scId => some scId
  | .donated _ _ => none

/-- A thread's own reservation is always one it runs on: `ownScId?` is a
*narrowing* of `scId?` rather than a second, independent resolution, so the two
can never name different contexts. -/
theorem ownScId?_eq_scId?_of_isSome (b : SchedContextBinding)
    {scId : SeLe4n.SchedContextId} (h : b.ownScId? = some scId) :
    b.scId? = some scId := by
  cases b <;> simp_all [ownScId?, scId?]

/-- A thread owns its reservation exactly on `.bound`. -/
@[simp] theorem ownScId?_bound (scId : SeLe4n.SchedContextId) :
    (SchedContextBinding.bound scId).ownScId? = some scId := rfl

/-- A donee owns no reservation: it runs on one it was lent, so its
thread-owned parameters stay its own — the seL4-MCS split. -/
@[simp] theorem ownScId?_donated
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) :
    (SchedContextBinding.donated scId owner).ownScId? = none := rfl

/-- An unbound thread owns no reservation. -/
@[simp] theorem ownScId?_unbound :
    SchedContextBinding.unbound.ownScId? = none := rfl

/-- The classifier's exact characterisation: owning a reservation *is* being
`.bound` to it.  Consumers that hold a fact about the binding shape and need
the classifier's form — or the reverse — go through this rather than re-casing,
so a later constructor cannot be handled at one site and forgotten at
another. -/
theorem eq_bound_of_ownScId? {b : SchedContextBinding}
    {scId : SeLe4n.SchedContextId} (h : b.ownScId? = some scId) :
    b = .bound scId := by
  cases b <;> simp_all [ownScId?]

/-- The converse reading, as an `iff`. -/
theorem ownScId?_eq_some_iff (b : SchedContextBinding)
    (scId : SeLe4n.SchedContextId) :
    b.ownScId? = some scId ↔ b = .bound scId :=
  ⟨eq_bound_of_ownScId?, fun h => by subst h; rfl⟩

/-- Check if the binding references any SchedContext. -/
@[inline] def isBound : SchedContextBinding → Bool
  | .unbound => false
  | _ => true

end SchedContextBinding

instance : Inhabited SchedContextBinding where
  default := .unbound

instance : BEq SchedContextBinding where
  beq
    | .unbound, .unbound => true
    | .bound a, .bound b => a == b
    | .donated a1 a2, .donated b1 b2 => a1 == b1 && a2 == b2
    | _, _ => false

-- ============================================================================
-- Z1-P: BEq instance for SchedContext
-- ============================================================================

/-- Manual BEq for SchedContext — field-wise comparison.
Non-lawful due to List comparison semantics.

**WS-SM SM3.A audit-pass-7**: extended to include the per-SchedContext
`lock : RwLockState` field added in SM3.A.6.  Without this conjunct,
two SchedContexts that differ only in their lock state would
compare equal — masking SM3.A.11 invariant regressions in any
caller that relies on `==` for object/state comparison (including
`BEq KernelObject`'s dispatch on the `.schedContext` variant).
`RwLockState` derives `DecidableEq`, so its `==` agrees with `=`. -/
instance : BEq SchedContext where
  beq a b :=
    a.scId == b.scId && a.budget == b.budget && a.period == b.period &&
    a.priority == b.priority && a.deadline == b.deadline && a.domain == b.domain &&
    a.budgetRemaining == b.budgetRemaining && a.periodStart == b.periodStart &&
    a.replenishments == b.replenishments && a.boundThread == b.boundThread &&
    -- WS-OD OD2.1: the reply-stack head participates in structural equality, so
    -- a push or a pop is visible to every caller that compares with `==`.
    a.scReply == b.scReply &&
    a.isActive == b.isActive &&
    -- WS-SM SM3.A audit-pass-7: per-SchedContext lock state participates
    -- in structural equality so lock-state regressions are not masked.
    a.lock == b.lock

end SeLe4n.Kernel
