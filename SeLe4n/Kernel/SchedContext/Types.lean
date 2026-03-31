/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude

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

/-- Refill budget up to a ceiling value. -/
@[inline] def refill (b : Budget) (ceiling : Budget) : Budget :=
  ⟨min b.val ceiling.val⟩

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
/-- Utilization in per-mille (parts per thousand). -/
@[inline] def utilization (bw : Bandwidth) : Nat :=
  if bw.period > 0 then bw.budget * 1000 / bw.period else 0
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
  isActive : Bool := false
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

/-- Extract the SchedContextId if bound or donated, `none` if unbound. -/
@[inline] def scId? : SchedContextBinding → Option SeLe4n.SchedContextId
  | .unbound => none
  | .bound scId => some scId
  | .donated scId _ => some scId

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
Non-lawful due to List comparison semantics. -/
instance : BEq SchedContext where
  beq a b :=
    a.scId == b.scId && a.budget == b.budget && a.period == b.period &&
    a.priority == b.priority && a.deadline == b.deadline && a.domain == b.domain &&
    a.budgetRemaining == b.budgetRemaining && a.periodStart == b.periodStart &&
    a.replenishments == b.replenishments && a.boundThread == b.boundThread &&
    a.isActive == b.isActive

end SeLe4n.Kernel
