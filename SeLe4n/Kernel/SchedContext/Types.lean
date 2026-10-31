-- SPDX-License-Identifier: GPL-3.0-or-later
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
  /-- WS-ZA ZA5.2: the pending replenishments, read through
      `SchedContext.replenishments` and written through
      `SchedContext.withReplenishments`.  The first entry is held in the
      context's own fields (`refillHeadPresent`, `refillHeadAmount`,
      `refillHeadEligibleAt`), so the refill a configure installs is written
      in the context's slot; a list held whole was two fresh cells on a
      context with no refill yet. -/
  refillHeadPresent : Bool := false
  refillHeadAmount : Nat := 0
  refillHeadEligibleAt : Nat := 0
  /-- WS-ZA ZA6.3: the replenishments after the first, as seL4-MCS keeps its
      refills in the scheduling context's own storage (`sc_refills`): a count
      and `maxReplenishments - 1` slots of the context's own fields, read
      through `SchedContext.refillTail`.  A refill scheduled behind the first
      writes a slot in place; a list was a fresh cell and a fresh entry. -/
  refillTailCount : Nat := 0
  refillSlot1Amount : Nat := 0
  refillSlot1EligibleAt : Nat := 0
  refillSlot2Amount : Nat := 0
  refillSlot2EligibleAt : Nat := 0
  refillSlot3Amount : Nat := 0
  refillSlot3EligibleAt : Nat := 0
  refillSlot4Amount : Nat := 0
  refillSlot4EligibleAt : Nat := 0
  refillSlot5Amount : Nat := 0
  refillSlot5EligibleAt : Nat := 0
  refillSlot6Amount : Nat := 0
  refillSlot6EligibleAt : Nat := 0
  refillSlot7Amount : Nat := 0
  refillSlot7EligibleAt : Nat := 0
  /-- WS-ZA ZA5.2: the thread this context is bound to, as its code
      (`SeLe4n.ThreadId.optCode`; `0` is none), read through
      `SchedContext.boundThread`.  A bound thread written as `some t` was a heap
      cell on every bind and donation. -/
  boundThreadCode : Nat := 0
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
  /-- **WS-HP HP10.3: the reservation's ORIGIN** — the thread that owned this
      scheduling context when it first left, recorded so that the donation return
      does not have to derive its recipient from reply-stack *reachability*.

      **Why the stack is not enough.**  The pop's bottom-of-stack arm binds the
      thread the surviving stack names as outermost, and a removal takes frames
      *off* that stack — so at reply-stack depth 2 a delegate answering the client
      out of order leaves the client's frame gone and the later in-order pop
      settles the reservation on the **intermediate** caller, with the owner
      `.unbound` for good (`tests/SmpIpcSuite.lean` §3.20, whose two accounting
      halves have been PAYOFF rows since HP10.9 closed this).  Both removal
      policies write `none` into
      the frame above a *bottom* frame, so WS-HP HP6's splice provably cannot
      reach that case; seL4-MCS derives the recipient the same way
      (`reply_pop` donates to the answered frame's own `replyTCB`, read at master,
      13.0.0, 12.1.0, 12.0.0 and 11.0.0), so it has the same loss and no remedy.

      **This field is HISTORY the kernel validates, not an invariant.**  No
      `donationChainWellFormed` clause relates it to the stack, and none can: the
      property is "the origin is the bottom frame's thread, **or** a thread whose
      frame was removed", whose second disjunct is not stateable from the store,
      and a clause carrying only the first would be *false* on exactly the states
      this field exists for.  What makes acting on it safe is the pop's own guard
      (`donationRecipientAcceptable`) — so it is a hint that is checked, never a
      fact that is trusted, and a Tier 3 negative refuses a chain conjunct over
      it.

      **Thread-id reuse is the one hazard, and it is closed structurally.**  The
      kernel writes the origin from the donor's own identity, so it can never
      name a thread that did not own the reservation — unless that thread is
      destroyed and its id reused.  `lifecyclePreRetypeCleanup` therefore clears
      the origin of any context naming the retyped thread, exactly as it already
      refuses a context that still heads a stack.

      `none` means "no reservation is on loan from a recorded owner", which is
      every state before the first donation and every state after the loan ends.
      Erased by `projectKernelObject` in the same cut that adds it — a *ThreadId*
      naming a possibly-high caller is the same cross-domain linkage `boundThread`
      and `scReply` are erased for — and refused on a boot SchedContext by
      `bootSafeSchedContextCheck`, since a config-supplied origin could only name
      a loan no boot state has made. -/
  donationOrigin : Option SeLe4n.ThreadId := none
  isActive : Bool := false
  /-- WS-ZA ZA6.3: the context's place in a core's release queue, which links
      through the scheduling contexts as seL4-MCS's links through the TCBs
      (`tcbSchedNext` in the release queue): the next context as a code
      (`SeLe4n.SchedContextId.optCode`; `0` is none), the core whose queue
      holds it as a code (`0` is none, `c + 1` is core `c`), and the time its
      queued refill is released.  The queue is singly linked: an insert walks
      from the head to its sorted place anyway, and a removal walks the same
      way to the predecessor.  The queue's head is the core's
      (`SchedulerState.releaseHeadCode`); the links agree with the abstract
      queue (`SystemState.releaseQueueRefined`). -/
  releaseNextCode : Nat := 0
  releaseCoreCode : Nat := 0
  releaseAt : Nat := 0
  /-- WS-ZA ZA6.5: the time this context has been charged for since it was
      last read, seL4-MCS's `sc->scConsumed`.  Every charge adds the time run
      (`SchedContext.chargeBudget`, as seL4's `chargeBudget` adds its
      `consumed`), and the read takes it back (`SchedContext.updateConsumed`,
      seL4's `schedContext_updateConsumed`).  A number held in the context's
      own slot, as the refills are, so a charge allocates nothing.  Outside the
      refill view (`SchedContext.refillView`): no refill invariant reads it. -/
  consumed : Nat := 0
  /-- WS-ZA ZA6.6: **the thread that has yielded to this context**, seL4-MCS's
      `sc->scYieldFrom`, as a code (`SeLe4n.ThreadId.optCode`; `0` is none),
      read through `SchedContext.yieldFrom`.  The thread names the context back
      (`TCB.yieldToCode`, `tcb->tcbYieldTo`); the two ends agree kernel-wide
      (`SystemState.yieldLinksAgree`).  A plain number in the context's own
      slot, as `boundThreadCode` holds a binding.  Outside the refill view. -/
  yieldFromCode : Nat := 0
deriving Repr

/-- WS-ZA ZA5.2: the thread this context is bound to, read from its code.
Reducible, so a record update that leaves the code alone reads the old value by
`rfl`.  Written as `boundThreadCode := SeLe4n.ThreadId.optCode t`. -/
@[reducible, inline] def SchedContext.boundThread (sc : SchedContext) :
    Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode sc.boundThreadCode

/-- WS-ZA ZA6.6: the thread that has yielded to this context (seL4-MCS's
`scYieldFrom`), read from its code.  Reducible, as `boundThread` is. -/
@[reducible, inline] def SchedContext.yieldFrom (sc : SchedContext) :
    Option SeLe4n.ThreadId :=
  SeLe4n.ThreadId.ofOptCode sc.yieldFromCode

/-- WS-ZA ZA6.5: the context with `t` more consumed time (seL4-MCS's
`sc->scConsumed += consumed` in `chargeBudget`).  One field written, so a
context held once is written in place. -/
@[inline] def SchedContext.addConsumed (sc : SchedContext) (t : Nat) : SchedContext :=
  { sc with consumed := sc.consumed + t }

/-- WS-ZA ZA6.5: the most one read of the consumed time returns: a machine
word, the one message register it is returned in (seL4-MCS's
`getMaxTicksToUs()`, the most a read converts without overflow; this kernel's
time is in ticks, so the bound is the word's). -/
def consumedReadMax : Nat := SeLe4n.machineWordMax - 1

/-- WS-ZA ZA6.5: the consumed time a read returns (seL4-MCS's
`schedContext_updateConsumed` result): all of it, or a word's worth when more
has accumulated. -/
@[inline] def SchedContext.consumedReading (sc : SchedContext) : Nat :=
  min sc.consumed consumedReadMax

/-- WS-ZA ZA6.5: the context after a read of its consumed time (seL4-MCS's
`schedContext_updateConsumed`): what the read returned is taken off, so the
count restarts at 0, or keeps what a word could not hold. -/
@[inline] def SchedContext.updateConsumed (sc : SchedContext) : SchedContext :=
  { sc with consumed := sc.consumed - sc.consumedReading }

/-- The read returns a word. -/
theorem SchedContext.consumedReading_lt_word (sc : SchedContext) :
    sc.consumedReading < SeLe4n.machineWordMax := by
  unfold SchedContext.consumedReading consumedReadMax
  have : 0 < SeLe4n.machineWordMax := by decide
  omega

/-- The read loses no time: what it returns and what it leaves add up to what
had accumulated. -/
theorem SchedContext.consumedReading_add_updateConsumed (sc : SchedContext) :
    sc.consumedReading + sc.updateConsumed.consumed = sc.consumed := by
  unfold SchedContext.updateConsumed SchedContext.consumedReading
  dsimp only
  omega

/-- seL4-MCS's two cases: a count a word holds is returned whole and reset to
0; a larger one returns a word's worth and keeps the rest. -/
theorem SchedContext.updateConsumed_cases (sc : SchedContext) :
    (sc.consumed < consumedReadMax ∧ sc.consumedReading = sc.consumed ∧
        sc.updateConsumed.consumed = 0) ∨
      (consumedReadMax ≤ sc.consumed ∧ sc.consumedReading = consumedReadMax ∧
        sc.updateConsumed.consumed = sc.consumed - consumedReadMax) := by
  unfold SchedContext.updateConsumed SchedContext.consumedReading
  dsimp only
  omega

/-- WS-ZA ZA6.3: how many replenishments the context holds after its first. -/
def refillTailCapacity : Nat := maxReplenishments - 1

/-- WS-ZA ZA6.3: the `i`-th replenishment after the first (`0`-based), read
from its slot; past the last slot, an empty entry. -/
@[inline] def SchedContext.tailSlot (sc : SchedContext) : Nat → ReplenishmentEntry
  | 0 => { amount := ⟨sc.refillSlot1Amount⟩, eligibleAt := sc.refillSlot1EligibleAt }
  | 1 => { amount := ⟨sc.refillSlot2Amount⟩, eligibleAt := sc.refillSlot2EligibleAt }
  | 2 => { amount := ⟨sc.refillSlot3Amount⟩, eligibleAt := sc.refillSlot3EligibleAt }
  | 3 => { amount := ⟨sc.refillSlot4Amount⟩, eligibleAt := sc.refillSlot4EligibleAt }
  | 4 => { amount := ⟨sc.refillSlot5Amount⟩, eligibleAt := sc.refillSlot5EligibleAt }
  | 5 => { amount := ⟨sc.refillSlot6Amount⟩, eligibleAt := sc.refillSlot6EligibleAt }
  | 6 => { amount := ⟨sc.refillSlot7Amount⟩, eligibleAt := sc.refillSlot7EligibleAt }
  | _ => { amount := ⟨0⟩, eligibleAt := 0 }

/-- WS-ZA ZA6.3: the context with its `i`-th replenishment after the first
written into its slot; past the last slot, the context as it is.  Each arm is
one record update, so a context held once is written in place. -/
@[inline] def SchedContext.setTailSlot (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    SchedContext :=
  match i with
  | 0 => { sc with refillSlot1Amount := e.amount.val, refillSlot1EligibleAt := e.eligibleAt }
  | 1 => { sc with refillSlot2Amount := e.amount.val, refillSlot2EligibleAt := e.eligibleAt }
  | 2 => { sc with refillSlot3Amount := e.amount.val, refillSlot3EligibleAt := e.eligibleAt }
  | 3 => { sc with refillSlot4Amount := e.amount.val, refillSlot4EligibleAt := e.eligibleAt }
  | 4 => { sc with refillSlot5Amount := e.amount.val, refillSlot5EligibleAt := e.eligibleAt }
  | 5 => { sc with refillSlot6Amount := e.amount.val, refillSlot6EligibleAt := e.eligibleAt }
  | 6 => { sc with refillSlot7Amount := e.amount.val, refillSlot7EligibleAt := e.eligibleAt }
  | _ => sc

/-- WS-ZA ZA6.3: the replenishments after the first, read from the slots. -/
def SchedContext.refillTail (sc : SchedContext) : List ReplenishmentEntry :=
  (List.range (min sc.refillTailCount refillTailCapacity)).map sc.tailSlot

/-- WS-ZA ZA5.2: the context's pending replenishments, its first entry read
from its fields and the rest from its slots (ZA6.3).  A record update that
leaves the refill fields alone reads the old list (`replenishments_mk_self`). -/
@[inline] def SchedContext.replenishments (sc : SchedContext) :
    List ReplenishmentEntry :=
  if sc.refillHeadPresent then
    { amount := ⟨sc.refillHeadAmount⟩, eligibleAt := sc.refillHeadEligibleAt } :: sc.refillTail
  else []

/-- WS-ZA ZA5.2: a record update that leaves the refill fields reads the old
list. -/
@[simp] theorem SchedContext.replenishments_mk_self (sc : SchedContext)
    (scId : SeLe4n.SchedContextId) (budget : Budget) (period : Period)
    (priority : SeLe4n.Priority) (deadline : SeLe4n.Deadline) (domain : SeLe4n.DomainId)
    (budgetRemaining : Budget) (periodStart : Nat) (boundThreadCode : Nat)
    (scReply : Option SeLe4n.ReplyId) (donationOrigin : Option SeLe4n.ThreadId)
    (isActive : Bool) (releaseNextCode : Nat)
    (releaseCoreCode : Nat) (releaseAt : Nat) (consumed : Nat) (yieldFromCode : Nat) :
    (SchedContext.mk scId budget period priority deadline domain budgetRemaining periodStart sc.refillHeadPresent sc.refillHeadAmount sc.refillHeadEligibleAt sc.refillTailCount sc.refillSlot1Amount sc.refillSlot1EligibleAt sc.refillSlot2Amount sc.refillSlot2EligibleAt sc.refillSlot3Amount sc.refillSlot3EligibleAt sc.refillSlot4Amount sc.refillSlot4EligibleAt sc.refillSlot5Amount sc.refillSlot5EligibleAt sc.refillSlot6Amount sc.refillSlot6EligibleAt sc.refillSlot7Amount sc.refillSlot7EligibleAt boundThreadCode scReply donationOrigin isActive releaseNextCode releaseCoreCode releaseAt consumed yieldFromCode).replenishments = sc.replenishments := rfl

/-- WS-ZA ZA6.3: a context with a first entry reads it first. -/
@[simp] theorem SchedContext.replenishments_of_present {sc : SchedContext}
    (h : sc.refillHeadPresent = true) :
    sc.replenishments =
      { amount := ⟨sc.refillHeadAmount⟩, eligibleAt := sc.refillHeadEligibleAt } :: sc.refillTail := by
  simp [SchedContext.replenishments, h]

/-- WS-ZA ZA6.3: a context with no first entry holds none. -/
@[simp] theorem SchedContext.replenishments_of_not_present {sc : SchedContext}
    (h : sc.refillHeadPresent = false) : sc.replenishments = [] := by
  simp [SchedContext.replenishments, h]

/-- WS-ZA ZA6.3: a context with no replenishment after its first holds none. -/
@[simp] theorem SchedContext.refillTail_of_count_zero {sc : SchedContext}
    (h : sc.refillTailCount = 0) : sc.refillTail = [] := by
  simp [SchedContext.refillTail, h]

/-- WS-ZA ZA6.3: the slots from `i` on written with `l`, one slot each. -/
def SchedContext.writeTail (sc : SchedContext) : Nat → List ReplenishmentEntry → SchedContext
  | _, [] => sc
  | i, e :: l => (sc.setTailSlot i e).writeTail (i + 1) l

/-- WS-ZA ZA5.2: the context with `rs` as its pending replenishments, the first
entry written into its fields and the rest into its slots (ZA6.3). -/
@[inline] def SchedContext.withReplenishments (sc : SchedContext)
    (rs : List ReplenishmentEntry) : SchedContext :=
  { sc.writeTail 0 rs.tail with
    refillHeadPresent := !rs.isEmpty
    refillHeadAmount := match rs with | e :: _ => e.amount.val | [] => sc.refillHeadAmount
    refillHeadEligibleAt := match rs with | e :: _ => e.eligibleAt | [] => sc.refillHeadEligibleAt
    refillTailCount := rs.tail.length }

@[simp] theorem SchedContext.setTailSlot_scId (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).scId = sc.scId := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_budget (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).budget = sc.budget := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_period (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).period = sc.period := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_priority (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).priority = sc.priority := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_deadline (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).deadline = sc.deadline := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_domain (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).domain = sc.domain := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_budgetRemaining (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).budgetRemaining = sc.budgetRemaining := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_periodStart (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).periodStart = sc.periodStart := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_boundThreadCode (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).boundThreadCode = sc.boundThreadCode := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_scReply (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).scReply = sc.scReply := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_donationOrigin (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).donationOrigin = sc.donationOrigin := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_isActive (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).isActive = sc.isActive := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_releaseNextCode (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).releaseNextCode = sc.releaseNextCode := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_releaseCoreCode (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).releaseCoreCode = sc.releaseCoreCode := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_releaseAt (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).releaseAt = sc.releaseAt := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_refillHeadPresent (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).refillHeadPresent = sc.refillHeadPresent := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_refillHeadAmount (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).refillHeadAmount = sc.refillHeadAmount := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_refillHeadEligibleAt (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).refillHeadEligibleAt = sc.refillHeadEligibleAt := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.setTailSlot_refillTailCount (sc : SchedContext) (i : Nat) (e : ReplenishmentEntry) :
    (sc.setTailSlot i e).refillTailCount = sc.refillTailCount := by
  unfold SchedContext.setTailSlot; split <;> rfl

@[simp] theorem SchedContext.writeTail_scId (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).scId = sc.scId := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_scId]

@[simp] theorem SchedContext.writeTail_budget (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).budget = sc.budget := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_budget]

@[simp] theorem SchedContext.writeTail_period (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).period = sc.period := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_period]

@[simp] theorem SchedContext.writeTail_priority (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).priority = sc.priority := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_priority]

@[simp] theorem SchedContext.writeTail_deadline (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).deadline = sc.deadline := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_deadline]

@[simp] theorem SchedContext.writeTail_domain (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).domain = sc.domain := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_domain]

@[simp] theorem SchedContext.writeTail_budgetRemaining (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).budgetRemaining = sc.budgetRemaining := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_budgetRemaining]

@[simp] theorem SchedContext.writeTail_periodStart (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).periodStart = sc.periodStart := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_periodStart]

@[simp] theorem SchedContext.writeTail_boundThreadCode (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).boundThreadCode = sc.boundThreadCode := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_boundThreadCode]

@[simp] theorem SchedContext.writeTail_scReply (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).scReply = sc.scReply := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_scReply]

@[simp] theorem SchedContext.writeTail_donationOrigin (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).donationOrigin = sc.donationOrigin := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_donationOrigin]

@[simp] theorem SchedContext.writeTail_isActive (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).isActive = sc.isActive := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_isActive]

@[simp] theorem SchedContext.writeTail_releaseNextCode (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).releaseNextCode = sc.releaseNextCode := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_releaseNextCode]

@[simp] theorem SchedContext.writeTail_releaseCoreCode (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).releaseCoreCode = sc.releaseCoreCode := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_releaseCoreCode]

@[simp] theorem SchedContext.writeTail_releaseAt (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).releaseAt = sc.releaseAt := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_releaseAt]

@[simp] theorem SchedContext.writeTail_refillHeadPresent (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).refillHeadPresent = sc.refillHeadPresent := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_refillHeadPresent]

@[simp] theorem SchedContext.writeTail_refillHeadAmount (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).refillHeadAmount = sc.refillHeadAmount := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_refillHeadAmount]

@[simp] theorem SchedContext.writeTail_refillHeadEligibleAt (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).refillHeadEligibleAt = sc.refillHeadEligibleAt := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_refillHeadEligibleAt]

@[simp] theorem SchedContext.writeTail_refillTailCount (sc : SchedContext) (i : Nat) (l : List ReplenishmentEntry) :
    (sc.writeTail i l).refillTailCount = sc.refillTailCount := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih => simp only [SchedContext.writeTail, ih, SchedContext.setTailSlot_refillTailCount]

@[simp] theorem SchedContext.withReplenishments_scId (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).scId = sc.scId := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_budget (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).budget = sc.budget := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_period (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).period = sc.period := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_priority (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).priority = sc.priority := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_deadline (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).deadline = sc.deadline := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_domain (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).domain = sc.domain := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_budgetRemaining (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).budgetRemaining = sc.budgetRemaining := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_periodStart (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).periodStart = sc.periodStart := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_boundThreadCode (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).boundThreadCode = sc.boundThreadCode := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_scReply (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).scReply = sc.scReply := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_donationOrigin (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).donationOrigin = sc.donationOrigin := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_isActive (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).isActive = sc.isActive := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_releaseNextCode (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).releaseNextCode = sc.releaseNextCode := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_releaseCoreCode (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).releaseCoreCode = sc.releaseCoreCode := by
  simp [SchedContext.withReplenishments]

@[simp] theorem SchedContext.withReplenishments_releaseAt (sc : SchedContext)
    (rs : List ReplenishmentEntry) : (sc.withReplenishments rs).releaseAt = sc.releaseAt := by
  simp [SchedContext.withReplenishments]

/-- WS-ZA ZA6.3: a slot written reads back; every other slot reads as before. -/
theorem SchedContext.tailSlot_setTailSlot (sc : SchedContext) (i j : Nat) (e : ReplenishmentEntry)
    (hi : i < refillTailCapacity) :
    (sc.setTailSlot i e).tailSlot j = if j = i then e else sc.tailSlot j := by
  rcases e with ⟨⟨a⟩, t⟩
  have hi' : i < 7 := hi
  match i, hi' with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ =>
    match j with
    | 0 | 1 | 2 | 3 | 4 | 5 | 6 => simp [SchedContext.setTailSlot, SchedContext.tailSlot]
    | _ + 7 => simp [SchedContext.setTailSlot, SchedContext.tailSlot]

/-- WS-ZA ZA6.3: writing the slots from `i` on leaves the slots before `i`. -/
theorem SchedContext.writeTail_tailSlot_lt (sc : SchedContext) (i j : Nat)
    (l : List ReplenishmentEntry) (hj : j < i) (hl : i + l.length ≤ refillTailCapacity) :
    (sc.writeTail i l).tailSlot j = sc.tailSlot j := by
  induction l generalizing sc i with
  | nil => rfl
  | cons e l ih =>
    simp only [List.length_cons] at hl
    simp only [SchedContext.writeTail]
    rw [ih _ (i + 1) (by omega) (by omega),
      SchedContext.tailSlot_setTailSlot _ _ _ _ (by omega), if_neg (by omega)]

/-- WS-ZA ZA6.3: writing the slots from `i` on with `l` puts `l`'s `k`-th entry
in slot `i + k`. -/
theorem SchedContext.writeTail_tailSlot (sc : SchedContext) (i : Nat)
    (l : List ReplenishmentEntry) (hl : i + l.length ≤ refillTailCapacity) (k : Nat)
    (hk : k < l.length) :
    (sc.writeTail i l).tailSlot (i + k) = l[k] := by
  induction l generalizing sc i k with
  | nil => simp at hk
  | cons e l ih =>
    simp only [List.length_cons] at hl hk
    simp only [SchedContext.writeTail]
    cases k with
    | zero =>
      rw [SchedContext.writeTail_tailSlot_lt _ _ _ _ (by omega) (by omega),
        SchedContext.tailSlot_setTailSlot _ _ _ _ (by omega), if_pos (by omega)]
      rfl
    | succ k =>
      rw [show i + (k + 1) = (i + 1) + k by omega, ih _ (i + 1) (by omega) k (by omega)]
      rfl

/-- WS-ZA ZA6.3: the slots read through a record update of the other fields. -/
theorem SchedContext.tailSlot_of_slots_eq {sc sc' : SchedContext}
    (h1 : sc'.refillSlot1Amount = sc.refillSlot1Amount ∧ sc'.refillSlot1EligibleAt = sc.refillSlot1EligibleAt)
    (h2 : sc'.refillSlot2Amount = sc.refillSlot2Amount ∧ sc'.refillSlot2EligibleAt = sc.refillSlot2EligibleAt)
    (h3 : sc'.refillSlot3Amount = sc.refillSlot3Amount ∧ sc'.refillSlot3EligibleAt = sc.refillSlot3EligibleAt)
    (h4 : sc'.refillSlot4Amount = sc.refillSlot4Amount ∧ sc'.refillSlot4EligibleAt = sc.refillSlot4EligibleAt)
    (h5 : sc'.refillSlot5Amount = sc.refillSlot5Amount ∧ sc'.refillSlot5EligibleAt = sc.refillSlot5EligibleAt)
    (h6 : sc'.refillSlot6Amount = sc.refillSlot6Amount ∧ sc'.refillSlot6EligibleAt = sc.refillSlot6EligibleAt)
    (h7 : sc'.refillSlot7Amount = sc.refillSlot7Amount ∧ sc'.refillSlot7EligibleAt = sc.refillSlot7EligibleAt)
    (j : Nat) : sc'.tailSlot j = sc.tailSlot j := by
  match j with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | _ + 7 =>
    simp only [SchedContext.tailSlot, h1.1, h1.2, h2.1, h2.2, h3.1, h3.2, h4.1, h4.2, h5.1, h5.2,
      h6.1, h6.2, h7.1, h7.2]

/-- WS-ZA ZA6.3: a slot rewritten with what it holds is the context. -/
theorem SchedContext.setTailSlot_self (sc : SchedContext) (i : Nat) (hi : i < refillTailCapacity) :
    sc.setTailSlot i (sc.tailSlot i) = sc := by
  have hi' : i < 7 := hi
  match i, hi' with
  | 0, _ | 1, _ | 2, _ | 3, _ | 4, _ | 5, _ | 6, _ => rfl

/-- WS-ZA ZA6.3: writing two lists is writing their join. -/
theorem SchedContext.writeTail_append (sc : SchedContext) (i : Nat)
    (l₁ l₂ : List ReplenishmentEntry) :
    sc.writeTail i (l₁ ++ l₂) = (sc.writeTail i l₁).writeTail (i + l₁.length) l₂ := by
  induction l₁ generalizing sc i with
  | nil => rfl
  | cons e l ih =>
    simp only [List.cons_append, SchedContext.writeTail, List.length_cons, ih]
    rw [Nat.add_assoc, Nat.add_comm 1]

/-- WS-ZA ZA6.3: the slots rewritten with what they hold are the context. -/
theorem SchedContext.writeTail_range'_self (sc : SchedContext) (i k : Nat)
    (h : i + k ≤ refillTailCapacity) :
    sc.writeTail i ((List.range' i k).map sc.tailSlot) = sc := by
  induction k generalizing i with
  | zero => rfl
  | succ k ih =>
    simp only [List.range'_succ, List.map_cons, SchedContext.writeTail]
    rw [SchedContext.setTailSlot_self _ _ (by omega)]
    exact ih (i + 1) (by omega)

/-- WS-ZA ZA6.3: the replenishments after the first, rewritten into the slots,
are the context, when they fit. -/
theorem SchedContext.writeTail_refillTail (sc : SchedContext) :
    sc.writeTail 0 sc.refillTail = sc := by
  unfold SchedContext.refillTail
  rw [List.range_eq_range']
  exact SchedContext.writeTail_range'_self sc 0 _ (by omega)

/-- WS-ZA ZA5.2: the replenishments written read back, when they fit the
context's storage (ZA6.3: the first entry and `refillTailCapacity` slots), as
every writer's do (`truncateReplenishments_length_le`). -/
@[simp] theorem SchedContext.withReplenishments_replenishments (sc : SchedContext)
    (rs : List ReplenishmentEntry) (h : rs.length ≤ maxReplenishments) :
    (sc.withReplenishments rs).replenishments = rs := by
  cases rs with
  | nil => rfl
  | cons e rest =>
    rcases e with ⟨⟨a⟩, t⟩
    have hl : rest.length ≤ refillTailCapacity := by
      simp only [List.length_cons] at h; unfold refillTailCapacity; omega
    simp only [SchedContext.replenishments, SchedContext.withReplenishments, List.isEmpty_cons,
      Bool.not_false, if_true, List.cons.injEq, true_and, List.tail_cons]
    unfold SchedContext.refillTail
    apply List.ext_getElem
    · simp only [List.length_map, List.length_range]; omega
    · intro k hk _
      simp only [List.getElem_map, List.getElem_range]
      have hk' : k < rest.length := by
        simp only [List.length_map, List.length_range] at hk; omega
      have := SchedContext.writeTail_tailSlot sc 0 rest (by omega) k hk'
      rw [Nat.zero_add] at this
      rw [← this]
      exact SchedContext.tailSlot_of_slots_eq ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩
        ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ ⟨rfl, rfl⟩ k

/-- WS-ZA ZA6.3: the context's replenishments never exceed its storage. -/
theorem SchedContext.replenishments_length_le (sc : SchedContext) :
    sc.replenishments.length ≤ maxReplenishments := by
  unfold SchedContext.replenishments SchedContext.refillTail
  split
  · simp only [List.length_cons, List.length_map, List.length_range]
    unfold refillTailCapacity maxReplenishments; omega
  · simp

/-- WS-ZA ZA6.3: a filter of the context's replenishments fits its storage. -/
@[simp] theorem SchedContext.length_filter_replenishments_le (sc : SchedContext)
    (p : ReplenishmentEntry → Bool) :
    (sc.replenishments.filter p).length ≤ maxReplenishments :=
  Nat.le_trans (List.length_filter_le _ _) sc.replenishments_length_le

/-- WS-ZA ZA6.3: the replenishments after the first number `refillTailCount`,
up to the slots. -/
theorem SchedContext.refillTail_length (sc : SchedContext) :
    sc.refillTail.length = min sc.refillTailCount refillTailCapacity := by
  simp [SchedContext.refillTail]

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
@[inline] def isDonated : SchedContextBinding → Bool
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

/-! WS-ZA ZA5.2: a binding as two scalar codes, the form the TCB stores it in
(`TCB.scBindingScCode`, `TCB.scBindingOwnerCode`): a constructor with a payload
is a heap cell, so a store of `.bound scId` allocated on every bind.  The context
code is `0` for `unbound` and the context's id plus one otherwise; the owner code
is the donation's original owner plus one, `0` for any other binding. -/

/-- The context word of the binding's code. -/
@[inline] def scCode : SchedContextBinding → Nat
  | .unbound => 0
  | .bound s => s.val + 1
  | .donated s _ => s.val + 1

/-- The owner word of the binding's code. -/
@[inline] def ownerCode : SchedContextBinding → Nat
  | .donated _ o => o.val + 1
  | _ => 0

/-- The binding a pair of codes stands for. -/
@[inline] def ofCodes (sc owner : Nat) : SchedContextBinding :=
  match sc with
  | 0 => .unbound
  | s + 1 =>
    match owner with
    | 0 => .bound ⟨s⟩
    | o + 1 => .donated ⟨s⟩ ⟨o⟩

@[simp] theorem ofCodes_codes (b : SchedContextBinding) :
    ofCodes b.scCode b.ownerCode = b := by
  cases b <;> rfl

@[simp] theorem ownerCode_bound (s : SchedContextId) : (bound s).ownerCode = 0 := rfl
@[simp] theorem ownerCode_unbound : unbound.ownerCode = 0 := rfl
@[simp] theorem scCode_unbound : unbound.scCode = 0 := rfl

/-- A `.bound` binding's codes read back as that binding once its owner word has
been simplified to `0` (`ownerCode_bound`). -/
@[simp] theorem ofCodes_scCode_bound (s : SchedContextId) : ofCodes (bound s).scCode 0 = bound s := rfl

@[simp] theorem ofCodes_zero (owner : Nat) : ofCodes 0 owner = .unbound := rfl

@[simp] theorem scCode_ofCodes (sc owner : Nat) : (ofCodes sc owner).scCode = sc := by
  cases sc <;> cases owner <;> rfl

/-- The owner word of a binding read from codes is the stored owner word, when
the context word names a context: the one case the owner word is read in. -/
theorem ownerCode_ofCodes_succ (s owner : Nat) :
    (ofCodes (s + 1) owner).ownerCode = owner := by
  cases owner <;> rfl

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
    -- WS-OD OD2.1: the reply-stack head participates in structural equality, so
    -- a push or a pop is visible to every caller that compares with `==`.
    a.scReply == b.scReply &&
    -- WS-HP HP10.3: and so does the recorded origin, for the same reason — a
    -- write that records or clears the loan's owner is visible to every caller
    -- that compares with `==`, including the frozen surface's differential.
    a.donationOrigin == b.donationOrigin &&
    a.isActive == b.isActive &&
    -- WS-ZA ZA6.3: and the context's release-queue place, as a thread's
    -- run-queue links take part in its own.
    a.releaseNextCode == b.releaseNextCode && a.releaseCoreCode == b.releaseCoreCode &&
    a.releaseAt == b.releaseAt &&
    -- WS-ZA ZA6.5: and the consumed time, so a charge that accumulates it
    -- differently on the frozen surface is a disagreement.
    a.consumed == b.consumed &&
    -- WS-ZA ZA6.6: and the yield link, compared as its code.
    a.yieldFromCode == b.yieldFromCode

end SeLe4n.Kernel
