-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Selection

/-!
# The reschedule-SGI accumulator — the key-change hook and the flag-derived SGIs

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md` (the accumulator slice;
WS-CB's `reschedulePendingOnCore` is the same flag, `HIERARCHICAL_CBS_PLAN.md`
§4.1 / §4.4).  `SchedulerState.reschedulePending` records, per core, that a
scheduling point is owed; `Model/State.lean` holds the field, its accessor and
the slot-level marks.  This module holds the two pieces that need the scheduler
operations:

* `markKeyChangeFor` — the one hook every writer of a thread's **effective
  key** (`effectiveSchedParams`: `TCB.priority`, `TCB.pipBoost`,
  `TCB.schedContextBinding`, the bound context's deadline, `TCB.domain`) calls
  after its write.  It is the single-thread instance of the commit diff's rules
  (`crossCoreSgiBody`, `PriorityInheritance/PerCore.lean`): a queued thread
  whose key changed flags its home core; a current thread whose effective
  priority dropped, whose effective deadline moved later or whose domain moved
  flags the core running it; a raise, an unchanged key, or a thread placed nowhere flags
  nothing.  The writer hands in the key it read **before** the write, so the
  hook is exact at O(1) and never keeps the pre-state alive.

* `rescheduleSgisFromFlags` — the `.reschedule` SGIs a step owes, read off a
  captured pre-dispatch flag vector and the post-state's: one per core (the
  executing core included) whose flag went `false → true`.  **Not yet the live decider**: in this slice
  the syscall commit still runs `computeCrossCoreSgis` (the whole-object-index
  diff), and the Tier 2 `reschedule_pending_suite` pins this list against the
  diff on every SMP scenario; the seam switch is the row's PR C and the
  set-equality theorem its PR B.

Slot writers (`enqueueRunnableOnCore`, `removeRunnableOnCore`,
`removeRunnableStepOnCore`, `migrateRunQueueOnAffinityChange`, the
SchedContext bind / unbind / yield placements) mark directly through
`SchedulerState.markReschedulePendingOnCore` — they already name the core they
write.  The flag is cleared only by the flagged core's own scheduling points,
`handleRescheduleSgiOnCore` and `scheduleEffectiveOnCore`, as their last write.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind allCores numCores)

/-- Mark every core of `cs` on which `p` holds — the key-change hook's write,
which flags each core whose queue or current slot holds the re-keyed thread
without assuming the thread sits on one core only. -/
def markReschedulePendingWhere (st : SystemState) (p : CoreId → Bool) :
    List CoreId → SystemState
  | [] => st
  | c :: cs => markReschedulePendingWhere
      (if p c then st.markReschedulePendingOnCore c else st) p cs

/-- Any projection the single mark leaves alone, the multi-core mark leaves
alone. -/
theorem markReschedulePendingWhere_extract_frame {F : Type} (extract : SystemState → F)
    (h : ∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s)
    (st : SystemState) (p : CoreId → Bool) (cs : List CoreId) :
    extract (markReschedulePendingWhere st p cs) = extract st := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    simp only [markReschedulePendingWhere]
    rw [ih]
    split
    · exact h st c
    · rfl

/-- A core's flag after the multi-core mark: the old flag, or `p` on a listed
core. -/
theorem markReschedulePendingWhere_reschedulePendingOnCore (st : SystemState)
    (p : CoreId → Bool) (cs : List CoreId) (c' : CoreId) :
    (markReschedulePendingWhere st p cs).scheduler.reschedulePendingOnCore c' =
      (st.scheduler.reschedulePendingOnCore c' || (p c' && decide (c' ∈ cs))) := by
  induction cs generalizing st with
  | nil => simp [markReschedulePendingWhere]
  | cons c cs ih =>
    simp only [markReschedulePendingWhere]
    rw [ih]
    by_cases hc : c = c'
    · subst hc
      cases p c <;> simp [SystemState.markReschedulePendingOnCore]
    · split <;> simp [SystemState.markReschedulePendingOnCore, hc, List.mem_cons, Ne.symm hc]

/-- Flag every core whose scheduling decision a key write on `tid` has staled.
`preKey` is `effectiveSchedParams` of `tid` read on the state before the write
(effective priority, effective deadline, domain); `st` is the state after it.
Mirrors `crossCoreSgiBody` for the one thread: a core whose run queue holds
`tid` is flagged when the key moved, and a core whose current slot holds `tid`
when its effective priority dropped, its effective deadline moved later, or its
domain moved (the selector admits only threads of the core's active domain, so
a current thread whose domain moved may no longer be eligible to run there).  Every core is checked, so the hook assumes no
placement invariant (`markKeyChangeFor_covers` needs none); under the kernel
invariants the thread sits on one core and at most one flag is raised.  The
queue membership and the current slot are read from `st` because a key writer
moves neither (the placements that do mark the core themselves).  A write that
left no TCB under `tid` counts as a moved key. -/
def markKeyChangeFor (st : SystemState) (tid : SeLe4n.ThreadId)
    (preKey : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) : SystemState :=
  let postKey? := (st.getTcb? tid).map (effectiveSchedParams st)
  let moved : Bool := match postKey? with
    | some k => !(preKey.1 == k.1 && preKey.2.1.val == k.2.1.val && preKey.2.2 == k.2.2)
    | none => true
  let weakened : Bool := match postKey? with
    | some k => k.1.val < preKey.1.val || preKey.2.1.val < k.2.1.val || preKey.2.2 != k.2.2
    | none => false
  let staled : CoreId → Bool := fun c =>
    (moved && st.queuedOn c tid) ||
      (weakened && st.scheduler.currentOnCore c == some tid)
  markReschedulePendingWhere st staled allCores

/-- Any projection that the flag write leaves alone, the hook leaves alone:
the hook is a sequence of `markReschedulePendingOnCore`s. -/
theorem markKeyChangeFor_extract_frame {F : Type} (extract : SystemState → F)
    (st : SystemState) (tid : SeLe4n.ThreadId) (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (h : ∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s) :
    extract (markKeyChangeFor st tid k) = extract st := by
  unfold markKeyChangeFor
  exact markReschedulePendingWhere_extract_frame extract h st _ allCores

/-- WS-ZA ZA4.7: a thread's effective deadline, `effectiveSchedParams`'s middle
component, read without building the triple. -/
@[inline] def effectiveDeadline (st : SystemState) (tcb : TCB) : SeLe4n.Deadline :=
  match tcb.schedContextBinding with
  | .unbound => tcb.deadline
  | .bound scId =>
    match st.getSchedContext? scId with
    | some sc => sc.deadline
    | none => tcb.deadline
  | .donated scId _ =>
    match st.getSchedContext? scId with
    | some sc => sc.deadline
    | none => tcb.deadline

theorem effectiveSchedParams_eq_parts (st : SystemState) (tcb : TCB) :
    effectiveSchedParams st tcb = (tcb.boostedPriority, effectiveDeadline st tcb, tcb.domain) := by
  unfold effectiveSchedParams effectiveDeadline
  cases tcb.schedContextBinding with
  | unbound => rfl
  | bound scId => cases h : st.getSchedContext? scId <;> simp only [h]
  | donated scId _ => cases h : st.getSchedContext? scId <;> simp only [h]

/-- WS-ZA ZA4.7: the key hook's flag writes over `cores`, with the re-keyed
thread's run-core code `rc` and its weakening already read: a core is flagged
when it queues the thread, or when the key weakened and it runs the thread.
Recursion over the cores, so no predicate closure is built. -/
def markKeyFlagsOver (st : SystemState) (tid : SeLe4n.ThreadId) (rc : Nat) (weakened : Bool) :
    List CoreId → SystemState
  | [] => st
  | c :: cs => markKeyFlagsOver
      (if rc == c.val + 1 || (weakened && (st.scheduler.currentOnCore c).isEqSome tid)
       then st.markReschedulePendingOnCore c else st) tid rc weakened cs

/-- WS-ZA ZA4.7: `markKeyChangeFor` with the pre-write key handed in as its
three parts.  The thread's new key is read off its TCB as fields; an unmoved
key flags nothing, so the state is answered as it is. -/
def markKeyChangeParts (st : SystemState) (tid : SeLe4n.ThreadId) (p0 : SeLe4n.Priority)
    (d0 : SeLe4n.Deadline) (dom0 : SeLe4n.DomainId) : SystemState :=
  match st.getTcb? tid with
  | some t =>
    let p := t.boostedPriority
    let d := effectiveDeadline st t
    if p0 == p && d0.val == d.val && dom0 == t.domain then st
    else
      markKeyFlagsOver st tid t.runCoreCode
        (p.val < p0.val || d0.val < d.val || dom0 != t.domain) allCores
  | none => st

theorem markReschedulePendingWhere_of_false (st : SystemState) (p : CoreId → Bool)
    (cs : List CoreId) (h : ∀ c, p c = false) : markReschedulePendingWhere st p cs = st := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih => simp only [markReschedulePendingWhere, h c, Bool.false_eq_true, ↓reduceIte, ih]

/-- The flag loop is the hook's fold: the predicate reads the current slots of
the state the fold started from, which the marks never move. -/
theorem markReschedulePendingWhere_eq_markKeyFlagsOver (st0 : SystemState)
    (tid : SeLe4n.ThreadId) (rc : Nat) (w : Bool) (cs : List CoreId) :
    ∀ st : SystemState, (∀ c, st.scheduler.currentOnCore c = st0.scheduler.currentOnCore c) →
      markReschedulePendingWhere st
          (fun c => rc == c.val + 1 || (w && st0.scheduler.currentOnCore c == some tid)) cs =
        markKeyFlagsOver st tid rc w cs := by
  induction cs with
  | nil => intro _ _; rfl
  | cons c cs ih =>
    intro st hCur
    have hEq : (st0.scheduler.currentOnCore c == some tid) =
        (st.scheduler.currentOnCore c).isEqSome tid := by
      rw [hCur c]; cases st0.scheduler.currentOnCore c <;> rfl
    simp only [markReschedulePendingWhere, markKeyFlagsOver, hEq]
    apply ih
    intro c'
    split
    · simp only [SystemState.markReschedulePendingOnCore_scheduler,
        SchedulerState.markReschedulePendingOnCore_currentOnCore, hCur]
    · exact hCur c'

theorem markKeyChangeFor_eq_parts (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    markKeyChangeFor st tid k = markKeyChangeParts st tid k.1 k.2.1 k.2.2 := by
  obtain ⟨p0, d0, dom0⟩ := k
  unfold markKeyChangeFor markKeyChangeParts
  cases hT : st.getTcb? tid with
  | none =>
    apply markReschedulePendingWhere_of_false
    intro c
    simp [SystemState.queuedOn, hT]
  | some t =>
    simp only [Option.map_some, effectiveSchedParams_eq_parts]
    by_cases hK : (p0 == t.boostedPriority && d0.val == (effectiveDeadline st t).val &&
        dom0 == t.domain) = true
    · rw [if_pos hK]
      apply markReschedulePendingWhere_of_false
      intro c
      simp only [Bool.and_eq_true, beq_iff_eq] at hK
      obtain ⟨⟨h1, h2⟩, h3⟩ := hK
      subst h1 h3
      simp [h2]
    · rw [if_neg hK]
      simp only [Bool.eq_false_iff.mpr hK, Bool.not_false, Bool.true_and]
      have hQ : ∀ c, st.queuedOn c tid = (t.runCoreCode == c.val + 1) := fun c => by
        simp [SystemState.queuedOn, hT]
      simp only [hQ]
      exact markReschedulePendingWhere_eq_markKeyFlagsOver st tid _ _ allCores st (fun _ => rfl)

/-- WS-ZA ZA4.7: the compiled `markKeyChangeFor`.  Inlined, so a caller that
builds the key as a triple hands its parts straight in. -/
@[inline] def markKeyChangeForImpl (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) : SystemState :=
  markKeyChangeParts st tid k.1 k.2.1 k.2.2

@[csimp] theorem markKeyChangeFor_eq_impl : @markKeyChangeFor = @markKeyChangeForImpl := by
  funext st tid k
  exact markKeyChangeFor_eq_parts st tid k

/-- Any projection the single mark leaves alone, the flag loop leaves alone. -/
theorem markKeyFlagsOver_extract_frame {F : Type} (extract : SystemState → F)
    (h : ∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s)
    (st : SystemState) (tid : SeLe4n.ThreadId) (rc : Nat) (w : Bool) (cs : List CoreId) :
    extract (markKeyFlagsOver st tid rc w cs) = extract st := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    simp only [markKeyFlagsOver]
    rw [ih]
    split
    · exact h st c
    · rfl

/-- WS-ZA ZA6.2: **the candidacy hook.**  The selector admits a queued thread
only when it has budget (`hasSufficientBudget`, read by
`chooseBestRunnableEffective` beside the key), so a write that gives a queued
thread budget it lacked stales its core's decision as surely as a key move,
with the key unchanged: a refill, a reconfigure, an unbind or a donation can
each do it.  `preElig` is `hasSufficientBudget` of `tid` read before the write;
each core whose queue holds `tid` is flagged when `tid` was ineligible then and
is eligible now.  Losing eligibility flags nothing: a candidate leaving the
field stales no decision, as a queue removal does not. -/
def markCandidacyGainFor (st : SystemState) (tid : SeLe4n.ThreadId) (preElig : Bool) :
    SystemState :=
  if preElig then st
  else
    match st.getTcb? tid with
    | some t =>
      if hasSufficientBudget st t then markKeyFlagsOver st tid t.runCoreCode false allCores
      else st
    | none => st

/-- Any projection the single mark leaves alone, the candidacy hook leaves alone. -/
theorem markCandidacyGainFor_extract_frame {F : Type} (extract : SystemState → F)
    (st : SystemState) (tid : SeLe4n.ThreadId) (e : Bool)
    (h : ∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s) :
    extract (markCandidacyGainFor st tid e) = extract st := by
  unfold markCandidacyGainFor
  split
  · rfl
  · split
    · split
      · exact markKeyFlagsOver_extract_frame extract h st tid _ false allCores
      · rfl
    · rfl

/-- The candidacy hook's flags: a core's old flag, or the gain on a core whose
queue holds `tid`. -/
theorem markCandidacyGainFor_reschedulePendingOnCore (st : SystemState)
    (tid : SeLe4n.ThreadId) (e : Bool) (c : CoreId) :
    (markCandidacyGainFor st tid e).scheduler.reschedulePendingOnCore c =
      (st.scheduler.reschedulePendingOnCore c ||
        (!e && ((st.getTcb? tid).map (hasSufficientBudget st) == some true) &&
          st.queuedOn c tid)) := by
  unfold markCandidacyGainFor
  cases e with
  | true => simp
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte, Bool.not_false, Bool.true_and]
    cases hT : st.getTcb? tid with
    | none => simp
    | some t =>
      simp only [Option.map_some]
      cases hB : hasSufficientBudget st t with
      | false => simp
      | true =>
        simp only [↓reduceIte]
        rw [← markReschedulePendingWhere_eq_markKeyFlagsOver st tid t.runCoreCode false allCores st
          (fun _ => rfl), markReschedulePendingWhere_reschedulePendingOnCore]
        have hQ : st.queuedOn c tid = (t.runCoreCode == c.val + 1) := by
          simp [SystemState.queuedOn, hT]
        simp [hQ, Concurrency.mem_allCores]

/-- The candidacy hook never lowers a flag. -/
theorem markCandidacyGainFor_reschedulePendingOnCore_mono (st : SystemState)
    (tid : SeLe4n.ThreadId) (e : Bool) (c : CoreId)
    (h : st.scheduler.reschedulePendingOnCore c = true) :
    (markCandidacyGainFor st tid e).scheduler.reschedulePendingOnCore c = true := by
  rw [markCandidacyGainFor_reschedulePendingOnCore, h, Bool.true_or]

/-- The candidacy hook writes the reschedule flags only. -/
theorem markCandidacyGainFor_eq_with_scheduler (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : Bool) :
    markCandidacyGainFor st tid e =
      { st with scheduler := { st.scheduler with reschedulePending :=
          (markCandidacyGainFor st tid e).scheduler.reschedulePending } } :=
  let Y := markCandidacyGainFor st tid e
  markCandidacyGainFor_extract_frame
    (fun s => ({ s with scheduler := { s.scheduler with reschedulePending :=
      Y.scheduler.reschedulePending } } : SystemState)) st tid e (fun _ _ => rfl)

@[simp] theorem markCandidacyGainFor_objects (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : Bool) : (markCandidacyGainFor st tid e).objects = st.objects :=
  markCandidacyGainFor_extract_frame (fun s => s.objects) st tid e (fun _ _ => rfl)

@[simp] theorem markCandidacyGainFor_machine (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : Bool) : (markCandidacyGainFor st tid e).machine = st.machine :=
  markCandidacyGainFor_extract_frame (fun s => s.machine) st tid e (fun _ _ => rfl)

@[simp] theorem markCandidacyGainFor_currentOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : Bool) (c : CoreId) :
    (markCandidacyGainFor st tid e).scheduler.currentOnCore c = st.scheduler.currentOnCore c :=
  markCandidacyGainFor_extract_frame (fun s => s.scheduler.currentOnCore c) st tid e
    (fun _ _ => by simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_getTcb? (st : SystemState) (tid t : SeLe4n.ThreadId)
    (e : Bool) : (markCandidacyGainFor st tid e).getTcb? t = st.getTcb? t := by
  unfold SystemState.getTcb?; rw [markCandidacyGainFor_objects]

@[simp] theorem markCandidacyGainFor_queuedOn (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : Bool) (c : CoreId) (t : SeLe4n.ThreadId) :
    (markCandidacyGainFor st tid e).queuedOn c t = st.queuedOn c t :=
  (SystemState.RunCoresAgree.of_objects (markCandidacyGainFor_objects st tid e)).queuedOn c t

/-- The key hook for a writer that hands in its **pre-state** rather than a key
it already read: `tid`'s key is read on `pre`, the flags are raised on `post`.
A thread with no TCB in `pre` had no key, so every core still holding it in a
queue or the current slot is flagged.  A move that leaves the key alone but
makes `tid` budget-eligible where it was not (a binding to a context with
budget left) is a candidacy gain the chooser reads, so it flags `tid`'s queued
cores too (`markCandidacyGainFor`).  The binding writers (donation, its
return, the donation cancels) end in this, once per thread whose binding they
moved. -/
def markKeyChangeFrom (pre post : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  match pre.getTcb? tid with
  | some tcb => markKeyChangeFor (markCandidacyGainFor post tid (hasSufficientBudget pre tcb)) tid
      (effectiveSchedParams pre tcb)
  | none => markReschedulePendingWhere post
      (fun c => post.queuedOn c tid ||
        post.scheduler.currentOnCore c == some tid) allCores

theorem markKeyChangeFrom_extract_frame {F : Type} (extract : SystemState → F)
    (pre post : SystemState) (tid : SeLe4n.ThreadId)
    (h : ∀ (s : SystemState) c, extract (s.markReschedulePendingOnCore c) = extract s) :
    extract (markKeyChangeFrom pre post tid) = extract post := by
  unfold markKeyChangeFrom
  split
  · exact (markKeyChangeFor_extract_frame extract _ tid _ h).trans
      (markCandidacyGainFor_extract_frame extract post tid _ h)
  · exact markReschedulePendingWhere_extract_frame extract h post _ allCores

/-- The `.reschedule` SGIs a step owes, from the flag vector captured before
dispatch and the committed state's: one per core whose flag went
`false → true`.  A core already pending at the step's start is not re-poked
(its SGI is outstanding).  The list covers the whole-index diff (every core the
diff names is named here or was already pending) and may name more: the flags
over-approximate, costing at most a spurious reschedule IPI.

**The executing core included.**  A flag the step raised on its own core and
left up (the commit's local reschedule clears it on a vacated core) is a
scheduling point the core owes itself: a writer weakened the caller's own key
or queued a thread that may outrank it.  The core interrupts itself, and the
SGI is taken as the entry returns, where the reschedule entry runs the
receiver under the core's own lock.  Running the receiver inline instead would
write the core's run queue and current slot under a step whose lock footprint
need not cover them; leaving the flag up would hold the reschedule to the
core's next scheduling point and swallow the `false → true` edge a later remote
writer needs. -/
def rescheduleSgisFromFlags (pre post : PerCoreFlags) :
    List (CoreId × SgiKind) :=
  (allCores.filter fun c => !pre.get c && post.get c).map
    fun c => (c, SgiKind.reschedule)

/-- WS-ZA ZA4.7: the `.reschedule` SGIs a raised-flag word names, one per set
core in core order.  A seam hands the runtime the word
(`PerCoreFlags.raised`) and the runtime fires from it without building this
list; the list is how the word is read in proofs. -/
def sgisOfRaised (m : PerCoreFlags) : List (CoreId × SgiKind) :=
  (allCores.filter m.get).map fun c => (c, SgiKind.reschedule)

theorem rescheduleSgisFromFlags_eq_sgisOfRaised (pre post : PerCoreFlags) :
    rescheduleSgisFromFlags pre post = sgisOfRaised (pre.raised post) := by
  unfold rescheduleSgisFromFlags sgisOfRaised
  congr 2
  funext c
  exact (PerCoreFlags.get_raised pre post c).symm

/-- The flag set a seam captures before its transition.  A call rather than
a field read on purpose: the compiler sinks a projection to its use, which would
hold the pre-state's scheduler alive across the transition and force the
transition to copy it instead of updating it in place; a call is not sunk. -/
@[noinline] def reschedulePendingSnapshot (st : SystemState) : PerCoreFlags :=
  st.scheduler.reschedulePending

/-- Membership in the flag-derived list, spelled out. -/
theorem mem_rescheduleSgisFromFlags_iff (pre post : PerCoreFlags) (c : CoreId)
    (k : SgiKind) :
    (c, k) ∈ rescheduleSgisFromFlags pre post ↔
      k = SgiKind.reschedule ∧ pre.get c = false ∧ post.get c = true := by
  unfold rescheduleSgisFromFlags
  simp only [List.mem_map, List.mem_filter, Concurrency.mem_allCores, true_and, Prod.mk.injEq]
  constructor
  · intro h
    obtain ⟨c', hc', hEq⟩ := h
    obtain ⟨rfl, rfl⟩ := hEq
    simp only [Bool.and_eq_true, Bool.not_eq_true'] at hc'
    exact ⟨rfl, hc'.1, hc'.2⟩
  · rintro ⟨rfl, hpre, hpost⟩
    exact ⟨c, by simp [hpre, hpost], rfl, rfl⟩

/-- Every flag-derived SGI is a `.reschedule` (the counterpart of
`computeCrossCoreSgis_all_reschedule`). -/
theorem rescheduleSgisFromFlags_all_reschedule (pre post : PerCoreFlags)
    (p : CoreId × SgiKind) (h : p ∈ rescheduleSgisFromFlags pre post) :
    p.2 = SgiKind.reschedule := by
  obtain ⟨c, k⟩ := p
  exact ((mem_rescheduleSgisFromFlags_iff pre post c k).mp h).1

/-- A flag that was already set surfaces nothing — the list names only the
cores this step raised. -/
theorem rescheduleSgisFromFlags_nil_of_eq (v : PerCoreFlags) :
    rescheduleSgisFromFlags v v = [] := by
  unfold rescheduleSgisFromFlags
  rw [List.map_eq_nil_iff, List.filter_eq_nil_iff]
  intro c _
  cases v.get c <;> simp

/-! ### Frames: the key hook writes one flag and nothing else -/

@[simp] theorem markKeyChangeFor_objects (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).objects = st.objects :=
  markKeyChangeFor_extract_frame (fun s => s.objects) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_queuedOn (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (c : CoreId) (t : SeLe4n.ThreadId) :
    (markKeyChangeFor st tid k).queuedOn c t = st.queuedOn c t :=
  (SystemState.RunCoresAgree.of_objects (markKeyChangeFor_objects st tid k)).queuedOn c t

/-- WS-ZA ZA4.5: the hook rewrites the scheduler alone. -/
theorem markKeyChangeFor_onlyObjectsSchedulerDiffer (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    SystemState.onlyObjectsSchedulerDiffer (markKeyChangeFor st tid k) st :=
  let post := markKeyChangeFor st tid k
  markKeyChangeFor_extract_frame
    (fun s : SystemState => ({ s with objects := post.objects, scheduler := post.scheduler } : SystemState))
    st tid k (fun _ _ => rfl)

@[simp] theorem markKeyChangeFor_objectIndex (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).objectIndex = st.objectIndex :=
  markKeyChangeFor_extract_frame (fun s => s.objectIndex) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_machine (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).machine = st.machine :=
  markKeyChangeFor_extract_frame (fun s => s.machine) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_cdt (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).cdt = st.cdt :=
  markKeyChangeFor_extract_frame (fun s => s.cdt) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_irqHandlers (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).irqHandlers = st.irqHandlers :=
  markKeyChangeFor_extract_frame (fun s => s.irqHandlers) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_tlbShootdown (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).tlbShootdown = st.tlbShootdown :=
  markKeyChangeFor_extract_frame (fun s => s.tlbShootdown) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_perCoreTlb (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).perCoreTlb = st.perCoreTlb :=
  markKeyChangeFor_extract_frame (fun s => s.perCoreTlb) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_perCoreICache (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).perCoreICache = st.perCoreICache :=
  markKeyChangeFor_extract_frame (fun s => s.perCoreICache) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_pendingIcacheMaintenance (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).pendingIcacheMaintenance = st.pendingIcacheMaintenance :=
  markKeyChangeFor_extract_frame (fun s => s.pendingIcacheMaintenance) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_pendingPhysicalWrites (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).pendingPhysicalWrites = st.pendingPhysicalWrites :=
  markKeyChangeFor_extract_frame (fun s => s.pendingPhysicalWrites) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_objectIndexSet (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).objectIndexSet = st.objectIndexSet :=
  markKeyChangeFor_extract_frame (fun s => s.objectIndexSet) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_lifecycle (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).lifecycle = st.lifecycle :=
  markKeyChangeFor_extract_frame (fun s => s.lifecycle) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_asidTable (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).asidTable = st.asidTable :=
  markKeyChangeFor_extract_frame (fun s => s.asidTable) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_interfaceRegistry (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).interfaceRegistry = st.interfaceRegistry :=
  markKeyChangeFor_extract_frame (fun s => s.interfaceRegistry) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_tlb (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).tlb = st.tlb :=
  markKeyChangeFor_extract_frame (fun s => s.tlb) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_declassificationAuditLog (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).declassificationAuditLog = st.declassificationAuditLog :=
  markKeyChangeFor_extract_frame (fun s => s.declassificationAuditLog) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_declassificationAuditEpoch (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).declassificationAuditEpoch = st.declassificationAuditEpoch :=
  markKeyChangeFor_extract_frame (fun s => s.declassificationAuditEpoch) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_declassificationRefusals (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).declassificationRefusals = st.declassificationRefusals :=
  markKeyChangeFor_extract_frame (fun s => s.declassificationRefusals) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_declassificationTaint (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).declassificationTaint = st.declassificationTaint :=
  markKeyChangeFor_extract_frame (fun s => s.declassificationTaint) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_getTcb? (st : SystemState) (tid tid' : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).getTcb? tid' = st.getTcb? tid' := by
  unfold SystemState.getTcb?; rw [markKeyChangeFor_objects]

@[simp] theorem markKeyChangeFor_getSchedContext? (st : SystemState) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?; rw [markKeyChangeFor_objects]

@[simp] theorem markKeyChangeFor_runQueueOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.runQueueOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_currentOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.currentOnCore c = st.scheduler.currentOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.currentOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_replenishQueueOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.replenishQueueOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_activeDomainOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.activeDomainOnCore c
      = st.scheduler.activeDomainOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.activeDomainOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_domainTimeRemainingOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.domainTimeRemainingOnCore c
      = st.scheduler.domainTimeRemainingOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.domainTimeRemainingOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_domainScheduleIndexOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.domainScheduleIndexOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_lastTimeoutErrorsOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (c : CoreId) :
    (markKeyChangeFor st tid k).scheduler.lastTimeoutErrorsOnCore c
      = st.scheduler.lastTimeoutErrorsOnCore c :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.lastTimeoutErrorsOnCore c) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_domainSchedule (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).scheduler.domainSchedule = st.scheduler.domainSchedule :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.domainSchedule) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_configDefaultTimeSlice (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).scheduler.configDefaultTimeSlice = st.scheduler.configDefaultTimeSlice :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.configDefaultTimeSlice) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

/-- Queue membership on some core reads the threads' run-queue cores alone,
which the hook never writes. -/
@[simp] theorem markKeyChangeFor_runnableOnSomeCore (st : SystemState)
    (tid tid' : SeLe4n.ThreadId) (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    runnableOnSomeCore (markKeyChangeFor st tid k) tid' = runnableOnSomeCore st tid' := by
  unfold runnableOnSomeCore
  simp only [markKeyChangeFor_queuedOn]

/-- The placement resolver reads the threads' run-queue cores and the current
slots alone, which the hook never writes. -/
@[simp] theorem markKeyChangeFor_placedCoreOf? (st : SystemState)
    (tid tid' : SeLe4n.ThreadId) (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    placedCoreOf? (markKeyChangeFor st tid k) tid' = placedCoreOf? st tid' := by
  unfold placedCoreOf?
  simp only [markKeyChangeFor_queuedOn, markKeyChangeFor_currentOnCore]

/-- Marking one core never lowers another's flag (nor its own). -/
theorem _root_.SeLe4n.Model.SchedulerState.markReschedulePendingOnCore_reschedulePendingOnCore_of
    (s : SchedulerState) (c c' : CoreId) (h : s.reschedulePendingOnCore c = true) :
    (s.markReschedulePendingOnCore c').reschedulePendingOnCore c = true := by
  by_cases hc : c' = c
  · subst hc; simp
  · simp [hc, h]

/-- The hook never lowers a flag: a core pending before it is pending after. -/
theorem markKeyChangeFor_reschedulePendingOnCore_mono (st : SystemState)
    (tid : SeLe4n.ThreadId) (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) (c : CoreId)
    (h : st.scheduler.reschedulePendingOnCore c = true) :
    (markKeyChangeFor st tid k).scheduler.reschedulePendingOnCore c = true := by
  simp only [markKeyChangeFor, markReschedulePendingWhere_reschedulePendingOnCore,
    h, Bool.true_or]

/-! ### Frames: the pre-state form of the hook writes flags and nothing else -/

@[simp] theorem markKeyChangeFrom_objects (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).objects = st.objects :=
  markKeyChangeFrom_extract_frame (fun s => s.objects) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_queuedOn (pre st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (t : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).queuedOn c t = st.queuedOn c t :=
  (SystemState.RunCoresAgree.of_objects (markKeyChangeFrom_objects pre st tid)).queuedOn c t

@[simp] theorem markKeyChangeFrom_objectIndex (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).objectIndex = st.objectIndex :=
  markKeyChangeFrom_extract_frame (fun s => s.objectIndex) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_machine (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).machine = st.machine :=
  markKeyChangeFrom_extract_frame (fun s => s.machine) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_cdt (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).cdt = st.cdt :=
  markKeyChangeFrom_extract_frame (fun s => s.cdt) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_irqHandlers (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).irqHandlers = st.irqHandlers :=
  markKeyChangeFrom_extract_frame (fun s => s.irqHandlers) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_tlbShootdown (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).tlbShootdown = st.tlbShootdown :=
  markKeyChangeFrom_extract_frame (fun s => s.tlbShootdown) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_perCoreTlb (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).perCoreTlb = st.perCoreTlb :=
  markKeyChangeFrom_extract_frame (fun s => s.perCoreTlb) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_perCoreICache (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).perCoreICache = st.perCoreICache :=
  markKeyChangeFrom_extract_frame (fun s => s.perCoreICache) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_pendingIcacheMaintenance (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).pendingIcacheMaintenance = st.pendingIcacheMaintenance :=
  markKeyChangeFrom_extract_frame (fun s => s.pendingIcacheMaintenance) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_pendingPhysicalWrites (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).pendingPhysicalWrites = st.pendingPhysicalWrites :=
  markKeyChangeFrom_extract_frame (fun s => s.pendingPhysicalWrites) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_objectIndexSet (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).objectIndexSet = st.objectIndexSet :=
  markKeyChangeFrom_extract_frame (fun s => s.objectIndexSet) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_lifecycle (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).lifecycle = st.lifecycle :=
  markKeyChangeFrom_extract_frame (fun s => s.lifecycle) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_asidTable (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).asidTable = st.asidTable :=
  markKeyChangeFrom_extract_frame (fun s => s.asidTable) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_interfaceRegistry (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).interfaceRegistry = st.interfaceRegistry :=
  markKeyChangeFrom_extract_frame (fun s => s.interfaceRegistry) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_tlb (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).tlb = st.tlb :=
  markKeyChangeFrom_extract_frame (fun s => s.tlb) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_declassificationAuditLog (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).declassificationAuditLog = st.declassificationAuditLog :=
  markKeyChangeFrom_extract_frame (fun s => s.declassificationAuditLog) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_declassificationAuditEpoch (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).declassificationAuditEpoch = st.declassificationAuditEpoch :=
  markKeyChangeFrom_extract_frame (fun s => s.declassificationAuditEpoch) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_declassificationRefusals (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).declassificationRefusals = st.declassificationRefusals :=
  markKeyChangeFrom_extract_frame (fun s => s.declassificationRefusals) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_declassificationTaint (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).declassificationTaint = st.declassificationTaint :=
  markKeyChangeFrom_extract_frame (fun s => s.declassificationTaint) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_getTcb? (pre st : SystemState) (tid tid' : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).getTcb? tid' = st.getTcb? tid' := by
  unfold SystemState.getTcb?; rw [markKeyChangeFrom_objects]

@[simp] theorem markKeyChangeFrom_getSchedContext? (pre st : SystemState) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) :
    (markKeyChangeFrom pre st tid).getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?; rw [markKeyChangeFrom_objects]

@[simp] theorem markKeyChangeFrom_runQueueOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.runQueueOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_currentOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.currentOnCore c = st.scheduler.currentOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.currentOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_replenishQueueOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.replenishQueueOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFor_releaseSlots (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    (markKeyChangeFor st tid k).scheduler.releaseSlots = st.scheduler.releaseSlots :=
  markKeyChangeFor_extract_frame (fun s => s.scheduler.releaseSlots) st tid k
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_releaseSlots (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).scheduler.releaseSlots = st.scheduler.releaseSlots :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.releaseSlots) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_activeDomainOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.activeDomainOnCore c
      = st.scheduler.activeDomainOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.activeDomainOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_domainTimeRemainingOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.domainTimeRemainingOnCore c
      = st.scheduler.domainTimeRemainingOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.domainTimeRemainingOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_domainScheduleIndexOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.domainScheduleIndexOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_lastTimeoutErrorsOnCore (pre st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) :
    (markKeyChangeFrom pre st tid).scheduler.lastTimeoutErrorsOnCore c
      = st.scheduler.lastTimeoutErrorsOnCore c :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.lastTimeoutErrorsOnCore c) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_domainSchedule (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).scheduler.domainSchedule = st.scheduler.domainSchedule :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.domainSchedule) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_configDefaultTimeSlice (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    (markKeyChangeFrom pre st tid).scheduler.configDefaultTimeSlice = st.scheduler.configDefaultTimeSlice :=
  markKeyChangeFrom_extract_frame (fun s => s.scheduler.configDefaultTimeSlice) pre st tid
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markKeyChangeFrom_runnableOnSomeCore (pre st : SystemState)
    (tid tid' : SeLe4n.ThreadId) :
    runnableOnSomeCore (markKeyChangeFrom pre st tid) tid' = runnableOnSomeCore st tid' := by
  unfold runnableOnSomeCore
  simp only [markKeyChangeFrom_queuedOn]

@[simp] theorem markKeyChangeFrom_placedCoreOf? (pre st : SystemState)
    (tid tid' : SeLe4n.ThreadId) :
    placedCoreOf? (markKeyChangeFrom pre st tid) tid' = placedCoreOf? st tid' := by
  unfold placedCoreOf?
  simp only [markKeyChangeFrom_queuedOn, markKeyChangeFrom_currentOnCore]

@[simp] theorem markKeyChangeFrom_getObject? (pre st : SystemState) (tid : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) :
    (markKeyChangeFrom pre st tid).getObject? oid = st.getObject? oid := by
  unfold SystemState.getObject?; rw [markKeyChangeFrom_objects]

@[simp] theorem markKeyChangeFrom_getReply? (pre st : SystemState) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    (markKeyChangeFrom pre st tid).getReply? rid = st.getReply? rid := by
  unfold SystemState.getReply?; rw [markKeyChangeFrom_objects]

/-! ### Frames: the candidacy hook writes flags and nothing else -/

@[simp] theorem markCandidacyGainFor_objectIndex (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).objectIndex = st.objectIndex :=
  markCandidacyGainFor_extract_frame (fun s => s.objectIndex) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_cdt (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).cdt = st.cdt :=
  markCandidacyGainFor_extract_frame (fun s => s.cdt) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_irqHandlers (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).irqHandlers = st.irqHandlers :=
  markCandidacyGainFor_extract_frame (fun s => s.irqHandlers) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_tlbShootdown (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).tlbShootdown = st.tlbShootdown :=
  markCandidacyGainFor_extract_frame (fun s => s.tlbShootdown) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_perCoreTlb (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).perCoreTlb = st.perCoreTlb :=
  markCandidacyGainFor_extract_frame (fun s => s.perCoreTlb) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_perCoreICache (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).perCoreICache = st.perCoreICache :=
  markCandidacyGainFor_extract_frame (fun s => s.perCoreICache) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_pendingIcacheMaintenance (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).pendingIcacheMaintenance = st.pendingIcacheMaintenance :=
  markCandidacyGainFor_extract_frame (fun s => s.pendingIcacheMaintenance) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_pendingPhysicalWrites (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).pendingPhysicalWrites = st.pendingPhysicalWrites :=
  markCandidacyGainFor_extract_frame (fun s => s.pendingPhysicalWrites) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_objectIndexSet (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).objectIndexSet = st.objectIndexSet :=
  markCandidacyGainFor_extract_frame (fun s => s.objectIndexSet) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_lifecycle (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).lifecycle = st.lifecycle :=
  markCandidacyGainFor_extract_frame (fun s => s.lifecycle) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_asidTable (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).asidTable = st.asidTable :=
  markCandidacyGainFor_extract_frame (fun s => s.asidTable) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_interfaceRegistry (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).interfaceRegistry = st.interfaceRegistry :=
  markCandidacyGainFor_extract_frame (fun s => s.interfaceRegistry) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_tlb (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).tlb = st.tlb :=
  markCandidacyGainFor_extract_frame (fun s => s.tlb) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_declassificationAuditLog (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).declassificationAuditLog = st.declassificationAuditLog :=
  markCandidacyGainFor_extract_frame (fun s => s.declassificationAuditLog) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_declassificationAuditEpoch (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).declassificationAuditEpoch = st.declassificationAuditEpoch :=
  markCandidacyGainFor_extract_frame (fun s => s.declassificationAuditEpoch) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_declassificationRefusals (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).declassificationRefusals = st.declassificationRefusals :=
  markCandidacyGainFor_extract_frame (fun s => s.declassificationRefusals) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_declassificationTaint (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).declassificationTaint = st.declassificationTaint :=
  markCandidacyGainFor_extract_frame (fun s => s.declassificationTaint) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_getSchedContext? (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool)
    (scId : SeLe4n.SchedContextId) :
    (markCandidacyGainFor st tid b).getSchedContext? scId = st.getSchedContext? scId := by
  unfold SystemState.getSchedContext?; rw [markCandidacyGainFor_objects]

@[simp] theorem markCandidacyGainFor_runQueueOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) (c : CoreId) :
    (markCandidacyGainFor st tid b).scheduler.runQueueOnCore c = st.scheduler.runQueueOnCore c :=
  markCandidacyGainFor_extract_frame (fun s => s.scheduler.runQueueOnCore c) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_replenishQueueOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) (c : CoreId) :
    (markCandidacyGainFor st tid b).scheduler.replenishQueueOnCore c
      = st.scheduler.replenishQueueOnCore c :=
  markCandidacyGainFor_extract_frame (fun s => s.scheduler.replenishQueueOnCore c) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_activeDomainOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) (c : CoreId) :
    (markCandidacyGainFor st tid b).scheduler.activeDomainOnCore c
      = st.scheduler.activeDomainOnCore c :=
  markCandidacyGainFor_extract_frame (fun s => s.scheduler.activeDomainOnCore c) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_domainTimeRemainingOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) (c : CoreId) :
    (markCandidacyGainFor st tid b).scheduler.domainTimeRemainingOnCore c
      = st.scheduler.domainTimeRemainingOnCore c :=
  markCandidacyGainFor_extract_frame (fun s => s.scheduler.domainTimeRemainingOnCore c) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_domainScheduleIndexOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) (c : CoreId) :
    (markCandidacyGainFor st tid b).scheduler.domainScheduleIndexOnCore c
      = st.scheduler.domainScheduleIndexOnCore c :=
  markCandidacyGainFor_extract_frame (fun s => s.scheduler.domainScheduleIndexOnCore c) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_lastTimeoutErrorsOnCore (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) (c : CoreId) :
    (markCandidacyGainFor st tid b).scheduler.lastTimeoutErrorsOnCore c
      = st.scheduler.lastTimeoutErrorsOnCore c :=
  markCandidacyGainFor_extract_frame (fun s => s.scheduler.lastTimeoutErrorsOnCore c) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_domainSchedule (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).scheduler.domainSchedule = st.scheduler.domainSchedule :=
  markCandidacyGainFor_extract_frame (fun s => s.scheduler.domainSchedule) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_configDefaultTimeSlice (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    (markCandidacyGainFor st tid b).scheduler.configDefaultTimeSlice = st.scheduler.configDefaultTimeSlice :=
  markCandidacyGainFor_extract_frame (fun s => s.scheduler.configDefaultTimeSlice) st tid b
    (fun _ _ => by first | rfl | simp [SystemState.markReschedulePendingOnCore])

@[simp] theorem markCandidacyGainFor_runnableOnSomeCore (st : SystemState)
    (tid tid' : SeLe4n.ThreadId) (b : Bool) :
    runnableOnSomeCore (markCandidacyGainFor st tid b) tid' = runnableOnSomeCore st tid' := by
  unfold runnableOnSomeCore
  simp only [markCandidacyGainFor_queuedOn]

@[simp] theorem markCandidacyGainFor_placedCoreOf? (st : SystemState)
    (tid tid' : SeLe4n.ThreadId) (b : Bool) :
    placedCoreOf? (markCandidacyGainFor st tid b) tid' = placedCoreOf? st tid' := by
  unfold placedCoreOf?
  simp only [markCandidacyGainFor_queuedOn, markCandidacyGainFor_currentOnCore]

@[simp] theorem markCandidacyGainFor_getObject? (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool)
    (oid : SeLe4n.ObjId) :
    (markCandidacyGainFor st tid b).getObject? oid = st.getObject? oid := by
  unfold SystemState.getObject?; rw [markCandidacyGainFor_objects]

@[simp] theorem markCandidacyGainFor_getReply? (st : SystemState) (tid : SeLe4n.ThreadId) (b : Bool)
    (rid : SeLe4n.ReplyId) :
    (markCandidacyGainFor st tid b).getReply? rid = st.getReply? rid := by
  unfold SystemState.getReply?; rw [markCandidacyGainFor_objects]

/-- The hook writes the scheduler record only: the state after it is the state
before it with the hook's scheduler.  The form a store-chain decomposition
states its final step in, so every non-scheduler reading of the step is
definitional. -/
theorem markKeyChangeFrom_eq_with_scheduler (pre st : SystemState) (tid : SeLe4n.ThreadId) :
    markKeyChangeFrom pre st tid =
      { st with scheduler := (markKeyChangeFrom pre st tid).scheduler } :=
  markKeyChangeFrom_extract_frame
    (fun s => ({ s with scheduler := (markKeyChangeFrom pre st tid).scheduler } : SystemState))
    pre st tid (fun _ _ => rfl)

/-- Two hooks in a row (a binding writer's pair) write the reschedule flags
only: the result is its input with the result's flag vector — the form the
donation and return store chains state their last step in, so every other reading of the step is definitional. -/
theorem markKeyChangeFrom_twice_eq_with (pre X : SystemState) (a b : SeLe4n.ThreadId) :
    markKeyChangeFrom pre (markKeyChangeFrom pre X a) b =
      { X with
          scheduler := { X.scheduler with reschedulePending :=
            (markKeyChangeFrom pre (markKeyChangeFrom pre X a) b).scheduler.reschedulePending }} :=
  let Y := markKeyChangeFrom pre (markKeyChangeFrom pre X a) b
  let f := fun s : SystemState =>
    ({ s with scheduler := { s.scheduler with reschedulePending := Y.scheduler.reschedulePending }} : SystemState)
  (markKeyChangeFrom_extract_frame f pre _ b (fun _ _ => rfl)).trans
    (markKeyChangeFrom_extract_frame f pre X a (fun _ _ => rfl))

/-- An unchanged scheduler is in particular unchanged except for its flags —
the bridge from a whole-scheduler frame to the binding writers' form. -/
theorem schedulerEqExceptReschedule_of_eq {a b : SystemState}
    (h : a.scheduler = b.scheduler) :
    a.scheduler = { b.scheduler with reschedulePending := a.scheduler.reschedulePending } := by
  rw [h]

/-! ### The reschedule flags as run-queue agreement stages (WS-ZA ZA4.5)

Every flag writer here writes the per-core flag word and nothing the agreement
reads (the object store, the queues, their ends). -/

/-- The state a run-queue agreement reads. -/
private def runQueueReading (s : SystemState) :=
  (s.objects, s.scheduler.runQueue, s.scheduler.runQueueEnds, s.scheduler.currentCode,
    s.referenceTables, s.scheduler.releaseSlots, s.machine.residentCode)

private theorem RunQueueStage_of_reading {st st' : SystemState}
    (h : runQueueReading st' = runQueueReading st) : SystemState.RunQueueStage st st' := by
  simp only [runQueueReading, Prod.mk.injEq] at h
  exact SystemState.RunQueueStage.of_frame h.1 h.2.1 h.2.2.1 h.2.2.2.1 h.2.2.2.2.1 h.2.2.2.2.2.1
    h.2.2.2.2.2.2

theorem markReschedulePendingWhere_runQueueStage (st : SystemState) (p : CoreId → Bool)
    (cs : List CoreId) : SystemState.RunQueueStage st (markReschedulePendingWhere st p cs) :=
  RunQueueStage_of_reading
    (markReschedulePendingWhere_extract_frame runQueueReading (fun _ _ => rfl) st p cs)

theorem markKeyChangeFor_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    SystemState.RunQueueStage st (markKeyChangeFor st tid k) :=
  RunQueueStage_of_reading (markKeyChangeFor_extract_frame runQueueReading st tid k (fun _ _ => rfl))

/-- WS-ZA ZA6.4: the key hook writes flags alone: every context and every
release queue is kept. -/
theorem markKeyChangeFor_refillsKeptOff (P : SeLe4n.SchedContextId → Prop) (st : SystemState)
    (tid : SeLe4n.ThreadId) (k : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId) :
    SystemState.RefillsKeptOff P (markKeyChangeFor st tid k) st :=
  .of_releaseSlots (.of_objects_eq (markKeyChangeFor_objects st tid k))
    (markKeyChangeFor_extract_frame (fun s => s.scheduler.releaseSlots) st tid k (fun _ _ => rfl))

theorem markCandidacyGainFor_runQueueStage (st : SystemState) (tid : SeLe4n.ThreadId)
    (b : Bool) : SystemState.RunQueueStage st (markCandidacyGainFor st tid b) :=
  RunQueueStage_of_reading (markCandidacyGainFor_extract_frame runQueueReading st tid b (fun _ _ => rfl))

theorem markKeyChangeFrom_runQueueStage (pre post : SystemState) (tid : SeLe4n.ThreadId) :
    SystemState.RunQueueStage post (markKeyChangeFrom pre post tid) :=
  RunQueueStage_of_reading
    (markKeyChangeFrom_extract_frame runQueueReading pre post tid (fun _ _ => rfl))

end SeLe4n.Kernel
