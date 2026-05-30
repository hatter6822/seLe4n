-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.Selection
import SeLe4n.Kernel.Scheduler.Invariant.PerCore
import SeLe4n.Kernel.Concurrency.Locks.RwLock
import SeLe4n.Kernel.Concurrency.Locks.Kind

/-!
# WS-SM SM5.A — Per-core `chooseThread` (lock-set, independence, completeness)

This module is the SM5.A deliverable of the WS-SM Phase 5 per-core
scheduler (plan `docs/planning/SMP_PER_CORE_SCHEDULER_PLAN.md` §3.1, §5).
The per-core selection function `chooseThreadOnCore` itself lives in the
production module `Scheduler.Operations.Selection` (SM5.A.1), because the
legacy single-core `chooseThread` is now defined to delegate to it
(SM5.A.5).  This module collects the *forward-looking* SM5.A theorems —
the lock-set declaration, the per-core-independence frame, the
idle-fallback completeness theorems, the selection-soundness
(membership) result, and the decidability witnesses — staged until SM5's
per-core scheduler wires `chooseThreadOnCore` into a runtime dispatch
loop.

## What this module proves

* **SM5.A.2** `RunQueueLockId` + the cross-domain `SchedLockId` + the unified
  `chooseThreadOnCoreLockSet` — the per-core run-queue lock identifier (total
  order keyed by `CoreId` + the §4.4 `runQueueLockLevel`) **and** the unified
  cross-domain lock identifier `SchedLockId` (object-domain `LockId` ⊕ run-queue
  `RunQueueLockId`, with the plan §4.4 total order: every object lock precedes
  every run-queue lock — `SchedLockId.object_lt_runQueue`).  The read-only
  footprint of `chooseThreadOnCore c` is now the *complete* two-domain set
  `[(object objStore-table-lock, read), (runQueue c, read)]`: the object-store
  read lock guards the `st.objects.get?` TCB resolutions the selection performs,
  closing the run-queue-only footprint's under-locking gap.
* **SM5.A.3** per-core independence (Theorem 3.1.2): `chooseThreadOnCore_frame`
  + the named `chooseThreadOnCore_perCore_independence` + corollaries — the
  selection on core `c` reads only core `c`'s run-queue and active-domain
  slots; and selection **optimality** (Theorem 3.1.1):
  `chooseThreadOnCore_selects_highest` — no active-domain thread in the
  maximum-priority bucket beats the selection.
* **SM5.A.4** idle-fallback completeness — `chooseThreadOnCore` never errors on
  a well-formed state, returns `none` only when no in-domain runnable thread
  exists, and returns `some` whenever one is present (the foundation SM5.E
  discharges with the per-core idle thread).
* **SM5.A.6** `chooseThreadOnCore_some_mem_runQueueOnCore` (+ the literal
  `chooseThreadOnCore_preserves_wellFormed` anchor) — selection soundness.
* **SM5.A.7** decidability witnesses for the selection result.
* **Budget-aware companion (§6)** — the CBS-budget-aware `chooseThreadEffectiveOnCore`
  (its production def + legacy migration live in `Selection.lean`): per-core
  independence, non-erroring, completeness, selection soundness, and — unique to
  the budget variant — `chooseThreadEffectiveOnCore_selected_has_budget` (a
  dispatched thread genuinely has budget).

Axiom-clean: every theorem depends only on the standard foundational
axioms (`propext` / `Quot.sound` / `Classical.choice`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId allCores)

-- ============================================================================
-- §1  SM5.A.2 — Per-core run-queue lock identifier + chooseThread lock-set
-- ============================================================================

/-- WS-SM SM5.A.2: per-core run-queue lock identifier (plan §3.1 / §3.2's
`LockId.runQueue c`).

The per-core run queue is a `SchedulerState` field (`Vector RunQueue
numCores`), **not** a kernel object, so it is *not* addressed by the SM0.I
object-lock `LockId` hierarchy (which keys on `(LockKind, ObjId)`).  A
run-queue lock is identified purely by its `CoreId`.  Keeping it a distinct
typed identifier — rather than overloading the carefully-pinned 10-level
SM0.I `LockKind` hierarchy (`level_strictMono` / `level_surjective` /
`level_bounded`) with an eleventh "runQueue" kind — both preserves that
pinning and faithfully matches the data model: run queues are per-core,
indexed by `CoreId`, never by `ObjId`. -/
structure RunQueueLockId where
  /-- The core whose run-queue slot this lock guards. -/
  core : CoreId
  deriving DecidableEq, Repr

-- The `chooseThreadOnCore` lock-set footprint (`chooseThreadOnCoreLockSet`)
-- and its theorems are defined in §1b below — after both the `RunQueueLockId`
-- order *and* the unified cross-domain `SchedLockId` order it now ranges over.
-- (Post-audit cross-domain unification: the footprint includes the
-- object-store read lock that the `st.objects.get?` resolutions require, not
-- only the per-core run-queue lock; see §1b.)

namespace RunQueueLockId

/-- WS-SM SM5.A.2 (lock-order, post-audit): the total order on per-core
run-queue locks, keyed by `CoreId` (the underlying `Fin numCores` order).  A
proper lock identifier needs a total order for the deadlock-freedom argument
(acquire in ascending order ⇒ no wait-cycle); this provides it within the
run-queue-lock domain.

The full SM3 integration — folding object `LockId`s and run-queue locks into a
single `withLockSet` acquisition sequence with the *cross-domain* order of plan
§4.4 ("TCB object-locks at level 3 are always acquired before any run-queue
lock") — is SM5.B work, where the first mixed object+run-queue lock-set
appears (`switchToThreadOnCore`).  This intra-domain order plus
`runQueueLockLevel` are the SM5.A foundation SM5.B consumes; keeping them a
self-contained typed order (rather than overloading the pinned SM0.I 10-level
`LockKind` hierarchy) is the maintainer-chosen "order + defer to SM5.B"
disposition. -/
protected def le (l₁ l₂ : RunQueueLockId) : Prop := l₁.core ≤ l₂.core

/-- WS-SM SM5.A.2: strict order on run-queue locks. -/
protected def lt (l₁ l₂ : RunQueueLockId) : Prop := l₁.core < l₂.core

instance : LE RunQueueLockId := ⟨RunQueueLockId.le⟩
instance : LT RunQueueLockId := ⟨RunQueueLockId.lt⟩

instance (a b : RunQueueLockId) : Decidable (a ≤ b) :=
  inferInstanceAs (Decidable (a.core ≤ b.core))
instance (a b : RunQueueLockId) : Decidable (a < b) :=
  inferInstanceAs (Decidable (a.core < b.core))

/-- SM5.A.2: reflexivity. -/
theorem le_refl (l : RunQueueLockId) : l ≤ l := Nat.le_refl l.core.val

/-- SM5.A.2: transitivity. -/
theorem le_trans {a b c : RunQueueLockId} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c :=
  Nat.le_trans (show a.core.val ≤ b.core.val from h₁) (show b.core.val ≤ c.core.val from h₂)

/-- SM5.A.2: antisymmetry (the `core` field determines the lock). -/
theorem le_antisymm {a b : RunQueueLockId} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  have hcore : a.core = b.core :=
    Fin.ext (Nat.le_antisymm (show a.core.val ≤ b.core.val from h₁)
      (show b.core.val ≤ a.core.val from h₂))
  cases a; cases b; simp_all

/-- SM5.A.2: totality — any two run-queue locks are comparable. -/
theorem le_total (a b : RunQueueLockId) : a ≤ b ∨ b ≤ a := Nat.le_total a.core.val b.core.val

/-- SM5.A.2: strict-order irreflexivity. -/
theorem lt_irrefl (l : RunQueueLockId) : ¬ l < l := Nat.lt_irrefl l.core.val

/-- SM5.A.2: strict-order asymmetry (the lock-ladder property the
deadlock-freedom argument rests on). -/
theorem lt_asymm {a b : RunQueueLockId} (h : a < b) : ¬ b < a :=
  Nat.lt_asymm (show a.core.val < b.core.val from h)

/-- WS-SM SM5.A.2 (plan §4.4 lock-order level): run-queue locks sit *after*
every SM0.I object-lock level (`objStore`=0 .. `page`=9), hence `10`.  This
encodes "object locks before run-queue locks": every object-lock level (≤ 9)
is strictly below `runQueueLockLevel`.  The unified cross-domain order built on
top of this level fact is `SchedLockId` (§1b); its runtime acquisition sequence
(`withLockSet`) is SM5.B. -/
def runQueueLockLevel : Nat := 10

/-- SM5.A.2: every SM0.I object-lock level (0..9) is strictly below the
run-queue lock level — the arithmetic foundation under the plan §4.4 "object
locks acquired before run-queue locks" rule.  The order-theoretic form is
`SchedLockId.object_lt_runQueue` (§1b). -/
theorem objectLockLevels_lt_runQueueLockLevel : ∀ n : Nat, n ≤ 9 → n < runQueueLockLevel := by
  intro n hn; unfold runQueueLockLevel; omega

end RunQueueLockId

-- ============================================================================
-- §1b  SM5.A.2 (cross-domain unification, plan §4.4) — SchedLockId + the
--      complete `chooseThreadOnCore` footprint (object-store + run-queue locks)
-- ============================================================================

/-- WS-SM SM5.A.2 (cross-domain unification): the canonical object-store
*table* lock, as an SM0.I `LockId`.  `chooseThreadOnCore` resolves every
runnable thread's priority / deadline / domain through `st.objects.get?`
(threaded into `chooseBestInBucket`), so the selection reads the RobinHood
object store.  Per SM3.A.10 that table is guarded by the single table-level
lock at the top of the SM0.I hierarchy (`LockKind.objStore`, level 0); a
`.objStore` `LockId` routes to `SystemState.objStoreLock` regardless of its
`objId`, so the canonical form carries `ObjId.sentinel`. -/
def schedObjStoreLockId : Concurrency.LockId :=
  ⟨Concurrency.LockKind.objStore, SeLe4n.ObjId.sentinel⟩

/-- WS-SM SM5.A.2 (cross-domain unification, plan §4.4): the unified lock
identifier spanning **both** lock domains the per-core scheduler touches — the
SM0.I object-lock domain (`LockId`, kind levels 0..9) and the per-core
run-queue domain (`RunQueueLockId`).  A single `withLockSet` acquisition
sequence must order locks drawn from both domains; `SchedLockId` is that
common order.

Keeping the two domains as constructors of one sum — rather than adding an
eleventh "runQueue" kind to the carefully-pinned 10-level SM0.I `LockKind`
hierarchy (`level_surjective` / `level_bounded`) — preserves that pinning while
giving the cross-domain total order plan §4.4 requires: **every object-domain
lock is acquired before every run-queue lock** (`object_lt_runQueue`). -/
inductive SchedLockId where
  /-- An SM0.I object-domain lock (the `objStore` table lock, a per-object TCB
  lock, …) keyed by `(LockKind, ObjId)`. -/
  | object (l : Concurrency.LockId)
  /-- A per-core run-queue lock. -/
  | runQueue (r : RunQueueLockId)
  deriving DecidableEq, Repr

namespace SchedLockId

/-- WS-SM SM5.A.2: the unified cross-domain order.  Object-domain locks compare
by the SM0.I `LockId` lex order; run-queue locks by `CoreId`; and **every**
object lock precedes **every** run-queue lock (plan §4.4 — object levels 0..9
acquired before the notional run-queue level 10). -/
protected def le : SchedLockId → SchedLockId → Prop
  | .object l₁,   .object l₂   => l₁ ≤ l₂
  | .object _,    .runQueue _  => True
  | .runQueue _,  .object _     => False
  | .runQueue r₁, .runQueue r₂ => r₁.core.val ≤ r₂.core.val

/-- WS-SM SM5.A.2: strict cross-domain order. -/
protected def lt (a b : SchedLockId) : Prop := SchedLockId.le a b ∧ ¬ SchedLockId.le b a

instance decLeAux (a b : SchedLockId) : Decidable (SchedLockId.le a b) := by
  cases a <;> cases b <;> simp only [SchedLockId.le] <;> infer_instance

instance : LE SchedLockId := ⟨SchedLockId.le⟩
instance : LT SchedLockId := ⟨SchedLockId.lt⟩

instance (a b : SchedLockId) : Decidable (a ≤ b) := decLeAux a b
instance (a b : SchedLockId) : Decidable (a < b) :=
  inferInstanceAs (Decidable (SchedLockId.le a b ∧ ¬ SchedLockId.le b a))

/-- SM5.A.2: reflexivity (reuses each domain's reflexivity). -/
protected theorem le_refl (l : SchedLockId) : l ≤ l := by
  cases l with
  | object a => exact Concurrency.LockId.le_refl a
  | runQueue r => exact RunQueueLockId.le_refl r

/-- SM5.A.2: transitivity across both domains (cross-domain edges go
object→runQueue only, so no transitivity violation is possible). -/
protected theorem le_trans {a b c : SchedLockId} (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;>
    first
      | exact Concurrency.LockId.le_trans _ _ _ h₁ h₂
      | exact Nat.le_trans h₁ h₂
      | exact True.intro
      | exact (h₁ : False).elim
      | exact (h₂ : False).elim

/-- SM5.A.2: antisymmetry (the cross-domain edges are strict, so equal-pair
hypotheses force the same domain). -/
protected theorem le_antisymm {a b : SchedLockId} (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  cases a <;> cases b
  · exact congrArg SchedLockId.object (Concurrency.LockId.le_antisymm _ _ h₁ h₂)
  · exact (h₂ : False).elim
  · exact (h₁ : False).elim
  · exact congrArg SchedLockId.runQueue (RunQueueLockId.le_antisymm h₁ h₂)

/-- SM5.A.2: totality — any two locks (same or cross domain) are comparable. -/
protected theorem le_total (a b : SchedLockId) : a ≤ b ∨ b ≤ a := by
  cases a <;> cases b
  · exact Concurrency.LockId.le_total _ _
  · exact Or.inl True.intro
  · exact Or.inr True.intro
  · exact RunQueueLockId.le_total _ _

/-- SM5.A.2: strict-order irreflexivity. -/
protected theorem lt_irrefl (l : SchedLockId) : ¬ l < l := fun h => h.2 h.1

/-- SM5.A.2: strict-order asymmetry (the lock-ladder property the
deadlock-freedom argument rests on). -/
protected theorem lt_asymm {a b : SchedLockId} (h : a < b) : ¬ b < a := fun h' => h.2 h'.1

/-- WS-SM SM5.A.2 (plan §4.4): every object-domain lock is strictly below every
run-queue lock — "object locks acquired before run-queue locks", now a theorem
on the unified order itself rather than only an arithmetic fact about the
levels (`RunQueueLockId.objectLockLevels_lt_runQueueLockLevel`). -/
theorem object_lt_runQueue (l : Concurrency.LockId) (r : RunQueueLockId) :
    SchedLockId.object l < SchedLockId.runQueue r :=
  ⟨True.intro, fun h => h⟩

end SchedLockId

/-- WS-SM SM5.A.2 (cross-domain unification): the **complete** lock-set
footprint of `chooseThreadOnCore c`.

`chooseThreadOnCore c` reads two distinct kinds of state:
* core `c`'s run-queue slot and active-domain slot (the per-core scheduler
  state), and
* the RobinHood **object store** — it resolves every runnable thread's
  priority / deadline / domain through `st.objects.get?` (threaded into
  `chooseBestInBucket`).

The footprint therefore declares a lock from *both* domains, in plan §4.4
ascending order (object-domain lock first):
`[(SchedLockId.object schedObjStoreLockId, .read), (SchedLockId.runQueue ⟨c⟩, .read)]`.

The object-store read lock (`schedObjStoreLockId`, the SM3.A.10 table-level
lock) is what makes the footprint sound under the SM5.B `withLockSet`
integration: holding it read-locked prevents a concurrent retype / delete /
write of a queued TCB from changing the selection (or turning it into
`schedulerInvariantViolation`) while only the run-queue lock is held.  The two
reads `chooseThreadOnCore_frame` identifies — `objects` and (`runQueueOnCore
c`, `activeDomainOnCore c`) — are guarded respectively by the object-store and
run-queue locks.  The cross-domain acquisition *order* is
`chooseThreadOnCoreLockSet_object_before_runQueue`; the *runtime* acquisition
wiring (`withLockSet`) is SM5.B. -/
def chooseThreadOnCoreLockSet (c : CoreId) :
    List (SchedLockId × Concurrency.AccessMode) :=
  [ (SchedLockId.object schedObjStoreLockId, .read)
  , (SchedLockId.runQueue ⟨c⟩, .read) ]

/-- SM5.A.2 (cross-domain): the footprint is the two-lock object-store +
run-queue set. -/
@[simp] theorem chooseThreadOnCoreLockSet_length (c : CoreId) :
    (chooseThreadOnCoreLockSet c).length = 2 := rfl

/-- SM5.A.2: every lock in the `chooseThreadOnCore` footprint is acquired in
**read** mode — the selection is a pure read of both domains. -/
theorem chooseThreadOnCoreLockSet_read_only (c : CoreId) :
    ∀ p ∈ chooseThreadOnCoreLockSet c, p.2 = Concurrency.AccessMode.read := by
  intro p hp
  simp only [chooseThreadOnCoreLockSet, List.mem_cons,
    List.not_mem_nil, or_false] at hp
  rcases hp with h | h <;> subst h <;> rfl

/-- SM5.A.2 (cross-domain — the audit-fix witness): the object-store read lock
is in the footprint, so the `st.objects.get?` TCB resolutions
`chooseThreadOnCore` performs are guarded.  This is the lock the run-queue-only
footprint omitted. -/
theorem chooseThreadOnCoreLockSet_contains_objStore_read (c : CoreId) :
    (SchedLockId.object schedObjStoreLockId, Concurrency.AccessMode.read)
      ∈ chooseThreadOnCoreLockSet c := by
  simp [chooseThreadOnCoreLockSet]

/-- SM5.A.2: the per-core run-queue read lock is in the footprint. -/
theorem chooseThreadOnCoreLockSet_contains_runQueue_read (c : CoreId) :
    (SchedLockId.runQueue ⟨c⟩, Concurrency.AccessMode.read)
      ∈ chooseThreadOnCoreLockSet c := by
  simp [chooseThreadOnCoreLockSet]

/-- SM5.A.2 (plan §4.4): inside the footprint the object-store lock is
acquired *before* the run-queue lock — the cross-domain ascending order. -/
theorem chooseThreadOnCoreLockSet_object_before_runQueue (c : CoreId) :
    SchedLockId.object schedObjStoreLockId
      < SchedLockId.runQueue (⟨c⟩ : RunQueueLockId) :=
  SchedLockId.object_lt_runQueue _ _

/-- SM5.A.2: the footprint's projected keys are duplicate-free — the
object-store lock and the run-queue lock are distinct (different
constructors), mirroring the SM3.B `LockSet.hUniqueKeys` invariant. -/
theorem chooseThreadOnCoreLockSet_keys_nodup (c : CoreId) :
    ((chooseThreadOnCoreLockSet c).map (·.1)).Nodup := by
  simp [chooseThreadOnCoreLockSet]

-- ============================================================================
-- §2  SM5.A.3 — Per-core independence (plan §3.1, Theorem 3.1.2)
-- ============================================================================

/-- WS-SM SM5.A.3 (Theorem 3.1.2, frame form): `chooseThreadOnCore`'s read
footprint on core `c` is exactly `(objects, runQueueOnCore c,
activeDomainOnCore c)`.  Two states that agree on those three reads agree
on the selection.  Everything else about the two states — every *other*
core's run queue / active domain / current thread, the rest of the object
store's shape beyond the lookup function, the machine registers — is
irrelevant to the selection on core `c`.  This is the structural heart of
per-core independence. -/
theorem chooseThreadOnCore_frame (s₁ s₂ : SystemState) (c : CoreId)
    (hObj : s₁.objects = s₂.objects)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c) :
    chooseThreadOnCore s₁ c = chooseThreadOnCore s₂ c := by
  unfold chooseThreadOnCore
  rw [hObj, hRQ, hAD]

/-- WS-SM SM5.A.3 (Theorem 3.1.2): per-core independence under a run-queue
write.  Writing core `c'`'s run-queue slot (for `c' ≠ c`) leaves
`chooseThreadOnCore · c` unchanged — the selection on `c` cannot observe a
sibling core's run queue.  This is the property the SM5.A.2 read-only
lock-set encodes: cores outside the lock-set are not in the read
footprint. -/
theorem chooseThreadOnCore_independent_of_setRunQueueOnCore
    (s : SystemState) (c c' : CoreId) (rq : RunQueue) (h : c ≠ c') :
    chooseThreadOnCore
        { s with scheduler := s.scheduler.setRunQueueOnCore c' rq } c
      = chooseThreadOnCore s c := by
  apply chooseThreadOnCore_frame
  · rfl
  · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne s.scheduler c' c rq (Ne.symm h)
  · exact SchedulerState.setRunQueueOnCore_activeDomainOnCore s.scheduler c' c rq

/-- WS-SM SM5.A.3: per-core independence under an active-domain write.
Writing core `c'`'s active-domain slot (for `c' ≠ c`) leaves
`chooseThreadOnCore · c` unchanged. -/
theorem chooseThreadOnCore_independent_of_setActiveDomainOnCore
    (s : SystemState) (c c' : CoreId) (d : SeLe4n.DomainId) (h : c ≠ c') :
    chooseThreadOnCore
        { s with scheduler := s.scheduler.setActiveDomainOnCore c' d } c
      = chooseThreadOnCore s c := by
  apply chooseThreadOnCore_frame
  · rfl
  · exact SchedulerState.setActiveDomainOnCore_runQueueOnCore s.scheduler c' c d
  · exact SchedulerState.setActiveDomainOnCore_activeDomainOnCore_ne s.scheduler c' c d (Ne.symm h)

/-- WS-SM SM5.A.3: `chooseThreadOnCore` does **not** read the `current`
slot at all — so a write to *any* core's current thread (including core
`c`'s own) leaves the selection unchanged.  Selection reads the run queue
and active domain; the current thread is set as a *consequence* of
selection (`switchToThreadOnCore`, SM5.B), never an input to it. -/
theorem chooseThreadOnCore_independent_of_setCurrentOnCore
    (s : SystemState) (c c' : CoreId) (v : Option SeLe4n.ThreadId) :
    chooseThreadOnCore
        { s with scheduler := s.scheduler.setCurrentOnCore c' v } c
      = chooseThreadOnCore s c := by
  apply chooseThreadOnCore_frame
  · rfl
  · exact SchedulerState.setCurrentOnCore_runQueueOnCore s.scheduler c' c v
  · exact SchedulerState.setCurrentOnCore_activeDomainOnCore s.scheduler c' c v

/-- WS-SM SM5.A.3 / SM5.A.2 bridge: a run-queue write on a core whose
run-queue lock is *not* a key of `chooseThreadOnCoreLockSet c` (equivalently,
any `c' ≠ c`) leaves the selection unchanged.  This connects the SM5.A.2
unified footprint to the SM5.A.3 independence result: the only run-queue lock
the footprint declares is `c`'s own, and that is precisely the run queue the
selection depends on.  (The footprint's *other* key — the object-store read
lock — guards the orthogonal `st.objects` read footprint, so it does not
appear in this run-queue-write statement.) -/
theorem chooseThreadOnCore_independent_of_write_off_lockSet
    (s : SystemState) (c c' : CoreId) (rq : RunQueue)
    (h : SchedLockId.runQueue (⟨c'⟩ : RunQueueLockId)
          ∉ (chooseThreadOnCoreLockSet c).map (·.1)) :
    chooseThreadOnCore
        { s with scheduler := s.scheduler.setRunQueueOnCore c' rq } c
      = chooseThreadOnCore s c := by
  have hne : c ≠ c' := by
    intro heq
    subst heq
    apply h
    simp [chooseThreadOnCoreLockSet]
  exact chooseThreadOnCore_independent_of_setRunQueueOnCore s c c' rq hne

/-- WS-SM SM5.A.3 (plan §3.1.2, the named `chooseThreadOnCore_perCore_independence`
form): the selection on core `c₁` does **not** depend on a distinct core
`c₂`'s run queue.  This is the plan's canonical statement of per-core
independence; it is exactly the run-queue-write corollary above, restated with
the plan's `c₁ ≠ c₂` variable naming for traceability. -/
theorem chooseThreadOnCore_perCore_independence
    (s : SystemState) (c₁ c₂ : CoreId) (h : c₁ ≠ c₂) (rq : RunQueue) :
    chooseThreadOnCore { s with scheduler := s.scheduler.setRunQueueOnCore c₂ rq } c₁
      = chooseThreadOnCore s c₁ :=
  chooseThreadOnCore_independent_of_setRunQueueOnCore s c₁ c₂ rq h

-- ============================================================================
-- §3  SM5.A.4 — Idle-fallback completeness (plan §3.5, Theorem 3.5.2)
-- ============================================================================
--
-- The completeness results rest on three structural facts about the
-- bucket-scan fold `chooseBestRunnableBy`, proved by induction on the
-- scanned list:
--
--   * once a candidate is recorded (`best = some _`) the scan never
--     "forgets" it (`_some_ne_ok_none`);
--   * a scan that finds nothing (`= .ok none`) means every scanned TCB was
--     ineligible (`_none_no_eligible`);
--   * a scan over a list of genuine TCBs never errors (`_ok_of_allTcb`).
--
-- These lift through `chooseBestInBucket` (max-bucket scan then full-list
-- fallback) to `chooseThreadOnCore`.

/-- SM5.A.4 helper: once the fold has recorded a candidate (`best = some
x`), it can never return `.ok none` — the recorded candidate is only ever
replaced by another `some`, never dropped.  (It may still `.error` if a
later list entry fails to resolve to a TCB.) -/
private theorem chooseBestRunnableBy_some_ne_ok_none
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (x : SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline),
      chooseBestRunnableBy objects eligible list (some x) ≠ .ok none := by
  intro list
  induction list with
  | nil => intro x h; simp [chooseBestRunnableBy] at h
  | cons hd tl ih =>
    intro x h
    obtain ⟨xt, xp, xd⟩ := x
    unfold chooseBestRunnableBy at h
    cases hObj : objects hd.toObjId with
    | none => rw [hObj] at h; simp at h
    | some obj =>
      cases obj with
      | tcb tcb =>
        rw [hObj] at h
        by_cases hElig : eligible tcb
        · by_cases hBetter : isBetterCandidate xp xd tcb.priority tcb.deadline
          · simp only [hElig, hBetter, if_true] at h; exact ih _ h
          · simp only [hElig, hBetter, if_true] at h; exact ih _ h
        · simp only [hElig] at h; exact ih _ h
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ => rw [hObj] at h; simp at h

/-- SM5.A.4 helper: a fold starting from `none` that returns `.ok none`
witnesses that **every** scanned TCB was ineligible.  (A non-TCB entry
would have produced `.error`, and an eligible TCB would have produced
`.ok (some _)` by `_some_ne_ok_none`.) -/
theorem chooseBestRunnableBy_none_no_eligible
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId),
      chooseBestRunnableBy objects eligible list none = .ok none →
      ∀ tid ∈ list, ∀ tcb : TCB,
        objects tid.toObjId = some (.tcb tcb) → eligible tcb = false := by
  intro list
  induction list with
  | nil => intro _ tid hmem; simp at hmem
  | cons hd tl ih =>
    intro h tid hmem tcb hObjTid
    have hHdReduce := h
    unfold chooseBestRunnableBy at hHdReduce
    rcases List.mem_cons.mp hmem with hEq | hMemTl
    · -- tid = hd: the recorded best would be `some` if eligible, so eligible = false
      subst hEq
      rw [hObjTid] at hHdReduce
      by_cases hElig : eligible tcb
      · exfalso
        simp only [hElig, if_true] at hHdReduce
        exact chooseBestRunnableBy_some_ne_ok_none objects eligible tl _ hHdReduce
      · exact eq_false_of_ne_true (by simpa using hElig)
    · -- tid ∈ tl: peel hd off and apply the induction hypothesis
      cases hHdObj : objects hd.toObjId with
      | none => rw [hHdObj] at hHdReduce; simp at hHdReduce
      | some obj =>
        cases obj with
        | tcb hdTcb =>
          rw [hHdObj] at hHdReduce
          by_cases hHdElig : eligible hdTcb
          · exfalso
            simp only [hHdElig, if_true] at hHdReduce
            exact chooseBestRunnableBy_some_ne_ok_none objects eligible tl _ hHdReduce
          · simp only [hHdElig] at hHdReduce
            exact ih hHdReduce tid hMemTl tcb hObjTid
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
        | schedContext _ => rw [hHdObj] at hHdReduce; simp at hHdReduce

/-- SM5.A.4 helper: a fold over a list whose every entry resolves to a TCB
never errors — it returns `.ok _`.  This is the "no `schedulerInvariant`
violation under a well-formed run queue" property the idle-fallback
completeness rests on. -/
theorem chooseBestRunnableBy_ok_of_allTcb
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)),
      (∀ t ∈ list, ∃ tcb : TCB, objects t.toObjId = some (.tcb tcb)) →
      ∃ r, chooseBestRunnableBy objects eligible list best = .ok r := by
  intro list
  induction list with
  | nil => intro best _; exact ⟨best, rfl⟩
  | cons hd tl ih =>
    intro best hAll
    obtain ⟨hdTcb, hHdObj⟩ := hAll hd (List.mem_cons_self ..)
    have hAllTl : ∀ t ∈ tl, ∃ tcb : TCB, objects t.toObjId = some (.tcb tcb) :=
      fun t ht => hAll t (List.mem_cons_of_mem _ ht)
    unfold chooseBestRunnableBy
    rw [hHdObj]
    exact ih _ hAllTl

/-- SM5.A.4 helper: the result of a fold (from any `best`) over a list of
genuine TCBs whose recorded candidate is `some (rt, _, _)` has `rt ∈ list`
or `rt` was already the recorded `best`.  Specialised to `best = none`
below to give selection soundness. -/
private theorem chooseBestRunnableBy_result_mem_aux
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
      (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline),
      chooseBestRunnableBy objects eligible list best = .ok (some (rt, rp, rd)) →
      rt ∈ list ∨ (∃ p d, best = some (rt, p, d)) := by
  intro list
  induction list with
  | nil =>
    intro best rt rp rd h
    simp only [chooseBestRunnableBy] at h
    exact Or.inr ⟨rp, rd, by rw [Except.ok.injEq] at h; rw [h]⟩
  | cons hd tl ih =>
    intro best rt rp rd h
    unfold chooseBestRunnableBy at h
    cases hObj : objects hd.toObjId with
    | none => rw [hObj] at h; simp at h
    | some obj =>
      cases obj with
      | tcb tcb =>
        rw [hObj] at h
        -- the fold continues on `tl` with an updated `best'`; analyse cases
        by_cases hElig : eligible tcb
        · cases best with
          | none =>
            simp only [hElig, if_true] at h
            rcases ih _ rt rp rd h with hTl | ⟨p, d, hb⟩
            · exact Or.inl (List.mem_cons_of_mem _ hTl)
            · simp only [Option.some.injEq, Prod.mk.injEq] at hb
              exact Or.inl (List.mem_cons.mpr (Or.inl hb.1.symm))
          | some y =>
            obtain ⟨yt, yp, yd⟩ := y
            by_cases hBetter : isBetterCandidate yp yd tcb.priority tcb.deadline
            · simp only [hElig, hBetter, if_true] at h
              rcases ih _ rt rp rd h with hTl | ⟨p, d, hb⟩
              · exact Or.inl (List.mem_cons_of_mem _ hTl)
              · simp only [Option.some.injEq, Prod.mk.injEq] at hb
                exact Or.inl (List.mem_cons.mpr (Or.inl hb.1.symm))
            · simp only [hElig, hBetter, if_true] at h
              rcases ih _ rt rp rd h with hTl | ⟨p, d, hb⟩
              · exact Or.inl (List.mem_cons_of_mem _ hTl)
              · exact Or.inr ⟨p, d, hb⟩
        · simp only [hElig] at h
          rcases ih _ rt rp rd h with hTl | hb
          · exact Or.inl (List.mem_cons_of_mem _ hTl)
          · exact Or.inr hb
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ => rw [hObj] at h; simp at h

/-- SM5.A.4 / SM5.A.6 helper: selection soundness for a `none`-seeded
fold — a recorded candidate is a member of the scanned list. -/
theorem chooseBestRunnableBy_result_mem
    (objects : SeLe4n.ObjId → Option KernelObject) (eligible : TCB → Bool)
    (list : List SeLe4n.ThreadId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (h : chooseBestRunnableBy objects eligible list none = .ok (some (rt, rp, rd))) :
    rt ∈ list := by
  rcases chooseBestRunnableBy_result_mem_aux objects eligible list none rt rp rd h with
    hMem | ⟨_, _, hb⟩
  · exact hMem
  · exact absurd hb (by simp)

-- ── Bridges through `chooseBestInBucket` (max-bucket scan + full-list
--    fallback) and the `chooseThreadOnCore` wrapper. ──

/-- SM5.A.4 helper: a `.ok none` from the bucket-first selector forces the
full-list fallback scan to also be `.ok none` (the max-bucket scan must
have been `.ok none` to reach the fallback). -/
theorem chooseBestInBucket_none_imp_toList_none
    (objects : SeLe4n.ObjId → Option KernelObject) (rq : RunQueue)
    (ad : SeLe4n.DomainId)
    (h : chooseBestInBucket objects rq ad = .ok none) :
    chooseBestRunnableInDomain objects rq.toList ad none = .ok none := by
  rw [bucketFirst_fullScan_equivalence] at h
  cases hMax : chooseBestRunnableInDomain objects rq.maxPriorityBucket ad none with
  | error e => rw [hMax] at h; simp at h
  | ok val =>
    cases val with
    | some r => rw [hMax] at h; simp at h
    | none => rw [hMax] at h; simpa using h

/-- SM5.A.4 helper: a bucket-first scan over a well-formed run queue whose
every member resolves to a TCB never errors.  The max-priority bucket is a
subset of the run queue (by well-formedness), so its members are also TCBs;
both the bucket scan and the full-list fallback therefore succeed. -/
theorem chooseBestInBucket_ok_of_allTcb
    (objects : SeLe4n.ObjId → Option KernelObject) (rq : RunQueue)
    (ad : SeLe4n.DomainId)
    (hwf : rq.wellFormed)
    (hAll : ∀ t ∈ rq.toList, ∃ tcb : TCB, objects t.toObjId = some (.tcb tcb)) :
    ∃ val, chooseBestInBucket objects rq ad = .ok val := by
  have hMaxAll : ∀ t ∈ rq.maxPriorityBucket, ∃ tcb : TCB,
      objects t.toObjId = some (.tcb tcb) := by
    intro t ht
    exact hAll t (RunQueue.membership_implies_flat rq t
      (RunQueue.maxPriorityBucket_subset rq hwf t ht))
  obtain ⟨maxVal, hMax⟩ :
      ∃ r, chooseBestRunnableInDomain objects rq.maxPriorityBucket ad none = .ok r :=
    chooseBestRunnableBy_ok_of_allTcb objects (fun tcb => tcb.domain == ad)
      rq.maxPriorityBucket none hMaxAll
  rw [bucketFirst_fullScan_equivalence, hMax]
  cases maxVal with
  | some r => exact ⟨some r, rfl⟩
  | none =>
    exact chooseBestRunnableBy_ok_of_allTcb objects (fun tcb => tcb.domain == ad)
      rq.toList none hAll

/-- SM5.A.6 helper: a selected candidate from the bucket-first scan over a
well-formed all-TCB run queue is a genuine member of the run queue's flat
list. -/
theorem chooseBestInBucket_result_mem
    (objects : SeLe4n.ObjId → Option KernelObject) (rq : RunQueue)
    (ad : SeLe4n.DomainId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (hwf : rq.wellFormed)
    (h : chooseBestInBucket objects rq ad = .ok (some (rt, rp, rd))) :
    rt ∈ rq.toList := by
  rw [bucketFirst_fullScan_equivalence] at h
  cases hMax : chooseBestRunnableInDomain objects rq.maxPriorityBucket ad none with
  | error e => rw [hMax] at h; simp at h
  | ok val =>
    cases val with
    | some r =>
      rw [hMax] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      have hrtMem : rt ∈ rq.maxPriorityBucket :=
        chooseBestRunnableBy_result_mem objects (fun tcb => tcb.domain == ad)
          rq.maxPriorityBucket rt rp rd hMax
      exact RunQueue.membership_implies_flat rq rt
        (RunQueue.maxPriorityBucket_subset rq hwf rt hrtMem)
    | none =>
      rw [hMax] at h
      exact chooseBestRunnableBy_result_mem objects (fun tcb => tcb.domain == ad)
        rq.toList rt rp rd h

/-- SM5.A.4 helper: `chooseThreadOnCore = .ok none` forces the underlying
bucket-first scan to be `.ok none`. -/
theorem chooseThreadOnCore_eq_none_imp_bucket_none
    (st : SystemState) (c : CoreId) (h : chooseThreadOnCore st c = .ok none) :
    chooseBestInBucket st.objects.get? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok none := by
  unfold chooseThreadOnCore at h
  cases hB : chooseBestInBucket st.objects.get? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) with
  | error e => rw [hB] at h; simp at h
  | ok val =>
    cases val with
    | none => rfl
    | some triple => obtain ⟨tid, p, d⟩ := triple; rw [hB] at h; simp at h

/-- SM5.A.6 helper: `chooseThreadOnCore = .ok (some tid)` exposes the
selected `(tid, priority, deadline)` triple from the bucket-first scan. -/
theorem chooseThreadOnCore_eq_some_imp_bucket_some
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    ∃ p d, chooseBestInBucket st.objects.get? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok (some (tid, p, d)) := by
  unfold chooseThreadOnCore at h
  cases hB : chooseBestInBucket st.objects.get? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) with
  | error e => rw [hB] at h; simp at h
  | ok val =>
    cases val with
    | none => rw [hB] at h; simp at h
    | some triple =>
      obtain ⟨t, tp, td⟩ := triple
      rw [hB] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      exact ⟨tp, td, rfl⟩

/-- SM5.A.4 helper: a `.ok` from the bucket-first scan lifts to a `.ok`
from `chooseThreadOnCore` (the wrapper only renames `some (tid, _, _)` to
`some tid`). -/
theorem chooseThreadOnCore_ok_of_bucket_ok
    (st : SystemState) (c : CoreId)
    (val : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (h : chooseBestInBucket st.objects.get? (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok val) :
    ∃ r, chooseThreadOnCore st c = .ok r := by
  unfold chooseThreadOnCore
  rw [h]
  cases val with
  | none => exact ⟨none, rfl⟩
  | some triple => obtain ⟨tid, p, d⟩ := triple; exact ⟨some tid, rfl⟩

/-- SM5.A.4 / SM5.A.6 helper: bridge `runnableThreadsAreTCBsOnCore` (stated
with the typed `getTcb?` accessor) to the raw `objects.get?` form the
selection fold consumes.  The two are definitionally connected through
`getTcb?_eq_some_iff` plus `RHTable[k]? = RHTable.get? k`. -/
private theorem runnableThreadsAreTCBs_objects_get?
    (st : SystemState) (c : CoreId) (hRunnable : runnableThreadsAreTCBsOnCore st c) :
    ∀ t ∈ (st.scheduler.runQueueOnCore c).toList,
      ∃ tcb : TCB, st.objects.get? t.toObjId = some (.tcb tcb) := by
  intro t ht
  obtain ⟨tcb, htcb⟩ := hRunnable t ht
  exact ⟨tcb, (SystemState.getTcb?_eq_some_iff st t tcb).mp htcb⟩

-- ── Public SM5.A.4 theorems: completeness / idle-fallback. ──

/-- WS-SM SM5.A.4: `chooseThreadOnCore` never errors on a well-formed run
queue whose every member resolves to a TCB.  The `.error` branch
(`schedulerInvariantViolation`, signalling a corrupted run queue) is
unreachable under the per-core scheduler invariant — so on any valid state
the selection returns either `.ok none` (no eligible thread → fall back to
idle) or `.ok (some tid)`.  This is the "the selection is total on valid
states" half of idle-fallback completeness. -/
theorem chooseThreadOnCore_ok_of_runnableTCBs
    (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c) :
    ∃ r, chooseThreadOnCore st c = .ok r := by
  obtain ⟨val, hbucket⟩ := chooseBestInBucket_ok_of_allTcb st.objects.get?
    (st.scheduler.runQueueOnCore c) (st.scheduler.activeDomainOnCore c) hwf
    (runnableThreadsAreTCBs_objects_get? st c hRunnable)
  exact chooseThreadOnCore_ok_of_bucket_ok st c val hbucket

/-- WS-SM SM5.A.4: completeness of selection — `chooseThreadOnCore` returns
the idle-fallback signal `.ok none` **only** when there is genuinely no
runnable thread of core `c`'s active domain in its run queue.  Equivalently:
every run-queue member is outside the active domain.  This is what makes the
idle fallback *complete* — the scheduler runs the idle thread exactly when
no domain-eligible thread is available, never dropping a runnable one. -/
theorem chooseThreadOnCore_none_no_eligible
    (st : SystemState) (c : CoreId)
    (h : chooseThreadOnCore st c = .ok none) :
    ∀ tid ∈ (st.scheduler.runQueueOnCore c).toList, ∀ tcb : TCB,
      st.getTcb? tid = some tcb →
      tcb.domain ≠ st.scheduler.activeDomainOnCore c := by
  intro tid hmem tcb htcb
  have hbucket := chooseThreadOnCore_eq_none_imp_bucket_none st c h
  have htoList := chooseBestInBucket_none_imp_toList_none st.objects.get?
    (st.scheduler.runQueueOnCore c) (st.scheduler.activeDomainOnCore c) hbucket
  have hObjGet : st.objects.get? tid.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp htcb
  have hElig := chooseBestRunnableBy_none_no_eligible st.objects.get?
    (fun t => t.domain == st.scheduler.activeDomainOnCore c)
    (st.scheduler.runQueueOnCore c).toList htoList tid hmem tcb hObjGet
  simpa using hElig

/-- WS-SM SM5.A.4 (idle-fallback completeness, plan §3.5.2 foundation): when
core `c`'s run queue holds a runnable thread in its active domain, the
selection succeeds with `some`.  This is the conditional form SM5.E
discharges by supplying the per-core idle thread as the always-present
in-domain candidate, yielding the unconditional
`chooseThreadOnCore_always_succeeds`. -/
theorem chooseThreadOnCore_some_of_eligible
    (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (tid₀ : SeLe4n.ThreadId) (tcb₀ : TCB)
    (hMem : tid₀ ∈ (st.scheduler.runQueueOnCore c).toList)
    (hTcb : st.getTcb? tid₀ = some tcb₀)
    (hDom : tcb₀.domain = st.scheduler.activeDomainOnCore c) :
    ∃ tid, chooseThreadOnCore st c = .ok (some tid) := by
  obtain ⟨r, hr⟩ := chooseThreadOnCore_ok_of_runnableTCBs st c hwf hRunnable
  cases r with
  | some tid => exact ⟨tid, hr⟩
  | none =>
    exact absurd hDom (chooseThreadOnCore_none_no_eligible st c hr tid₀ hMem tcb₀ hTcb)

-- ── Public SM5.A.6 theorems: selection soundness + preservation. ──

/-- WS-SM SM5.A.6 (selection soundness): a thread chosen by
`chooseThreadOnCore` is a genuine member of core `c`'s run queue.  This is
the substantive "preserves well-formedness" content for a read-only
selection: the choice respects the run queue's structure — it never invents
a thread, so the run queue's membership invariant is honoured downstream
(e.g. by `switchToThreadOnCore`'s dequeue in SM5.B). -/
theorem chooseThreadOnCore_some_mem_runQueueOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    tid ∈ (st.scheduler.runQueueOnCore c).toList := by
  obtain ⟨p, d, hbucket⟩ := chooseThreadOnCore_eq_some_imp_bucket_some st c tid h
  exact chooseBestInBucket_result_mem st.objects.get? (st.scheduler.runQueueOnCore c)
    (st.scheduler.activeDomainOnCore c) tid p d hwf hbucket

/-- WS-SM SM5.A.6 (preservation form): the `Kernel`-monad `chooseThread` is
a pure read, so it preserves every core's run-queue well-formedness.  This
is the literal "`chooseThread` preserves `wellFormed`" statement; it follows
trivially from `chooseThread_preserves_state` (the selection threads the
state unchanged). -/
theorem chooseThread_preserves_runQueueOnCore_wellFormed
    (st st' : SystemState) (next : Option SeLe4n.ThreadId) (c : CoreId)
    (hStep : chooseThread st = .ok (next, st'))
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed) :
    (st'.scheduler.runQueueOnCore c).wellFormed := by
  rw [chooseThread_preserves_state st st' next hStep]; exact hwf

/-- WS-SM SM5.A.6 (the plan's literal `chooseThreadOnCore_preserves_wellFormed`
name): `chooseThreadOnCore` is a pure read, so it leaves core `c`'s run queue
— and hence its well-formedness — unchanged (there is no post-state to
"preserve").  The *substantive* "respects well-formedness" content is the
membership result `chooseThreadOnCore_some_mem_runQueueOnCore`; this theorem
is the plan-named anchor, bundling the (trivial) preservation of the
well-formed run queue with the (substantive) membership of the chosen
thread. -/
theorem chooseThreadOnCore_preserves_wellFormed
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    (st.scheduler.runQueueOnCore c).wellFormed ∧
      tid ∈ (st.scheduler.runQueueOnCore c).toList :=
  ⟨hwf, chooseThreadOnCore_some_mem_runQueueOnCore st c tid hwf h⟩

-- ============================================================================
-- §3b  SM5.A.3 — Selection optimality (plan §3.1.1, Theorem 3.1.1)
-- ============================================================================

/-- WS-SM SM5.A.3 (plan §3.1.1, `chooseThreadOnCore_selects_highest`): the
selected thread is the optimal (priority / EDF-deadline / FIFO best, via
`isBetterCandidate`) eligible thread among core `c`'s **maximum-priority
bucket** — no active-domain thread in that bucket beats the selection.

**Why the maximum-priority bucket, not the whole run queue.**  The selector
`chooseBestInBucket` is bucket-first: it buckets by *effective* priority
(`threadPriority`, which under the scheduler invariant equals
`effectiveRunQueuePriority`, i.e. `max(base, pipBoost)`) and, within the
highest-effective-priority bucket, picks the `isBetterCandidate`-best by the
thread's *base* priority + deadline.  Because `effectiveRunQueuePriority ≥
base priority`, a thread in a *lower* effective bucket can have a *higher*
base priority than the selection — so a global "highest base priority over
the whole queue" claim would be **false**, and is deliberately not made here.
The faithful optimality is therefore stated over the maximum-priority bucket,
where the selection genuinely competes.  This is non-vacuous in the
bucket-success path (the selection is the bucket's best) and vacuously true
in the full-scan fallback (no active-domain thread sits in the maximum
bucket, which is exactly why the fallback fired). -/
theorem chooseThreadOnCore_selects_highest
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) (selTcb : TCB)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c)
    (hSel : chooseThreadOnCore st c = .ok (some tid))
    (hSelTcb : st.getTcb? tid = some selTcb) :
    ∀ t ∈ (st.scheduler.runQueueOnCore c).maxPriorityBucket, ∀ tcb : TCB,
      st.getTcb? t = some tcb →
      tcb.domain = st.scheduler.activeDomainOnCore c →
        isBetterCandidate selTcb.priority selTcb.deadline tcb.priority tcb.deadline = false := by
  intro t ht tcb htTcb htDom
  obtain ⟨resPrio, resDl, hbucket⟩ := chooseThreadOnCore_eq_some_imp_bucket_some st c tid hSel
  have hSelObj : st.objects.get? tid.toObjId = some (.tcb selTcb) :=
    (SystemState.getTcb?_eq_some_iff st tid selTcb).mp hSelTcb
  have hTObj : st.objects.get? t.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st t tcb).mp htTcb
  have hMaxAll : ∀ u ∈ (st.scheduler.runQueueOnCore c).maxPriorityBucket,
      ∃ utcb : TCB, st.objects.get? u.toObjId = some (.tcb utcb) := by
    intro u hu
    exact runnableThreadsAreTCBs_objects_get? st c hRunnable u
      (RunQueue.membership_implies_flat _ u
        (RunQueue.maxPriorityBucket_subset _ hwf u hu))
  have hElig : (fun tc : TCB => tc.domain == st.scheduler.activeDomainOnCore c) tcb = true := by
    simp [htDom]
  rw [bucketFirst_fullScan_equivalence] at hbucket
  cases hMax : chooseBestRunnableInDomain st.objects.get?
      (st.scheduler.runQueueOnCore c).maxPriorityBucket
      (st.scheduler.activeDomainOnCore c) none with
  | error e => rw [hMax] at hbucket; simp at hbucket
  | ok val =>
    cases val with
    | some r =>
      rw [hMax] at hbucket
      simp only [Except.ok.injEq, Option.some.injEq] at hbucket
      rw [hbucket] at hMax
      obtain ⟨resTcb, hResTcb, hResP, hResD⟩ :=
        chooseBestRunnableBy_result_fields st.objects.get?
          (fun tc => tc.domain == st.scheduler.activeDomainOnCore c)
          (st.scheduler.runQueueOnCore c).maxPriorityBucket none tid resPrio resDl hMax
          (by intro _ _ _ h; simp at h)
      rw [hSelObj] at hResTcb; cases hResTcb
      have hOpt := chooseBestRunnableBy_optimal st.objects.get?
        (fun tc => tc.domain == st.scheduler.activeDomainOnCore c)
        (st.scheduler.runQueueOnCore c).maxPriorityBucket tid resPrio resDl hMax hMaxAll
      have hNoBeat := hOpt t ht tcb hTObj hElig
      rw [hResP, hResD]
      exact hNoBeat
    | none =>
      rw [hMax] at hbucket
      have hNoElig := chooseBestRunnableBy_none_no_eligible st.objects.get?
        (fun tc => tc.domain == st.scheduler.activeDomainOnCore c)
        (st.scheduler.runQueueOnCore c).maxPriorityBucket hMax t ht tcb hTObj
      simp [htDom] at hNoElig

-- ============================================================================
-- §4  SM5.A.7 — Decidability of the selection result
-- ============================================================================

/-- WS-SM SM5.A.7: "core `c` selects `tid`" — the decidable proposition the
SM5.A unit tests discharge on concrete states by `decide`.  Its `Decidable`
instance is supplied explicitly just below (Lean core does **not** derive
`DecidableEq (Except _ _)`, so the instance cannot be `inferInstance`d; it is
discharged by structural case analysis on the evaluated selection result). -/
def chooseThreadOnCoreSelects (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : Prop :=
  chooseThreadOnCore st c = .ok (some tid)

/-- WS-SM SM5.A.7: `chooseThreadOnCoreSelects` is decidable.  Lean core does
not derive `DecidableEq (Except _ _)`, so the instance is discharged by a
structural case analysis on the (fully-evaluated) selection result rather
than by `inferInstance`. -/
instance (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    Decidable (chooseThreadOnCoreSelects st c tid) :=
  match h : chooseThreadOnCore st c with
  | .ok (some t) =>
      if ht : t = tid then .isTrue (by simp [chooseThreadOnCoreSelects, h, ht])
      else .isFalse (by simp [chooseThreadOnCoreSelects, h, ht])
  | .ok none => .isFalse (by simp [chooseThreadOnCoreSelects, h])
  | .error e => .isFalse (by simp [chooseThreadOnCoreSelects, h])

/-- WS-SM SM5.A.7: "core `c` has no domain-eligible thread, so its scheduler
must fall back to idle" — the decidable complement of
`chooseThreadOnCoreSelects`. -/
def chooseThreadOnCoreIdleFallback (st : SystemState) (c : CoreId) : Prop :=
  chooseThreadOnCore st c = .ok none

instance (st : SystemState) (c : CoreId) :
    Decidable (chooseThreadOnCoreIdleFallback st c) :=
  match h : chooseThreadOnCore st c with
  | .ok none => .isTrue (by simp [chooseThreadOnCoreIdleFallback, h])
  | .ok (some t) => .isFalse (by simp [chooseThreadOnCoreIdleFallback, h])
  | .error e => .isFalse (by simp [chooseThreadOnCoreIdleFallback, h])

/-- WS-SM SM5.A.7 (budget variant): "core `c`'s budget-aware selection picks
`tid`". -/
def chooseThreadEffectiveOnCoreSelects (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) : Prop :=
  chooseThreadEffectiveOnCore st c = .ok (some tid)

instance (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId) :
    Decidable (chooseThreadEffectiveOnCoreSelects st c tid) :=
  match h : chooseThreadEffectiveOnCore st c with
  | .ok (some t) =>
      if ht : t = tid then .isTrue (by simp [chooseThreadEffectiveOnCoreSelects, h, ht])
      else .isFalse (by simp [chooseThreadEffectiveOnCoreSelects, h, ht])
  | .ok none => .isFalse (by simp [chooseThreadEffectiveOnCoreSelects, h])
  | .error e => .isFalse (by simp [chooseThreadEffectiveOnCoreSelects, h])

/-- WS-SM SM5.A.7 (budget variant): "core `c`'s budget-aware selection finds no
in-budget in-domain thread, so it falls back to idle". -/
def chooseThreadEffectiveOnCoreIdleFallback (st : SystemState) (c : CoreId) : Prop :=
  chooseThreadEffectiveOnCore st c = .ok none

instance (st : SystemState) (c : CoreId) :
    Decidable (chooseThreadEffectiveOnCoreIdleFallback st c) :=
  match h : chooseThreadEffectiveOnCore st c with
  | .ok none => .isTrue (by simp [chooseThreadEffectiveOnCoreIdleFallback, h])
  | .ok (some t) => .isFalse (by simp [chooseThreadEffectiveOnCoreIdleFallback, h])
  | .error e => .isFalse (by simp [chooseThreadEffectiveOnCoreIdleFallback, h])

-- ============================================================================
-- §5  Corollaries via the SM4.C aggregate `schedulerInvariant_perCore`
-- ============================================================================

/-- WS-SM SM5.A.4 (plan §3.5.2 form): under the aggregate per-core scheduler
invariant, `chooseThreadOnCore` never errors.  Discharges the well-formed +
runnable-are-TCBs hypotheses of `chooseThreadOnCore_ok_of_runnableTCBs` from
`schedulerInvariant_perCore`. -/
theorem chooseThreadOnCore_ok_of_schedulerInvariant
    (st : SystemState) (c : CoreId) (h : schedulerInvariant_perCore st c) :
    ∃ r, chooseThreadOnCore st c = .ok r :=
  chooseThreadOnCore_ok_of_runnableTCBs st c
    (schedulerInvariant_perCore_to_runQueueOnCoreWellFormed h)
    (schedulerInvariant_perCore_to_runnableThreadsAreTCBs h)

/-- WS-SM SM5.A.6 (plan §3.5.2 form): under the aggregate per-core scheduler
invariant, a chosen thread is a genuine run-queue member. -/
theorem chooseThreadOnCore_some_mem_of_schedulerInvariant
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : schedulerInvariant_perCore st c)
    (h : chooseThreadOnCore st c = .ok (some tid)) :
    tid ∈ (st.scheduler.runQueueOnCore c).toList :=
  chooseThreadOnCore_some_mem_runQueueOnCore st c tid
    (schedulerInvariant_perCore_to_runQueueOnCoreWellFormed hInv) h

-- ============================================================================
-- §6  Budget-aware per-core selection (`chooseThreadEffectiveOnCore`)
-- ============================================================================
--
-- `chooseThreadEffectiveOnCore` (in `Selection.lean`) is the CBS-budget-aware
-- companion to `chooseThreadOnCore`: it additionally rejects threads whose
-- SchedContext budget is exhausted (`hasSufficientBudget`).  This section
-- mirrors the SM5.A theorems for it: per-core independence, non-erroring,
-- completeness, selection soundness, and — the property unique to the
-- budget-aware variant — that a *selected* thread genuinely has budget.

/-- SM5.A budget helper: the effective fold over a list of genuine TCBs never
errors. -/
theorem chooseBestRunnableEffective_ok_of_allTcb
    (st : SystemState) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)),
      (∀ t ∈ list, ∃ tcb : TCB, st.objects.get? t.toObjId = some (.tcb tcb)) →
      ∃ r, chooseBestRunnableEffective st eligible list best = .ok r := by
  intro list
  induction list with
  | nil => intro best _; exact ⟨best, rfl⟩
  | cons hd tl ih =>
    intro best hAll
    obtain ⟨hdTcb, hHdObj⟩ := hAll hd (List.mem_cons_self ..)
    have hAllTl : ∀ t ∈ tl, ∃ tcb : TCB, st.objects.get? t.toObjId = some (.tcb tcb) :=
      fun t ht => hAll t (List.mem_cons_of_mem _ ht)
    unfold chooseBestRunnableEffective
    rw [hHdObj]
    exact ih _ hAllTl

/-- SM5.A budget helper: `hasSufficientBudget` reads the state only through
the object store, so two states with equal `objects` agree on it. -/
theorem hasSufficientBudget_objects_congr (s₁ s₂ : SystemState) (tcb : TCB)
    (h : s₁.objects = s₂.objects) :
    hasSufficientBudget s₁ tcb = hasSufficientBudget s₂ tcb := by
  unfold hasSufficientBudget SystemState.getSchedContext?
  rw [h]

/-- SM5.A budget helper: `resolveEffectivePrioDeadline` reads the state only
through the object store, so two states with equal `objects` agree on it. -/
theorem resolveEffectivePrioDeadline_objects_congr (s₁ s₂ : SystemState) (tcb : TCB)
    (h : s₁.objects = s₂.objects) :
    resolveEffectivePrioDeadline s₁ tcb = resolveEffectivePrioDeadline s₂ tcb := by
  unfold resolveEffectivePrioDeadline SystemState.getSchedContext?
  rw [h]

/-- SM5.A budget helper: the effective fold reads the state only through the
object store (the run queue / active domain enter as explicit arguments), so
two states with equal `objects` produce identical folds.  This is the
congruence that makes the budget-aware per-core selection frameable. -/
theorem chooseBestRunnableEffective_objects_congr (s₁ s₂ : SystemState)
    (eligible : TCB → Bool) (h : s₁.objects = s₂.objects) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline)),
      chooseBestRunnableEffective s₁ eligible list best
        = chooseBestRunnableEffective s₂ eligible list best := by
  intro list
  induction list with
  | nil => intro best; rfl
  | cons hd tl ih =>
    intro best
    have h' : s₂.objects = s₁.objects := h.symm
    cases hObj : s₁.objects.get? hd.toObjId with
    | none =>
      have hObj2 : s₂.objects.get? hd.toObjId = none := by rw [h']; exact hObj
      unfold chooseBestRunnableEffective; simp only [hObj, hObj2]
    | some obj =>
      have hObj2 : s₂.objects.get? hd.toObjId = some obj := by rw [h']; exact hObj
      cases obj with
      | tcb tcb =>
        unfold chooseBestRunnableEffective
        simp only [hObj, hObj2, hasSufficientBudget_objects_congr s₁ s₂ tcb h,
          resolveEffectivePrioDeadline_objects_congr s₁ s₂ tcb h]
        exact ih _
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ =>
        unfold chooseBestRunnableEffective; simp only [hObj, hObj2]

/-- SM5.A budget helper: the bucket-first effective selector is objects-only
dependent. -/
theorem chooseBestInBucketEffective_objects_congr (s₁ s₂ : SystemState)
    (rq : RunQueue) (ad : SeLe4n.DomainId) (h : s₁.objects = s₂.objects) :
    chooseBestInBucketEffective s₁ rq ad = chooseBestInBucketEffective s₂ rq ad := by
  unfold chooseBestInBucketEffective chooseBestRunnableInDomainEffective
  simp only [chooseBestRunnableEffective_objects_congr s₁ s₂ (fun tcb => tcb.domain == ad) h]

/-- WS-SM SM5.A.3 (budget variant, frame form): `chooseThreadEffectiveOnCore`'s
read footprint on core `c` is `(objects, runQueueOnCore c, activeDomainOnCore
c)`.  Unlike the non-budget `chooseThreadOnCore_frame`, full `objects` equality
is genuinely required (not just a lookup function) because the budget check and
effective-priority resolution traverse SchedContexts in the object store. -/
theorem chooseThreadEffectiveOnCore_frame (s₁ s₂ : SystemState) (c : CoreId)
    (hObj : s₁.objects = s₂.objects)
    (hRQ : s₁.scheduler.runQueueOnCore c = s₂.scheduler.runQueueOnCore c)
    (hAD : s₁.scheduler.activeDomainOnCore c = s₂.scheduler.activeDomainOnCore c) :
    chooseThreadEffectiveOnCore s₁ c = chooseThreadEffectiveOnCore s₂ c := by
  unfold chooseThreadEffectiveOnCore
  rw [hRQ, hAD, chooseBestInBucketEffective_objects_congr s₁ s₂ _ _ hObj]

/-- WS-SM SM5.A.3 (budget variant): per-core independence under a sibling-core
run-queue write.  Writing core `c'`'s run queue (`c' ≠ c`) leaves
`chooseThreadEffectiveOnCore · c` unchanged. -/
theorem chooseThreadEffectiveOnCore_independent_of_setRunQueueOnCore
    (s : SystemState) (c c' : CoreId) (rq : RunQueue) (h : c ≠ c') :
    chooseThreadEffectiveOnCore
        { s with scheduler := s.scheduler.setRunQueueOnCore c' rq } c
      = chooseThreadEffectiveOnCore s c := by
  apply chooseThreadEffectiveOnCore_frame
  · rfl
  · exact SchedulerState.setRunQueueOnCore_runQueueOnCore_ne s.scheduler c' c rq (Ne.symm h)
  · exact SchedulerState.setRunQueueOnCore_activeDomainOnCore s.scheduler c' c rq

/-- SM5.A budget helper: the bucket-first effective selector unfolds to "scan
the max-priority bucket, then fall back to a full-list scan" (the effective
analogue of `bucketFirst_fullScan_equivalence`).  Stated as a `rfl`-lemma so
the explicit match form is `rw`-able (a raw `unfold` produces a compiled match
whose scrutinee is not rewritable). -/
theorem bucketFirstEffective_fullScan_equivalence
    (st : SystemState) (rq : RunQueue) (ad : SeLe4n.DomainId) :
    chooseBestInBucketEffective st rq ad =
      (match chooseBestRunnableInDomainEffective st rq.maxPriorityBucket ad none with
       | .error e => .error e
       | .ok (some result) => .ok (some result)
       | .ok none => chooseBestRunnableInDomainEffective st rq.toList ad none) := rfl

/-- SM5.A budget helper: a recorded candidate of the effective fold (from any
`best`) either is a genuine member of the scanned list that **passed both the
domain-eligibility and the budget filter**, or was already the recorded
`best`.  Specialised to `best = none` below for the budget-soundness +
selection-soundness results. -/
private theorem chooseBestRunnableEffective_result_props_aux
    (st : SystemState) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (best : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
      (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline),
      chooseBestRunnableEffective st eligible list best = .ok (some (rt, rp, rd)) →
      (rt ∈ list ∧ ∃ rtcb : TCB, st.objects.get? rt.toObjId = some (.tcb rtcb)
          ∧ eligible rtcb = true ∧ hasSufficientBudget st rtcb = true)
        ∨ (∃ p d, best = some (rt, p, d)) := by
  intro list
  induction list with
  | nil =>
    intro best rt rp rd h
    simp only [chooseBestRunnableEffective] at h
    exact Or.inr ⟨rp, rd, by rw [Except.ok.injEq] at h; rw [h]⟩
  | cons hd tl ih =>
    intro best rt rp rd h
    unfold chooseBestRunnableEffective at h
    cases hObj : st.objects.get? hd.toObjId with
    | none => rw [hObj] at h; simp at h
    | some obj =>
      cases obj with
      | tcb tcb =>
        rw [hObj] at h
        by_cases hCond : (eligible tcb && hasSufficientBudget st tcb) = true
        · obtain ⟨hEl, hBu⟩ := And.intro
            (by simpa using (Bool.and_eq_true _ _ ▸ hCond).1)
            (by simpa using (Bool.and_eq_true _ _ ▸ hCond).2)
          -- recorded path: best' records `hd` (when it beats `best`) or keeps `best`.
          cases best with
          | none =>
            simp only [hCond, if_true] at h
            rcases ih _ rt rp rd h with hprops | ⟨p, d, hb⟩
            · exact Or.inl ⟨List.mem_cons_of_mem _ hprops.1, hprops.2⟩
            · simp only [Option.some.injEq, Prod.mk.injEq] at hb
              exact Or.inl ⟨List.mem_cons.mpr (Or.inl hb.1.symm),
                tcb, hb.1.symm ▸ hObj, hEl, hBu⟩
          | some y =>
            obtain ⟨yt, yp, yd⟩ := y
            by_cases hBetter : isBetterCandidate yp yd
                (resolveEffectivePrioDeadline st tcb).1 (resolveEffectivePrioDeadline st tcb).2
            · simp only [hCond, if_true, hBetter] at h
              rcases ih _ rt rp rd h with hprops | ⟨p, d, hb⟩
              · exact Or.inl ⟨List.mem_cons_of_mem _ hprops.1, hprops.2⟩
              · simp only [Option.some.injEq, Prod.mk.injEq] at hb
                exact Or.inl ⟨List.mem_cons.mpr (Or.inl hb.1.symm),
                  tcb, hb.1.symm ▸ hObj, hEl, hBu⟩
            · simp only [hCond, if_true, hBetter] at h
              rcases ih _ rt rp rd h with hprops | hb
              · exact Or.inl ⟨List.mem_cons_of_mem _ hprops.1, hprops.2⟩
              · exact Or.inr hb
        · simp only [Bool.not_eq_true] at hCond
          simp only [hCond] at h
          rcases ih _ rt rp rd h with hprops | hb
          · exact Or.inl ⟨List.mem_cons_of_mem _ hprops.1, hprops.2⟩
          · exact Or.inr hb
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ => rw [hObj] at h; simp at h

/-- SM5.A budget helper: a `none`-seeded effective scan that selects `rt`
witnesses that `rt` is a member of the scanned list, resolves to a TCB, and
passed both the domain-eligibility and the CBS budget filter. -/
theorem chooseBestRunnableEffective_result_props
    (st : SystemState) (eligible : TCB → Bool) (list : List SeLe4n.ThreadId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (h : chooseBestRunnableEffective st eligible list none = .ok (some (rt, rp, rd))) :
    rt ∈ list ∧ ∃ rtcb : TCB, st.objects.get? rt.toObjId = some (.tcb rtcb)
      ∧ eligible rtcb = true ∧ hasSufficientBudget st rtcb = true := by
  rcases chooseBestRunnableEffective_result_props_aux st eligible list none rt rp rd h with
    hp | ⟨_, _, hb⟩
  · exact hp
  · exact absurd hb (by simp)

/-- SM5.A budget helper: a selected candidate of the bucket-first effective
scan over a well-formed run queue is a genuine run-queue member that is
in-domain and has sufficient budget. -/
theorem chooseBestInBucketEffective_result_props
    (st : SystemState) (rq : RunQueue) (ad : SeLe4n.DomainId)
    (rt : SeLe4n.ThreadId) (rp : SeLe4n.Priority) (rd : SeLe4n.Deadline)
    (hwf : rq.wellFormed)
    (h : chooseBestInBucketEffective st rq ad = .ok (some (rt, rp, rd))) :
    rt ∈ rq.toList ∧ ∃ rtcb : TCB, st.objects.get? rt.toObjId = some (.tcb rtcb)
      ∧ rtcb.domain = ad ∧ hasSufficientBudget st rtcb = true := by
  rw [bucketFirstEffective_fullScan_equivalence] at h
  cases hMax : chooseBestRunnableInDomainEffective st rq.maxPriorityBucket ad none with
  | error e => rw [hMax] at h; simp at h
  | ok val =>
    cases val with
    | some r =>
      rw [hMax] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      rw [h] at hMax
      obtain ⟨hMem, rtcb, hObj, hElig, hBudget⟩ :=
        chooseBestRunnableEffective_result_props st (fun tc => tc.domain == ad)
          rq.maxPriorityBucket rt rp rd hMax
      exact ⟨RunQueue.membership_implies_flat rq rt
          (RunQueue.maxPriorityBucket_subset rq hwf rt hMem),
        rtcb, hObj, eq_of_beq hElig, hBudget⟩
    | none =>
      rw [hMax] at h
      obtain ⟨hMem, rtcb, hObj, hElig, hBudget⟩ :=
        chooseBestRunnableEffective_result_props st (fun tc => tc.domain == ad)
          rq.toList rt rp rd h
      exact ⟨hMem, rtcb, hObj, eq_of_beq hElig, hBudget⟩

/-- SM5.A budget helper: `chooseThreadEffectiveOnCore = .ok (some tid)` exposes
the selected `(tid, priority, deadline)` triple. -/
theorem chooseThreadEffectiveOnCore_eq_some_imp_bucket_some
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (h : chooseThreadEffectiveOnCore st c = .ok (some tid)) :
    ∃ p d, chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok (some (tid, p, d)) := by
  unfold chooseThreadEffectiveOnCore at h
  cases hB : chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) with
  | error e => rw [hB] at h; simp at h
  | ok val =>
    cases val with
    | none => rw [hB] at h; simp at h
    | some triple =>
      obtain ⟨t, tp, td⟩ := triple
      rw [hB] at h
      simp only [Except.ok.injEq, Option.some.injEq] at h
      subst h
      exact ⟨tp, td, rfl⟩

/-- SM5.A budget helper: a `.ok` bucket-first effective scan lifts to a `.ok`
from `chooseThreadEffectiveOnCore`. -/
theorem chooseThreadEffectiveOnCore_ok_of_bucket_ok
    (st : SystemState) (c : CoreId)
    (val : Option (SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline))
    (h : chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok val) :
    ∃ r, chooseThreadEffectiveOnCore st c = .ok r := by
  unfold chooseThreadEffectiveOnCore
  rw [h]
  cases val with
  | none => exact ⟨none, rfl⟩
  | some triple => obtain ⟨tid, p, d⟩ := triple; exact ⟨some tid, rfl⟩

/-- SM5.A budget helper: the bucket-first effective scan never errors on a
well-formed all-TCB run queue. -/
theorem chooseBestInBucketEffective_ok_of_allTcb
    (st : SystemState) (rq : RunQueue) (ad : SeLe4n.DomainId)
    (hwf : rq.wellFormed)
    (hAll : ∀ t ∈ rq.toList, ∃ tcb : TCB, st.objects.get? t.toObjId = some (.tcb tcb)) :
    ∃ val, chooseBestInBucketEffective st rq ad = .ok val := by
  have hMaxAll : ∀ t ∈ rq.maxPriorityBucket, ∃ tcb : TCB,
      st.objects.get? t.toObjId = some (.tcb tcb) := by
    intro t ht
    exact hAll t (RunQueue.membership_implies_flat rq t
      (RunQueue.maxPriorityBucket_subset rq hwf t ht))
  obtain ⟨maxVal, hMax⟩ :
      ∃ r, chooseBestRunnableInDomainEffective st rq.maxPriorityBucket ad none = .ok r :=
    chooseBestRunnableEffective_ok_of_allTcb st (fun tc => tc.domain == ad)
      rq.maxPriorityBucket none hMaxAll
  rw [bucketFirstEffective_fullScan_equivalence, hMax]
  cases maxVal with
  | some r => exact ⟨some r, rfl⟩
  | none =>
    exact chooseBestRunnableEffective_ok_of_allTcb st (fun tc => tc.domain == ad)
      rq.toList none hAll

-- ── Public budget-aware theorems. ──

/-- WS-SM SM5.A.4 (budget variant): `chooseThreadEffectiveOnCore` never errors
on a well-formed all-TCB run queue. -/
theorem chooseThreadEffectiveOnCore_ok_of_runnableTCBs
    (st : SystemState) (c : CoreId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (hRunnable : runnableThreadsAreTCBsOnCore st c) :
    ∃ r, chooseThreadEffectiveOnCore st c = .ok r := by
  obtain ⟨val, hbucket⟩ := chooseBestInBucketEffective_ok_of_allTcb st
    (st.scheduler.runQueueOnCore c) (st.scheduler.activeDomainOnCore c) hwf
    (runnableThreadsAreTCBs_objects_get? st c hRunnable)
  exact chooseThreadEffectiveOnCore_ok_of_bucket_ok st c val hbucket

/-- WS-SM SM5.A.6 (budget variant, selection soundness): a thread chosen by
`chooseThreadEffectiveOnCore` is a genuine member of core `c`'s run queue. -/
theorem chooseThreadEffectiveOnCore_some_mem_runQueueOnCore
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : chooseThreadEffectiveOnCore st c = .ok (some tid)) :
    tid ∈ (st.scheduler.runQueueOnCore c).toList := by
  obtain ⟨p, d, hbucket⟩ := chooseThreadEffectiveOnCore_eq_some_imp_bucket_some st c tid h
  exact (chooseBestInBucketEffective_result_props st (st.scheduler.runQueueOnCore c)
    (st.scheduler.activeDomainOnCore c) tid p d hwf hbucket).1

/-- WS-SM SM5.A (budget variant — the property unique to the budget-aware
selector): a thread chosen by `chooseThreadEffectiveOnCore` genuinely has
**sufficient CBS budget** (and is in core `c`'s active domain).  This is the
soundness of the budget filter — the whole reason the budget-aware variant
exists: it never dispatches a thread whose SchedContext budget is exhausted. -/
theorem chooseThreadEffectiveOnCore_selected_has_budget
    (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hwf : (st.scheduler.runQueueOnCore c).wellFormed)
    (h : chooseThreadEffectiveOnCore st c = .ok (some tid)) :
    ∃ tcb : TCB, st.getTcb? tid = some tcb
      ∧ hasSufficientBudget st tcb = true
      ∧ tcb.domain = st.scheduler.activeDomainOnCore c := by
  obtain ⟨p, d, hbucket⟩ := chooseThreadEffectiveOnCore_eq_some_imp_bucket_some st c tid h
  obtain ⟨_hMem, rtcb, hObj, hDom, hBudget⟩ :=
    chooseBestInBucketEffective_result_props st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) tid p d hwf hbucket
  exact ⟨rtcb, (SystemState.getTcb?_eq_some_iff st tid rtcb).mpr hObj, hBudget, hDom⟩

-- ── Budget-aware completeness. ──

/-- SM5.A budget helper: once the effective fold has recorded a candidate it
never returns `.ok none`. -/
theorem chooseBestRunnableEffective_some_ne_ok_none
    (st : SystemState) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId)
      (x : SeLe4n.ThreadId × SeLe4n.Priority × SeLe4n.Deadline),
      chooseBestRunnableEffective st eligible list (some x) ≠ .ok none := by
  intro list
  induction list with
  | nil => intro x h; simp [chooseBestRunnableEffective] at h
  | cons hd tl ih =>
    intro x h
    obtain ⟨xt, xp, xd⟩ := x
    unfold chooseBestRunnableEffective at h
    cases hObj : st.objects.get? hd.toObjId with
    | none => rw [hObj] at h; simp at h
    | some obj =>
      cases obj with
      | tcb tcb =>
        rw [hObj] at h
        by_cases hCond : (eligible tcb && hasSufficientBudget st tcb) = true
        · simp only [hCond, if_true] at h
          split at h <;> exact ih _ h
        · simp only [Bool.not_eq_true] at hCond
          simp only [hCond] at h; exact ih _ h
      | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
      | schedContext _ => rw [hObj] at h; simp at h

/-- SM5.A budget helper: a `none`-seeded effective scan returning `.ok none`
witnesses that **no** scanned TCB was both domain-eligible and had sufficient
budget. -/
theorem chooseBestRunnableEffective_none_no_eligible
    (st : SystemState) (eligible : TCB → Bool) :
    ∀ (list : List SeLe4n.ThreadId),
      chooseBestRunnableEffective st eligible list none = .ok none →
      ∀ tid ∈ list, ∀ tcb : TCB,
        st.objects.get? tid.toObjId = some (.tcb tcb) →
        (eligible tcb && hasSufficientBudget st tcb) = false := by
  intro list
  induction list with
  | nil => intro _ tid hmem; simp at hmem
  | cons hd tl ih =>
    intro h tid hmem tcb hObjTid
    have hHdReduce := h
    unfold chooseBestRunnableEffective at hHdReduce
    rcases List.mem_cons.mp hmem with hEq | hMemTl
    · subst hEq
      rw [hObjTid] at hHdReduce
      by_cases hCond : (eligible tcb && hasSufficientBudget st tcb) = true
      · exfalso
        simp only [hCond, if_true] at hHdReduce
        exact chooseBestRunnableEffective_some_ne_ok_none st eligible tl _ hHdReduce
      · simpa using hCond
    · cases hHdObj : st.objects.get? hd.toObjId with
      | none => rw [hHdObj] at hHdReduce; simp at hHdReduce
      | some obj =>
        cases obj with
        | tcb hdTcb =>
          rw [hHdObj] at hHdReduce
          by_cases hHdCond : (eligible hdTcb && hasSufficientBudget st hdTcb) = true
          · exfalso
            simp only [hHdCond, if_true] at hHdReduce
            exact chooseBestRunnableEffective_some_ne_ok_none st eligible tl _ hHdReduce
          · simp only [Bool.not_eq_true] at hHdCond
            simp only [hHdCond] at hHdReduce
            exact ih hHdReduce tid hMemTl tcb hObjTid
        | endpoint _ | notification _ | cnode _ | vspaceRoot _ | untyped _
        | schedContext _ => rw [hHdObj] at hHdReduce; simp at hHdReduce

/-- SM5.A budget helper: a `.ok none` from the bucket-first effective selector
forces the full-list fallback scan to also be `.ok none`. -/
theorem chooseBestInBucketEffective_none_imp_toList_none
    (st : SystemState) (rq : RunQueue) (ad : SeLe4n.DomainId)
    (h : chooseBestInBucketEffective st rq ad = .ok none) :
    chooseBestRunnableInDomainEffective st rq.toList ad none = .ok none := by
  rw [bucketFirstEffective_fullScan_equivalence] at h
  cases hMax : chooseBestRunnableInDomainEffective st rq.maxPriorityBucket ad none with
  | error e => rw [hMax] at h; simp at h
  | ok val =>
    cases val with
    | some r => rw [hMax] at h; simp at h
    | none => rw [hMax] at h; simpa using h

/-- SM5.A budget helper: `chooseThreadEffectiveOnCore = .ok none` forces the
underlying bucket-first effective scan to be `.ok none`. -/
theorem chooseThreadEffectiveOnCore_eq_none_imp_bucket_none
    (st : SystemState) (c : CoreId) (h : chooseThreadEffectiveOnCore st c = .ok none) :
    chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) = .ok none := by
  unfold chooseThreadEffectiveOnCore at h
  cases hB : chooseBestInBucketEffective st (st.scheduler.runQueueOnCore c)
      (st.scheduler.activeDomainOnCore c) with
  | error e => rw [hB] at h; simp at h
  | ok val =>
    cases val with
    | none => rfl
    | some triple => obtain ⟨tid, p, d⟩ := triple; rw [hB] at h; simp at h

/-- WS-SM SM5.A.4 (budget variant, completeness): `chooseThreadEffectiveOnCore`
returns the idle-fallback signal `.ok none` **only** when no thread in core
`c`'s run queue is both in its active domain and has sufficient CBS budget —
so the budget-aware idle fallback never drops a runnable, in-budget thread. -/
theorem chooseThreadEffectiveOnCore_none_no_eligible
    (st : SystemState) (c : CoreId)
    (h : chooseThreadEffectiveOnCore st c = .ok none) :
    ∀ tid ∈ (st.scheduler.runQueueOnCore c).toList, ∀ tcb : TCB,
      st.getTcb? tid = some tcb →
      ¬(tcb.domain = st.scheduler.activeDomainOnCore c ∧ hasSufficientBudget st tcb = true) := by
  intro tid hmem tcb htcb ⟨hDom, hBudget⟩
  have hbucket := chooseThreadEffectiveOnCore_eq_none_imp_bucket_none st c h
  have htoList := chooseBestInBucketEffective_none_imp_toList_none st
    (st.scheduler.runQueueOnCore c) (st.scheduler.activeDomainOnCore c) hbucket
  have hObjGet : st.objects.get? tid.toObjId = some (.tcb tcb) :=
    (SystemState.getTcb?_eq_some_iff st tid tcb).mp htcb
  have hElig := chooseBestRunnableEffective_none_no_eligible st
    (fun t => t.domain == st.scheduler.activeDomainOnCore c)
    (st.scheduler.runQueueOnCore c).toList htoList tid hmem tcb hObjGet
  simp [hDom, hBudget] at hElig

end SeLe4n.Kernel
