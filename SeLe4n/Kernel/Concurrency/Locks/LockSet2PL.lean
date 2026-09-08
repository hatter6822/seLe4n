-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Concurrency.Locks.Kind
import SeLe4n.Kernel.Concurrency.Locks.LockSet
import SeLe4n.Kernel.Concurrency.Locks.LockIdProjection
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
import SeLe4n.Kernel.Concurrency.Locks.WithLockSet
import SeLe4n.Kernel.Concurrency.Locks.LockSetHeld

/-!
# WS-SM SM3.C.5 / C.6 / C.7 / C.8 — Two-phase-locking discipline theorems

The four substantive theorems for SM3.C:

* **SM3.C.5** `lockSet_acquired_in_order`: every lock acquisition
  via `withLockSet` happens in `LockId` ascending order.  Follows
  from `lockAcquireSequence_ordered` (SM3.B.6) and the structural
  shape of `acquireAll` (sequential fold over the sorted list).

* **SM3.C.6** `lockSet_released_in_reverse`: every lock release
  via `withLockSet` happens in `LockId` *descending* order.
  Follows from the same SM3.B.6 lemma applied to
  `lockAcquireSequence.reverse`.

* **SM3.C.7** `lockSet_atomic_under_2pl`: the visible state
  transitions during `withLockSet` form an atomic span — every
  external observer sees either the pre-acquire state or the
  post-release state, never an intermediate.  Follows from
  strict-2PL: no early releases occur.

* **SM3.C.8** `lockSet_invariant_preserved` (plan §3.9 Corollary
  2.1.11): under `lockSetHeld c (lockSet τ args) s` precondition,
  the kernel action's postcondition holds whenever the action
  succeeds.  This is the operational form of the architectural
  lever that keeps WS-SM's proof cost tractable: every existing
  single-core kernel-transition theorem lifts to the SMP form
  with this precondition.

## Strict-2PL discipline

The 2PL discipline is *strict* in seLe4n: locks are not released
until ALL of the action's mutations are complete.  This is what
makes the serializability theorem (SM3.E.3) immediate: the
commit-time of every transaction is unambiguously the
post-action moment, so the conflict graph is a strict total
order.

## Proof techniques

The four theorems share a common discharge pattern:

1. Unfold `withLockSet` to expose the three phases.
2. For ordering claims (C.5/C.6), appeal to
   `lockAcquireSequence_ordered` plus a structural lemma about
   `acquireAll` / `releaseAll` preserving the input list's
   order.
3. For atomicity (C.7), observe that no `acquireLockOnObject` /
   `releaseLockOnObject` call interleaves with the action: the
   acquires complete before the action runs, and the releases
   start after the action finishes.
4. For invariant preservation (C.8), use `lockSetHeld_subset`
   plus per-transition postcondition lemmas (proven separately
   per kernel API in SM3.E.6's metatheorem).
-/

namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- §1 — `acquireOrder` / `releaseOrder` projection helpers
-- ============================================================================

/-- WS-SM SM3.C.5 helper: extract the LockId-ordered acquisition
sequence from a `LockSet`.  This is the *order* in which
`withLockSet` invokes `acquireLockOnObject`, separated from the
state-update fold so the ordering theorem can target it directly. -/
def acquireOrder (S : LockSet) : List LockId :=
  S.lockAcquireSequence.map Prod.fst

/-- WS-SM SM3.C.6 helper: extract the LockId-ordered release
sequence — the reverse of the acquisition sequence. -/
def releaseOrder (S : LockSet) : List LockId :=
  acquireOrder S |>.reverse

/-- WS-SM SM3.C.5 / C.6: round-trip — the release order is the
reverse of the acquire order. -/
@[simp] theorem releaseOrder_eq_acquireOrder_reverse (S : LockSet) :
    releaseOrder S = (acquireOrder S).reverse := rfl

-- ============================================================================
-- §2 — SM3.C.5 — `lockSet_acquired_in_order`
-- ============================================================================

/-- WS-SM SM3.C.5 (plan §5.3): every acquisition via `withLockSet`
happens in `LockId` ascending order.

The acquire order — `acquireOrder S` — is the projection of
`lockAcquireSequence S` onto its `fst` components.  Since
`lockAcquireSequence` is canonically sorted by `LockId` ascending
(SM3.B.6), the projection inherits the ordering.

This is the cornerstone witness for SM3.D's deadlock-freedom
theorem: any cycle in the wait-graph would require some core to
acquire a *lower* LockId than one it already holds, contradicting
this lemma. -/
theorem lockSet_acquired_in_order (S : LockSet) :
    (acquireOrder S).Pairwise (· ≤ ·) := by
  unfold acquireOrder
  -- `lockAcquireSequence` is Pairwise (· ≤ ·) on the fst projection.
  have h := S.lockAcquireSequence_ordered
  -- Lift the Pairwise on pairs (with fst-comparator) to Pairwise on the fst list.
  exact List.Pairwise.map _ (fun a b h => h) h

-- ============================================================================
-- §3 — SM3.C.6 — `lockSet_released_in_reverse`
-- ============================================================================

/-- WS-SM SM3.C.6 (plan §5.3): every release via `withLockSet`
happens in `LockId` descending order (i.e., the reverse of the
acquire order).

Follows from SM3.C.5's ordering by reversing the list: the
reverse of an ascending list is descending.  Combined with
`releaseOrder_eq_acquireOrder_reverse`, this gives the strict-2PL
LIFO release discipline. -/
theorem lockSet_released_in_reverse (S : LockSet) :
    (releaseOrder S).Pairwise (· ≥ ·) := by
  unfold releaseOrder
  -- The reverse of an ascending list is descending.
  rw [List.pairwise_reverse]
  -- Goal: (acquireOrder S).Pairwise (fun a b => b ≤ a) — but ≥ flips it.
  exact lockSet_acquired_in_order S

-- ============================================================================
-- §4 — SM3.C.7 — `lockSet_atomic_under_2pl`
-- ============================================================================

/-- WS-SM SM3.C.7 helper: structural decomposition theorem —
`withLockSet` factors into three sequentially-composed phases:
acquire, action, release.

This is a definitional unfolding witness; SM3.E's serializability
proof appeals to it to argue that no external observer can
interleave with the action phase. -/
theorem withLockSet_three_phase_decomposition {α : Type} (S : LockSet)
    (core : CoreId) (action : SystemState → SystemState × α)
    (s : SystemState) :
    let acquired := acquireAll core S.lockAcquireSequence s
    let (postAction, result) := action acquired
    let unwound := unwindAll core S.lockAcquireSequence.reverse postAction
    withLockSet S core action s = (unwound, result) := by
  rfl

/-- WS-SM SM3.C.7 (plan §5.3 Theorem 2.1.10 operational form):
the `withLockSet` combinator yields an atomic-from-observer-view
state transition.

"Atomic from observer view" means: the post-state at the conclusion
of `withLockSet` is the post-state of `action` (with all the
action's mutations) composed with `releaseAll`.  No external
observer that does NOT hold a conflicting lock can see an
intermediate state where some of the action's mutations have
applied but others haven't — because all of `action`'s state
mutations happen "between" the acquire fold and the release fold.

The formal statement: the result of `withLockSet S core action s`
is determined by `action`'s result on the post-acquire state, plus
the deterministic release-fold afterwards.  Whether or not the
release-fold modifies the state visibly to other cores depends on
the lock-bridge layer (SM2.D's typed FFI wrappers); from the
abstract Lean state perspective, the release simply un-marks the
locks. -/
theorem lockSet_atomic_under_2pl {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    let acquired := acquireAll core S.lockAcquireSequence s
    let (postAction, result) := action acquired
    withLockSet S core action s =
      (unwindAll core S.lockAcquireSequence.reverse postAction, result) := by
  rfl

-- ============================================================================
-- §4b — SM3.C.7 — Observational atomicity (lock-insensitive observer)
-- ============================================================================
--
-- The structural decomposition above (`lockSet_atomic_under_2pl`) records the
-- 3-phase shape definitionally.  The theorems below give the *substantive*
-- atomicity content the plan's "atomic from observer view (Thm 2.1.10)"
-- contract asks for: an external observer whose view is **lock-insensitive**
-- (it projects only business state, not the lock-bookkeeping fields) cannot
-- observe ANY effect of the acquire fold or the release fold — it sees exactly
-- the action's mutation, with the entire 2PL lock machinery invisible.  No
-- intermediate state in which "some of the action's mutations applied and
-- others did not" is observable, because the observer's projection is
-- unchanged across both folds and changes only through `action`.

/-- WS-SM SM3.C.7: a state projection `π` is **acquire-insensitive** for `core`
when acquiring any lock leaves `π` unchanged.  Business-state observers (the
object keyset, per-object kind tags, scheduler fields, IPC queues, …) are
acquire-insensitive because `acquireLockOnObject` only advances `RwLockState`
fields. -/
def AcquireInsensitive {β : Type} (core : CoreId) (π : SystemState → β) : Prop :=
  ∀ (s : SystemState) (l : LockId) (m : AccessMode),
    π (acquireLockOnObject s core l m) = π s

/-- WS-SM SM3.C.7 (broadened at **WS-LC LC4.5**): the shrinking-phase
counterpart of `AcquireInsensitive` — the projection is unchanged by either
step the shrinking phase takes at a member.

Two clauses, because the shrinking phase is two operations since LC4.1: it
**withdraws** and then **releases**, since a release is the identity for a
core that is not a holder and so could not give back the members the growing
phase only managed to queue on.  Naming the predicate after the *phase*
rather than after one of its halves is deliberate — a separate
`CancelInsensitive` beside a `UnwindInsensitive` would be one question with
two answers, and the capstones would then have to remember to demand both.

Discharging it costs nothing over the old single clause: both operations
write the same `lock` fields through the same two writers, so a witness for
one is the witness for the other with a single name changed. -/
def UnwindInsensitive {β : Type} (core : CoreId) (π : SystemState → β) : Prop :=
  (∀ (s : SystemState) (l : LockId) (m : AccessMode),
    π (releaseLockOnObject s core l m) = π s) ∧
  (∀ (s : SystemState) (l : LockId) (m : AccessMode),
    π (cancelLockOnObject s core l m) = π s)

/-- WS-SM SM3.C.7: the acquire fold is invisible to an acquire-insensitive
observer — `π (acquireAll core pairs s) = π s`.  Induction on the sequence. -/
theorem acquireAll_lockInsensitive {β : Type} (core : CoreId) (π : SystemState → β)
    (h : AcquireInsensitive core π) :
    ∀ (pairs : List (LockId × AccessMode)) (s : SystemState),
      π (acquireAll core pairs s) = π s := by
  intro pairs
  induction pairs with
  | nil => intro s; rfl
  | cons head tail ih =>
      intro s
      show π (acquireAll core tail (acquireLockOnObject s core head.fst head.snd)) = π s
      rw [ih (acquireLockOnObject s core head.fst head.snd)]
      exact h s head.fst head.snd

/-- WS-SM SM3.C.7: the release fold is invisible to a release-insensitive
observer — `π (releaseAll core pairs s) = π s`. -/
theorem releaseAll_lockInsensitive {β : Type} (core : CoreId) (π : SystemState → β)
    (h : UnwindInsensitive core π) :
    ∀ (pairs : List (LockId × AccessMode)) (s : SystemState),
      π (releaseAll core pairs s) = π s := by
  intro pairs
  induction pairs with
  | nil => intro s; rfl
  | cons head tail ih =>
      intro s
      show π (releaseAll core tail (releaseLockOnObject s core head.fst head.snd)) = π s
      rw [ih (releaseLockOnObject s core head.fst head.snd)]
      exact h.1 s head.fst head.snd

/-- **WS-LC LC4.5**: the withdrawal fold is invisible to the same observer. -/
theorem cancelAll_lockInsensitive {β : Type} (core : CoreId) (π : SystemState → β)
    (h : UnwindInsensitive core π) :
    ∀ (pairs : List (LockId × AccessMode)) (s : SystemState),
      π (cancelAll core pairs s) = π s := by
  intro pairs
  induction pairs with
  | nil => intro s; rfl
  | cons head tail ih =>
      intro s
      show π (cancelAll core tail (cancelLockOnObject s core head.fst head.snd)) = π s
      rw [ih (cancelLockOnObject s core head.fst head.snd)]
      exact h.2 s head.fst head.snd

/-- **WS-LC LC4.5**: hence the whole shrinking phase is. -/
theorem unwindAll_lockInsensitive {β : Type} (core : CoreId) (π : SystemState → β)
    (h : UnwindInsensitive core π) :
    ∀ (pairs : List (LockId × AccessMode)) (s : SystemState),
      π (unwindAll core pairs s) = π s := by
  intro pairs s
  rw [unwindAll_eq_releaseAll_cancelAll, releaseAll_lockInsensitive core π h,
      cancelAll_lockInsensitive core π h]

/-- WS-SM SM3.C.7 (plan §5.3 Theorem 2.1.10, **observational** form): for a
release-insensitive observer `π`, the post-`withLockSet` projection equals the
projection of the action applied to the post-acquire state — the release fold
contributes nothing observable.  Lifts `releaseAll_lockInsensitive` through
`withLockSet_fst`. -/
theorem withLockSet_unwind_invisible {α β : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (π : SystemState → β) (hRel : UnwindInsensitive core π) :
    π (withLockSet S core action s).1
      = π (action (acquireAll core S.lockAcquireSequence s)).1 := by
  rw [withLockSet_fst]
  exact unwindAll_lockInsensitive core π hRel S.lockAcquireSequence.reverse _

/-- WS-SM SM3.C.7 (plan §5.3 Theorem 2.1.10, observer-atomicity capstone): for
an observer `π` that is BOTH acquire- and release-insensitive, the entire 2PL
lock machinery is invisible.  Concretely, two facts hold simultaneously:

* the action runs on a state whose `π`-projection equals the pre-state's
  (`π (acquireAll …) = π s`), and
* the post-`withLockSet` projection equals the action's projection
  (`π (withLockSet …).1 = π (action …).1`).

Together: from the observer's view the transition is atomic — it sees `π s`
before and the action's `π`-image after, never a partial state arising from
the lock acquire/release folds.  This is the honest, abstract-model form of
"no observer without a conflicting lock sees an intermediate state": for a
lock-insensitive observer there IS no observable intermediate, because the
folds are projection-invariant and only `action` moves `π`. -/
theorem lockSet_observer_atomic {α β : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (π : SystemState → β)
    (hAcq : AcquireInsensitive core π) (hRel : UnwindInsensitive core π) :
    π (acquireAll core S.lockAcquireSequence s) = π s ∧
    π (withLockSet S core action s).1
      = π (action (acquireAll core S.lockAcquireSequence s)).1 :=
  ⟨acquireAll_lockInsensitive core π hAcq S.lockAcquireSequence s,
   withLockSet_unwind_invisible S core action s π hRel⟩

-- ============================================================================
-- §4c — WS-SM SM6.E: guarded observer atomicity
-- ============================================================================
-- The unguarded `AcquireInsensitive` quantifies over ALL states, which only
-- observers of lock-free *fields* (scheduler, registries) can satisfy.
-- Observers that read the **object store** (per-object business fields
-- through `getTcb?` etc.) are insensitive only on states satisfying the
-- RHTable extension invariant `invExt` — the per-object lock write is an
-- `updateObjectAt` insert, whose lookup frames need it.  The `On`-family
-- below is the `P`-guarded generalisation: insensitivity holds on `P`-states
-- and the guard is threaded through the folds by a stability hypothesis.

/-- WS-SM SM6.E: `P`-guarded acquire-insensitivity — the projection is
unchanged by any single lock acquire *on states satisfying `P`*. -/
def AcquireInsensitiveOn {β : Type} (P : SystemState → Prop) (core : CoreId)
    (π : SystemState → β) : Prop :=
  ∀ (s : SystemState) (l : LockId) (m : AccessMode),
    P s → π (acquireLockOnObject s core l m) = π s

/-- WS-SM SM6.E (broadened at **WS-LC LC4.5**): the shrinking-phase
counterpart of `AcquireInsensitiveOn`.  Two clauses, for the reason
`UnwindInsensitive` gives. -/
def UnwindInsensitiveOn {β : Type} (P : SystemState → Prop) (core : CoreId)
    (π : SystemState → β) : Prop :=
  (∀ (s : SystemState) (l : LockId) (m : AccessMode),
    P s → π (releaseLockOnObject s core l m) = π s) ∧
  (∀ (s : SystemState) (l : LockId) (m : AccessMode),
    P s → π (cancelLockOnObject s core l m) = π s)

/-- **WS-RR RR7.4**: an observer that reads only the object store, and that a
lock-field-only write leaves alone, is insensitive to **all three** lock
primitives at once.

The two hypotheses are the whole content, stated where the primitives are
rather than re-derived per observer:

* `hObjectsOnly` — `π` is a function of `SystemState.objects`.  This discharges
  the `.objStore` arm, which advances the state-level `objStoreLock` field and
  touches no object, and the `.page` arm, which is the identity.
* `hLockWrite` — a lock-field-only object write is invisible to `π`.  This
  discharges the eight per-object arms, all of which are `updateObjectLockAt`.

Before RR7.4 every observer restated the same three-way case analysis, once per
primitive: four copies in `Cancellation.lean` alone, and the five SM6
transitions this row covers would have added ten more.  One question, one
answer. -/
theorem lockPrimitives_insensitiveOn_of_objectStoreObserver {β : Type}
    (core : CoreId) (π : SystemState → β)
    (hObjectsOnly : ∀ s₁ s₂ : SystemState, s₁.objects = s₂.objects → π s₁ = π s₂)
    (hLockWrite : ∀ (s : SystemState) (l : LockId) (op : RwLockOp),
      s.objects.invExt → π (updateObjectLockAt s l op) = π s) :
    AcquireInsensitiveOn (fun s => s.objects.invExt) core π ∧
    UnwindInsensitiveOn (fun s => s.objects.invExt) core π := by
  refine ⟨?_, ?_, ?_⟩
  · intro s l m hExt
    unfold acquireLockOnObject
    cases l.kind <;> first
      | exact hObjectsOnly _ _ rfl
      | exact hLockWrite s l _ hExt
  · intro s l m hExt
    unfold releaseLockOnObject
    cases l.kind <;> first
      | exact hObjectsOnly _ _ rfl
      | exact hLockWrite s l _ hExt
  · intro s l m hExt
    unfold cancelLockOnObject
    cases l.kind <;> first
      | exact hObjectsOnly _ _ rfl
      | exact hLockWrite s l _ hExt

-- ---------------------------------------------------------------------------
-- WS-RR RR7.4: the two shared decisive observers of the IPC surface
--
-- Register §4 finding 7: every `_atomic_under_lockSet` theorem is a `rfl`
-- instance of the body-agnostic `lockSet_atomic_under_2pl`, and the
-- *substantive* form `lockSet_observer_atomic_on` was instantiated at exactly
-- two sites, both cancellation.  The five remaining SM6 transitions —
-- `endpointCall`, `endpointReply`, `endpointReplyRecv`, `notificationSignal`,
-- `notificationWait` — each need an observer and its two insensitivity facts,
-- and every one of them watches either a thread's IPC state or a
-- notification's delivery state.  Two observers, declared once, rather than
-- five copies of each.
--
-- Parameterised by an arbitrary thread / notification rather than by "the"
-- decisive one: the capstones then hold for *every* choice, which is strictly
-- stronger than picking the receiver, and removes the judgement call about
-- which participant a composite transition's decisive observable is.
-- ---------------------------------------------------------------------------

/-- **WS-RR RR7.4**: a thread's IPC state — the field every IPC rendezvous
writes and the one a partially-locked intermediate would expose. -/
def threadIpcStateObserver (tid : SeLe4n.ThreadId) : SystemState → Option ThreadIpcState :=
  fun s => (s.getTcb? tid).map TCB.ipcState

/-- **WS-RR RR7.4**: a notification's delivery state — its `state` (which
carries the pending badge) and its waiter list, as one projection so a caller
cannot watch half of the rendezvous. -/
def notificationDeliveryObserver (nid : SeLe4n.ObjId) :
    SystemState → Option (NotificationState × SeLe4n.NoDupList SeLe4n.ThreadId) :=
  fun s => (s.getNotification? nid).map (fun n => (n.state, n.waitingThreads))

/-- **WS-RR RR7.4**: the thread-IPC-state observer is blind to all three lock
primitives, under the object-store guard. -/
theorem threadIpcStateObserver_insensitiveOn (core : CoreId) (tid : SeLe4n.ThreadId) :
    AcquireInsensitiveOn (fun s => s.objects.invExt) core (threadIpcStateObserver tid) ∧
    UnwindInsensitiveOn (fun s => s.objects.invExt) core (threadIpcStateObserver tid) :=
  lockPrimitives_insensitiveOn_of_objectStoreObserver core _
    (fun _ _ h => by simp only [threadIpcStateObserver, SystemState.getTcb?, h])
    (fun s l op hExt => updateObjectLockAt_getTcb?_ipcState s l op tid hExt)

/-- **WS-RR RR7.4**: and so is the notification-delivery observer. -/
theorem notificationDeliveryObserver_insensitiveOn (core : CoreId) (nid : SeLe4n.ObjId) :
    AcquireInsensitiveOn (fun s => s.objects.invExt) core
      (notificationDeliveryObserver nid) ∧
    UnwindInsensitiveOn (fun s => s.objects.invExt) core
      (notificationDeliveryObserver nid) :=
  lockPrimitives_insensitiveOn_of_objectStoreObserver core _
    (fun _ _ h => by simp only [notificationDeliveryObserver, SystemState.getNotification?, h])
    (fun s l op hExt => updateObjectLockAt_getNotification?_delivery s l op nid hExt)

/-- WS-SM SM6.E: the acquire fold is invisible to a `P`-guardedly
acquire-insensitive observer, and threads the guard — provided `P` is stable
under single acquires. -/
theorem acquireAll_lockInsensitiveOn {β : Type} (P : SystemState → Prop)
    (core : CoreId) (π : SystemState → β)
    (hIns : AcquireInsensitiveOn P core π)
    (hStable : ∀ s l m, P s → P (acquireLockOnObject s core l m)) :
    ∀ (pairs : List (LockId × AccessMode)) (s : SystemState), P s →
      π (acquireAll core pairs s) = π s ∧ P (acquireAll core pairs s) := by
  intro pairs
  induction pairs with
  | nil => intro s hP; exact ⟨rfl, hP⟩
  | cons head tail ih =>
      intro s hP
      have hP' := hStable s head.fst head.snd hP
      have hTail := ih (acquireLockOnObject s core head.fst head.snd) hP'
      refine ⟨?_, hTail.2⟩
      show π (acquireAll core tail (acquireLockOnObject s core head.fst head.snd))
        = π s
      rw [hTail.1]
      exact hIns s head.fst head.snd hP

/-- WS-SM SM6.E: the release fold is invisible to a `P`-guardedly
release-insensitive observer, and threads the guard. -/
theorem releaseAll_lockInsensitiveOn {β : Type} (P : SystemState → Prop)
    (core : CoreId) (π : SystemState → β)
    (hIns : UnwindInsensitiveOn P core π)
    (hStable : ∀ s l m, P s → P (releaseLockOnObject s core l m)) :
    ∀ (pairs : List (LockId × AccessMode)) (s : SystemState), P s →
      π (releaseAll core pairs s) = π s ∧ P (releaseAll core pairs s) := by
  intro pairs
  induction pairs with
  | nil => intro s hP; exact ⟨rfl, hP⟩
  | cons head tail ih =>
      intro s hP
      have hP' := hStable s head.fst head.snd hP
      have hTail := ih (releaseLockOnObject s core head.fst head.snd) hP'
      refine ⟨?_, hTail.2⟩
      show π (releaseAll core tail (releaseLockOnObject s core head.fst head.snd))
        = π s
      rw [hTail.1]
      exact hIns.1 s head.fst head.snd hP

/-- **WS-LC LC4.5**: the withdrawal fold, guarded the same way. -/
theorem cancelAll_lockInsensitiveOn {β : Type} (P : SystemState → Prop)
    (core : CoreId) (π : SystemState → β)
    (hIns : UnwindInsensitiveOn P core π)
    (hStable : ∀ s l m, P s → P (cancelLockOnObject s core l m)) :
    ∀ (pairs : List (LockId × AccessMode)) (s : SystemState), P s →
      π (cancelAll core pairs s) = π s ∧ P (cancelAll core pairs s) := by
  intro pairs
  induction pairs with
  | nil => intro s hP; exact ⟨rfl, hP⟩
  | cons head tail ih =>
      intro s hP
      have hP' := hStable s head.fst head.snd hP
      have hTail := ih (cancelLockOnObject s core head.fst head.snd) hP'
      refine ⟨?_, hTail.2⟩
      show π (cancelAll core tail (cancelLockOnObject s core head.fst head.snd))
        = π s
      rw [hTail.1]
      exact hIns.2 s head.fst head.snd hP

/-- **WS-LC LC4.5**: hence the whole guarded shrinking phase. -/
theorem unwindAll_lockInsensitiveOn {β : Type} (P : SystemState → Prop)
    (core : CoreId) (π : SystemState → β)
    (hIns : UnwindInsensitiveOn P core π)
    (hRelStable : ∀ s l m, P s → P (releaseLockOnObject s core l m))
    (hCanStable : ∀ s l m, P s → P (cancelLockOnObject s core l m)) :
    ∀ (pairs : List (LockId × AccessMode)) (s : SystemState), P s →
      π (unwindAll core pairs s) = π s ∧ P (unwindAll core pairs s) := by
  intro pairs s hP
  have hCan := cancelAll_lockInsensitiveOn P core π hIns hCanStable pairs s hP
  have hRel := releaseAll_lockInsensitiveOn P core π hIns hRelStable pairs _ hCan.2
  exact ⟨by rw [unwindAll_eq_releaseAll_cancelAll, hRel.1, hCan.1],
    by rw [unwindAll_eq_releaseAll_cancelAll]; exact hRel.2⟩

/-- WS-SM SM6.E (guarded observer-atomicity capstone): the `P`-guarded
generalisation of `lockSet_observer_atomic` — for an observer insensitive on
`P`-states, with `P` stable under both lock primitives, holding on the
pre-state, and re-established by the action (the caller discharges this with
the action's own `P`-preservation theorem): the entire 2PL lock machinery is
invisible.  This is what makes object-store observers (per-object business
fields, guarded by `invExt`) usable in the observer-atomicity contract. -/
theorem lockSet_observer_atomic_on {α β : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (P : SystemState → Prop) (π : SystemState → β)
    (hAcq : AcquireInsensitiveOn P core π) (hRel : UnwindInsensitiveOn P core π)
    (hAcqStable : ∀ s' l m, P s' → P (acquireLockOnObject s' core l m))
    (hRelStable : ∀ s' l m, P s' → P (releaseLockOnObject s' core l m))
    -- WS-LC LC4.5: the shrinking phase withdraws before it releases, so the
    -- guard must survive a withdrawal too.  Every discharge in the tree is
    -- the release form with one name changed.
    (hCanStable : ∀ s' l m, P s' → P (cancelLockOnObject s' core l m))
    (hP : P s)
    (hActionP : P (action (acquireAll core S.lockAcquireSequence s)).1) :
    π (acquireAll core S.lockAcquireSequence s) = π s ∧
    π (withLockSet S core action s).1
      = π (action (acquireAll core S.lockAcquireSequence s)).1 := by
  refine ⟨(acquireAll_lockInsensitiveOn P core π hAcq hAcqStable
    S.lockAcquireSequence s hP).1, ?_⟩
  rw [withLockSet_fst]
  exact (unwindAll_lockInsensitiveOn P core π hRel hRelStable hCanStable
    S.lockAcquireSequence.reverse _ hActionP).1

/-- **WS-RR RR7.4**: the observer-atomicity capstone, packaged for the shape
every IPC transition has.

`lockSet_observer_atomic_on` takes six discharges, five of which are the same
every time: the observer's two insensitivity facts and the three lock
primitives' `invExt` stability.  Only the sixth — that the transition itself
preserves `invExt` on the acquired state — is the transition's own.  This
wrapper takes exactly that one, so an instantiation is one line and the five
SM6 transitions cannot each get the boilerplate subtly different. -/
theorem lockSet_observer_atomic_of_objectStoreObserver {α β : Type}
    (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) (π : SystemState → β)
    (hIns : AcquireInsensitiveOn (fun s => s.objects.invExt) core π ∧
            UnwindInsensitiveOn (fun s => s.objects.invExt) core π)
    (hInv : s.objects.invExt)
    (hActionInv : ∀ s', s'.objects.invExt → (action s').1.objects.invExt) :
    π (acquireAll core S.lockAcquireSequence s) = π s ∧
    π (withLockSet S core action s).1
      = π (action (acquireAll core S.lockAcquireSequence s)).1 := by
  have hAcqStable : ∀ (s' : SystemState) l m, s'.objects.invExt →
      (acquireLockOnObject s' core l m).objects.invExt :=
    fun s' l m h => acquireLockOnObject_preserves_invExt s' core l m h
  have hInvAcq : (acquireAll core S.lockAcquireSequence s).objects.invExt :=
    (acquireAll_lockInsensitiveOn _ core π hIns.1 hAcqStable _ s hInv).2
  exact lockSet_observer_atomic_on S core action s (fun st => st.objects.invExt) π
    hIns.1 hIns.2 hAcqStable
    (fun s' l m h => releaseLockOnObject_preserves_invExt s' core l m h)
    (fun s' l m h => cancelLockOnObject_preserves_invExt s' core l m h)
    hInv (hActionInv _ hInvAcq)

-- ============================================================================
-- §5 — SM3.C.8 — `lockSet_invariant_preserved` (Corollary 2.1.11)
-- ============================================================================

/-- WS-SM SM3.C.8 (plan §3.9 Corollary 2.1.11): the SMP-migration
metatheorem in *substantive* form.

The crucial fact that makes Corollary 2.1.11 hold "with the same
proof" is: **the lock acquire fold preserves every business-relevant
projection of the state.**  A single-core invariant `post` phrased
over a lock-insensitive projection (the object keyset, per-object
kind tags, scheduler fields, etc.) is preserved across the
`acquireAll` fold that `withLockSet` prepends to the action.

Concretely: if
* `post` holds on the pre-acquire state `s` (the single-core
  precondition), and
* `post` is preserved by `acquireLockOnObject` for every lock in
  the canonical sequence (the lock-insensitivity hypothesis,
  discharged once per invariant via the substantive structural
  lemmas `acquireLockOnObject_preserves_objStoreLock_of_modeled`
  and `updateObjectAt_preserves_objectType_at`),

then `post` holds on the post-acquire state that the action sees.

This is the genuine lever (not a tautology): it reduces the SMP
proof obligation to "the invariant is lock-insensitive", which is
discharged structurally for each invariant class.  The single-core
proof of the action itself is then reused verbatim.

The `hLockInsensitive` hypothesis is the lock-insensitivity
witness; SM4..SM6 phase migrations discharge it per invariant
using the WithLockSet structural-preservation lemmas. -/
theorem lockSet_invariant_preserved (S : LockSet) (core : CoreId)
    (s : SystemState)
    (post : SystemState → Prop)
    (hPre : post s)
    (hLockInsensitive : ∀ (l : LockId) (m : AccessMode) (s' : SystemState),
      post s' → post (acquireLockOnObject s' core l m)) :
    post (acquireAll core S.lockAcquireSequence s) := by
  -- The acquire fold preserves `post` by the lock-insensitivity
  -- hypothesis, applied stepwise.
  unfold acquireAll
  -- Generalize over the sorted sequence and induct.
  have hFold : ∀ (pairs : List (LockId × AccessMode)) (s₀ : SystemState),
      post s₀ →
      post (pairs.foldl
        (fun st p => acquireLockOnObject st core p.fst p.snd) s₀) := by
    intro pairs
    induction pairs with
    | nil => intro s₀ h; exact h
    | cons head rest ih =>
      intro s₀ h
      simp only [List.foldl_cons]
      apply ih
      exact hLockInsensitive head.fst head.snd s₀ h
  exact hFold S.lockAcquireSequence s hPre

/-- WS-SM SM3.C.8 corollary: the *full* 2PL invariant-preservation
form — under lock-insensitivity for both acquire and release, the
entire `withLockSet`-wrapped transition preserves a lock-insensitive
invariant whenever the bare action does.

This composes the acquire-fold preservation (`lockSet_invariant_preserved`)
with the action's single-core preservation and the release-fold
preservation, yielding the full Corollary 2.1.11 closure that
SM4..SM6 phase migrations consume. -/
theorem withLockSet_invariant_preserved {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState)
    (post : SystemState → Prop)
    (hPre : post s)
    (hAcquireInsensitive : ∀ (l : LockId) (m : AccessMode) (s' : SystemState),
      post s' → post (acquireLockOnObject s' core l m))
    (hActionPreserves : ∀ s', post s' → post (action s').1)
    (hReleaseInsensitive : ∀ (l : LockId) (m : AccessMode) (s' : SystemState),
      post s' → post (releaseLockOnObject s' core l m))
    -- WS-LC LC4.5: the shrinking phase withdraws before it releases, so an
    -- invariant carried across the bracket must survive a withdrawal too.
    (hCancelInsensitive : ∀ (l : LockId) (m : AccessMode) (s' : SystemState),
      post s' → post (cancelLockOnObject s' core l m)) :
    post (withLockSet S core action s).1 := by
  rw [withLockSet_fst]
  -- Phase 1: acquire fold preserves post.
  have hAfterAcquire : post (acquireAll core S.lockAcquireSequence s) :=
    lockSet_invariant_preserved S core s post hPre hAcquireInsensitive
  -- Phase 2: action preserves post.
  have hAfterAction : post (action (acquireAll core S.lockAcquireSequence s)).1 :=
    hActionPreserves _ hAfterAcquire
  -- Phase 3: the shrinking phase preserves post — the withdrawal fold, then
  -- the release fold (WS-LC LC4.5).
  have hRelFold : ∀ (pairs : List (LockId × AccessMode)) (s₀ : SystemState),
      post s₀ →
      post (pairs.foldl
        (fun st p => releaseLockOnObject st core p.fst p.snd) s₀) := by
    intro pairs
    induction pairs with
    | nil => intro s₀ h; exact h
    | cons head rest ih =>
      intro s₀ h
      simp only [List.foldl_cons]
      apply ih
      exact hReleaseInsensitive head.fst head.snd s₀ h
  have hCanFold : ∀ (pairs : List (LockId × AccessMode)) (s₀ : SystemState),
      post s₀ →
      post (pairs.foldl
        (fun st p => cancelLockOnObject st core p.fst p.snd) s₀) := by
    intro pairs
    induction pairs with
    | nil => intro s₀ h; exact h
    | cons head rest ih =>
      intro s₀ h
      simp only [List.foldl_cons]
      apply ih
      exact hCancelInsensitive head.fst head.snd s₀ h
  show post (unwindAll core S.lockAcquireSequence.reverse
    (action (acquireAll core S.lockAcquireSequence s)).1)
  rw [unwindAll_eq_releaseAll_cancelAll]
  unfold releaseAll
  exact hRelFold S.lockAcquireSequence.reverse _
    (hCanFold S.lockAcquireSequence.reverse _ hAfterAction)

/-- WS-SM SM3.C.8 (audit-pass-2): **worked instantiation** of
`lockSet_invariant_preserved` — demonstrates the metatheorem's lever
is genuinely dischargeable, not merely well-typed.

Concretely: the acquire fold preserves the well-formedness of the
table-level `objStoreLock`.  The `hLockInsensitive` hypothesis is
discharged here for the invariant `post := fun st => st.objStoreLock.wf`:

* for a per-object lock (kind ≠ `.objStore`), `acquireLockOnObject`
  leaves `objStoreLock` untouched
  (`acquireLockOnObject_preserves_objStoreLock_of_modeled`), so `wf`
  is trivially preserved;
* for the `.objStore` lock, `objStoreLock` advances via
  `RwLockState.applyOp`, and SM2.C's per-op wf-preservation
  (`rwLock_tryAcquireRead/Write_preserves_wf`) keeps it well-formed.

This proves the SM3.C.8 contract is usable: a real, lock-insensitive
kernel invariant (the table lock's well-formedness) survives the
2PL acquire fold.  It is the concrete witness that the metatheorem
is not a vacuous false-anchor. -/
theorem acquireAll_preserves_objStoreLock_wf (S : LockSet) (core : CoreId)
    (s : SystemState) (hwf : s.objStoreLock.wf) :
    (acquireAll core S.lockAcquireSequence s).objStoreLock.wf := by
  apply lockSet_invariant_preserved S core s
    (fun st => st.objStoreLock.wf) hwf
  -- Discharge hLockInsensitive: acquiring any lock preserves objStoreLock.wf.
  intro l m s' hs'
  by_cases hKind : l.kind = .objStore
  · -- objStore lock: objStoreLock advances via applyOp, which preserves wf.
    unfold acquireLockOnObject
    rw [hKind]
    simp only
    -- Post objStoreLock = s'.objStoreLock.applyOp (m.toAcquireOp core).
    cases m with
    | read => exact rwLock_tryAcquireRead_preserves_wf _ core hs'
    | write => exact rwLock_tryAcquireWrite_preserves_wf _ core hs'
  · -- per-object lock: objStoreLock unchanged.
    rw [acquireLockOnObject_preserves_objStoreLock_of_modeled s' core l m hKind]
    exact hs'

/-- WS-SM SM3.C.8 (audit-pass-1, Comment 7): **substantive**
acquire-establishes-holding theorem — replaces the previous
tautological `_unchanged_outside_lockSet` placeholder the codex
review correctly flagged as a false verification anchor.

Under the precondition that the table-level `objStoreLock` is
**available** (`unheld`), acquiring it via `acquireLockOnObject`
produces a state where the lock is genuinely **held** by `core`
in the requested mode — `lockHeld core ⟨.objStore, oid⟩ mode`
holds on the post-acquire state.

This is the honest bridge the reviewer asked for: it actually
involves the acquire phase and the transformed state, proving that
on an available lock the action runs with the lock held (not merely
`hHeld → hHeld`).  Lifts `RwLockState.unheld_acquire_grants`
through the `acquireLockOnObject` `.objStore` branch and the
`lockHeld` `.objStore` projection. -/
theorem acquireLockOnObject_objStore_establishes_lockHeld
    (s : SystemState) (core : CoreId) (oid : SeLe4n.ObjId) (mode : AccessMode)
    (hAvail : s.objStoreLock = RwLockState.unheld) :
    lockHeld core ⟨.objStore, oid⟩ mode
      (acquireLockOnObject s core ⟨.objStore, oid⟩ mode) := by
  -- The objStore branch sets objStoreLock := s.objStoreLock.applyOp …
  unfold acquireLockOnObject lockHeld
  simp only
  -- Post-state objStoreLock = unheld.applyOp (mode.toAcquireOp core).
  rw [hAvail]
  exact RwLockState.unheld_acquire_grants core mode

/-- WS-SM SM3.C.8 (audit-pass-1, Comment 4): acquiring then releasing
the table-level lock from an **available** state returns it to
`unheld` — NO waiter leak.

Refutes the waiter-leak concern for the abstract single-core model:
because the acquire GRANTED (the lock was available), the symmetric
release cleanly removes the holder and the lock round-trips to
`unheld`.  Lifts `RwLockState.unheld_acquire_release_roundtrip`
through the `acquireLockOnObject` / `releaseLockOnObject`
`.objStore` branches. -/
theorem acquireLockOnObject_objStore_release_roundtrip
    (s : SystemState) (core : CoreId) (oid : SeLe4n.ObjId) (mode : AccessMode)
    (hAvail : s.objStoreLock = RwLockState.unheld) :
    (releaseLockOnObject (acquireLockOnObject s core ⟨.objStore, oid⟩ mode)
      core ⟨.objStore, oid⟩ mode).objStoreLock = RwLockState.unheld := by
  unfold acquireLockOnObject releaseLockOnObject
  simp only
  rw [hAvail]
  exact RwLockState.unheld_acquire_release_roundtrip core mode

/-- WS-SM SM3.C.8 helper: two `LockId`s with equal `kind` and `objId`
components are equal (`LockId` carries exactly those two fields). -/
theorem lockId_eq_of_components {l₁ l₂ : LockId}
    (hk : l₁.kind = l₂.kind) (ho : l₁.objId = l₂.objId) : l₁ = l₂ := by
  cases l₁; cases l₂; simp_all

/-- WS-SM SM3.C.8 foundation: in a well-formed `LockSet` whose every pair
resolves to a present object of matching kind, the canonical acquisition
sequence has pairwise-distinct ObjIds.

Two pairs sharing an ObjId would both resolve to the object stored there, hence
have that object's `lockKind`, hence the same `kind` AND the same `objId`, hence
the same `LockId` key — contradicting the `Nodup`-keys invariant
(`LockSet.fst_inj_at_pairs`).  This is why the SM3.C.8 multi-lock establishment
hypothesis (distinct ObjIds) is automatically met by any state-resolvable
lock set. -/
theorem lockAcquireSequence_distinct_objId_of_resolves (S : LockSet)
    (s : SystemState)
    (hEach : ∀ p ∈ S.pairs, ∃ o, s.objects[p.fst.objId]? = some o ∧
        o.lockKind = p.fst.kind) :
    S.lockAcquireSequence.Pairwise (fun a b => a.fst.objId ≠ b.fst.objId) := by
  have hPairsNodup : S.pairs.Nodup :=
    (List.pairwise_map.mp S.hUniqueKeys).imp
      (fun hfst heq => hfst (congrArg Prod.fst heq))
  have hSeqNodup : S.lockAcquireSequence.Nodup :=
    (LockSet.lockAcquireSequence_perm S).nodup_iff.mpr hPairsNodup
  refine hSeqNodup.imp_of_mem ?_
  intro a b ha hb hab hObjEq
  apply hab
  have haP : a ∈ S.pairs :=
    (LockSet.mem_def a S).mp ((LockSet.lockAcquireSequence_complete S a).mpr ha)
  have hbP : b ∈ S.pairs :=
    (LockSet.mem_def b S).mp ((LockSet.lockAcquireSequence_complete S b).mpr hb)
  obtain ⟨oa, hPa, hKa⟩ := hEach a haP
  obtain ⟨ob, hPb, hKb⟩ := hEach b hbP
  have hoEq : oa = ob := by
    have hObj : s.objects[a.fst.objId]? = s.objects[b.fst.objId]? := by rw [hObjEq]
    rw [hPa, hPb] at hObj
    exact Option.some.inj hObj
  have hKindEq : a.fst.kind = b.fst.kind := by rw [← hKa, hoEq, hKb]
  exact LockSet.fst_inj_at_pairs S haP hbP (lockId_eq_of_components hKindEq hObjEq)

/-- WS-SM SM3.C.8 (substantive — the LockSet-level "acquireAll establishes
lockSetHeld" theorem): `withLockSet`'s growing phase genuinely puts the
declared lock set into the held state.

If every lock in `S` resolves to a present, kind-matching, `unheld` object in
the pre-state `s`, then after the canonical acquire fold the executing `core`
holds the entire lock set: `lockSetHeld core S (acquireAll core
S.lockAcquireSequence s)`.

This is the bridge the SM3.C.8 metatheorem's `lockSetHeld` precondition rests
on — it is not an arbitrary assumption but a *consequence* of the 2PL growing
phase on an available lock set.  Combines the multi-lock establishment
(`acquireAll_establishes_lockHeld_of_distinct_present_unheld`) with the
automatic ObjId-distinctness
(`lockAcquireSequence_distinct_objId_of_resolves`) and the
sequence ↔ pairs membership bridge (`lockAcquireSequence_complete`). -/
theorem acquireAll_establishes_lockSetHeld (S : LockSet) (core : CoreId)
    (s : SystemState)
    (hExt : s.objects.invExt)
    (hEach : ∀ p ∈ S.pairs, ∃ o, s.objects[p.fst.objId]? = some o ∧
        o.lockKind = p.fst.kind ∧ o.objectLockOf = RwLockState.unheld) :
    lockSetHeld core S (acquireAll core S.lockAcquireSequence s) := by
  have hEachSeq : ∀ p ∈ S.lockAcquireSequence, ∃ o,
      s.objects[p.fst.objId]? = some o ∧ o.lockKind = p.fst.kind ∧
      o.objectLockOf = RwLockState.unheld := fun p hp =>
    hEach p ((LockSet.mem_def p S).mp ((LockSet.lockAcquireSequence_complete S p).mpr hp))
  have hDistinct := lockAcquireSequence_distinct_objId_of_resolves S s
    (fun p hp => by obtain ⟨o, h1, h2, _⟩ := hEach p hp; exact ⟨o, h1, h2⟩)
  have hAll := acquireAll_establishes_lockHeld_of_distinct_present_unheld core
    S.lockAcquireSequence s hExt hEachSeq hDistinct
  intro p hp
  exact hAll p ((LockSet.lockAcquireSequence_complete S p).mp ((LockSet.mem_def p S).mpr hp))

-- ============================================================================
-- §6 — SM3.C aggregator theorems (architectural anchors)
-- ============================================================================

/-- WS-SM SM3.C aggregate: every `withLockSet` invocation acquires
in ascending order AND releases in descending order.

This is the strict-2PL aggregator that combines SM3.C.5 and
SM3.C.6 into a single witness — useful as an architectural anchor
for SM3.D's deadlock-freedom proof. -/
theorem withLockSet_satisfies_strict_2PL (S : LockSet) :
    (acquireOrder S).Pairwise (· ≤ ·) ∧
    (releaseOrder S).Pairwise (· ≥ ·) :=
  ⟨lockSet_acquired_in_order S, lockSet_released_in_reverse S⟩

/-- WS-SM SM3.C aggregate: `withLockSet` produces the same result
state as `action` composed with `releaseAll` on the canonically-
ordered lock set, threaded through `acquireAll` on the pre-state.

This is the canonical "what does `withLockSet` compute" witness —
useful for SM3.E.3's serializability proof's serial-equivalent
construction. -/
theorem withLockSet_computation {α : Type} (S : LockSet) (core : CoreId)
    (action : SystemState → SystemState × α) (s : SystemState) :
    withLockSet S core action s =
      ( unwindAll core S.lockAcquireSequence.reverse
          (action (acquireAll core S.lockAcquireSequence s)).1,
        (action (acquireAll core S.lockAcquireSequence s)).2 ) :=
  withLockSet_eq_decomposition S core action s

end SeLe4n.Kernel.Concurrency
