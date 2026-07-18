-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Architecture.TlbShootdownProtocol
import SeLe4n.Kernel.Concurrency.Locks.Kind

/-!
# WS-SM SM7.B.7 — The shootdown round's lock-set

The cross-domain lock order and declared 2PL write footprint of a
TLB-shootdown round, discharging the SM7.A audit's registered
obligation: rounds are serialised system-wide under the single global
`ShootdownRoundLockId`, acquired after the initiating operation's
VSpaceRoot object lock and before any per-core
`ShootdownQueueLockId`.

## Why a new cross-domain sum

The round lock and the per-core queue locks are keyed by round /
`CoreId`, not by `ObjId`, so they are not `LockKind`/`LockId` members
(the SM0.I ten-kind object hierarchy is deliberately closed).
`TlbShootdownLockId` is the protocol's unified order — the exact
`SchedLockId` pattern (SM5.A.2), with the object domain below the
round lock below the queue domain:

    object (LockId lex order)  <  round (unique)  <  queue (by core)

* **object < round**: the §3.2 precondition — the initiator already
  holds the VSpaceRoot write lock of the address space it is
  invalidating when the round opens.
* **round < queue**: the SM7.A audit contract — the round lock is
  held before any queue is posted, and released only after
  `allAcked`, so the round-identity-free ack vector is a
  single-round resource (the interleaved-reset stale-TLB and
  mutual-hang modes are structurally excluded).
* **queue < queue by core**: ascending-core posting — defense-in-depth
  today (the round lock admits one poster at a time) and load-bearing
  under any post-1.0 relaxation to concurrent rounds.

## What `lockSet_tlbShootdown_correct` certifies

1. The acquisition sequence is strictly ascending in the unified
   order (deadlock-freedom along the SM3 lock-ladder argument) and
   duplicate-free.
2. The declared footprint covers the round's writes: the ack-vector
   reset/wait is under the round lock, each posted queue's write is
   under that core's queue lock, and the initiator's TLB-view write
   is under the object lock — including for the *diff-recovered*
   write set of the live coalescing commit
   (`lockSet_tlbShootdown_covers_commit`).
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- SM7.B.7 — The unified cross-domain lock identifier
-- ============================================================================

/-- **WS-SM SM7.B.7**: a lock in the shootdown round's footprint —
an SM0.I object-domain lock (the VSpaceRoot write lock of the §3.2
precondition), THE global round lock, or a per-core pending-queue
lock. -/
inductive TlbShootdownLockId where
  /-- An SM0.I object-domain lock, keyed `(LockKind, ObjId)` — the
  initiating operation's VSpaceRoot write lock. -/
  | object (l : Concurrency.LockId)
  /-- The single global shootdown-round lock (unique by
  `ShootdownRoundLockId.singleton`). -/
  | round (r : ShootdownRoundLockId)
  /-- Core `q.core`'s pending-shootdown-queue lock. -/
  | queue (q : ShootdownQueueLockId)
  deriving DecidableEq, Repr

namespace TlbShootdownLockId

/-- **WS-SM SM7.B.7**: the unified order — object locks by the SM0.I
lex order, the round lock above every object lock, queue locks above
both (by core among themselves). -/
protected def le : TlbShootdownLockId → TlbShootdownLockId → Prop
  | .object l₁, .object l₂ => l₁ ≤ l₂
  | .object _,  .round _   => True
  | .object _,  .queue _   => True
  | .round _,   .object _  => False
  | .round _,   .round _   => True
  | .round _,   .queue _   => True
  | .queue _,   .object _  => False
  | .queue _,   .round _   => False
  | .queue q₁,  .queue q₂  => q₁ ≤ q₂

/-- **WS-SM SM7.B.7**: strict order. -/
protected def lt (a b : TlbShootdownLockId) : Prop :=
  TlbShootdownLockId.le a b ∧ ¬ TlbShootdownLockId.le b a

instance decLeAux (a b : TlbShootdownLockId) :
    Decidable (TlbShootdownLockId.le a b) := by
  cases a <;> cases b <;> simp only [TlbShootdownLockId.le] <;> infer_instance

instance : LE TlbShootdownLockId := ⟨TlbShootdownLockId.le⟩
instance : LT TlbShootdownLockId := ⟨TlbShootdownLockId.lt⟩

instance (a b : TlbShootdownLockId) : Decidable (a ≤ b) := decLeAux a b
instance (a b : TlbShootdownLockId) : Decidable (a < b) :=
  inferInstanceAs (Decidable (TlbShootdownLockId.le a b ∧
    ¬ TlbShootdownLockId.le b a))

/-- SM7.B.7: reflexivity (each domain's reflexivity; the round arm is
trivially reflexive because the round lock is unique). -/
protected theorem le_refl (l : TlbShootdownLockId) : l ≤ l := by
  cases l with
  | object a => exact Concurrency.LockId.le_refl a
  | round r => exact True.intro
  | queue q => exact ShootdownQueueLockId.le_refl q

/-- SM7.B.7: transitivity across the three domains (cross-domain edges
only go upward, so no violation is possible). -/
protected theorem le_trans {a b c : TlbShootdownLockId}
    (h₁ : a ≤ b) (h₂ : b ≤ c) : a ≤ c := by
  cases a <;> cases b <;> cases c <;>
    first
      | exact Concurrency.LockId.le_trans _ _ _ h₁ h₂
      | exact ShootdownQueueLockId.le_trans h₁ h₂
      | exact True.intro
      | exact (h₁ : False).elim
      | exact (h₂ : False).elim

/-- SM7.B.7: antisymmetry (the round arm collapses by uniqueness). -/
protected theorem le_antisymm {a b : TlbShootdownLockId}
    (h₁ : a ≤ b) (h₂ : b ≤ a) : a = b := by
  cases a <;> cases b <;>
    first
      | exact congrArg TlbShootdownLockId.object
          (Concurrency.LockId.le_antisymm _ _ h₁ h₂)
      | exact congrArg TlbShootdownLockId.round
          (ShootdownRoundLockId.singleton _ _)
      | exact congrArg TlbShootdownLockId.queue
          (ShootdownQueueLockId.le_antisymm h₁ h₂)
      | exact (h₁ : False).elim
      | exact (h₂ : False).elim

/-- SM7.B.7: totality — any two locks in the footprint are comparable,
so the acquisition sequence can always be sorted ascending. -/
protected theorem le_total (a b : TlbShootdownLockId) : a ≤ b ∨ b ≤ a := by
  cases a <;> cases b <;>
    first
      | exact Concurrency.LockId.le_total _ _
      | exact ShootdownQueueLockId.le_total _ _
      | exact Or.inl True.intro
      | exact Or.inr True.intro

/-- SM7.B.7: strict-order irreflexivity. -/
protected theorem lt_irrefl (l : TlbShootdownLockId) : ¬ l < l :=
  fun h => h.2 h.1

/-- SM7.B.7: strict-order asymmetry — the lock-ladder property the
deadlock-freedom argument rests on. -/
protected theorem lt_asymm {a b : TlbShootdownLockId} (h : a < b) :
    ¬ b < a := fun h' => h.2 h'.1

/-- SM7.B.7: strictly-below is never equal. -/
protected theorem ne_of_lt {a b : TlbShootdownLockId} (h : a < b) :
    a ≠ b := by
  intro hEq
  subst hEq
  exact TlbShootdownLockId.lt_irrefl a h

/-- **WS-SM SM7.B.7** (cross-domain edge): every object-domain lock is
strictly below the round lock — the §3.2 precondition's VSpaceRoot
write lock is acquired before the round opens. -/
theorem object_lt_round (l : Concurrency.LockId) (r : ShootdownRoundLockId) :
    TlbShootdownLockId.object l < TlbShootdownLockId.round r :=
  ⟨True.intro, fun h => h⟩

/-- **WS-SM SM7.B.7** (cross-domain edge): the round lock is strictly
below every per-core queue lock — the SM7.A audit contract's
"`ShootdownRoundLockId` acquired before any per-core
`ShootdownQueueLockId`", now a theorem on the unified order. -/
theorem round_lt_queue (r : ShootdownRoundLockId)
    (q : ShootdownQueueLockId) :
    TlbShootdownLockId.round r < TlbShootdownLockId.queue q :=
  ⟨True.intro, fun h => h⟩

/-- **WS-SM SM7.B.7** (cross-domain edge): every object-domain lock is
strictly below every queue lock. -/
theorem object_lt_queue (l : Concurrency.LockId)
    (q : ShootdownQueueLockId) :
    TlbShootdownLockId.object l < TlbShootdownLockId.queue q :=
  ⟨True.intro, fun h => h⟩

/-- SM7.B.7: strict order between queue locks is strict core order. -/
theorem queue_lt_queue_iff (q₁ q₂ : ShootdownQueueLockId) :
    TlbShootdownLockId.queue q₁ < TlbShootdownLockId.queue q₂ ↔
      q₁.core.val < q₂.core.val := by
  constructor
  · intro ⟨hle, hnle⟩
    have hle' : q₁.core.val ≤ q₂.core.val := hle
    have hnle' : ¬ q₂.core.val ≤ q₁.core.val := hnle
    omega
  · intro h
    exact ⟨Nat.le_of_lt h, fun h' => Nat.not_le_of_lt h h'⟩

end TlbShootdownLockId

-- ============================================================================
-- SM7.B.7 — The round's canonical acquisition sequence
-- ============================================================================

/-- **WS-SM SM7.B.7**: the canonical lock-acquisition sequence of a
shootdown round initiated by `initiator` on the address space guarded
by `vspaceRootLock`:

    vspaceRootLock (W)  →  round lock  →  queue locks, ascending core

The initiating operation (unmap / remap / ASID retire / retype) holds
`vspaceRootLock` per its own SM3 lock-set; the round lock brackets the
entire round (release only after `allAcked` — the serialisation the
round-identity-free ack vector requires); each target's queue lock
guards that queue's posting write. -/
def lockSet_tlbShootdown (vspaceRootLock : Concurrency.LockId)
    (initiator : CoreId) : List TlbShootdownLockId :=
  TlbShootdownLockId.object vspaceRootLock ::
    TlbShootdownLockId.round ⟨⟩ ::
    (shootdownTargets initiator).map
      (fun c => TlbShootdownLockId.queue ⟨c⟩)

/-- **WS-SM SM7.B.7**: `allCores` is strictly ascending by core id —
the enumeration order the target set (and hence the queue-lock
sequence) inherits. -/
theorem allCores_pairwise_lt :
    List.Pairwise (fun a b : CoreId => a.val < b.val) allCores := by
  decide

/-- **WS-SM SM7.B.7**: the target set is strictly ascending by core id
(filtering preserves the `allCores` order). -/
theorem shootdownTargets_pairwise_lt (initiator : CoreId) :
    List.Pairwise (fun a b : CoreId => a.val < b.val)
      (shootdownTargets initiator) :=
  allCores_pairwise_lt.filter _

/-- **WS-SM SM7.B.7** (`lockSet_tlbShootdown_correct`): the round's
acquisition sequence is strictly ascending in the unified cross-domain
order — the object lock first, the round lock second, the queue locks
last in ascending core order.  Ascending acquisition along a total
order is exactly the SM3 lock-ladder deadlock-freedom shape: no cycle
of waiters can form among shootdown initiators and the operations
whose object locks they compose with. -/
theorem lockSet_tlbShootdown_correct (vspaceRootLock : Concurrency.LockId)
    (initiator : CoreId) :
    List.Pairwise (· < ·)
      (lockSet_tlbShootdown vspaceRootLock initiator) := by
  unfold lockSet_tlbShootdown
  refine List.Pairwise.cons ?_ (List.Pairwise.cons ?_ ?_)
  · intro b hb
    rcases List.mem_cons.mp hb with hEq | hMem
    · subst hEq
      exact TlbShootdownLockId.object_lt_round vspaceRootLock ⟨⟩
    · obtain ⟨c, _, hbc⟩ := List.mem_map.mp hMem
      rw [← hbc]
      exact TlbShootdownLockId.object_lt_queue vspaceRootLock ⟨c⟩
  · intro b hb
    obtain ⟨c, _, hbc⟩ := List.mem_map.mp hb
    rw [← hbc]
    exact TlbShootdownLockId.round_lt_queue ⟨⟩ ⟨c⟩
  · rw [List.pairwise_map]
    exact (shootdownTargets_pairwise_lt initiator).imp
      (fun h => (TlbShootdownLockId.queue_lt_queue_iff _ _).mpr h)

/-- **WS-SM SM7.B.7**: the acquisition sequence is duplicate-free — a
strictly ascending sequence visits each lock at most once (no
re-acquisition, the 2PL growing-phase discipline). -/
theorem lockSet_tlbShootdown_nodup (vspaceRootLock : Concurrency.LockId)
    (initiator : CoreId) :
    (lockSet_tlbShootdown vspaceRootLock initiator).Nodup :=
  (lockSet_tlbShootdown_correct vspaceRootLock initiator).imp
    (fun h => TlbShootdownLockId.ne_of_lt h)

/-- **WS-SM SM7.B.7**: the round lock is in the footprint — the
ack-vector reset, the initiator's `allAcked` wait, and the handler
catch-up commit are all bracketed by it. -/
theorem lockSet_tlbShootdown_round_mem (vspaceRootLock : Concurrency.LockId)
    (initiator : CoreId) :
    TlbShootdownLockId.round ⟨⟩ ∈
      lockSet_tlbShootdown vspaceRootLock initiator :=
  List.mem_cons_of_mem _ (List.mem_cons_self ..)

/-- **WS-SM SM7.B.7**: the initiating operation's VSpaceRoot lock is
in the footprint — the TLB-view write (the initiator's local
invalidation) and the page-table write it follows are under it. -/
theorem lockSet_tlbShootdown_object_mem (vspaceRootLock : Concurrency.LockId)
    (initiator : CoreId) :
    TlbShootdownLockId.object vspaceRootLock ∈
      lockSet_tlbShootdown vspaceRootLock initiator :=
  List.mem_cons_self ..

/-- **WS-SM SM7.B.7**: every target core's queue lock is in the
footprint — each posting write is guarded. -/
theorem lockSet_tlbShootdown_queue_mem (vspaceRootLock : Concurrency.LockId)
    (initiator : CoreId) {c : CoreId} (hc : c ≠ initiator) :
    TlbShootdownLockId.queue ⟨c⟩ ∈
      lockSet_tlbShootdown vspaceRootLock initiator := by
  unfold lockSet_tlbShootdown
  exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _
    (List.mem_map.mpr ⟨c, (mem_shootdownTargets_iff initiator c).mpr hc, rfl⟩))

/-- **WS-SM SM7.B.7** (footprint honesty): the declared queue-lock set
covers the live commit's *actual* write set — every core whose pending
queue the coalescing broadcast changed has its queue lock in the
footprint.  (A non-target core's queue is framed by the posting fold,
so a changed queue implies a target, which implies the lock.) -/
theorem lockSet_tlbShootdown_covers_commit (vspaceRootLock : Concurrency.LockId)
    (st : SystemState) (initiator : CoreId) (op : TlbInvalidation) :
    ∀ c ∈ shootdownChangedTargets st
      (tlbShootdownBroadcastCoalescing st initiator
        (shootdownTargets initiator) op),
      TlbShootdownLockId.queue ⟨c⟩ ∈
        lockSet_tlbShootdown vspaceRootLock initiator := by
  intro c hc
  rw [mem_shootdownChangedTargets_iff] at hc
  by_cases hci : c = initiator
  · -- the initiator is never a target, and a non-target's queue is
    -- framed by the whole posting pipeline — contradiction with the
    -- observed change.
    exfalso
    apply hc
    show (postShootdownRoundCoalescing st.tlbShootdown initiator
      (shootdownTargets initiator) op).pendingOnCore c =
        st.tlbShootdown.pendingOnCore c
    unfold postShootdownRoundCoalescing
    rw [foldl_enqueueShootdownOrCoalesce_frame_pending _ _ _
          (by rw [hci]; exact initiator_not_mem_shootdownTargets initiator),
        beginShootdownRoundFor_frame_pending]
  · exact lockSet_tlbShootdown_queue_mem vspaceRootLock initiator hci

/-- **WS-SM SM7.B.7**: the footprint's size — the object lock, the
round lock, and one queue lock per target (`numCores - 1` of them on
the fully-online topology).  Well below the SM3 `maxLockSetSize`
worst case. -/
theorem lockSet_tlbShootdown_length (vspaceRootLock : Concurrency.LockId)
    (initiator : CoreId) :
    (lockSet_tlbShootdown vspaceRootLock initiator).length =
      2 + (shootdownTargets initiator).length := by
  unfold lockSet_tlbShootdown
  simp only [List.length_cons, List.length_map]
  omega

end SeLe4n.Kernel.Architecture
