-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Concurrency.Types
import SeLe4n.Kernel.Concurrency.Locks.LockSet

/-!
# The scheduler-domain footprint constructor

`schedCoreSegment`, `schedFootprintOfCores` and the SM5.H.4 parametric
migration footprints — the pure constructors every resolved scheduler footprint
is an instance of.  They are stated over `LockKey` and `CoreId` alone, and
nothing in them reads kernel state.

They lived in `Scheduler/Operations/PerCoreChooseThread.lean` (WS-SM SM6.E,
WS-RR RR2.4, generalised at RR8.12) until WS-LS LS2.5.  That module imports
the lifecycle, SchedContext and IPC transitions, so a footprint declared beside
one of those transitions could not reach the constructor, and the arms whose
modules sat below it were collected in `SyscallSchedFootprint.lean` instead.
Moving the constructor here, below every transition module, is what lets each
resolved footprint sit beside the transition it is about:
`schedLockSet_suspendThreadOnCore` in `IPC/CrossCore/SuspendFootprint.lean`,
`schedLockSet_lifecycleRetypeOnCore` in `Lifecycle/Operations/RetypeFootprint.lean`,
and so on.  The names and statements are unchanged.
-/

namespace SeLe4n.Kernel

open SeLe4n.Kernel.Concurrency (numCores CoreId LockKey)

-- ============================================================================
-- WS-SM SM6.E / WS-RR RR2.4, generalised at WS-RR RR8.12 — a same-kind
-- scheduler-lock segment over a *set* of cores
-- ============================================================================
--
-- A cross-domain footprint that touches several cores' slots of the *same* kind
-- (run queues, replenish queues) must emit them duplicate-free and in
-- `CoreId`-ascending order, so the declared list is itself the SM3.D acquisition
-- sequence.  The shape is shared by the `.tcbSuspend` cancellation footprint
-- (SM6.E), the `.call` / `.reply` donation footprints (RR2.4 / RR2.10), the PIP
-- chain walk's footprint (RR7.40) and the per-arm syscall-seam footprints
-- (RR8.12), so it lives here, with the `LockKey` order it is about, rather
-- than in any one of them.
--
-- **RR8.12 replaced two fixed-arity spellings with one.**  `sortedSchedCorePair`
-- and `sortedSchedCoreTriple` were the same question at two arities — "the
-- segment over this set of cores" — each with its own `_map_fst_mem` and
-- `_pairwise_le`, and `.receive` / `.replyRecv` were about to need a third
-- arity.  Adding one would have been the enumeration-standing-in-for-a-derivation
-- shape this project retires; `schedCoreSegment` takes the set.  That the two
-- were instances was measured before they were deleted, exhaustively over the
-- concrete core enumeration at both lock constructors, so the sweep changed no
-- footprint's value.

/-- **WS-RR RR8.12**: a duplicate-free, `CoreId`-ascending segment of same-kind
scheduler locks over a set of cores.

`f` names the kind (`fun c => LockKey.runQueue c` or the replenish-queue
counterpart), and the cores are canonicalised through
`Concurrency.canonicalCores`, so the segment is independent of the order and
multiplicity the resolver discovered them in.  Every member is a **write**: a
footprint segment exists because the transition moves those cores' slots.

The length bound is `numCores` rather than the supplied list's length
(`schedCoreSegment_length_le`), which is what makes a segment resolved from a
*walk* — a PIP chain, a reply stack — bounded without a separate argument. -/
def schedCoreSegment (f : CoreId → LockKey) (cs : List CoreId) :
    List (LockKey × Concurrency.AccessMode) :=
  (Concurrency.canonicalCores cs).map (fun c => (f c, .write))

/-- **WS-RR RR8.12**: every key of a segment is some supplied core's lock — the
case analysis every ordering proof over a composite footprint runs. -/
theorem schedCoreSegment_map_fst_mem {f : CoreId → LockKey} {cs : List CoreId}
    {x : LockKey} (hx : x ∈ (schedCoreSegment f cs).map (·.1)) :
    ∃ c ∈ cs, x = f c := by
  unfold schedCoreSegment at hx
  rw [List.map_map] at hx
  obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hx
  exact ⟨c, (Concurrency.mem_canonicalCores cs c).mp hc, rfl⟩

/-- **WS-RR RR8.12**: a core's write lock is in the segment exactly when the
core is in the set — the coverage half, and the direction a *false* footprint
fails.

`hInj` is discharged at each use by the constructor's own injectivity
(`LockKey.runQueue.inj` / `.replenishQueue.inj` composed with the wrapper's
field projection); without it the reverse direction would hold for a `f` that
collapsed two cores onto one lock, which is not a segment but an alias. -/
theorem mem_schedCoreSegment_iff {f : CoreId → LockKey}
    (hInj : ∀ c d : CoreId, f c = f d → c = d) (cs : List CoreId) (c : CoreId) :
    (f c, Concurrency.AccessMode.write) ∈ schedCoreSegment f cs ↔ c ∈ cs := by
  unfold schedCoreSegment
  constructor
  · intro h
    obtain ⟨d, hd, hEq⟩ := List.mem_map.mp h
    have hcd : c = d := hInj c d (congrArg Prod.fst hEq).symm
    exact hcd ▸ (Concurrency.mem_canonicalCores cs d).mp hd
  · intro h
    exact List.mem_map.mpr ⟨c, (Concurrency.mem_canonicalCores cs c).mpr h, rfl⟩

/-- **WS-RR RR8.12**: a segment's keys ascend under any `CoreId`-monotone lock
constructor — so the segment is its own acquisition sequence within its kind. -/
theorem schedCoreSegment_pairwise_le (f : CoreId → LockKey) (cs : List CoreId)
    (hMono : ∀ c d : CoreId, c ≤ d → f c ≤ f d) :
    ((schedCoreSegment f cs).map (·.1)).Pairwise (· ≤ ·) := by
  unfold schedCoreSegment
  rw [List.map_map]
  exact List.Pairwise.map _ (fun a b h => hMono a b h)
    (Concurrency.canonicalCores_pairwise_le cs)

/-- **WS-RR RR8.12**: a segment is write-only. -/
theorem schedCoreSegment_write_only (f : CoreId → LockKey) (cs : List CoreId) :
    ∀ p ∈ schedCoreSegment f cs, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  obtain ⟨_, _, rfl⟩ := List.mem_map.mp hp
  rfl

/-- **WS-RR RR8.12**: a segment's keys are duplicate-free — the obligation
`LockSet.ofList?` refuses a footprint for, and the one a `dedup`-based
segment would have had to prove separately. -/
theorem schedCoreSegment_keys_nodup {f : CoreId → LockKey}
    (hInj : ∀ c d : CoreId, f c = f d → c = d) (cs : List CoreId) :
    ((schedCoreSegment f cs).map (·.1)).Nodup := by
  unfold schedCoreSegment
  rw [List.map_map]
  exact List.Pairwise.map f (fun c d h hEq => h (hInj c d hEq))
    (Concurrency.canonicalCores_nodup cs)

/-- **WS-RR RR8.12**: a segment names at most one lock per core, however many
cores the resolver supplied. -/
theorem schedCoreSegment_length_le (f : CoreId → LockKey) (cs : List CoreId) :
    (schedCoreSegment f cs).length ≤ Concurrency.numCores := by
  unfold schedCoreSegment
  rw [List.length_map]
  exact Concurrency.canonicalCores_length_le cs

/-- **WS-RR RR8.12**: no cores, no segment. -/
@[simp] theorem schedCoreSegment_nil (f : CoreId → LockKey) :
    schedCoreSegment f [] = [] := by
  simp [schedCoreSegment]

/-- **WS-RR RR8.12**: one core, one member.

The arm every `Option CoreId`-shaped footprint resolver reaches: a footprint
that names at most one core of a kind — a deschedule's placed core, a wake's
target — is the segment over that core's singleton set, and this is what says
the segment has not quietly become something longer. -/
@[simp] theorem schedCoreSegment_singleton (f : CoreId → LockKey) (c : CoreId) :
    schedCoreSegment f [c] = [(f c, Concurrency.AccessMode.write)] := by
  simp [schedCoreSegment, Concurrency.canonicalCores_singleton]

/-- **WS-RR RR8.12**: a segment depends on the *set* of cores, not on the list —
the statement that its argument is a set rather than a claim about it.

A resolver that discovers a core twice, or discovers two cores in either order,
declares one segment.  This is what retires a hand-written deduplication at a
footprint; see `cancelIpcBlockingOnCoreLockSet`, whose `if placed = some c`
branch existed only to remove a duplicate the canonical form never emits. -/
theorem schedCoreSegment_congr (f : CoreId → LockKey) {cs ds : List CoreId}
    (h : ∀ c, c ∈ cs ↔ c ∈ ds) : schedCoreSegment f cs = schedCoreSegment f ds := by
  unfold schedCoreSegment
  rw [Concurrency.canonicalCores_congr h]

/-- **WS-RR RR8.12**: the run-queue constructor is injective in the core — the
`hInj` argument of `mem_schedCoreSegment_iff` and `schedCoreSegment_keys_nodup`
at the run-queue segment. -/
theorem runQueueLock_injective (c d : CoreId)
    (h : LockKey.runQueue c = LockKey.runQueue d) : c = d :=
  LockKey.runQueue.inj h

/-- **WS-RR RR8.12**: and the replenish-queue constructor. -/
theorem replenishQueueLock_injective (c d : CoreId)
    (h : LockKey.replenishQueue c = LockKey.replenishQueue d) : c = d :=
  LockKey.replenishQueue.inj h

/-- **WS-RR RR8.12**: a whole operation's scheduler-domain footprint — the
object-store table write lock, then the run-queue segment, then the
replenish-queue segment.

Every scheduler-domain footprint of a whole kernel operation in this tree is
this list at some pair of core sets: the `.call` and `.reply` dispatches, the
two donation hand-offs, the cancellation composite, the cross-core suspend
pipeline, and the per-arm syscall-seam footprints.  Before this definition each
spelled the three-domain ladder out again, and **four** carried a
byte-identical twenty-five-line `_pairwise_le` — one question with four
answers, about to become nine as the remaining syscall arms are declared.

The three segments are in the plan §4.4 cross-domain ascending order
`object < runQueue < replenishQueue`, and each same-kind segment is
`CoreId`-ascending and duplicate-free because `schedCoreSegment` canonicalises
its core set.  So the list **is** the SM3.D acquisition sequence
(`schedFootprintOfCores_pairwise_le`) and `LockSet.ofList?` accepts it
(`schedFootprintOfCores_keys_nodup`).

The two arguments are **sets**: a core named twice, or two cores a resolver
discovered in descending order, contribute one member in ascending position.
That is what retires the hand-written deduplication
`cancelIpcBlockingOnCoreLockSet` used to carry as an
`if placed = some c then … else … ++ [(runQueue ⟨c⟩, .write)]` — a question
about a *set*, answered by an `if`-chain over its two possible elements, which
is the shape RR8.12's first cut retired one level up.

**Which footprints are this, and which are not**, stated as a criterion rather
than a list, because a list cannot see the footprint nobody has written yet: a
footprint whose core arguments form a **set** — two or more of a kind, an
`Option` joined with another, a segment resolved from a walk — is this
constructor, because the ordering and the deduplication are then real questions
and the ladder proof is the twenty-five-line one.  A footprint at a **fixed
single** core of each kind is a literal: `wakeThreadLockSet`,
`descheduleThreadLockSet` and `cancelBoundDonationOnCoreLockSet` name at
most one run queue and at most one replenish queue, so there is nothing to sort
and nothing to merge, and their `_pairwise_le` is a two-element `simp`.
`migrateSchedContextReplenishmentLockSet` is not this shape at all — it is a
*sub*-footprint with no object-store member, declared so a composite can be
shown to cover it.

A fixed-single-core footprint that later gains a second core of a kind stops
being a literal and becomes this constructor in the same cut; that is the
question to ask when adding an argument, not which list a name is on.

**WS-RR RR8.12's seventh cut builds the per-arm syscall footprints over this**,
and does it by reading the SM8.B **write set** the arm's confinement theorem is
already stated at rather than resolving the cores a second time — so
`schedLockSet_notificationSignalBoundOnCore`,
`schedLockSet_notificationSignalOnCore`, `schedLockSet_notificationWaitOnCore`
and `schedLockSet_endpointSendOnCore` are each `schedFootprintOfCores` of a core
list the non-interference surface already owns.  A footprint and a confinement
claim that name different cores is the failure that arrangement makes
unstateable. -/
def schedFootprintOfCores (runCores replenishCores : List CoreId) :
    List (LockKey × Concurrency.AccessMode) :=
  (LockKey.objStore, .write) ::
    (schedCoreSegment (fun c => LockKey.runQueue c) runCores
      ++ schedCoreSegment (fun c => LockKey.replenishQueue c) replenishCores)

/-- **WS-RR RR8.12**: what a scheduler-domain footprint contains — the one
characterisation its consumers read.

Stated as a biconditional over the pair rather than left to each consumer's own
case analysis over the cons and the two segments: a second reading of the same
three-way split is the duplication this constructor exists to close, one level
down.  Everything below is an instance of it. -/
theorem mem_schedFootprintOfCores_iff (runCores replenishCores : List CoreId)
    (p : LockKey × Concurrency.AccessMode) :
    p ∈ schedFootprintOfCores runCores replenishCores ↔
      p = (LockKey.objStore, Concurrency.AccessMode.write)
        ∨ (∃ c ∈ runCores, p = (LockKey.runQueue c, Concurrency.AccessMode.write))
        ∨ (∃ c ∈ replenishCores,
            p = (LockKey.replenishQueue c, Concurrency.AccessMode.write)) := by
  unfold schedFootprintOfCores schedCoreSegment
  rw [List.mem_cons, List.mem_append]
  constructor
  · rintro (rfl | hp | hp)
    · exact Or.inl rfl
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
      exact Or.inr (Or.inl ⟨c, (Concurrency.mem_canonicalCores _ c).mp hc, rfl⟩)
    · obtain ⟨c, hc, rfl⟩ := List.mem_map.mp hp
      exact Or.inr (Or.inr ⟨c, (Concurrency.mem_canonicalCores _ c).mp hc, rfl⟩)
  · rintro (rfl | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl
        (List.mem_map.mpr ⟨c, (Concurrency.mem_canonicalCores _ c).mpr hc, rfl⟩))
    · exact Or.inr (Or.inr
        (List.mem_map.mpr ⟨c, (Concurrency.mem_canonicalCores _ c).mpr hc, rfl⟩))

/-- **WS-RR RR8.12**: a scheduler-domain footprint is write-only.  Every member
is a slot the operation mutates: the object store it stores through, the run
queues it enqueues on or removes from, the replenish queues it purges or
migrates. -/
theorem schedFootprintOfCores_write_only (runCores replenishCores : List CoreId) :
    ∀ p ∈ schedFootprintOfCores runCores replenishCores,
      p.2 = Concurrency.AccessMode.write := by
  intro p hp
  rcases (mem_schedFootprintOfCores_iff runCores replenishCores p).mp hp with
    rfl | ⟨_, _, rfl⟩ | ⟨_, _, rfl⟩ <;> rfl

/-- **WS-RR RR8.12**: the object-store table write lock is always a member —
every scheduler-domain footprint is a footprint of an operation that stores. -/
theorem schedFootprintOfCores_contains_objStore_write
    (runCores replenishCores : List CoreId) :
    (LockKey.objStore, Concurrency.AccessMode.write)
      ∈ schedFootprintOfCores runCores replenishCores :=
  List.mem_cons_self ..

/-- **WS-RR RR8.12**: a run core's run-queue write lock is a member exactly when
the core is in the run set — the coverage half, and the direction a *false*
footprint fails. -/
theorem mem_schedFootprintOfCores_runQueue_iff (runCores replenishCores : List CoreId)
    (c : CoreId) :
    (LockKey.runQueue c, Concurrency.AccessMode.write)
        ∈ schedFootprintOfCores runCores replenishCores ↔ c ∈ runCores := by
  rw [mem_schedFootprintOfCores_iff]
  constructor
  · rintro (h | ⟨d, hd, h⟩ | ⟨d, _, h⟩)
    · exact absurd (congrArg Prod.fst h) (by simp)
    · exact runQueueLock_injective c d (congrArg Prod.fst h) ▸ hd
    · exact absurd (congrArg Prod.fst h) (by simp)
  · exact fun h => Or.inr (Or.inl ⟨c, h, rfl⟩)

/-- **WS-RR RR8.12**: and a replenish core's replenish-queue write lock. -/
theorem mem_schedFootprintOfCores_replenishQueue_iff
    (runCores replenishCores : List CoreId) (c : CoreId) :
    (LockKey.replenishQueue c, Concurrency.AccessMode.write)
        ∈ schedFootprintOfCores runCores replenishCores ↔ c ∈ replenishCores := by
  rw [mem_schedFootprintOfCores_iff]
  constructor
  · rintro (h | ⟨d, _, h⟩ | ⟨d, hd, h⟩)
    · exact absurd (congrArg Prod.fst h) (by simp)
    · exact absurd (congrArg Prod.fst h) (by simp)
    · exact replenishQueueLock_injective c d (congrArg Prod.fst h) ▸ hd
  · exact fun h => Or.inr (Or.inr ⟨c, h, rfl⟩)

/-- **WS-RR RR8.12**: widening either core set widens the footprint — the
statement every `…_covers_…` obligation between a composite's footprint and a
component's is an instance of.

Over-declaring is the safe direction (a footprint that omits a written lock is
*false*), so this is the lemma a composite reaches for rather than a second
member-by-member case analysis. -/
theorem schedFootprintOfCores_subset
    {run₁ run₂ rep₁ rep₂ : List CoreId}
    (hRun : ∀ c ∈ run₁, c ∈ run₂) (hRep : ∀ c ∈ rep₁, c ∈ rep₂) :
    ∀ p ∈ schedFootprintOfCores run₁ rep₁, p ∈ schedFootprintOfCores run₂ rep₂ := by
  intro p hp
  rw [mem_schedFootprintOfCores_iff] at hp ⊢
  rcases hp with rfl | ⟨c, hc, rfl⟩ | ⟨c, hc, rfl⟩
  · exact Or.inl rfl
  · exact Or.inr (Or.inl ⟨c, hRun c hc, rfl⟩)
  · exact Or.inr (Or.inr ⟨c, hRep c hc, rfl⟩)

/-- **WS-RR RR8.12**: a scheduler-domain footprint's keys ascend in the
`LockKey` order — the full three-domain ladder
`object < runQueue < replenishQueue`, each same-kind segment `CoreId`-ascending.
So the declared list is its own SM3.D acquisition sequence.

Proved once here.  It was four copies before this cut. -/
theorem schedFootprintOfCores_pairwise_le (runCores replenishCores : List CoreId) :
    ((schedFootprintOfCores runCores replenishCores).map (·.1)).Pairwise (· ≤ ·) := by
  have hObjRQ : ∀ (c : CoreId), LockKey.objStore
      ≤ LockKey.runQueue c :=
    fun c => (LockKey.objStore_lt_runQueue _).1
  have hObjRep : ∀ (c : CoreId), LockKey.objStore
      ≤ LockKey.replenishQueue c :=
    fun c => (LockKey.objStore_lt_replenishQueue _).1
  have hRQRep : ∀ (c d : CoreId), LockKey.runQueue c
      ≤ LockKey.replenishQueue d :=
    fun c d => (LockKey.runQueue_lt_replenishQueue _ _).1
  unfold schedFootprintOfCores
  rw [List.map_cons, List.map_append, List.pairwise_cons]
  refine ⟨?_, ?_⟩
  · intro x hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨c, _, rfl⟩ := schedCoreSegment_map_fst_mem hx; exact hObjRQ c
    · obtain ⟨c, _, rfl⟩ := schedCoreSegment_map_fst_mem hx; exact hObjRep c
  · rw [List.pairwise_append]
    refine ⟨schedCoreSegment_pairwise_le _ _ (fun c d h => h),
      schedCoreSegment_pairwise_le _ _ (fun c d h => h), ?_⟩
    intro x hx y hy
    obtain ⟨c, _, rfl⟩ := schedCoreSegment_map_fst_mem hx
    obtain ⟨d, _, rfl⟩ := schedCoreSegment_map_fst_mem hy
    exact hRQRep c d

/-- **WS-RR RR8.12**: a scheduler-domain footprint's keys are duplicate-free —
the obligation `LockSet.ofList?` refuses a footprint for.

Each segment is duplicate-free by canonicalisation, the two segments are
disjoint because their keys carry different constructors, and the object key is
in neither. -/
theorem schedFootprintOfCores_keys_nodup (runCores replenishCores : List CoreId) :
    ((schedFootprintOfCores runCores replenishCores).map (·.1)).Nodup := by
  unfold schedFootprintOfCores
  rw [List.map_cons, List.map_append, List.nodup_cons]
  refine ⟨?_, ?_⟩
  · intro hx
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨_, _, h⟩ := schedCoreSegment_map_fst_mem hx; exact absurd h (by simp)
    · obtain ⟨_, _, h⟩ := schedCoreSegment_map_fst_mem hx; exact absurd h (by simp)
  · rw [List.nodup_append]
    refine ⟨schedCoreSegment_keys_nodup runQueueLock_injective _,
      schedCoreSegment_keys_nodup replenishQueueLock_injective _, ?_⟩
    intro x hx y hy
    obtain ⟨_, _, rfl⟩ := schedCoreSegment_map_fst_mem hx
    obtain ⟨_, _, rfl⟩ := schedCoreSegment_map_fst_mem hy
    simp

/-- **WS-RR RR8.12**: a scheduler-domain footprint names at most one lock per
core per kind, plus the object store — `1 + 2 * numCores`, however many cores
the resolvers supplied.

The bound is in `numCores` rather than in the supplied lists' lengths, which is
what makes a footprint resolved from a *walk* — a PIP chain, a reply stack —
bounded without a separate argument. -/
theorem schedFootprintOfCores_length_le (runCores replenishCores : List CoreId) :
    (schedFootprintOfCores runCores replenishCores).length
      ≤ 1 + 2 * Concurrency.numCores := by
  unfold schedFootprintOfCores
  rw [List.length_cons, List.length_append]
  have hRun := schedCoreSegment_length_le (fun c => LockKey.runQueue c) runCores
  have hRep := schedCoreSegment_length_le (fun c => LockKey.replenishQueue c)
    replenishCores
  omega

/-- **WS-RR RR8.12**: a footprint depends on the *sets* of cores, not on the
lists — `schedCoreSegment_congr` lifted to the whole three-domain ladder.

Two resolvers that discover the same cores declare the same footprint, so a
footprint that names a core twice needs no deduplication branch of its own. -/
theorem schedFootprintOfCores_congr {run₁ run₂ rep₁ rep₂ : List CoreId}
    (hRun : ∀ c, c ∈ run₁ ↔ c ∈ run₂) (hRep : ∀ c, c ∈ rep₁ ↔ c ∈ rep₂) :
    schedFootprintOfCores run₁ rep₁ = schedFootprintOfCores run₂ rep₂ := by
  unfold schedFootprintOfCores
  rw [schedCoreSegment_congr _ hRun, schedCoreSegment_congr _ hRep]

/-- WS-SM SM5.H.4 (lock-set): `migrateSchedContextReplenishment fromCore toCore`
writes both cores' replenish-queue slots. -/
def migrateSchedContextReplenishmentLockSet (fromCore toCore : CoreId) :
    List (LockKey × Concurrency.AccessMode) :=
  [ (LockKey.replenishQueue fromCore, .write)
  , (LockKey.replenishQueue toCore, .write) ]

/-- SM5.H.4: the migration footprint is the two replenish-queue write locks. -/
@[simp] theorem migrateSchedContextReplenishmentLockSet_length (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishmentLockSet fromCore toCore).length = 2 := rfl

/-- SM5.H.4: the migration footprint is write-only. -/
theorem migrateSchedContextReplenishmentLockSet_write_only (fromCore toCore : CoreId) :
    ∀ p ∈ migrateSchedContextReplenishmentLockSet fromCore toCore, p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [migrateSchedContextReplenishmentLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h <;> subst h <;> rfl

/-- SM5.H.4: for distinct cores the migration footprint's keys are duplicate-free. -/
theorem migrateSchedContextReplenishmentLockSet_keys_nodup (fromCore toCore : CoreId)
    (h : fromCore ≠ toCore) :
    ((migrateSchedContextReplenishmentLockSet fromCore toCore).map (·.1)).Nodup := by
  simp only [migrateSchedContextReplenishmentLockSet, List.map_cons, List.map_nil]
  refine List.Pairwise.cons (fun a ha => ?_) (List.pairwise_singleton _ _)
  rw [List.mem_singleton] at ha; subst ha
  intro hEq
  exact h (LockKey.replenishQueue.inj hEq)

/-- SM5.H.4 (plan §4.4 / SM3.D ladder): under the canonical core order
`fromCore.val ≤ toCore.val`, the migration footprint's keys are ascending — a valid
`withLockSet` acquisition sequence. -/
theorem migrateSchedContextReplenishmentLockSet_pairwise_le_of_core_le (fromCore toCore : CoreId)
    (h : fromCore.val ≤ toCore.val) :
    ((migrateSchedContextReplenishmentLockSet fromCore toCore).map (·.1)).Pairwise (· ≤ ·) := by
  simp only [migrateSchedContextReplenishmentLockSet, List.map_cons, List.map_nil]
  refine List.Pairwise.cons (fun a ha => ?_) (List.pairwise_singleton _ _)
  rw [List.mem_singleton] at ha; subst ha; exact h

/-- SM5.H.4: the migration footprint is within the `maxLockSetSize` cap.

**WS-RR RR7.11**: stated against the constant its name claims, not against the
numeral the constant happened to hold.  The five `_size_le_maxLockSetSize`
theorems in the scheduler all pinned `≤ 8` literally, so each was a statement
about a number while its name promised a relation to `maxLockSetSize` — and the
`wcrt_op_bounded_of_size` consumers, which take the relation, type-checked only
by coincidence.  Raising the constant is what surfaced it. -/
theorem migrateSchedContextReplenishmentLockSet_size_le_maxLockSetSize (fromCore toCore : CoreId) :
    (migrateSchedContextReplenishmentLockSet fromCore toCore).length
      ≤ Concurrency.maxLockSetSize := by
  rw [migrateSchedContextReplenishmentLockSet_length]; decide

-- WS-RR RR8.12 Cut C3b-i (`v0.35.167`): the two SM5.H.4 parametric footprints below
-- arrived from the staged `Scheduler/Operations/PerCoreCbs.lean`, for the reason the
-- RR2.4 relocation above gives and did not sweep onto its own siblings twenty lines
-- further down that file: `.tcbSetAffinity` is a live arm, so the footprint its
-- resolved production form (`schedLockSet_setThreadCpuAffinityOnCore`) must be shown
-- to cover cannot live in a staged module.  Verbatim, same namespace.

/-- WS-SM SM5.H.4 (lock-set): `migrateRunQueueOnAffinityChange fromCore toCore`
writes both cores' run-queue slots. -/
def migrateRunQueueOnAffinityChangeLockSet (fromCore toCore : CoreId) :
    List (LockKey × Concurrency.AccessMode) :=
  [ (LockKey.runQueue fromCore, .write)
  , (LockKey.runQueue toCore, .write) ]

/-- SM5.H.4: the run-queue-migration footprint is the two run-queue write locks. -/
@[simp] theorem migrateRunQueueOnAffinityChangeLockSet_length (fromCore toCore : CoreId) :
    (migrateRunQueueOnAffinityChangeLockSet fromCore toCore).length = 2 := rfl

/-- SM5.H.4: under the canonical core order the run-queue-migration footprint's keys
are ascending. -/
theorem migrateRunQueueOnAffinityChangeLockSet_pairwise_le_of_core_le (fromCore toCore : CoreId)
    (h : fromCore.val ≤ toCore.val) :
    ((migrateRunQueueOnAffinityChangeLockSet fromCore toCore).map (·.1)).Pairwise (· ≤ ·) := by
  simp only [migrateRunQueueOnAffinityChangeLockSet, List.map_cons, List.map_nil]
  refine List.Pairwise.cons (fun a ha => ?_) (List.pairwise_singleton _ _)
  rw [List.mem_singleton] at ha; subst ha; exact h

/-- WS-SM SM5.H.4 (lock-set): the **complete** footprint of the full
affinity-change-with-migration composite — the object-store write lock (the
affinity write, an SM3.A.10 table-level write), the two run-queue write locks
(the run-queue migration), and the two replenish-queue write locks (the
replenishment migration), in plan §4.4 ascending order (object < runQueue <
replenishQueue, then by `core.val`).  This is the footprint a `withLockSet`
caller (the SM5.I `tcbSetAffinity` runtime path) acquires. -/
def setThreadCpuAffinityWithMigrationLockSet (oldCore newCore : CoreId) :
    List (LockKey × Concurrency.AccessMode) :=
  -- #5 (Codex P2 review): order the per-core run-queue / replenish-queue locks by
  -- core (lower-numbered core first) regardless of the old→new migration direction,
  -- so the footprint's keys are `LockKey`-ascending **unconditionally** (a valid
  -- `withLockSet` acquisition sequence — a concurrent opposite-direction migration
  -- acquires the same queue locks in the same order, so no reverse-direction
  -- deadlock; see `setThreadCpuAffinityWithMigrationLockSet_pairwise_le`).
  let loCore := if oldCore.val ≤ newCore.val then oldCore else newCore
  let hiCore := if oldCore.val ≤ newCore.val then newCore else oldCore
  [ (LockKey.objStore, .write)
  , (LockKey.runQueue loCore, .write)
  , (LockKey.runQueue hiCore, .write)
  , (LockKey.replenishQueue loCore, .write)
  , (LockKey.replenishQueue hiCore, .write) ]

/-- SM5.H.4: the composite footprint has the five cross-domain write locks. -/
@[simp] theorem setThreadCpuAffinityWithMigrationLockSet_length (oldCore newCore : CoreId) :
    (setThreadCpuAffinityWithMigrationLockSet oldCore newCore).length = 5 := rfl

/-- SM5.H.4: the composite footprint is write-only. -/
theorem setThreadCpuAffinityWithMigrationLockSet_write_only (oldCore newCore : CoreId) :
    ∀ p ∈ setThreadCpuAffinityWithMigrationLockSet oldCore newCore,
      p.2 = Concurrency.AccessMode.write := by
  intro p hp
  simp only [setThreadCpuAffinityWithMigrationLockSet, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with h | h | h | h | h <;> subst h <;> rfl

/-- SM5.H.4: the composite footprint contains the object-store write lock (the
affinity write). -/
theorem setThreadCpuAffinityWithMigrationLockSet_contains_objStore_write (oldCore newCore : CoreId) :
    (LockKey.objStore, Concurrency.AccessMode.write)
      ∈ setThreadCpuAffinityWithMigrationLockSet oldCore newCore := by
  simp [setThreadCpuAffinityWithMigrationLockSet]

/-- SM5.H.4 (#5, Codex P2 — plan §4.4 / SM3.D ladder): the composite footprint's keys
form an ascending acquisition sequence **unconditionally** (object < runQueue <
replenishQueue, then by core) — the lock-set lists the per-core queue locks
lower-core-first regardless of the old→new migration direction, so a `withLockSet`
caller acquires them in canonical order and cannot deadlock against a concurrent
opposite-direction migration. -/
theorem setThreadCpuAffinityWithMigrationLockSet_pairwise_le (oldCore newCore : CoreId) :
    ((setThreadCpuAffinityWithMigrationLockSet oldCore newCore).map (·.1)).Pairwise (· ≤ ·) := by
  have hObjRq : ∀ (r : CoreId), LockKey.objStore ≤ LockKey.runQueue r :=
    fun r => (LockKey.objStore_lt_runQueue _).1
  have hObjRpq : ∀ (r : CoreId), LockKey.objStore ≤ LockKey.replenishQueue r :=
    fun r => (LockKey.objStore_lt_replenishQueue _).1
  have hRqRpq : ∀ (q : CoreId) (r : CoreId),
      LockKey.runQueue q ≤ LockKey.replenishQueue r := fun q r => (LockKey.runQueue_lt_replenishQueue _ _).1
  have hLoHi : (if oldCore.val ≤ newCore.val then oldCore else newCore).val
             ≤ (if oldCore.val ≤ newCore.val then newCore else oldCore).val := by
    by_cases hc : oldCore.val ≤ newCore.val
    · simp only [hc, if_true]
    · simp only [hc, if_false]; omega
  simp only [setThreadCpuAffinityWithMigrationLockSet, List.map_cons, List.map_nil]
  refine List.Pairwise.cons (fun a ha => ?_) (List.Pairwise.cons (fun a ha => ?_)
    (List.Pairwise.cons (fun a ha => ?_) (List.Pairwise.cons (fun a ha => ?_)
      (List.pairwise_singleton _ _))))
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact hObjRq _
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hObjRq _
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hObjRpq _
    rcases List.mem_singleton.mp ha with rfl; exact hObjRpq _
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact hLoHi
    rcases List.mem_cons.mp ha with rfl | ha
    · exact hRqRpq _ _
    rcases List.mem_singleton.mp ha with rfl; exact hRqRpq _ _
  · rcases List.mem_cons.mp ha with rfl | ha
    · exact hRqRpq _ _
    rcases List.mem_singleton.mp ha with rfl; exact hRqRpq _ _
  · rcases List.mem_singleton.mp ha with rfl; exact hLoHi

/-- SM5.H.4 (retained): the conditional form, now immediate from the unconditional
`setThreadCpuAffinityWithMigrationLockSet_pairwise_le`. -/
theorem setThreadCpuAffinityWithMigrationLockSet_pairwise_le_of_core_le (oldCore newCore : CoreId)
    (_h : oldCore.val ≤ newCore.val) :
    ((setThreadCpuAffinityWithMigrationLockSet oldCore newCore).map (·.1)).Pairwise (· ≤ ·) :=
  setThreadCpuAffinityWithMigrationLockSet_pairwise_le oldCore newCore

/-- SM5.H.4 (WCRT): the composite footprint (5 locks) is within the SM3.D
`maxLockSetSize` cap — so its worst-case lock-wait is bounded. -/
theorem setThreadCpuAffinityWithMigrationLockSet_size_le_maxLockSetSize (oldCore newCore : CoreId) :
    (setThreadCpuAffinityWithMigrationLockSet oldCore newCore).length
      ≤ Concurrency.maxLockSetSize := by
  rw [setThreadCpuAffinityWithMigrationLockSet_length]; decide

end SeLe4n.Kernel
