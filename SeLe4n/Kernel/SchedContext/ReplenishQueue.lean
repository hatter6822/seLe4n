/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.SchedContext.Types

/-! # ReplenishQueue — WS-Z Phase Z3

System-wide replenishment queue tracking when each SchedContext's CBS budget
becomes eligible for refill. Entries are sorted by eligibility time (ascending)
for O(1) peek at the earliest due entry and O(k) prefix split for due entries.

## Operations:
- `insert`: Sorted insertion by eligibility time — O(n)
- `popDue`: Collect all entries due at current time — O(k) prefix split
- `remove`: Cancel all replenishments for a SchedContext — O(n) filter
- `peek`: Next due time — O(1) via sorted invariant

## Invariants:
- `replenishQueueSorted`: Entries sorted ascending by eligibility time
- `replenishQueueSizeConsistent`: Cached `size` matches list length
- `replenishQueueConsistent`: Every entry references an active SchedContext
-/

namespace SeLe4n.Kernel

-- ============================================================================
-- Z3-A: ReplenishQueue structure
-- ============================================================================

/-- System-wide CBS replenishment queue. Entries are sorted by eligibility time
(ascending). The `Nat` component is the absolute tick at which the SchedContext
becomes eligible for budget replenishment. -/
structure ReplenishQueue where
  /-- Sorted list of (SchedContextId, eligibleAt) pairs. -/
  entries : List (SchedContextId × Nat)
  /-- Cached entry count for O(1) size queries. -/
  size : Nat
deriving Repr, Inhabited

namespace ReplenishQueue

-- ============================================================================
-- Z3-B: ReplenishQueue.empty
-- ============================================================================

/-- Empty replenishment queue. -/
@[inline] def empty : ReplenishQueue :=
  { entries := [], size := 0 }

-- ============================================================================
-- Z3-C: ReplenishQueue.insert (sorted insertion)
-- ============================================================================

/-- Insert a SchedContextId at the correct sorted position by eligibility time.
Maintains ascending order. O(n) where n = number of entries. Typically n < 64
(bounded by number of active SchedContexts). -/
def insertSorted (entries : List (SchedContextId × Nat)) (scId : SchedContextId)
    (eligibleAt : Nat) : List (SchedContextId × Nat) :=
  match entries with
  | [] => [(scId, eligibleAt)]
  | (hId, hTime) :: tail =>
    if eligibleAt ≤ hTime then
      (scId, eligibleAt) :: (hId, hTime) :: tail
    else
      (hId, hTime) :: insertSorted tail scId eligibleAt

/-- Insert a replenishment entry maintaining sorted order.

**Duplicate SchedContextId policy**: Multiple entries for the same SchedContextId
are permitted. In the CBS model a SchedContext may have multiple pending
replenishments at different eligibility times (e.g., after budget exhaustion at
different periods). `processReplenishments` is idempotent — consuming an entry
when the SchedContext is already replenished is a safe no-op. This avoids the
overhead of an O(n) deduplication scan on every insert while preserving
correctness. Callers that require at-most-one semantics should call `remove`
before `insert`. -/
def insert (rq : ReplenishQueue) (scId : SchedContextId) (eligibleAt : Nat)
    : ReplenishQueue :=
  { entries := insertSorted rq.entries scId eligibleAt
    size := rq.size + 1 }

-- ============================================================================
-- Z3-D: ReplenishQueue.popDue (collect eligible entries)
-- ============================================================================

/-- Split entries into (due, remaining) at the given time. Since entries are
sorted by eligibility time, this is a prefix split: all entries with
`eligibleAt ≤ currentTime` form a prefix. O(k) where k = number of due entries. -/
def splitDue (entries : List (SchedContextId × Nat)) (currentTime : Nat)
    : List SchedContextId × List (SchedContextId × Nat) :=
  match entries with
  | [] => ([], [])
  | (scId, eligibleAt) :: tail =>
    if eligibleAt ≤ currentTime then
      let (due, remaining) := splitDue tail currentTime
      (scId :: due, remaining)
    else
      -- First entry not due means no subsequent entries are due (sorted)
      ([], (scId, eligibleAt) :: tail)

/-- Collect all entries due at `currentTime` and return the remaining queue. -/
def popDue (rq : ReplenishQueue) (currentTime : Nat)
    : ReplenishQueue × List SchedContextId :=
  let (due, remaining) := splitDue rq.entries currentTime
  ({ entries := remaining, size := rq.size - due.length }, due)

-- ============================================================================
-- Z3-E: ReplenishQueue.remove (cancel replenishment)
-- ============================================================================

/-- Remove all entries for a given SchedContext. Used when a SchedContext is
unbound or destroyed. O(n) filter. -/
def remove (rq : ReplenishQueue) (scId : SchedContextId) : ReplenishQueue :=
  let filtered := rq.entries.filter (fun (id, _) => !(id == scId))
  { entries := filtered
    size := filtered.length }

-- ============================================================================
-- Z3-F: ReplenishQueue.peek (next due time)
-- ============================================================================

/-- The eligibility time of the earliest entry, or `none` if empty.
O(1) via the sorted invariant — the earliest entry is always the head. -/
@[inline] def peek (rq : ReplenishQueue) : Option Nat :=
  match rq.entries with
  | [] => none
  | (_, eligibleAt) :: _ => some eligibleAt

/-- Check if the queue is empty. -/
@[inline] def isEmpty (rq : ReplenishQueue) : Bool :=
  rq.entries.isEmpty

/-- Check if any entries are due at the given time. O(1). -/
@[inline] def hasDue (rq : ReplenishQueue) (currentTime : Nat) : Bool :=
  match rq.entries with
  | [] => false
  | (_, eligibleAt) :: _ => eligibleAt ≤ currentTime

end ReplenishQueue

-- ============================================================================
-- Z3-G: Sorted invariant definition
-- ============================================================================

/-- A list of pairs is sorted ascending by second component.
Defined as: every element's time ≤ the next element's time. -/
def pairwiseSortedBy : List (SchedContextId × Nat) → Prop
  | [] => True
  | [_] => True
  | (_, t1) :: (id2, t2) :: rest =>
    t1 ≤ t2 ∧ pairwiseSortedBy ((id2, t2) :: rest)

/-- The replenishment queue is sorted by eligibility time (ascending). -/
def replenishQueueSorted (rq : ReplenishQueue) : Prop :=
  pairwiseSortedBy rq.entries

/-- The cached size matches the actual list length. -/
def replenishQueueSizeConsistent (rq : ReplenishQueue) : Prop :=
  rq.size = rq.entries.length

-- ============================================================================
-- Z3-G helpers: pairwiseSortedBy lemmas
-- ============================================================================

@[simp] theorem pairwiseSortedBy_nil : pairwiseSortedBy ([] : List (SchedContextId × Nat)) := by
  simp [pairwiseSortedBy]

@[simp] theorem pairwiseSortedBy_singleton (e : SchedContextId × Nat) :
    pairwiseSortedBy [e] := by simp [pairwiseSortedBy]

/-- If a sorted list has head with time t₁ and second element with time t₂,
then t₁ ≤ t₂. -/
theorem pairwiseSortedBy_head_le_second
    {id1 : SchedContextId} {t1 : Nat} {id2 : SchedContextId} {t2 : Nat}
    {rest : List (SchedContextId × Nat)}
    (h : pairwiseSortedBy ((id1, t1) :: (id2, t2) :: rest))
    : t1 ≤ t2 := h.1

/-- Tail of a sorted list is sorted. -/
theorem pairwiseSortedBy_tail
    {e : SchedContextId × Nat} {rest : List (SchedContextId × Nat)}
    (h : pairwiseSortedBy (e :: rest)) : pairwiseSortedBy rest := by
  match e, rest with
  | _, [] => exact trivial
  | (_, _), _ :: _ => exact h.2

/-- Cons onto a sorted list preserves sortedness when head time ≤ first element's time. -/
theorem pairwiseSortedBy_cons
    {id : SchedContextId} {t : Nat}
    {rest : List (SchedContextId × Nat)}
    (hrest : pairwiseSortedBy rest)
    (hle : ∀ e ∈ rest.head?, t ≤ e.2) :
    pairwiseSortedBy ((id, t) :: rest) := by
  match rest with
  | [] => exact trivial
  | (id2, t2) :: _ =>
    exact ⟨hle (id2, t2) rfl, hrest⟩

-- ============================================================================
-- Z3-H: insert_preserves_sorted
-- ============================================================================

/-- Helper: all times in a sorted list starting with (_, t) have time ≥ t. -/
private theorem pairwiseSortedBy_head_le_all
    {id : SchedContextId} {t : Nat} {rest : List (SchedContextId × Nat)}
    (h : pairwiseSortedBy ((id, t) :: rest)) :
    ∀ e ∈ rest, t ≤ e.2 := by
  intro e he
  match rest with
  | [] => simp at he
  | (id2, t2) :: tail =>
    have hle : t ≤ t2 := pairwiseSortedBy_head_le_second h
    have htail : pairwiseSortedBy ((id2, t2) :: tail) := pairwiseSortedBy_tail h
    rcases List.mem_cons.mp he with heq | hmem
    · rw [heq]; exact hle
    · have := pairwiseSortedBy_head_le_all htail e hmem
      exact Nat.le_trans hle this

private theorem insertSorted_head_ge
    {entries : List (SchedContextId × Nat)}
    {scId : SchedContextId} {eligibleAt : Nat}
    {lb : Nat} (hle : lb ≤ eligibleAt)
    (hall : ∀ e ∈ entries, lb ≤ e.2) :
    ∀ e ∈ ReplenishQueue.insertSorted entries scId eligibleAt, lb ≤ e.2 := by
  induction entries with
  | nil =>
    intro e he
    simp [ReplenishQueue.insertSorted] at he
    exact he ▸ hle
  | cons hd tail ih =>
    intro e he
    obtain ⟨hId, hTime⟩ := hd
    simp [ReplenishQueue.insertSorted] at he
    split at he
    case isTrue _ =>
      rcases List.mem_cons.mp he with heq | hmem
      · exact heq ▸ hle
      · exact hall e hmem
    case isFalse _ =>
      rcases List.mem_cons.mp he with heq | hmem
      · exact heq ▸ (hall (hId, hTime) (List.mem_cons_self ..))
      · exact ih (fun e' he' => hall e' (List.mem_cons_of_mem _ he')) e hmem

private theorem insertSorted_head_time_ge
    {entries : List (SchedContextId × Nat)}
    {scId : SchedContextId} {eligibleAt : Nat}
    {lb : Nat} (hle : lb ≤ eligibleAt)
    (hall : ∀ e ∈ entries, lb ≤ e.2) :
    ∀ e ∈ (ReplenishQueue.insertSorted entries scId eligibleAt).head?,
      lb ≤ e.2 := by
  match entries with
  | [] =>
    simp [ReplenishQueue.insertSorted, List.head?]
    exact hle
  | (hId, hTime) :: tail =>
    unfold ReplenishQueue.insertSorted
    split
    case isTrue _ =>
      simp [List.head?]
      exact hle
    case isFalse _ =>
      simp [List.head?]
      exact hall _ (List.mem_cons_self ..)

theorem insertSorted_preserves_sorted
    {entries : List (SchedContextId × Nat)}
    {scId : SchedContextId} {eligibleAt : Nat}
    (h : pairwiseSortedBy entries) :
    pairwiseSortedBy (ReplenishQueue.insertSorted entries scId eligibleAt) := by
  induction entries with
  | nil => simp [ReplenishQueue.insertSorted]
  | cons hd tail ih =>
    obtain ⟨hId, hTime⟩ := hd
    unfold ReplenishQueue.insertSorted
    split
    case isTrue hle =>
      -- eligibleAt ≤ hTime: new element goes before head
      exact pairwiseSortedBy_cons h (by intro e he; cases he; exact hle)
    case isFalse hgt =>
      -- eligibleAt > hTime: recurse into tail
      have hlt : hTime < eligibleAt := Nat.lt_of_not_le hgt
      have htail_sorted : pairwiseSortedBy tail := pairwiseSortedBy_tail h
      have ih_result := ih htail_sorted
      -- Cons (hId, hTime) onto sorted insertSorted result
      exact pairwiseSortedBy_cons ih_result
        (insertSorted_head_time_ge (Nat.le_of_lt hlt) (pairwiseSortedBy_head_le_all h))

theorem insert_preserves_sorted {rq : ReplenishQueue} {scId : SchedContextId}
    {eligibleAt : Nat} (h : replenishQueueSorted rq) :
    replenishQueueSorted (rq.insert scId eligibleAt) :=
  insertSorted_preserves_sorted h

-- ============================================================================
-- Z3-I: popDue_preserves_sorted
-- ============================================================================

/-- Dropping a sorted prefix from a sorted list yields a sorted suffix. -/
theorem splitDue_remaining_sorted
    {entries : List (SchedContextId × Nat)} {currentTime : Nat}
    (h : pairwiseSortedBy entries) :
    pairwiseSortedBy (ReplenishQueue.splitDue entries currentTime).2 := by
  induction entries with
  | nil => simp [ReplenishQueue.splitDue]
  | cons hd tail ih =>
    obtain ⟨scId, eligibleAt⟩ := hd
    simp [ReplenishQueue.splitDue]
    split
    case isTrue _ =>
      -- This entry is due; recurse on tail
      exact ih (pairwiseSortedBy_tail h)
    case isFalse _ =>
      -- This entry is not due; entire remaining list is the suffix
      exact h

theorem popDue_preserves_sorted {rq : ReplenishQueue} {currentTime : Nat}
    (h : replenishQueueSorted rq) :
    replenishQueueSorted (rq.popDue currentTime).1 :=
  splitDue_remaining_sorted h

/-- splitDue preserves total length: due.length + remaining.length = entries.length. -/
theorem splitDue_length_additive
    (entries : List (SchedContextId × Nat)) (currentTime : Nat) :
    (ReplenishQueue.splitDue entries currentTime).1.length +
      (ReplenishQueue.splitDue entries currentTime).2.length = entries.length := by
  induction entries with
  | nil => simp [ReplenishQueue.splitDue]
  | cons hd tail ih =>
    obtain ⟨scId, eligibleAt⟩ := hd
    simp only [ReplenishQueue.splitDue]
    split
    case isTrue _ =>
      -- Entry is due: prepended to due list, tail recurses
      simp [List.length_cons]
      omega
    case isFalse _ =>
      -- Entry not due: entire list becomes remaining
      simp

/-- popDue preserves size consistency. -/
theorem popDue_sizeConsistent {rq : ReplenishQueue} {currentTime : Nat}
    (h : replenishQueueSizeConsistent rq) :
    replenishQueueSizeConsistent (rq.popDue currentTime).1 := by
  simp [replenishQueueSizeConsistent, ReplenishQueue.popDue]
  have hadd := splitDue_length_additive rq.entries currentTime
  rw [h]
  omega

-- ============================================================================
-- Z3-J: remove_preserves_sorted
-- ============================================================================

/-- All elements in a filtered sorted list have times ≥ the head's time. -/
private theorem filter_head_time_ge
    {entries : List (SchedContextId × Nat)}
    {p : (SchedContextId × Nat) → Bool}
    {id : SchedContextId} {t : Nat}
    (h : pairwiseSortedBy ((id, t) :: entries))
    : ∀ e ∈ (entries.filter p).head?, t ≤ e.2 := by
  intro e he
  -- head? returns some only when the list is non-empty
  match hfilt : entries.filter p with
  | [] => simp [hfilt] at he
  | (id2, t2) :: _ =>
    simp [hfilt] at he
    subst he
    have hmem : (id2, t2) ∈ entries.filter p := hfilt ▸ List.mem_cons_self ..
    have hmem_orig : (id2, t2) ∈ entries := (List.mem_filter.mp hmem).1
    exact pairwiseSortedBy_head_le_all h _ hmem_orig

/-- Filtering a sorted list preserves sortedness. -/
theorem filter_preserves_pairwiseSortedBy
    {entries : List (SchedContextId × Nat)}
    {p : (SchedContextId × Nat) → Bool}
    (h : pairwiseSortedBy entries) :
    pairwiseSortedBy (entries.filter p) := by
  induction entries with
  | nil => simp [List.filter]
  | cons hd tail ih =>
    obtain ⟨hId, hTime⟩ := hd
    have htail := pairwiseSortedBy_tail h
    have ih_result := ih htail
    simp only [List.filter]
    split
    next hp =>
      -- hd passes filter: cons onto filtered tail
      exact pairwiseSortedBy_cons ih_result (filter_head_time_ge h)
    next _ =>
      -- hd doesn't pass filter; result is filtered tail
      exact ih_result

theorem remove_preserves_sorted {rq : ReplenishQueue} {scId : SchedContextId}
    (h : replenishQueueSorted rq) :
    replenishQueueSorted (rq.remove scId) := by
  simp [ReplenishQueue.remove, replenishQueueSorted]
  exact filter_preserves_pairwiseSortedBy h

-- ============================================================================
-- Z3-K: replenishQueueConsistent invariant
-- ============================================================================

/-- Every SchedContextId in the replenishment queue corresponds to an active
SchedContext in the object store with `isActive = true`. This connects queue
membership to kernel object state, ensuring no dangling references.

Note: This invariant is parameterized by the object store lookup function
to decouple the queue module from the full SystemState definition. The
concrete instantiation occurs in CrossSubsystem.lean (Phase Z9). -/
def replenishQueueConsistent
    (rq : ReplenishQueue)
    (lookupSchedContext : SchedContextId → Option SchedContext) : Prop :=
  ∀ (scId : SchedContextId) (t : Nat),
    (scId, t) ∈ rq.entries →
    ∃ sc, lookupSchedContext scId = some sc ∧ sc.isActive = true

-- ============================================================================
-- Additional useful theorems
-- ============================================================================

/-- Empty queue is sorted. -/
theorem empty_sorted : replenishQueueSorted ReplenishQueue.empty := by
  simp [replenishQueueSorted, ReplenishQueue.empty]

/-- Empty queue has consistent size. -/
theorem empty_sizeConsistent :
    replenishQueueSizeConsistent ReplenishQueue.empty := rfl

/-- Empty queue is consistent with any lookup. -/
theorem empty_consistent (lookup : SchedContextId → Option SchedContext) :
    replenishQueueConsistent ReplenishQueue.empty lookup := by
  intro _ _ h
  simp [ReplenishQueue.empty] at h

/-- insertSorted increases list length by exactly 1. -/
theorem insertSorted_length (entries : List (SchedContextId × Nat))
    (scId : SchedContextId) (eligibleAt : Nat) :
    (ReplenishQueue.insertSorted entries scId eligibleAt).length
      = entries.length + 1 := by
  induction entries with
  | nil => rfl
  | cons hd tail ih =>
    obtain ⟨hId, hTime⟩ := hd
    unfold ReplenishQueue.insertSorted
    split
    case isTrue _ => simp
    case isFalse _ => simp [ih]

/-- insert preserves size consistency. -/
theorem insert_sizeConsistent {rq : ReplenishQueue}
    {scId : SchedContextId} {eligibleAt : Nat}
    (h : replenishQueueSizeConsistent rq) :
    replenishQueueSizeConsistent (rq.insert scId eligibleAt) := by
  simp [replenishQueueSizeConsistent, ReplenishQueue.insert]
  rw [insertSorted_length, h]

/-- remove preserves size consistency (size recomputed from filtered length). -/
theorem remove_sizeConsistent {rq : ReplenishQueue} {scId : SchedContextId} :
    replenishQueueSizeConsistent (rq.remove scId) := by
  simp [replenishQueueSizeConsistent, ReplenishQueue.remove]

/-- The new entry is a member of the result of insertSorted. -/
theorem mem_insertSorted (entries : List (SchedContextId × Nat))
    (scId : SchedContextId) (eligibleAt : Nat) :
    (scId, eligibleAt) ∈ ReplenishQueue.insertSorted entries scId eligibleAt := by
  induction entries with
  | nil => exact List.mem_cons_self ..
  | cons hd tail ih =>
    simp [ReplenishQueue.insertSorted]
    split
    case isTrue _ => exact List.mem_cons_self ..
    case isFalse _ => exact List.mem_cons_of_mem _ ih

/-- Existing entries are preserved by insertSorted. -/
theorem subset_insertSorted (entries : List (SchedContextId × Nat))
    (scId : SchedContextId) (eligibleAt : Nat) :
    ∀ e ∈ entries,
      e ∈ ReplenishQueue.insertSorted entries scId eligibleAt := by
  intro e he
  induction entries with
  | nil => simp at he
  | cons hd tail ih =>
    simp [ReplenishQueue.insertSorted]
    split
    case isTrue _ =>
      exact List.mem_cons_of_mem _ he
    case isFalse _ =>
      rcases List.mem_cons.mp he with heq | hmem
      · exact heq ▸ List.mem_cons_self ..
      · exact List.mem_cons_of_mem _ (ih hmem)

end SeLe4n.Kernel
