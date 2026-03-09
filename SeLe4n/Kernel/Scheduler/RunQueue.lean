import SeLe4n.Prelude
namespace SeLe4n.Kernel
open SeLe4n
structure RunQueue where
  byPriority : Std.HashMap Priority (List ThreadId)
  membership : Std.HashSet ThreadId
  threadPriority : Std.HashMap ThreadId Priority
  flat : List ThreadId
  size : Nat
  maxPriority : Option Priority
  /-- WS-G4: Structural invariant — every flat-list entry is in the HashSet.
      Needed to bridge `∈ rq.flat` (flat list) and `∈ rq` (HashSet) in proofs. -/
  flat_wf : ∀ tid, tid ∈ flat → membership.contains tid = true
  /-- WS-H6: Reverse structural invariant — every HashSet member appears in
      the flat list. Together with `flat_wf`, this yields bidirectional
      consistency between O(1) membership checks and list-based scans. -/
  flat_wf_rev : ∀ tid, membership.contains tid = true → tid ∈ flat
  /- WS-G4: Implicit invariant (maintained structurally by `insert`/`remove` API):
     Every thread in `membership` has a corresponding entry in `threadPriority`,
     and vice versa. This is NOT enforced as a proof obligation in the structure
     because it would complicate the API without adding formal value — the only
     mutations go through `insert` (adds both) and `remove` (erases both).
     Violation would require direct structure construction bypassing the API.
     Runtime verification: `InvariantChecks.runQueueThreadPriorityConsistentB`. -/
namespace RunQueue
@[inline] def empty : RunQueue where
  byPriority := {}; membership := {}; threadPriority := {}
  flat := []; size := 0; maxPriority := none
  flat_wf := fun _ h => nomatch h
  flat_wf_rev := by
    intro tid h
    simp [Std.HashSet.contains_empty] at h
instance : Inhabited RunQueue where default := empty
instance : EmptyCollection RunQueue where emptyCollection := empty
instance : Repr RunQueue where reprPrec rq _ := repr rq.flat
@[inline] def contains (rq : RunQueue) (tid : ThreadId) : Bool :=
  rq.membership.contains tid
instance : Membership ThreadId RunQueue where
  mem := fun rq tid => rq.contains tid = true
instance (tid : ThreadId) (rq : RunQueue) : Decidable (tid ∈ rq) :=
  show Decidable (rq.contains tid = true) from inferInstance

private def recomputeMaxPriority (byPrio : Std.HashMap Priority (List ThreadId)) : Option Priority :=
  byPrio.fold (fun acc prio bucket =>
    if bucket.isEmpty then acc
    else match acc with
      | none => some prio
      | some mp => if prio.toNat > mp.toNat then some prio else some mp
  ) none

def insert (rq : RunQueue) (tid : ThreadId) (prio : Priority) : RunQueue :=
  if rq.contains tid then rq
  else
    { byPriority := rq.byPriority.insert prio ((rq.byPriority[prio]?).getD [] ++ [tid])
      membership := rq.membership.insert tid
      threadPriority := rq.threadPriority.insert tid prio
      flat := rq.flat ++ [tid]
      size := rq.size + 1
      maxPriority := match rq.maxPriority with
        | none => some prio
        | some mp => if prio.toNat > mp.toNat then some prio else some mp
      flat_wf := by
        intro x hx
        simp only [List.mem_append, List.mem_singleton] at hx
        rcases hx with h | rfl
        · have := rq.flat_wf x h
          simp [Std.HashSet.contains_insert, this]
        · simp [Std.HashSet.contains_insert]
      flat_wf_rev := by
        intro x hx
        have hx0 : tid = x ∨ rq.membership.contains x = true := by
          simpa [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] using hx
        have hx' : x = tid ∨ rq.membership.contains x = true :=
          hx0.elim (fun h => Or.inl h.symm) Or.inr
        rcases hx' with rfl | hOld
        · exact List.mem_append.mpr (Or.inr (by simp))
        · exact List.mem_append.mpr (Or.inl (rq.flat_wf_rev x hOld)) }

def remove (rq : RunQueue) (tid : ThreadId) : RunQueue :=
  let prio := rq.threadPriority[tid]?
  -- WS-G4 refinement: compute filtered bucket once, reuse for both byPriority and maxPriority
  let (byPrio', maxPrio') := match prio with
    | none => (rq.byPriority, rq.maxPriority)
    | some p =>
        let bucket := ((rq.byPriority[p]?).getD []).filter (· ≠ tid)
        let byPrio' := if bucket.isEmpty then rq.byPriority.erase p
                        else rq.byPriority.insert p bucket
        let maxPrio' := if rq.maxPriority == some p && bucket.isEmpty then
                           recomputeMaxPriority byPrio'
                         else rq.maxPriority
        (byPrio', maxPrio')
  { byPriority := byPrio'
    membership := rq.membership.erase tid
    threadPriority := rq.threadPriority.erase tid
    flat := rq.flat.filter (· ≠ tid)
    size := if rq.contains tid then rq.size - 1 else rq.size
    maxPriority := maxPrio'
    flat_wf := by
      intro x hx
      have ⟨hFlat, hNe⟩ := List.mem_filter.mp hx
      have hXNeTid : x ≠ tid := by simpa using hNe
      have hMem := rq.flat_wf x hFlat
      simp [Std.HashSet.contains_erase, hMem, Ne.symm hXNeTid]
    flat_wf_rev := by
      intro x hx
      have hx' : rq.membership.contains x = true ∧ x ≠ tid := by
        have hx0 : tid ≠ x ∧ rq.membership.contains x = true := by
          simpa [Std.HashSet.contains_erase, Bool.and_eq_true, beq_iff_eq] using hx
        exact ⟨hx0.2, fun hEq => hx0.1 hEq.symm⟩
      have hFlat : x ∈ rq.flat := rq.flat_wf_rev x hx'.1
      exact List.mem_filter.mpr ⟨hFlat, by simpa [beq_iff_eq] using hx'.2⟩ }

def rotateHead (rq : RunQueue) (tid : ThreadId) (prio : Priority) : RunQueue :=
  if hc : rq.contains tid then
    match rq.byPriority[prio]? with
    | none => rq
    | some bucket =>
        match bucket with
        | [] => rq
        | hd :: tl =>
            if hd == tid then
              { rq with
                  byPriority := rq.byPriority.insert prio (tl ++ [tid])
                  flat := rq.flat.erase tid ++ [tid]
                  flat_wf := by
                    intro x hx
                    simp only [List.mem_append, List.mem_singleton] at hx
                    rcases hx with h | rfl
                    · exact rq.flat_wf x (List.mem_of_mem_erase h)
                    · exact hc
                  flat_wf_rev := by
                    intro x hx
                    have hFlat : x ∈ rq.flat := rq.flat_wf_rev x hx
                    by_cases hEq : x = tid
                    · subst hEq
                      exact List.mem_append.mpr (Or.inr (by simp))
                    · exact List.mem_append.mpr (Or.inl ((List.mem_erase_of_ne hEq).2 hFlat)) }
            else rq
  else rq

def rotateToBack (rq : RunQueue) (tid : ThreadId) : RunQueue :=
  if hc : rq.contains tid then
    let prio := rq.threadPriority[tid]?.getD ⟨0⟩
    let bucket := (rq.byPriority[prio]?).getD []
    let bucket' := bucket.filter (· ≠ tid) ++ [tid]
    { rq with
        byPriority := rq.byPriority.insert prio bucket'
        flat := rq.flat.erase tid ++ [tid]
        flat_wf := by
          intro x hx
          simp only [List.mem_append, List.mem_singleton] at hx
          rcases hx with h | rfl
          · exact rq.flat_wf x (List.mem_of_mem_erase h)
          · exact hc
        flat_wf_rev := by
          intro x hx
          have hFlat : x ∈ rq.flat := rq.flat_wf_rev x hx
          by_cases hEq : x = tid
          · subst hEq
            exact List.mem_append.mpr (Or.inr (by simp))
          · exact List.mem_append.mpr (Or.inl ((List.mem_erase_of_ne hEq).2 hFlat)) }
  else rq

@[inline] def toList (rq : RunQueue) : List ThreadId := rq.flat
def filterToList (rq : RunQueue) (p : ThreadId → Bool) : List ThreadId := rq.flat.filter p
def atPriority (rq : RunQueue) (prio : Priority) : List ThreadId := (rq.byPriority[prio]?).getD []

/-- WS-G4/F-P07: Return the max-priority bucket contents, or `[]` if the queue is empty.
    This enables O(k) best-candidate selection where k is the bucket size (typically 1-3). -/
@[inline] def maxPriorityBucket (rq : RunQueue) : List ThreadId :=
  match rq.maxPriority with
  | none => []
  | some prio => rq.atPriority prio

/-- WS-G4/F-P07: Return the max-priority value, or 0 as a fallback. -/
@[inline] def maxPriorityValue (rq : RunQueue) : Priority :=
  rq.maxPriority.getD ⟨0⟩
def ofList (entries : List (ThreadId × Priority)) : RunQueue :=
  entries.foldl (fun rq (tid, prio) => rq.insert tid prio) empty

-- Bridge lemmas

@[simp] theorem mem_iff_contains {rq : RunQueue} {tid : ThreadId} :
    tid ∈ rq ↔ rq.contains tid = true := Iff.rfl

theorem contains_false_of_not_mem {rq : RunQueue} {tid : ThreadId}
    (h : ¬(tid ∈ rq)) : rq.contains tid = false := by
  cases hc : rq.contains tid <;> simp_all

theorem not_mem_empty (tid : ThreadId) : ¬(tid ∈ (empty : RunQueue)) := by
  intro h; simp [Membership.mem, contains, RunQueue.empty] at h

theorem mem_insert (rq : RunQueue) (tid : ThreadId) (prio : Priority) (x : ThreadId) :
    x ∈ rq.insert tid prio ↔ x ∈ rq ∨ x = tid := by
  show (rq.insert tid prio).contains x = true ↔ rq.contains x = true ∨ x = tid
  unfold insert contains
  split
  · rename_i h
    exact ⟨Or.inl, fun hOr => hOr.elim id (fun heq => heq ▸ h)⟩
  · rename_i h
    rw [Std.HashSet.contains_insert]; simp only [Bool.or_eq_true, beq_iff_eq]
    exact ⟨fun h => h.elim (fun h => Or.inr h.symm) Or.inl,
           fun h => h.elim Or.inr (fun h => Or.inl h.symm)⟩

theorem mem_remove (rq : RunQueue) (tid : ThreadId) (x : ThreadId) :
    x ∈ rq.remove tid ↔ x ∈ rq ∧ x ≠ tid := by
  show (rq.remove tid).contains x = true ↔ rq.contains x = true ∧ x ≠ tid
  unfold remove contains
  constructor
  · intro h
    have h0 : tid ≠ x ∧ rq.contains x = true := by
      simpa [Std.HashSet.contains_erase, Bool.and_eq_true, beq_iff_eq] using h
    exact ⟨h0.2, fun hEq => h0.1 hEq.symm⟩
  · intro h
    rcases h with ⟨hx, hne⟩
    have hne' : tid ≠ x := fun hEq => hne hEq.symm
    simp [Std.HashSet.contains_erase, hne', hx]

theorem mem_rotateHead (rq : RunQueue) (tid : ThreadId) (prio : Priority) (x : ThreadId) :
    x ∈ rq.rotateHead tid prio ↔ x ∈ rq := by
  show (rq.rotateHead tid prio).contains x = true ↔ rq.contains x = true
  suffices h : (rq.rotateHead tid prio).membership = rq.membership by
    simp only [contains]; rw [h]
  unfold rotateHead
  split
  · split <;> try rfl
    split <;> try rfl
    split <;> rfl
  · rfl

theorem mem_rotateToBack (rq : RunQueue) (tid : ThreadId) (x : ThreadId) :
    x ∈ rq.rotateToBack tid ↔ x ∈ rq := by
  show (rq.rotateToBack tid).contains x = true ↔ rq.contains x = true
  suffices h : (rq.rotateToBack tid).membership = rq.membership by
    simp only [contains]; rw [h]
  unfold rotateToBack
  split <;> rfl

theorem not_mem_remove_self (rq : RunQueue) (tid : ThreadId) :
    ¬(tid ∈ rq.remove tid) := by
  rw [mem_remove]; exact fun ⟨_, hne⟩ => hne rfl

/-- Bridge: if tid is not in the RunQueue (HashSet), then tid is not in the flat list.
    Contrapositive of `flat_wf`. -/
theorem not_mem_toList_of_not_mem (rq : RunQueue) (tid : ThreadId)
    (h : ¬(tid ∈ rq)) : tid ∉ rq.toList := by
  simp only [toList]
  intro hFlat
  have := rq.flat_wf tid hFlat
  exact h (by rw [mem_iff_contains]; exact this)

/-- WS-H6: Reverse bridge from O(1) HashSet membership to flat-list membership. -/
theorem membership_implies_flat (rq : RunQueue) (tid : ThreadId)
    (h : tid ∈ rq) : tid ∈ rq.toList := by
  exact rq.flat_wf_rev tid (by simpa [mem_iff_contains] using h)

/-- WS-H6: Bidirectional consistency between `toList` membership and O(1)
HashSet membership checks. -/
theorem mem_toList_iff_mem (rq : RunQueue) (tid : ThreadId) :
    tid ∈ rq.toList ↔ tid ∈ rq := by
  constructor
  · intro hFlat
    exact (by rw [mem_iff_contains]; exact rq.flat_wf tid hFlat)
  · intro hMem
    exact membership_implies_flat rq tid hMem

@[simp] theorem toList_empty : (empty : RunQueue).toList = [] := rfl

theorem toList_insert_not_mem (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (hNotMem : ¬(tid ∈ rq)) :
    (rq.insert tid prio).toList = rq.toList ++ [tid] := by
  suffices h : (rq.insert tid prio).flat = rq.flat ++ [tid] by
    simp only [toList]; exact h
  unfold insert
  have hf : rq.contains tid = false := contains_false_of_not_mem hNotMem
  split
  · rename_i hTrue; exact absurd hTrue (by simp [contains] at hf; simp [contains, hf])
  · rfl

private theorem filter_filter_ne_of_false {α : Type} [DecidableEq α]
    (xs : List α) (a : α) (p : α → Bool) (hp : p a = false) :
    (xs.filter (fun x => decide (x ≠ a))).filter p = xs.filter p := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    by_cases hxa : x = a
    · subst hxa
      simp only [List.filter, decide_eq_false (show ¬(x ≠ x) from fun h => h rfl)]
      split <;> simp_all
    · simp only [List.filter, decide_eq_true hxa]
      split <;> simp_all

theorem toList_filter_insert_neg (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (p : ThreadId → Bool) (hp : p tid = false) (hNotMem : ¬(tid ∈ rq)) :
    (rq.insert tid prio).toList.filter p = rq.toList.filter p := by
  rw [toList_insert_not_mem rq tid prio hNotMem]
  rw [List.filter_append]
  simp [List.filter, hp]

/-- WS-H12b: Like `toList_filter_insert_neg` but without the `hNotMem` assumption.
When `tid ∈ rq`, `insert` is a no-op, so the filter result is unchanged regardless. -/
theorem toList_filter_insert_neg' (rq : RunQueue) (tid : ThreadId) (prio : Priority)
    (p : ThreadId → Bool) (hp : p tid = false) :
    (rq.insert tid prio).toList.filter p = rq.toList.filter p := by
  by_cases hMem : tid ∈ rq
  · -- tid already in rq: insert is a no-op
    have hContains : rq.contains tid = true := by rwa [mem_iff_contains] at hMem
    simp only [insert, hContains, ite_true]
  · exact toList_filter_insert_neg rq tid prio p hp hMem

/-- WS-H12b: Inserting the same thread (possibly at different priorities) into two
run queues preserves filter equality, provided the thread passes the predicate
and both queues already have equal filtered lists.
When `tid ∈ rq`, insert is a no-op. When `tid ∉ rq`, insert appends tid. -/
theorem toList_filter_insert_congr (rq₁ rq₂ : RunQueue) (tid : ThreadId)
    (prio₁ prio₂ : Priority) (p : ThreadId → Bool) (hp : p tid = true)
    (hBase : rq₁.toList.filter p = rq₂.toList.filter p) :
    (rq₁.insert tid prio₁).toList.filter p = (rq₂.insert tid prio₂).toList.filter p := by
  -- Determine membership of tid in both queues
  -- From hBase and hp: tid ∈ rq₁ ↔ tid ∈ rq₂
  have hMem_iff : tid ∈ rq₁ ↔ tid ∈ rq₂ := by
    constructor
    · intro h
      have h1 : tid ∈ rq₁.toList := (mem_toList_iff_mem rq₁ tid).mpr h
      have h2 : tid ∈ rq₁.toList.filter p := List.mem_filter.mpr ⟨h1, by simp [hp]⟩
      rw [hBase] at h2
      exact (mem_toList_iff_mem rq₂ tid).mp (List.mem_filter.mp h2).1
    · intro h
      have h1 : tid ∈ rq₂.toList := (mem_toList_iff_mem rq₂ tid).mpr h
      have h2 : tid ∈ rq₂.toList.filter p := List.mem_filter.mpr ⟨h1, by simp [hp]⟩
      rw [← hBase] at h2
      exact (mem_toList_iff_mem rq₁ tid).mp (List.mem_filter.mp h2).1
  by_cases hMem₁ : tid ∈ rq₁
  · -- Both in: insert is no-op on both sides
    have hMem₂ := hMem_iff.mp hMem₁
    have hc₁ : rq₁.contains tid = true := by rwa [mem_iff_contains] at hMem₁
    have hc₂ : rq₂.contains tid = true := by rwa [mem_iff_contains] at hMem₂
    simp only [insert, hc₁, hc₂, ite_true]; exact hBase
  · -- Both not in: insert appends tid
    have hMem₂ : ¬(tid ∈ rq₂) := fun h => hMem₁ (hMem_iff.mpr h)
    rw [toList_insert_not_mem _ _ _ hMem₁, toList_insert_not_mem _ _ _ hMem₂]
    simp only [List.filter_append, List.filter, hp]
    exact congrArg (· ++ [tid]) hBase

theorem toList_filter_remove_neg (rq : RunQueue) (tid : ThreadId)
    (p : ThreadId → Bool) (hp : p tid = false) :
    (rq.remove tid).toList.filter p = rq.toList.filter p := by
  suffices h : (rq.remove tid).flat.filter p = rq.flat.filter p by
    simp only [toList]; exact h
  unfold remove
  exact filter_filter_ne_of_false rq.flat tid p hp

theorem toList_nodup_of_flat_nodup (rq : RunQueue) (h : rq.flat.Nodup) :
    rq.toList.Nodup := h

/-- After remove, tid is not in the flat list. -/
theorem not_mem_remove_toList (rq : RunQueue) (tid : ThreadId) :
    tid ∉ (rq.remove tid).toList := by
  simp only [toList]
  unfold remove
  intro h
  rw [List.mem_filter] at h
  exact absurd h.2 (by simp)

/-- tid is in the toList after rotateToBack. -/
theorem mem_toList_rotateToBack_self (rq : RunQueue) (tid : ThreadId) (hMem : tid ∈ rq) :
    tid ∈ (rq.rotateToBack tid).toList := by
  simp only [toList]
  unfold rotateToBack
  have hc : rq.contains tid = true := by rwa [← mem_iff_contains]
  simp [hc, List.mem_append]

/-- rotateToBack preserves Nodup on the toList. -/
theorem toList_rotateToBack_nodup (rq : RunQueue) (tid : ThreadId)
    (hNodup : rq.toList.Nodup) (hMem : tid ∈ rq) :
    (rq.rotateToBack tid).toList.Nodup := by
  simp only [toList]
  unfold rotateToBack
  have hc : rq.contains tid = true := by rwa [← mem_iff_contains]
  simp [hc]
  suffices (rq.flat.erase tid ++ [tid]).Nodup by exact this
  have hErase : (rq.flat.erase tid).Nodup := hNodup.erase tid
  have hNotMemErase : tid ∉ rq.flat.erase tid := List.Nodup.not_mem_erase hNodup
  refine List.nodup_append.2 ⟨hErase, ?_, ?_⟩
  · exact List.pairwise_singleton _ _
  · intro x hx y hy
    have : y = tid := by simpa using hy
    subst this; intro hEq; subst hEq
    exact hNotMemErase hx

/-- An element other than tid is in the toList after rotateToBack iff it was before. -/
theorem mem_toList_rotateToBack_ne (rq : RunQueue) (tid x : ThreadId)
    (hne : x ≠ tid) :
    x ∈ (rq.rotateToBack tid).toList ↔ x ∈ rq.toList := by
  simp only [toList]
  unfold rotateToBack
  split
  · simp only [List.mem_append, List.mem_singleton]
    constructor
    · intro h; cases h with
      | inl h => exact List.mem_of_mem_erase h
      | inr h => exact absurd h hne
    · intro h
      exact Or.inl (List.mem_erase_of_ne hne |>.mpr h)
  · exact Iff.rfl

/-- WS-H9: Erasing an element with `p a = false` preserves the filtered list. -/
private theorem filter_erase_of_false {α : Type} [DecidableEq α] [BEq α] [LawfulBEq α]
    (xs : List α) (a : α) (p : α → Bool) (hp : p a = false) :
    (xs.erase a).filter p = xs.filter p := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    by_cases hxa : x = a
    · subst hxa; simp [List.erase_cons_head, List.filter, hp]
    · have hBeq : (x == a) = false := by
        exact beq_false_of_ne hxa
      simp [hBeq, List.filter]
      cases hpx : p x <;> simp_all

/-- WS-H9: rotateToBack preserves filtered list when the rotated element is filtered out.
Since `p tid = false`, rotating `tid` to the back doesn't change the filtered result. -/
theorem toList_filter_rotateToBack_neg (rq : RunQueue) (tid : ThreadId)
    (p : ThreadId → Bool) (hp : p tid = false) :
    (rq.rotateToBack tid).toList.filter p = rq.toList.filter p := by
  simp only [toList]
  unfold rotateToBack
  split
  · -- tid ∈ rq: flat becomes flat.erase tid ++ [tid]
    rw [List.filter_append]
    simp [List.filter, hp]
    exact filter_erase_of_false rq.flat tid p hp
  · -- tid ∉ rq: no change
    rfl

-- ============================================================================
-- WS-H6: RunQueue well-formedness predicate
-- ============================================================================

/-- WS-H6: RunQueue well-formedness — priority-bucket structure is consistent
with the membership set and thread-priority mapping.

This captures the implicit structural invariant maintained by the
insert/remove/rotate API (see RunQueue structure comment, lines 18-24).

- **Forward**: every thread in a priority bucket is a run-queue member whose
  recorded priority matches the bucket's priority.
- **Reverse**: every run-queue member appears in its recorded-priority bucket. -/
def wellFormed (rq : RunQueue) : Prop :=
  (∀ prio tid, tid ∈ ((rq.byPriority[prio]?).getD []) →
     rq.membership.contains tid = true ∧ rq.threadPriority[tid]? = some prio) ∧
  (∀ tid, rq.membership.contains tid = true →
     ∃ prio, rq.threadPriority[tid]? = some prio ∧
       tid ∈ ((rq.byPriority[prio]?).getD []))

/-- WS-H6: If a thread is in the max-priority bucket and the RunQueue is
well-formed, then the thread is a member of the run queue. -/
theorem maxPriorityBucket_subset (rq : RunQueue) (hwf : rq.wellFormed)
    (t : ThreadId) (ht : t ∈ rq.maxPriorityBucket) : t ∈ rq := by
  unfold maxPriorityBucket at ht
  split at ht
  · simp at ht
  · rename_i prio _
    unfold atPriority at ht
    rw [mem_iff_contains]
    exact (hwf.1 prio t ht).1

/-- WS-H6: If a thread is in the max-priority bucket and the RunQueue is
well-formed, then its recorded priority equals the max-priority value. -/
theorem maxPriorityBucket_threadPriority (rq : RunQueue) (hwf : rq.wellFormed)
    (t : ThreadId) (ht : t ∈ rq.maxPriorityBucket) :
    ∃ prio, rq.maxPriority = some prio ∧ rq.threadPriority[t]? = some prio := by
  unfold maxPriorityBucket at ht
  split at ht
  · simp at ht
  · rename_i prio hMP
    unfold atPriority at ht
    exact ⟨prio, hMP, (hwf.1 prio t ht).2⟩

/-- WS-H6: If a thread is a run-queue member whose recorded priority matches
`maxPriority`, then the thread is in `maxPriorityBucket`. -/
theorem mem_maxPriorityBucket_of_threadPriority (rq : RunQueue) (hwf : rq.wellFormed)
    (t : ThreadId) (prio : Priority)
    (hMem : t ∈ rq) (hTP : rq.threadPriority[t]? = some prio)
    (hMP : rq.maxPriority = some prio) : t ∈ rq.maxPriorityBucket := by
  show t ∈ (match rq.maxPriority with | none => [] | some p => rq.atPriority p)
  rw [hMP]
  show t ∈ rq.atPriority prio
  unfold atPriority
  obtain ⟨p, hpTP, hpBucket⟩ := hwf.2 t (mem_iff_contains.mp hMem)
  have hEq : p = prio := Option.some.inj (hpTP.symm.trans hTP)
  subst hEq
  exact hpBucket

-- ============================================================================
-- WS-H6: rotateToBack field-preservation lemmas
-- ============================================================================

/-- `rotateToBack` does not change `membership`. -/
theorem rotateToBack_membership (rq : RunQueue) (tid : ThreadId) :
    (rq.rotateToBack tid).membership = rq.membership := by
  unfold rotateToBack
  split <;> rfl

/-- `rotateToBack` does not change `threadPriority`. -/
theorem rotateToBack_threadPriority (rq : RunQueue) (tid : ThreadId) :
    (rq.rotateToBack tid).threadPriority = rq.threadPriority := by
  unfold rotateToBack
  split <;> rfl

/-- `rotateToBack` does not change `maxPriority`. -/
theorem rotateToBack_maxPriority (rq : RunQueue) (tid : ThreadId) :
    (rq.rotateToBack tid).maxPriority = rq.maxPriority := by
  unfold rotateToBack
  split <;> rfl

/-- `rotateToBack` does not change `contains`. -/
theorem rotateToBack_contains (rq : RunQueue) (tid t : ThreadId) :
    (rq.rotateToBack tid).contains t = rq.contains t := by
  simp only [contains, rotateToBack_membership]

/-- `rotateToBack` preserves membership (∈). -/
theorem rotateToBack_mem_iff (rq : RunQueue) (tid t : ThreadId) :
    t ∈ rq.rotateToBack tid ↔ t ∈ rq := by
  simp only [mem_iff_contains, rotateToBack_contains]

/-- Elements of the rotated flat list were in the original flat list. -/
theorem rotateToBack_flat_subset (rq : RunQueue) (tid t : ThreadId) :
    t ∈ (rq.rotateToBack tid).flat → t ∈ rq.flat := by
  unfold rotateToBack
  split
  · intro h
    simp only [List.mem_append, List.mem_singleton] at h
    rcases h with h | rfl
    · exact List.mem_of_mem_erase h
    · exact rq.flat_wf_rev _ (by assumption)
  · exact id

/-- Original flat list elements appear in the rotated flat list. -/
theorem rotateToBack_flat_superset (rq : RunQueue) (tid t : ThreadId) :
    t ∈ rq.flat → t ∈ (rq.rotateToBack tid).flat := by
  unfold rotateToBack
  split
  · intro h
    simp only [List.mem_append, List.mem_singleton]
    by_cases hEq : t = tid
    · exact Or.inr hEq
    · exact Or.inl ((List.mem_erase_of_ne hEq).2 h)
  · exact id

/-- `rotateToBack` preserves `wellFormed`. -/
theorem rotateToBack_preserves_wellFormed (rq : RunQueue) (hwf : rq.wellFormed) (tid : ThreadId) :
    (rq.rotateToBack tid).wellFormed := by
  by_cases hc : rq.contains tid
  · -- tid is in the run queue; rotation applies
    have hTidMem : rq.membership.contains tid = true := hc
    obtain ⟨tidPrio, hTidTP, hTidBucket⟩ := hwf.2 tid hTidMem
    have hPrioVal : rq.threadPriority[tid]?.getD ⟨0⟩ = tidPrio := by
      simp only [hTidTP, Option.getD]
    -- Fully unfold the rotated wellFormed to access raw fields
    unfold wellFormed
    simp only [rotateToBack, hc, dite_true]
    -- Now goal has: rq.membership, rq.threadPriority, rq.byPriority.insert ...
    constructor
    · -- Forward: bucket member → membership ∧ threadPriority
      intro p t hMem
      simp only [HashMap_getElem?_insert] at hMem
      split at hMem
      · -- prio == p: t is in the modified bucket
        rename_i hPEq
        simp only [Option.getD] at hMem
        simp only [List.mem_append, List.mem_singleton] at hMem
        rcases hMem with hFilter | rfl
        · have hOrig := (List.mem_filter.mp hFilter).1
          have hFwd := hwf.1 (rq.threadPriority[tid]?.getD ⟨0⟩) t hOrig
          exact ⟨hFwd.1, by rw [(eq_of_beq hPEq).symm]; exact hFwd.2⟩
        · exact ⟨hTidMem, by rw [(eq_of_beq hPEq).symm, hPrioVal]; exact hTidTP⟩
      · -- prio ≠ p: bucket unchanged
        exact hwf.1 p t hMem
    · -- Reverse: membership → ∃ prio with bucket entry
      intro t hMem
      obtain ⟨p, hTP, hBucket⟩ := hwf.2 t hMem
      refine ⟨p, hTP, ?_⟩
      simp only [HashMap_getElem?_insert]
      split
      · -- prio == p
        rename_i hPEq
        simp only [Option.getD, List.mem_append, List.mem_singleton]
        by_cases hTEq : t = tid
        · exact Or.inr hTEq
        · rw [← eq_of_beq hPEq] at hBucket
          exact Or.inl (List.mem_filter.mpr ⟨hBucket, by simp [hTEq]⟩)
      · exact hBucket
  · -- tid not in run queue; rotateToBack is identity
    simp only [rotateToBack, show ¬(rq.contains tid = true) from hc]; exact hwf

-- ============================================================================
-- WS-H12b: insert field-preservation and wellFormed lemmas
-- ============================================================================

/-- `insert` sets `threadPriority` to `rq.threadPriority.insert tid prio`
when `tid` is not already a member (identity otherwise). -/
theorem insert_threadPriority (rq : RunQueue) (tid : ThreadId) (prio : Priority) :
    (rq.insert tid prio).threadPriority =
      if rq.contains tid then rq.threadPriority
      else rq.threadPriority.insert tid prio := by
  unfold insert
  split
  · simp
  · simp

/-- `insert` preserves `wellFormed`. -/
theorem insert_preserves_wellFormed (rq : RunQueue) (hwf : rq.wellFormed)
    (tid : ThreadId) (prio : Priority) :
    (rq.insert tid prio).wellFormed := by
  unfold insert
  split
  · exact hwf  -- contains = true: identity
  · -- contains = false: prove for the new struct
    rename_i hNotContains
    have hNotMem : ¬(rq.membership.contains tid = true) := hNotContains
    unfold wellFormed; dsimp
    constructor
    · -- Forward: bucket member → membership ∧ threadPriority
      intro p t hMem
      rw [HashMap_getElem?_insert] at hMem
      split at hMem
      · -- prio == p: t is in the modified bucket
        rename_i hPEq
        simp only [Option.getD, List.mem_append, List.mem_singleton] at hMem
        rcases hMem with hOrig | rfl
        · -- t was in original bucket at priority prio
          have hFwd := hwf.1 prio t hOrig
          constructor
          · simp [Std.HashSet.contains_insert, hFwd.1]
          · rw [Std.HashMap.getElem?_insert,
                show (tid == t) = false from by
                  simp; intro hEq; subst hEq; exact hNotMem hFwd.1]
            rw [← eq_of_beq hPEq]; exact hFwd.2
        · -- t = tid (newly inserted)
          exact ⟨by simp [Std.HashSet.contains_insert],
                 by rw [Std.HashMap.getElem?_insert]; simp [eq_of_beq hPEq]⟩
      · -- prio ≠ p: bucket unchanged
        have hFwd := hwf.1 p t hMem
        exact ⟨by simp [Std.HashSet.contains_insert, hFwd.1],
               by rw [Std.HashMap.getElem?_insert,
                    show (tid == t) = false from by
                      simp; intro hEq; subst hEq; exact hNotMem hFwd.1]
                  exact hFwd.2⟩
    · -- Reverse: membership → ∃ prio with bucket entry
      intro t hMem
      have hMemOr : tid = t ∨ rq.membership.contains t = true := by
        simpa [Std.HashSet.contains_insert, Bool.or_eq_true, beq_iff_eq] using hMem
      rcases hMemOr with rfl | hOld
      · -- t = tid: use prio
        refine ⟨prio, ?_, ?_⟩
        · rw [Std.HashMap.getElem?_insert]; simp
        · rw [HashMap_getElem?_insert]; simp [Option.getD, List.mem_append]
      · -- t ≠ tid (old member)
        obtain ⟨p, hTP, hBucket⟩ := hwf.2 t hOld
        have hNe : tid ≠ t := fun hEq => by subst hEq; exact hNotMem hOld
        refine ⟨p, ?_, ?_⟩
        · rw [Std.HashMap.getElem?_insert,
              show (tid == t) = false from by simp [hNe]]
          exact hTP
        · rw [HashMap_getElem?_insert]
          split
          · rename_i hPEq
            simp only [Option.getD, List.mem_append, List.mem_singleton]
            have hPrioEq := eq_of_beq hPEq
            exact Or.inl (hPrioEq ▸ hBucket)
          · exact hBucket

end RunQueue
end SeLe4n.Kernel
