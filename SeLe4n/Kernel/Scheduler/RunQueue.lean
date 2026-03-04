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
  /-- WS-H6/M-04: Reverse structural invariant — every HashSet member appears in
      the flat list. Together with `flat_wf`, this yields full bidirectional
      consistency between O(1) membership and list-based scheduling scans. -/
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
        have : x ∈ rq.membership ∨ x = tid := by
          have htmp : tid = x ∨ x ∈ rq.membership := by
            simpa [Std.HashSet.contains_insert, beq_iff_eq, Bool.or_eq_true] using hx
          exact htmp.elim (fun h => Or.inr h.symm) Or.inl
        rcases this with hOld | hEq
        · exact List.mem_append.mpr (Or.inl (rq.flat_wf_rev x hOld))
        · subst hEq
          exact List.mem_append.mpr (Or.inr (List.mem_singleton_self x)) }

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
      have hxNe : x ≠ tid := by
        intro hEq
        subst hEq
        simp [Std.HashSet.contains_erase] at hx
      have hxMem : x ∈ rq.membership := by
        have hFalse : (x == tid) = false := by simp [hxNe]
        have htmp : ¬ tid = x ∧ x ∈ rq.membership := by
          simpa [Std.HashSet.contains_erase, hFalse, Bool.and_eq_true] using hx
        exact htmp.2
      have hxFlat : x ∈ rq.flat := rq.flat_wf_rev x hxMem
      exact List.mem_filter.mpr ⟨hxFlat, by simp [hxNe]⟩ }

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
                    have hOld : x ∈ rq.flat := rq.flat_wf_rev x hx
                    by_cases hEq : x = tid
                    · subst hEq; exact List.mem_append.mpr (Or.inr (List.mem_singleton_self x))
                    · exact List.mem_append.mpr (Or.inl ((List.mem_erase_of_ne hEq).2 hOld)) }
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
          have hOld : x ∈ rq.flat := rq.flat_wf_rev x hx
          by_cases hEq : x = tid
          · subst hEq; exact List.mem_append.mpr (Or.inr (List.mem_singleton_self x))
          · exact List.mem_append.mpr (Or.inl ((List.mem_erase_of_ne hEq).2 hOld)) }
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
  simp only [Std.HashSet.contains_erase, Bool.and_eq_true]
  exact ⟨fun ⟨hne, hx⟩ => ⟨hx, fun heq => by subst heq; simp at hne⟩,
         fun ⟨hx, hne⟩ => ⟨by simp [Ne.symm hne], hx⟩⟩

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

/-- WS-H6/M-04: Reverse bridge from O(1) membership to flat-list membership. -/
theorem membership_implies_flat (rq : RunQueue) (tid : ThreadId)
    (h : tid ∈ rq) : tid ∈ rq.toList := by
  exact rq.flat_wf_rev tid (by simpa [mem_iff_contains] using h)

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

end RunQueue
end SeLe4n.Kernel
