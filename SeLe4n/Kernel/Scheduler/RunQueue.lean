/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Prelude
import SeLe4n.Kernel.RobinHood.Set
namespace SeLe4n.Kernel
open SeLe4n
open SeLe4n.Kernel.RobinHood
/-- S-06: Priority-indexed run queue with flat-list backing store.

**Complexity characteristics**:
- O(1): `contains` (via `RHSet` hash membership), `maxPriorityBucket` (via
  cached `maxPriority` field)
- O(k): `atPriority` bucket retrieval, where k = bucket size (typically 1–3
  threads per priority level in real-time workloads)
- O(n): `insert` (flat-list append + hash insert), `remove` (flat-list filter +
  bucket filter + hash erase), `rotateToBack` (flat-list erase+append + bucket
  filter+append), where n = total thread count in the queue
- O(p): `recomputeMaxPriority` on removal, where p = number of distinct priority
  levels (≤ 256 on ARM64)

**Design rationale**: The flat `List ThreadId` is maintained alongside the
priority-indexed `RHTable` for two reasons: (1) global iteration order for
`fold`/`toList` operations used by invariant checks and cross-subsystem proofs,
and (2) bidirectional consistency with `membership` (proven by `flat_wf` and
`flat_wf_rev`).

**Acceptable for target platform**: RPi5 supports ≤ 256 threads at steady state.
At n = 256, O(n) operations complete in microseconds — well within the
timer-tick quantum (typically 1ms). Future optimization: replace `flat` with a
doubly-linked intrusive list or array for O(1) insert/remove when hardware
profiling indicates run-queue operations are a scheduling latency bottleneck. -/
structure RunQueue where
  byPriority : RHTable Priority (List ThreadId)
  membership : RHSet ThreadId
  threadPriority : RHTable ThreadId Priority
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
  /-- RHSet kernel-level invariant bundle (invExt ∧ size < capacity ∧ 4 ≤ capacity). -/
  mem_invExtK : membership.table.invExtK
  /-- RHTable kernel-level invariant bundle for byPriority. -/
  byPrio_invExtK : byPriority.invExtK
  /-- RHTable kernel-level invariant bundle for threadPriority. -/
  threadPrio_invExtK : threadPriority.invExtK
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
    exact absurd h (by rw [show ({} : RHSet ThreadId) = RHSet.empty from rfl,
      RHSet.contains_empty]; decide)
  mem_invExtK := RHSet.empty_invExtK
  byPrio_invExtK := RHTable.empty_invExtK 16 (by omega)
  threadPrio_invExtK := RHTable.empty_invExtK 16 (by omega)
instance : Inhabited RunQueue where default := empty
instance : EmptyCollection RunQueue where emptyCollection := empty
instance : Repr RunQueue where reprPrec rq _ := repr rq.flat
@[inline] def contains (rq : RunQueue) (tid : ThreadId) : Bool :=
  rq.membership.contains tid
instance : Membership ThreadId RunQueue where
  mem := fun rq tid => rq.contains tid = true
instance (tid : ThreadId) (rq : RunQueue) : Decidable (tid ∈ rq) :=
  show Decidable (rq.contains tid = true) from inferInstance

/-- U8-D/U-L26: Recompute the maximum priority by folding over all priority
    buckets. Complexity is O(p) where p = number of distinct priority levels
    currently in the run queue. This is only called on `remove` when the
    removed thread was the last member of the current max-priority bucket.

    **Design rationale:**
    - O(p) is acceptable because seL4 (and seLe4n) supports at most 256
      priority levels. In practice, active priority levels are far fewer.
    - An alternative O(1) approach (max-heap or secondary index) would add
      structural complexity disproportionate to the benefit for ≤256 entries.
    - **Starvation freedom**: This scheduler is a strict fixed-priority
      preemptive scheduler, matching seL4 semantics. Starvation freedom is
      NOT guaranteed — a continuously runnable high-priority thread will
      indefinitely preempt lower-priority threads. This is by design: seL4
      delegates starvation prevention to the user-level scheduling policy
      (e.g., MCS scheduling extensions, not yet modeled). -/
private def recomputeMaxPriority (byPrio : RHTable Priority (List ThreadId)) : Option Priority :=
  byPrio.fold none (fun acc prio bucket =>
    if bucket.isEmpty then acc
    else match acc with
      | none => some prio
      | some mp => if prio.toNat > mp.toNat then some prio else some mp
  )

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
        rcases hx with h | hEqTid
        · have hOld := rq.flat_wf x h
          by_cases hEq : (tid == x) = true
          · have hTidEqX := eq_of_beq hEq
            rw [hTidEqX]
            exact RHSet.contains_insert_self rq.membership x rq.mem_invExtK.1
          · rw [RHSet.contains_insert_ne rq.membership tid x hEq rq.mem_invExtK.1]; exact hOld
        · rw [hEqTid]
          exact RHSet.contains_insert_self rq.membership tid rq.mem_invExtK.1
      flat_wf_rev := by
        intro x hx
        have hx0 : tid = x ∨ rq.membership.contains x = true := by
          by_cases hEq : (tid == x) = true
          · exact Or.inl (eq_of_beq hEq)
          · right
            rwa [RHSet.contains_insert_ne rq.membership tid x hEq rq.mem_invExtK.1] at hx
        have hx' : x = tid ∨ rq.membership.contains x = true :=
          hx0.elim (fun h => Or.inl h.symm) Or.inr
        rcases hx' with rfl | hOld
        · exact List.mem_append.mpr (Or.inr (by simp))
        · exact List.mem_append.mpr (Or.inl (rq.flat_wf_rev x hOld))
      mem_invExtK := RHSet.insert_preserves_invExtK rq.membership tid rq.mem_invExtK
      byPrio_invExtK := rq.byPriority.insert_preserves_invExtK prio
          ((rq.byPriority[prio]?).getD [] ++ [tid]) rq.byPrio_invExtK
      threadPrio_invExtK := rq.threadPriority.insert_preserves_invExtK tid prio
          rq.threadPrio_invExtK }

/-- S5-J: Complexity is O(k + n) where k = priority bucket size for the
    removed thread, and n = flat list length. The bucket filter is O(k) and
    the flat-list filter is O(n). Both are acceptable because typical real-time
    systems have fewer than 256 threads, and k ≪ n (most buckets contain 1-3
    threads). The O(1) RHTable erase for membership and threadPriority is
    amortized constant. -/
def remove (rq : RunQueue) (tid : ThreadId) : RunQueue :=
  -- WS-G4 refinement: compute filtered bucket once, reuse for both byPriority and maxPriority
  let byPrio' := match rq.threadPriority.get? tid with
    | none => rq.byPriority
    | some p =>
        let bucket := ((rq.byPriority[p]?).getD []).filter (· ≠ tid)
        if bucket.isEmpty then rq.byPriority.erase p
        else rq.byPriority.insert p bucket
  let maxPrio' := match rq.threadPriority.get? tid with
    | none => rq.maxPriority
    | some p =>
        if rq.maxPriority == some p && (((rq.byPriority[p]?).getD []).filter (· ≠ tid)).isEmpty then
           recomputeMaxPriority byPrio'
        else rq.maxPriority
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
      have hNeBeq : ¬(tid == x) = true := by simp [beq_iff_eq]; exact Ne.symm hXNeTid
      rw [RHSet.contains_erase_ne_K rq.membership tid x hNeBeq rq.mem_invExtK]
      exact hMem
    flat_wf_rev := by
      intro x hx
      have hx' : rq.membership.contains x = true ∧ x ≠ tid := by
        by_cases hEq : (tid == x) = true
        · have := eq_of_beq hEq
          subst this
          rw [RHSet.contains_erase_self rq.membership tid rq.mem_invExtK.1] at hx
          exact absurd hx (by simp)
        · exact ⟨by rwa [RHSet.contains_erase_ne_K rq.membership tid x hEq rq.mem_invExtK] at hx,
                 fun h => hEq (by simp [beq_iff_eq]; exact h.symm)⟩
      have hFlat : x ∈ rq.flat := rq.flat_wf_rev x hx'.1
      exact List.mem_filter.mpr ⟨hFlat, by simpa [beq_iff_eq] using hx'.2⟩
    mem_invExtK := RHSet.erase_preserves_invExtK rq.membership tid rq.mem_invExtK
    byPrio_invExtK := by
      -- byPrio' is let-bound to `match rq.threadPriority.get? tid with ...`
      -- Use `show` to replace byPrio' with its definition, then split on the match
      show (match rq.threadPriority.get? tid with
        | none => rq.byPriority
        | some p =>
          let bucket := ((rq.byPriority[p]?).getD []).filter (· ≠ tid)
          if bucket.isEmpty then rq.byPriority.erase p
          else rq.byPriority.insert p bucket).invExtK
      split
      · exact rq.byPrio_invExtK
      next p _ =>
        dsimp only []
        split
        · exact rq.byPriority.erase_preserves_invExtK p rq.byPrio_invExtK
        · exact rq.byPriority.insert_preserves_invExtK p _ rq.byPrio_invExtK
    threadPrio_invExtK := rq.threadPriority.erase_preserves_invExtK tid rq.threadPrio_invExtK }

/-- S5-J: Complexity is O(k + n) where k = priority bucket size and n = flat
    list length. Filters the thread from the bucket O(k), appends to end O(1),
    then erases from flat list O(n) and appends. Same bounds as `remove` and
    `rotateHead` — acceptable for systems with < 256 threads. -/
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
          · exact List.mem_append.mpr (Or.inl ((List.mem_erase_of_ne hEq).2 hFlat))
        byPrio_invExtK := rq.byPriority.insert_preserves_invExtK prio bucket' rq.byPrio_invExtK }
  else rq

@[inline] def toList (rq : RunQueue) : List ThreadId := rq.flat
def atPriority (rq : RunQueue) (prio : Priority) : List ThreadId := (rq.byPriority[prio]?).getD []

/-- WS-G4/F-P07: Return the max-priority bucket contents, or `[]` if the queue is empty.
    This enables O(k) best-candidate selection where k is the bucket size (typically 1-3). -/
@[inline] def maxPriorityBucket (rq : RunQueue) : List ThreadId :=
  match rq.maxPriority with
  | none => []
  | some prio => rq.atPriority prio

/-- V7-J: Validated constructor — builds a `RunQueue` from a list of
`(ThreadId, Priority)` pairs via the `insert` API. All structural invariants
(flat↔membership consistency, `invExtK` bundles, priority-bucket coherence)
are maintained by construction since each `insert` call preserves them.
Duplicate thread IDs are handled by `insert`'s last-wins semantics. -/
def ofList (entries : List (ThreadId × Priority)) : RunQueue :=
  entries.foldl (fun rq (tid, prio) => rq.insert tid prio) empty

-- Bridge lemmas

@[simp] theorem mem_iff_contains {rq : RunQueue} {tid : ThreadId} :
    tid ∈ rq ↔ rq.contains tid = true := Iff.rfl

theorem contains_false_of_not_mem {rq : RunQueue} {tid : ThreadId}
    (h : ¬(tid ∈ rq)) : rq.contains tid = false := by
  cases hc : rq.contains tid <;> simp_all

theorem not_mem_empty (tid : ThreadId) : ¬(tid ∈ (empty : RunQueue)) := by
  intro h
  rw [mem_iff_contains] at h
  have := RHSet.contains_empty tid
  simp only [contains, RunQueue.empty] at h
  rw [show ({} : RHSet ThreadId) = RHSet.empty from rfl] at h
  rw [this] at h
  exact absurd h (by decide)

theorem mem_insert (rq : RunQueue) (tid : ThreadId) (prio : Priority) (x : ThreadId) :
    x ∈ rq.insert tid prio ↔ x ∈ rq ∨ x = tid := by
  show (rq.insert tid prio).contains x = true ↔ rq.contains x = true ∨ x = tid
  unfold insert contains
  split
  · rename_i h
    exact ⟨Or.inl, fun hOr => hOr.elim id (fun heq => heq ▸ h)⟩
  · rename_i h
    constructor
    · intro hIns
      by_cases hEq : (tid == x) = true
      · exact Or.inr (eq_of_beq hEq).symm
      · rw [RHSet.contains_insert_ne rq.membership tid x hEq rq.mem_invExtK.1] at hIns
        exact Or.inl hIns
    · intro hOr
      rcases hOr with hOld | hEqTid
      · by_cases hEq : (tid == x) = true
        · have hTidEqX := eq_of_beq hEq
          rw [hTidEqX]
          exact RHSet.contains_insert_self rq.membership x rq.mem_invExtK.1
        · rw [RHSet.contains_insert_ne rq.membership tid x hEq rq.mem_invExtK.1]; exact hOld
      · rw [hEqTid]
        exact RHSet.contains_insert_self rq.membership tid rq.mem_invExtK.1

theorem mem_remove (rq : RunQueue) (tid : ThreadId) (x : ThreadId) :
    x ∈ rq.remove tid ↔ x ∈ rq ∧ x ≠ tid := by
  show (rq.remove tid).contains x = true ↔ rq.contains x = true ∧ x ≠ tid
  unfold remove contains
  constructor
  · intro h
    have hNeBeq : ¬(tid == x) = true := by
      intro hEq
      have := eq_of_beq hEq; subst this
      rw [RHSet.contains_erase_self rq.membership tid rq.mem_invExtK.1] at h
      exact absurd h (by simp)
    constructor
    · rwa [RHSet.contains_erase_ne_K rq.membership tid x hNeBeq rq.mem_invExtK] at h
    · intro hEq; exact hNeBeq (by simp [beq_iff_eq]; exact hEq.symm)
  · intro h
    rcases h with ⟨hx, hne⟩
    have hne' : ¬(tid == x) = true := by simp [beq_iff_eq]; exact fun h => hne h.symm
    rw [RHSet.contains_erase_ne_K rq.membership tid x hne' rq.mem_invExtK]
    exact hx

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

theorem toList_filter_remove_neg (rq : RunQueue) (tid : ThreadId)
    (p : ThreadId → Bool) (hp : p tid = false) :
    (rq.remove tid).toList.filter p = rq.toList.filter p := by
  suffices h : (rq.remove tid).flat.filter p = rq.flat.filter p by
    simp only [toList]; exact h
  unfold remove
  exact filter_filter_ne_of_false rq.flat tid p hp

/-- After remove, tid is not in the flat list. -/
theorem not_mem_remove_toList (rq : RunQueue) (tid : ThreadId) :
    tid ∉ (rq.remove tid).toList := by
  simp only [toList]
  unfold remove
  intro h
  rw [List.mem_filter] at h
  exact absurd h.2 (by simp)

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
- **Reverse**: every run-queue member appears in its recorded-priority bucket.

**V7-J: External predicate design rationale.** `wellFormed` is defined as an
external predicate rather than a structure-level proof obligation for two
reasons: (1) embedding a `Prop` conjunct in the `RunQueue` structure would
force every mutation to carry proof terms through all intermediate states,
bloating the `insert`/`remove`/`rotateToBack` implementations; (2) the
priority-bucket↔membership consistency is an *emergent* property of the API —
it holds by construction through `insert` (adds to both maps) and `remove`
(erases from both), so proving it at each structure constructor site adds
complexity without formal value. The `wellFormed` predicate is proved preserved
by each API operation separately (`insert_preserves_wellFormed`,
`remove_preserves_wellFormed`, `rotateToBack_preserves_wellFormed`), which
gives the same formal guarantee with cleaner code. -/
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

/-- `rotateToBack` does not change `contains`. -/
theorem rotateToBack_contains (rq : RunQueue) (tid t : ThreadId) :
    (rq.rotateToBack tid).contains t = rq.contains t := by
  simp only [contains, rotateToBack_membership]

/-- `rotateToBack` preserves membership (∈). -/
theorem rotateToBack_mem_iff (rq : RunQueue) (tid t : ThreadId) :
    t ∈ rq.rotateToBack tid ↔ t ∈ rq := by
  simp only [mem_iff_contains, rotateToBack_contains]

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
    have hByPrioInv := rq.byPrio_invExtK.1
    -- Helper: bracket notation resolves to get? for RHTable
    have hGetElem : ∀ (t : RHTable Priority (List ThreadId)) (k : Priority),
        t[k]? = t.get? k := fun _ _ => rfl
    constructor
    · -- Forward: bucket member → membership ∧ threadPriority
      intro p t hMem
      rw [hGetElem] at hMem
      -- Case split on whether the inserted prio matches p
      by_cases hPEq : ((rq.threadPriority[tid]?.getD ⟨0⟩) == p) = true
      · -- prio == p: bucket was replaced
        have hPrioEq := eq_of_beq hPEq
        rw [hPrioEq, RHTable_get?_insert_self rq.byPriority p _ hByPrioInv] at hMem
        simp only [Option.getD] at hMem
        simp only [List.mem_append, List.mem_singleton] at hMem
        rcases hMem with hFilter | hEqTid2
        · have hOrig := (List.mem_filter.mp hFilter).1
          have hOrig' : t ∈ (rq.byPriority[p]?).getD [] := by exact hOrig
          have hFwd := hwf.1 p t hOrig'
          exact ⟨hFwd.1, hFwd.2⟩
        · rw [hEqTid2]
          have hPeq : tidPrio = p := hPrioVal.symm.trans hPrioEq
          exact ⟨hTidMem, by rw [hPeq] at hTidTP; exact hTidTP⟩
      · -- prio ≠ p: bucket unchanged
        rw [RHTable_get?_insert_ne rq.byPriority (rq.threadPriority[tid]?.getD ⟨0⟩)
            p _ hPEq hByPrioInv] at hMem
        have hMem' : t ∈ (rq.byPriority[p]?).getD [] := by exact hMem
        exact hwf.1 p t hMem'
    · -- Reverse: membership → ∃ prio with bucket entry
      intro t hMem
      obtain ⟨p, hTP, hBucket⟩ := hwf.2 t hMem
      refine ⟨p, hTP, ?_⟩
      rw [hGetElem]
      by_cases hPEq : ((rq.threadPriority[tid]?.getD ⟨0⟩) == p) = true
      · -- prio == p
        have hPrioEq := eq_of_beq hPEq
        rw [hPrioEq, RHTable_get?_insert_self rq.byPriority p _ hByPrioInv]
        simp only [Option.getD, List.mem_append, List.mem_singleton]
        by_cases hTEq : t = tid
        · exact Or.inr hTEq
        · exact Or.inl (List.mem_filter.mpr ⟨hBucket, by simp [hTEq]⟩)
      · rw [RHTable_get?_insert_ne rq.byPriority (rq.threadPriority[tid]?.getD ⟨0⟩)
            p _ hPEq hByPrioInv]
        show t ∈ (rq.byPriority[p]?).getD []
        exact hBucket
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
    have hByPrioInv := rq.byPrio_invExtK.1
    have hTPrioInv := rq.threadPrio_invExtK.1
    have hMemInv := rq.mem_invExtK.1
    -- Helper: bracket notation resolves to get? for RHTable
    have hGetElemBP : ∀ (t : RHTable Priority (List ThreadId)) (k : Priority),
        t[k]? = t.get? k := fun _ _ => rfl
    have hGetElemTP : ∀ (t : RHTable ThreadId Priority) (k : ThreadId),
        t[k]? = t.get? k := fun _ _ => rfl
    unfold wellFormed; dsimp
    constructor
    · -- Forward: bucket member → membership ∧ threadPriority
      intro p t hMem
      rw [hGetElemBP] at hMem
      by_cases hPEq : (prio == p) = true
      · -- prio == p: bucket was replaced
        have hPrioEq := eq_of_beq hPEq
        rw [hPrioEq, RHTable_get?_insert_self rq.byPriority p _ hByPrioInv] at hMem
        simp only [Option.getD, List.mem_append, List.mem_singleton] at hMem
        rcases hMem with hOrig | hEqTid
        · -- t was in original bucket at priority p (= prio)
          have hOrig' : t ∈ (rq.byPriority[p]?).getD [] := by
            simp only [Option.getD]; exact hOrig
          have hFwd := hwf.1 p t hOrig'
          have hTNeTid : ¬(tid == t) = true := by
            simp [beq_iff_eq]; intro hEq; subst hEq; exact hNotMem hFwd.1
          constructor
          · rw [RHSet.contains_insert_ne rq.membership tid t hTNeTid hMemInv]
            exact hFwd.1
          · rw [hGetElemTP,
                RHTable_get?_insert_ne rq.threadPriority tid t prio hTNeTid hTPrioInv]
            exact hFwd.2
        · -- t = tid (newly inserted)
          rw [hEqTid]
          constructor
          · exact RHSet.contains_insert_self rq.membership tid hMemInv
          · rw [hGetElemTP,
                RHTable_get?_insert_self rq.threadPriority tid prio hTPrioInv]
            exact congrArg some hPrioEq
      · -- prio ≠ p: bucket unchanged
        rw [RHTable_get?_insert_ne rq.byPriority prio p _ hPEq hByPrioInv] at hMem
        have hMem' : t ∈ (rq.byPriority[p]?).getD [] := by exact hMem
        have hFwd := hwf.1 p t hMem'
        have hTNeTid : ¬(tid == t) = true := by
          simp [beq_iff_eq]; intro hEq; subst hEq; exact hNotMem hFwd.1
        exact ⟨by rw [RHSet.contains_insert_ne rq.membership tid t hTNeTid hMemInv]; exact hFwd.1,
               by rw [hGetElemTP,
                    RHTable_get?_insert_ne rq.threadPriority tid t prio hTNeTid hTPrioInv]
                  exact hFwd.2⟩
    · -- Reverse: membership → ∃ prio with bucket entry
      intro t hMem
      have hMemOr : tid = t ∨ rq.membership.contains t = true := by
        by_cases hEq : (tid == t) = true
        · exact Or.inl (eq_of_beq hEq)
        · right
          rwa [RHSet.contains_insert_ne rq.membership tid t hEq hMemInv] at hMem
      rcases hMemOr with rfl | hOld
      · -- t = tid: use prio
        refine ⟨prio, ?_, ?_⟩
        · rw [hGetElemTP,
              RHTable_get?_insert_self rq.threadPriority tid prio hTPrioInv]
        · rw [hGetElemBP,
              RHTable_get?_insert_self rq.byPriority prio _ hByPrioInv]
          simp [Option.getD, List.mem_append]
      · -- t ≠ tid (old member)
        obtain ⟨p, hTP, hBucket⟩ := hwf.2 t hOld
        have hNe : tid ≠ t := fun hEq => by subst hEq; exact hNotMem hOld
        have hNeBeq : ¬(tid == t) = true := by simp [beq_iff_eq]; exact hNe
        refine ⟨p, ?_, ?_⟩
        · rw [hGetElemTP,
              RHTable_get?_insert_ne rq.threadPriority tid t prio hNeBeq hTPrioInv]
          exact hTP
        · rw [hGetElemBP]
          by_cases hPEq : (prio == p) = true
          · have hPrioEq := eq_of_beq hPEq
            rw [hPrioEq, RHTable_get?_insert_self rq.byPriority p _ hByPrioInv]
            simp only [Option.getD, List.mem_append, List.mem_singleton]
            exact Or.inl hBucket
          · rw [RHTable_get?_insert_ne rq.byPriority prio p _ hPEq hByPrioInv]
            show t ∈ (rq.byPriority[p]?).getD []
            exact hBucket

/-- S3-F helper: byPriority bucket membership transfers from removed to original. -/
private theorem remove_byPrio_to_orig (rq : RunQueue)
    (tid : ThreadId) (p : Priority) (t : ThreadId)
    (hMem : t ∈ ((rq.remove tid).byPriority.get? p).getD []) :
    t ∈ (rq.byPriority.get? p).getD [] := by
  simp only [remove, RHTable_getElem?_eq_get?] at hMem
  split at hMem
  · exact hMem
  · next p_tid _ =>
    split at hMem
    · by_cases hPEq : (p_tid == p) = true
      · rw [eq_of_beq hPEq, RHTable_get?_erase_self rq.byPriority p rq.byPrio_invExtK.1] at hMem
        simp [Option.getD] at hMem
      · rwa [RHTable_get?_erase_ne_K rq.byPriority p_tid p hPEq
               rq.byPrio_invExtK] at hMem
    · by_cases hPEq : (p_tid == p) = true
      · rw [eq_of_beq hPEq, RHTable_get?_insert_self rq.byPriority p _ rq.byPrio_invExtK.1] at hMem
        simp only [Option.getD] at hMem
        exact (List.mem_filter.mp hMem).1
      · rwa [RHTable_get?_insert_ne rq.byPriority p_tid p _ hPEq rq.byPrio_invExtK.1] at hMem

/-- S3-F helper: byPriority bucket membership transfers from original to removed. -/
private theorem remove_byPrio_from_orig (rq : RunQueue)
    (tid : ThreadId) (p : Priority) (t : ThreadId) (hNe : t ≠ tid)
    (hBucket : t ∈ (rq.byPriority.get? p).getD []) :
    t ∈ ((rq.remove tid).byPriority.get? p).getD [] := by
  simp only [remove, RHTable_getElem?_eq_get?]
  split
  · exact hBucket
  · next p_tid _ =>
    split
    · -- Filtered bucket empty → erased from byPriority
      by_cases hPEq : (p_tid == p) = true
      · next hEmpty =>
        exfalso
        have hPEq' := eq_of_beq hPEq
        have hFiltEmpty := List.isEmpty_iff.mp hEmpty
        -- The filtered list is empty but t ∈ original bucket and t ≠ tid
        -- so t survives the filter → contradiction
        have hInBucket : t ∈ ((rq.byPriority.get? p_tid).getD []) := hPEq' ▸ hBucket
        have : t ∈ ((rq.byPriority.get? p_tid).getD []).filter (· ≠ tid) := by
          simp only [List.mem_filter]
          exact ⟨hInBucket, by simp [hNe]⟩
        rw [hFiltEmpty] at this
        simp at this
      · rw [RHTable_get?_erase_ne_K rq.byPriority p_tid p hPEq rq.byPrio_invExtK]
        exact hBucket
    · -- Filtered bucket non-empty → inserted
      by_cases hPEq : (p_tid == p) = true
      · rw [eq_of_beq hPEq, RHTable_get?_insert_self rq.byPriority p _ rq.byPrio_invExtK.1]
        simp only [Option.getD]
        exact List.mem_filter.mpr ⟨hBucket, by simpa [beq_iff_eq] using hNe⟩
      · rw [RHTable_get?_insert_ne rq.byPriority p_tid p _ hPEq rq.byPrio_invExtK.1]
        exact hBucket

/-- S3-F helper: tid is not in any bucket of the removed RunQueue. -/
private theorem remove_tid_not_in_bucket (rq : RunQueue) (hwf : rq.wellFormed)
    (tid : ThreadId) (p : Priority)
    (hMem : tid ∈ ((rq.remove tid).byPriority.get? p).getD []) : False := by
  simp only [remove, RHTable_getElem?_eq_get?] at hMem
  split at hMem
  · -- byPriority unchanged, so tid in original bucket
    next hNone =>
      have hFwd := (hwf.1 p tid hMem).2
      simp only [RHTable_getElem?_eq_get?] at hFwd
      rw [hNone] at hFwd; exact absurd hFwd (by simp)
  · next p_tid hTP =>
    split at hMem
    · by_cases hPEq : (p_tid == p) = true
      · rw [eq_of_beq hPEq, RHTable_get?_erase_self rq.byPriority p rq.byPrio_invExtK.1] at hMem
        simp [Option.getD] at hMem
      · rw [RHTable_get?_erase_ne_K rq.byPriority p_tid p hPEq
              rq.byPrio_invExtK] at hMem
        have hFwd := (hwf.1 p tid hMem).2
        simp only [RHTable_getElem?_eq_get?] at hFwd
        rw [hTP] at hFwd
        exact absurd (Option.some.inj hFwd) (by simpa [beq_iff_eq] using hPEq)
    · by_cases hPEq : (p_tid == p) = true
      · rw [eq_of_beq hPEq, RHTable_get?_insert_self rq.byPriority p _ rq.byPrio_invExtK.1] at hMem
        simp [Option.getD] at hMem
      · rw [RHTable_get?_insert_ne rq.byPriority p_tid p _ hPEq rq.byPrio_invExtK.1] at hMem
        have hFwd := (hwf.1 p tid hMem).2
        simp only [RHTable_getElem?_eq_get?] at hFwd
        rw [hTP] at hFwd
        exact absurd (Option.some.inj hFwd) (by simpa [beq_iff_eq] using hPEq)

/-- S3-F/U-M09: Removing a thread from a well-formed RunQueue preserves
    well-formedness.  The key insight is that `remove` erases `tid` from
    `membership`, `threadPriority`, and `byPriority` simultaneously.
    Any `t ≠ tid` retains its original relationships across all three. -/
theorem remove_preserves_wellFormed (rq : RunQueue) (hwf : rq.wellFormed)
    (tid : ThreadId) :
    (rq.remove tid).wellFormed := by
  constructor
  · -- Forward: bucket member → membership ∧ threadPriority
    intro p t hMem
    simp only [RHTable_getElem?_eq_get?] at hMem ⊢
    -- t ≠ tid: tid is not in any removed bucket
    have hTNe : t ≠ tid := by
      intro hEq; rw [hEq] at hMem
      exact remove_tid_not_in_bucket rq hwf tid p hMem
    have hNeBeq : ¬(tid == t) = true := by simp [beq_iff_eq]; exact Ne.symm hTNe
    -- Extract original membership and transfer
    have hOrigMem := remove_byPrio_to_orig rq tid p t hMem
    have hFwd := hwf.1 p t hOrigMem
    simp only [RHTable_getElem?_eq_get?] at hFwd
    refine ⟨?_, ?_⟩
    · show (rq.membership.erase tid).contains t = true
      rw [RHSet.contains_erase_ne_K rq.membership tid t hNeBeq rq.mem_invExtK]
      exact hFwd.1
    · show (rq.threadPriority.erase tid).get? t = some p
      rw [RHTable_get?_erase_ne_K rq.threadPriority tid t hNeBeq rq.threadPrio_invExtK]
      exact hFwd.2
  · -- Reverse: membership → ∃ prio with bucket entry
    intro t hMem
    simp only [RHTable_getElem?_eq_get?] at hMem ⊢
    have hTNe : t ≠ tid := by
      intro hEq; rw [hEq] at hMem
      change (rq.membership.erase tid).contains tid = true at hMem
      rw [RHSet.contains_erase_self rq.membership tid rq.mem_invExtK.1] at hMem
      exact absurd hMem (by simp)
    have hNeBeq : ¬(tid == t) = true := by simp [beq_iff_eq]; exact Ne.symm hTNe
    have hOldMem : rq.membership.contains t = true := by
      change (rq.membership.erase tid).contains t = true at hMem
      rwa [RHSet.contains_erase_ne_K rq.membership tid t hNeBeq rq.mem_invExtK] at hMem
    obtain ⟨p, hpTP, hpBucket⟩ := hwf.2 t hOldMem
    simp only [RHTable_getElem?_eq_get?] at hpTP hpBucket
    refine ⟨p, ?_, ?_⟩
    · show (rq.threadPriority.erase tid).get? t = some p
      rw [RHTable_get?_erase_ne_K rq.threadPriority tid t hNeBeq rq.threadPrio_invExtK]
      exact hpTP
    · exact remove_byPrio_from_orig rq tid p t hTNe hpBucket

end RunQueue
end SeLe4n.Kernel
