-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations.ReschedulePending
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore

/-!
# The reschedule flags cover the commit diff

The KSC-1 / HAL-3 row of `docs/REGISTERED_DEBT.md`, PR B.  A step `pre → post`
on executing core `e` **covers** a remote core `c` when it either raised (or
kept) `c`'s reschedule flag, or left `c`'s scheduling decision unstaled:
nothing joined `c`'s run queue, no queued thread's effective key moved,
`c`'s current slot is unchanged and its occupant's claim to the CPU did not
weaken (`coreDecisionUnstaled`).  The flags are allowed to over-approximate —
a raise that stales nothing costs one scheduling point that finds nothing to
do — so the relation is coverage, not equality.

The relation composes (`reschedulePendingCovers_trans`): a sequence of steps
each covering every remote core covers it end to end, provided no step lowers a
remote flag (`reschedulePendingMonotone`).  And it is what the commit needs
(`computeCrossCoreSgis_core_flagged_of_covers`): every core the whole-index
diff `computeCrossCoreSgis` names has its flag up in the post-state, so the
flag-derived list `rescheduleSgisFromFlags` names it unless it was already
pending at the step's start.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId SgiKind allCores numCores)
open SeLe4n.Kernel.PriorityInheritance (crossCoreSgiBody currentSlotChangeSgis
  computeCrossCoreSgis)

/-- A thread's effective scheduling key as the diff compares it: the effective
priority and the effective deadline's value, or `none` when no TCB is stored
under the id. -/
def schedKeyView (st : SystemState) (t : SeLe4n.ThreadId) :
    Option (SeLe4n.Priority × Nat) :=
  (st.getTcb? t).map fun tcb =>
    ((resolveEffectivePrioDeadline st tcb).1, (resolveEffectivePrioDeadline st tcb).2.val)

/-- The thread's claim to a CPU it holds did not weaken from `pre` to `post`:
its effective priority did not drop and its effective deadline did not move
later.  A thread with no TCB in `post` claims nothing. -/
def schedKeyNotWeakened (pre post : SystemState) (t : SeLe4n.ThreadId) : Prop :=
  ∀ kq, schedKeyView post t = some kq →
    ∃ kp, schedKeyView pre t = some kp ∧ kp.1.val ≤ kq.1.val ∧ kq.2 ≤ kp.2

/-- Core `c`'s scheduling decision is not staled by `pre → post`: every thread
queued on `c` afterwards was queued there before with the same key, the current
slot is unchanged, and its occupant's claim did not weaken.  (Removing a queued
thread, or strengthening the current one, stales nothing.) -/
def coreDecisionUnstaled (pre post : SystemState) (c : CoreId) : Prop :=
  (∀ t, t ∈ post.scheduler.runQueueOnCore c →
      t ∈ pre.scheduler.runQueueOnCore c ∧ schedKeyView pre t = schedKeyView post t) ∧
  post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c ∧
  (∀ t, post.scheduler.currentOnCore c = some t → schedKeyNotWeakened pre post t)

/-- The step `pre → post` on executing core `e` covers every remote core: each
one's flag is up afterwards, or its decision was not staled. -/
def reschedulePendingCovers (e : CoreId) (pre post : SystemState) : Prop :=
  ∀ c, c ≠ e →
    post.scheduler.reschedulePendingOnCore c = true ∨ coreDecisionUnstaled pre post c

/-- No remote flag is lowered by `st → st'` (only a core's own scheduling point
clears its flag, and on the syscall path that core is the executing one). -/
def reschedulePendingMonotone (e : CoreId) (st st' : SystemState) : Prop :=
  ∀ c, c ≠ e → st.scheduler.reschedulePendingOnCore c = true →
    st'.scheduler.reschedulePendingOnCore c = true

/-! ### Composition laws -/

theorem schedKeyNotWeakened_refl (st : SystemState) (t : SeLe4n.ThreadId) :
    schedKeyNotWeakened st st t :=
  fun kq h => ⟨kq, h, Nat.le_refl _, Nat.le_refl _⟩

theorem schedKeyNotWeakened_trans {a b c : SystemState} {t : SeLe4n.ThreadId}
    (h₁ : schedKeyNotWeakened a b t) (h₂ : schedKeyNotWeakened b c t) :
    schedKeyNotWeakened a c t := by
  intro kq hq
  obtain ⟨kb, hb, hb1, hb2⟩ := h₂ kq hq
  obtain ⟨ka, ha, ha1, ha2⟩ := h₁ kb hb
  exact ⟨ka, ha, Nat.le_trans ha1 hb1, Nat.le_trans hb2 ha2⟩

theorem schedKeyNotWeakened_of_eq {pre post : SystemState} {t : SeLe4n.ThreadId}
    (h : schedKeyView pre t = schedKeyView post t) : schedKeyNotWeakened pre post t :=
  fun kq hq => ⟨kq, h.trans hq, Nat.le_refl _, Nat.le_refl _⟩

theorem coreDecisionUnstaled_refl (st : SystemState) (c : CoreId) :
    coreDecisionUnstaled st st c :=
  ⟨fun _ h => ⟨h, rfl⟩, rfl, fun t _ => schedKeyNotWeakened_refl st t⟩

theorem coreDecisionUnstaled_trans {a b d : SystemState} {c : CoreId}
    (h₁ : coreDecisionUnstaled a b c) (h₂ : coreDecisionUnstaled b d c) :
    coreDecisionUnstaled a d c := by
  obtain ⟨hq₁, hc₁, hw₁⟩ := h₁
  obtain ⟨hq₂, hc₂, hw₂⟩ := h₂
  refine ⟨fun t ht => ?_, hc₂.trans hc₁, fun t ht => ?_⟩
  · obtain ⟨hb, hk₂⟩ := hq₂ t ht
    obtain ⟨ha, hk₁⟩ := hq₁ t hb
    exact ⟨ha, hk₁.trans hk₂⟩
  · exact schedKeyNotWeakened_trans (hw₁ t (hc₂ ▸ ht)) (hw₂ t ht)

theorem reschedulePendingCovers_refl (e : CoreId) (st : SystemState) :
    reschedulePendingCovers e st st :=
  fun c _ => Or.inr (coreDecisionUnstaled_refl st c)

theorem reschedulePendingMonotone_refl (e : CoreId) (st : SystemState) :
    reschedulePendingMonotone e st st :=
  fun _ _ h => h

theorem reschedulePendingMonotone_trans {e : CoreId} {a b d : SystemState}
    (h₁ : reschedulePendingMonotone e a b) (h₂ : reschedulePendingMonotone e b d) :
    reschedulePendingMonotone e a d :=
  fun c hc h => h₂ c hc (h₁ c hc h)

/-- Coverage composes: a step that covers every remote core, followed by one
that covers it and lowers no remote flag, covers it end to end. -/
theorem reschedulePendingCovers_trans {e : CoreId} {a b d : SystemState}
    (h₁ : reschedulePendingCovers e a b) (h₂ : reschedulePendingCovers e b d)
    (hMono : reschedulePendingMonotone e b d) :
    reschedulePendingCovers e a d := by
  intro c hc
  rcases h₂ c hc with hFlag | hU₂
  · exact Or.inl hFlag
  · rcases h₁ c hc with hFlag | hU₁
    · exact Or.inl (hMono c hc hFlag)
    · exact Or.inr (coreDecisionUnstaled_trans hU₁ hU₂)

/-! ### The bridge to the commit diff -/

/-- The key view of a stored TCB, spelled out. -/
theorem schedKeyView_of_getTcb {st : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    (h : st.getTcb? t = some tcb) :
    schedKeyView st t =
      some ((resolveEffectivePrioDeadline st tcb).1, (resolveEffectivePrioDeadline st tcb).2.val) := by
  simp [schedKeyView, h]

/-- Every object rule of the diff that fires names a remote core whose
decision the step staled.  `hId` is the store's self-identity at `oid` (a TCB
stored under `oid` is the thread `oid` names). -/
theorem crossCoreSgiBody_some_staled {pre post : SystemState} {e : CoreId} {oid : SeLe4n.ObjId}
    {c : CoreId} {k : SgiKind}
    (hId : ∀ tcb : TCB, post.getObject? oid = some (.tcb tcb) → tcb.tid.toObjId = oid)
    (h : crossCoreSgiBody pre post e oid = some (c, k)) :
    c ≠ e ∧ ¬ coreDecisionUnstaled pre post c := by
  unfold crossCoreSgiBody at h
  split at h
  next tpost hPost =>
    have hTid : tpost.tid.toObjId = oid := hId tpost hPost
    have hPostTcb : post.getTcb? tpost.tid = some tpost := by
      unfold SystemState.getTcb?
      rw [hTid]
      simp only [SystemState.getObject?] at hPost
      rw [hPost]
    split at h
    next tpre hPre =>
      dsimp only at h
      split at h
      next hQ =>
        split at h
        · exact absurd h (by simp)
        next hNotExec =>
          split at h
          · exact absurd h (by simp)
          next hFire =>
            simp only [Option.some.injEq, Prod.mk.injEq] at h
            obtain ⟨rfl, -⟩ := h
            refine ⟨by simpa using hNotExec, fun hU => hFire ?_⟩
            obtain ⟨hIn, hKey⟩ := hU.1 _ hQ
            rw [schedKeyView_of_getTcb hPre, schedKeyView_of_getTcb hPostTcb] at hKey
            simp only [Option.some.injEq, Prod.mk.injEq] at hKey
            simp [hIn, hKey.1, hKey.2]
      next hNotQ =>
        split at h
        next preCur hFind =>
          have hPreCur : pre.scheduler.currentOnCore preCur = some tpost.tid := by
            simpa using List.find?_some hFind
          split at h
          · exact absurd h (by simp)
          next hNotExec =>
            split at h
            next hDesched =>
              simp only [Option.some.injEq, Prod.mk.injEq] at h
              obtain ⟨rfl, -⟩ := h
              refine ⟨by simpa using hNotExec, fun hU => ?_⟩
              have : post.scheduler.currentOnCore preCur = some tpost.tid := hU.2.1.trans hPreCur
              simp [this] at hDesched
            next hStill =>
              have hPostCur : post.scheduler.currentOnCore preCur = some tpost.tid := by
                simpa using hStill
              split at h
              next hWeak =>
                simp only [Option.some.injEq, Prod.mk.injEq] at h
                obtain ⟨rfl, -⟩ := h
                refine ⟨by simpa using hNotExec, fun hU => ?_⟩
                obtain ⟨kp, hkp, h1, h2⟩ := hU.2.2 _ hPostCur _
                  (schedKeyView_of_getTcb hPostTcb)
                rw [schedKeyView_of_getTcb hPre] at hkp
                simp only [Option.some.injEq] at hkp
                subst hkp
                simp only [Bool.or_eq_true, decide_eq_true_eq] at hWeak
                simp only at h1 h2
                omega
              · exact absurd h (by simp)
        · exact absurd h (by simp)
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- The slot rule fires only on a remote core whose current slot changed, which
stales it. -/
theorem currentSlotChangeSgis_staled {pre post : SystemState} {e c : CoreId} {k : SgiKind}
    (h : (c, k) ∈ currentSlotChangeSgis pre post e) :
    c ≠ e ∧ ¬ coreDecisionUnstaled pre post c := by
  obtain ⟨hne, hChanged⟩ :=
    PriorityInheritance.currentSlotChangeSgis_not_execCore pre post e c k h
  exact ⟨hne, fun hU => hChanged hU.2.1⟩

/-- **The diff's cores are flagged.**  On a covering step, every core the
whole-index diff names has its reschedule flag up in the post-state.  `hId` is
the post-state store's self-identity (each stored TCB is the thread its slot
names). -/
theorem computeCrossCoreSgis_core_flagged_of_covers {e : CoreId} {pre post : SystemState}
    (hId : ∀ oid (tcb : TCB), post.getObject? oid = some (.tcb tcb) → tcb.tid.toObjId = oid)
    (hCov : reschedulePendingCovers e pre post)
    {c : CoreId} {k : SgiKind} (hMem : (c, k) ∈ computeCrossCoreSgis pre post e) :
    post.scheduler.reschedulePendingOnCore c = true := by
  have hSub := Concurrency.dedupCrossCoreSgis_subset _ (c, k) hMem
  have hStaled : c ≠ e ∧ ¬ coreDecisionUnstaled pre post c := by
    rcases List.mem_append.mp hSub with hObj | hSlot
    · obtain ⟨oid, -, hBody⟩ := List.mem_filterMap.mp hObj
      exact crossCoreSgiBody_some_staled (hId oid) hBody
    · exact currentSlotChangeSgis_staled hSlot
  rcases hCov c hStaled.1 with hFlag | hU
  · exact hFlag
  · exact absurd hU hStaled.2

/-- **What the commit's switch needs.**  On a covering step, every core the diff
names is named by the flag-derived list, unless its flag was already up before
the step (its SGI is outstanding). -/
theorem computeCrossCoreSgis_mem_flags_of_covers {e : CoreId} {pre post : SystemState}
    (hId : ∀ oid (tcb : TCB), post.getObject? oid = some (.tcb tcb) → tcb.tid.toObjId = oid)
    (hCov : reschedulePendingCovers e pre post)
    {c : CoreId} {k : SgiKind} (hMem : (c, k) ∈ computeCrossCoreSgis pre post e) :
    (c, SgiKind.reschedule) ∈
        rescheduleSgisFromFlags pre.scheduler.reschedulePending
          post.scheduler.reschedulePending e ∨
      pre.scheduler.reschedulePendingOnCore c = true := by
  have hFlag := computeCrossCoreSgis_core_flagged_of_covers hId hCov hMem
  have hne : c ≠ e := by
    have hSub := Concurrency.dedupCrossCoreSgis_subset _ (c, k) hMem
    rcases List.mem_append.mp hSub with hObj | hSlot
    · obtain ⟨oid, -, hBody⟩ := List.mem_filterMap.mp hObj
      exact (crossCoreSgiBody_some_staled (hId oid) hBody).1
    · exact (currentSlotChangeSgis_staled hSlot).1
  cases hPre : pre.scheduler.reschedulePendingOnCore c
  · left
    rw [mem_rescheduleSgisFromFlags_iff]
    exact ⟨rfl, hne, hPre, hFlag⟩
  · exact Or.inr rfl

/-! ### Key frames -/

/-- A TCB rewrite that keeps the four fields the effective key reads. -/
def schedKeyFieldsEq (a b : TCB) : Prop :=
  b.priority = a.priority ∧ b.deadline = a.deadline ∧
    b.schedContextBinding = a.schedContextBinding ∧ b.pipBoost = a.pipBoost

theorem schedKeyFieldsEq_ipcState (a : TCB) (s : ThreadIpcState) :
    schedKeyFieldsEq a { a with ipcState := s } := ⟨rfl, rfl, rfl, rfl⟩

/-- The effective key reads only the key fields and the scheduling contexts. -/
theorem resolveEffectivePrioDeadline_congr {st st' : SystemState} {a b : TCB}
    (hSc : ∀ sc, st'.getSchedContext? sc = st.getSchedContext? sc)
    (hK : schedKeyFieldsEq a b) :
    resolveEffectivePrioDeadline st' b = resolveEffectivePrioDeadline st a := by
  obtain ⟨hP, hD, hB, hPip⟩ := hK
  unfold resolveEffectivePrioDeadline
  rw [hP, hD, hB, hPip]
  cases a.schedContextBinding <;> simp only [hSc]

/-- The scheduler record is not read by the key. -/
@[simp] theorem schedKeyView_scheduler (st : SystemState) (s : SchedulerState)
    (t : SeLe4n.ThreadId) :
    schedKeyView { st with scheduler := s } t = schedKeyView st t := rfl

/-- A key-preserving TCB rewrite moves no thread's key. -/
theorem schedKeyView_rewriteObject_tcb {st : SystemState} {tid : SeLe4n.ThreadId}
    {tcb t' : TCB} (hOld : st.getTcb? tid = some tcb)
    (h : st.rewriteAdmissible tid.toObjId (.tcb t')) (hInv : st.objects.invExt)
    (hK : schedKeyFieldsEq tcb t') (t : SeLe4n.ThreadId) :
    schedKeyView (st.rewriteObject tid.toObjId (.tcb t') h) t = schedKeyView st t := by
  have hSc := SystemState.rewriteObject_tcb_getSchedContext? st tid.toObjId t' h hInv
  by_cases hEq : t = tid
  · subst hEq
    unfold schedKeyView
    rw [SystemState.rewriteObject_tcb_getTcb?_self st t t' h hInv, hOld]
    simp only [Option.map_some, resolveEffectivePrioDeadline_congr hSc hK]
  · have hNe : tid.toObjId ≠ t.toObjId :=
      fun h' => hEq (SeLe4n.ThreadId.toObjId_injective _ _ h').symm
    unfold schedKeyView
    rw [SystemState.rewriteObject_getTcb?_ne st _ _ h hInv t hNe]
    cases st.getTcb? t with
    | none => rfl
    | some x => simp only [Option.map_some, resolveEffectivePrioDeadline_congr hSc
                  (⟨rfl, rfl, rfl, rfl⟩ : schedKeyFieldsEq x x)]

/-! ### Coverage from frames -/

/-- A core whose slots are untouched and whose threads' keys did not move is
unstaled. -/
theorem coreDecisionUnstaled_of_frame {pre post : SystemState} {c : CoreId}
    (hKeys : ∀ t, schedKeyView post t = schedKeyView pre t)
    (hRq : ∀ t, t ∈ post.scheduler.runQueueOnCore c → t ∈ pre.scheduler.runQueueOnCore c)
    (hCur : post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c) :
    coreDecisionUnstaled pre post c :=
  ⟨fun t ht => ⟨hRq t ht, (hKeys t).symm⟩, hCur,
   fun t _ => schedKeyNotWeakened_of_eq (hKeys t).symm⟩

/-- A key-framing step covers every core it flags or leaves slot-unchanged
(a run queue may only shrink). -/
theorem reschedulePendingCovers_of_frame {e : CoreId} {pre post : SystemState}
    (hKeys : ∀ t, schedKeyView post t = schedKeyView pre t)
    (hSlots : ∀ c, c ≠ e → post.scheduler.reschedulePendingOnCore c = true ∨
      ((∀ t, t ∈ post.scheduler.runQueueOnCore c → t ∈ pre.scheduler.runQueueOnCore c) ∧
        post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c)) :
    reschedulePendingCovers e pre post := fun c hc =>
  (hSlots c hc).imp id fun ⟨hRq, hCur⟩ => coreDecisionUnstaled_of_frame hKeys hRq hCur

/-! ### The run-queue primitives -/

/-- The wake covers: it flags the core it inserts on and moves no key (the
woken TCB's rewrite only marks it `.ready`). -/
theorem enqueueRunnableOnCore_covers (e c : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    reschedulePendingCovers e st (enqueueRunnableOnCore st c tid) := by
  unfold enqueueRunnableOnCore
  cases hT : st.getTcbWitnessed? tid with
  | none => exact reschedulePendingCovers_refl e st
  | some p =>
    obtain ⟨tcb, hw⟩ := p
    simp only
    split
    · exact reschedulePendingCovers_refl e st
    · apply reschedulePendingCovers_of_frame
      · intro t
        exact (schedKeyView_scheduler _ _ t).trans
          (schedKeyView_rewriteObject_tcb hw _ hInv (schedKeyFieldsEq_ipcState tcb _) t)
      · intro c' _
        by_cases hc : c = c'
        · subst hc; left; simp
        · right; simp [hc]

theorem enqueueRunnableOnCore_monotone (e c : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    reschedulePendingMonotone e st (enqueueRunnableOnCore st c tid) := by
  intro c' _ hF
  unfold enqueueRunnableOnCore
  cases st.getTcbWitnessed? tid with
  | none => exact hF
  | some p =>
    obtain ⟨tcb, hw⟩ := p
    simp only
    split
    · exact hF
    · by_cases hc : c = c'
      · subst hc; simp
      · simp [hc, hF]

/-- The removal covers: a queue removal stales nothing, and clearing the
current slot raises the flag. -/
theorem removeRunnableOnCore_covers (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    reschedulePendingCovers e st (removeRunnableOnCore st tid c) := by
  apply reschedulePendingCovers_of_frame (fun t => schedKeyView_scheduler _ _ t)
  intro c' _
  by_cases hc : c = c'
  · subst hc
    by_cases hcur : st.scheduler.currentOnCore c = some tid
    · left; simp [hcur]
    · right
      refine ⟨fun t ht => ?_, by simp [hcur]⟩
      simp only [SchedulerState.markReschedulePendingOnCoreIf_runQueueOnCore,
        SchedulerState.setCurrentOnCore_runQueueOnCore,
        SchedulerState.setRunQueueOnCore_runQueueOnCore_self] at ht
      exact ((RunQueue.mem_remove _ _ _).mp ht).1
  · right; simp [hc]

theorem removeRunnableOnCore_monotone (e : CoreId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) :
    reschedulePendingMonotone e st (removeRunnableOnCore st tid c) := by
  intro c' _ hF
  by_cases hc : c = c'
  · subst hc; simp [removeRunnableOnCore, hF]
  · simp [removeRunnableOnCore, hc, hF]

end SeLe4n.Kernel
