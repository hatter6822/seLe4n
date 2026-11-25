-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.InformationFlow.LowEquivalencePairs
import SeLe4n.Kernel.SchedContext.NotificationDonation
import SeLe4n.Kernel.SchedContext.Invariant.ContextLenders

/-!
# The notification lend, in two runs

WS-SX SX9.1, restated by SX22 over seL4's unchecked lend: the notification lend
(`maybeDonateSchedContext`) to a thread labelled as the notification made in two
low-equivalent runs leaves them low-equivalent, for every observer.  The thread
carries the notification's label at every lend the kernel makes: the woken
thread of a signal by the carried agreement
(`notificationLabelsAgree_signalWokenThread`), a receive's waiter by its wait's
two-way gate; under equal binding labels the notification carries its
context's, so the lend is between equal labels (D30's check, which always
passed, is deleted).  Its other hypotheses: equal binding labels in both runs
(`bindingLabelsEqual`, D37), the two runs' agreement on the machine timer (the
context's release reads it, and the timer is outside the projection, covert
channel CC-2), that each run's run queues agree with its threads
(`runQueueRefined`, which every reachable state keeps: the enqueue's admission
and the bind's placement read a thread's run-core word, which the projection
erases, and the agreement reads it off the queue the observer sees), and that
each thread carries its own TCB's label (`threadObjectLabelsEqual`, a fact of
the labelling context that every deployment context meets, so the deployment
corollary does without it).

The visible case is the lend's five writes paired: the decision transfers
(`notificationContext?_pair`), the admission agrees
(`schedContextDonateAdmitted_pair`), and each write is its two-run lemma
(`schedContextBindPerform_lowEquivalent_pair`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId bootCoreId)

/-- **Each thread carries its own TCB's label**: a fact of the labelling
context, not of a state.  `LabelingContextValid` asks only that a thread's label
flow to its TCB's; the lend's two-run theorem reads the waiter's binding words
off its TCB, so it needs the two equal. -/
def threadObjectLabelsEqual (ctx : LabelingContext) : Prop :=
  ∀ tid : SeLe4n.ThreadId, ctx.threadLabelOf tid = ctx.objectLabelOf tid.toObjId

/-- Every deployment context meets it. -/
theorem deploymentLabelingContext_threadObjectLabelsEqual (d : DeploymentLabeling) :
    threadObjectLabelsEqual (deploymentLabelingContext d) :=
  fun tid => (deploymentLabelingContext_thread_object_label_eq d tid).symm

section NotificationLendTwoRun

variable {ctx : LabelingContext} {observer : IfObserver}

/-- **The lend to a hidden thread is no view's**: under equal binding labels a
notification carries its context's label, so the context lent to a thread
labelled as the notification is hidden too. -/
theorem maybeDonateSchedContext_lowEquivalent_hidden (st : SystemState)
    (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt)
    (hB : bindingLabelsEqual ctx st) (hTN : ctx.threadLabelOf t = ctx.objectLabelOf n)
    (hT : threadObservable ctx observer t = false)
    (hTo : objectObservable ctx observer t.toObjId = false) :
    lowEquivalent_smp ctx observer (maybeDonateSchedContext st n t) st := by
  refine maybeDonateSchedContext_lowEquivalent st n t hInv hT hTo (fun s hs => ?_)
  unfold objectObservable
  rw [← bindingLabelsEqual.notificationContext hB hs, ← hTN]
  exact hT

/-- Two low-equivalent states agree, up to the projection, on every slot the
observer sees. -/
theorem lowEquivalent_smp.slot {s₁ s₂ : SystemState} (h : lowEquivalent_smp ctx observer s₁ s₂)
    {k : SeLe4n.ObjId} (hk : objectObservable ctx observer k = true) :
    (s₁.objects[k]?).map (projectKernelObject ctx observer) =
      (s₂.objects[k]?).map (projectKernelObject ctx observer) := by
  have e := congrFun h.objects k
  unfold projectObjects SystemState.getObject? at e
  simpa [hk] using e

/-- Two words shown or erased by the same test, each shown wherever it is set,
are equal where their projections are. -/
theorem shownWord_eq {P : Nat → Bool} {w₁ w₂ : Nat}
    (h : (if P w₁ = true then w₁ else 0) = (if P w₂ = true then w₂ else 0))
    (h₁ : w₁ ≠ 0 → P w₁ = true) (h₂ : w₂ ≠ 0 → P w₂ = true) : w₁ = w₂ := by
  by_cases a : w₁ = 0 <;> by_cases b : w₂ = 0 <;> simp_all

/-- A context with the fields the projection erases or decides on its own
(the thread word) zeroed: two contexts projecting the same agree here. -/
def schedContextLinksErased (x : SchedContext) : SchedContext :=
  { x with boundThreadCode := 0, scReply := none, releaseNextCode := 0,
           notificationCode := 0, yieldFromCode := 0 }

/-- The release reads and writes the refill fields only. -/
theorem schedContextLinksErased_releaseOne (x : SchedContext) (τ : Nat) :
    (schedContextLinksErased x).releaseOne τ = schedContextLinksErased (x.releaseOne τ) := by
  unfold SchedContext.releaseOne SchedContext.refillPop
  by_cases hc : x.budgetRemaining.val = 0 ∧ x.refillHeadPresent = true ∧ x.refillHeadEligibleAt ≤ τ
  · rw [if_pos (show (schedContextLinksErased x).budgetRemaining.val = 0 ∧ (schedContextLinksErased x).refillHeadPresent = true ∧
      (schedContextLinksErased x).refillHeadEligibleAt ≤ τ from hc), if_pos hc]
    by_cases hp : (x.refillHeadPresent && decide (0 < x.tailUsed)) = true
    · rw [if_pos (show ((schedContextLinksErased x).refillHeadPresent && decide (0 < (schedContextLinksErased x).tailUsed)) = true
        from hp), if_pos hp]; rfl
    · rw [if_neg (show ¬ ((schedContextLinksErased x).refillHeadPresent && decide (0 < (schedContextLinksErased x).tailUsed)) = true
        from hp), if_neg hp]; rfl
  · rw [if_neg (show ¬ ((schedContextLinksErased x).budgetRemaining.val = 0 ∧ (schedContextLinksErased x).refillHeadPresent = true ∧
      (schedContextLinksErased x).refillHeadEligibleAt ≤ τ) from hc), if_neg hc]

/-- ...and so do the releases of a used-up head. -/
theorem schedContextLinksErased_releaseReadyHead (x : SchedContext) (τ : Nat) :
    (schedContextLinksErased x).releaseReadyHead τ = schedContextLinksErased (x.releaseReadyHead τ) := by
  unfold SchedContext.releaseReadyHead
  generalize maxReplenishments = n
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    unfold SchedContext.releaseReadyHeadN
    by_cases hd : x.releaseDue τ = true
    · rw [if_pos (show (schedContextLinksErased x).releaseDue τ = true from hd), if_pos hd, schedContextLinksErased_releaseOne, ih]
    · rw [if_neg (show ¬ (schedContextLinksErased x).releaseDue τ = true from hd), if_neg hd]

/-- Two contexts projecting the same agree off the erased fields. -/
theorem schedContextLinksErased_of_project {x y : SchedContext}
    (h : projectKernelObject ctx observer (.schedContext x) =
      projectKernelObject ctx observer (.schedContext y)) : schedContextLinksErased x = schedContextLinksErased y := by
  simp only [projectKernelObject, KernelObject.schedContext.injEq] at h
  have := congrArg (fun z : SchedContext => { z with boundThreadCode := 0 }) h
  exact this

/-- The bind's context rewrite, as `schedContextBindPerform` writes it. -/
def bindContextWrite (x : SchedContext) (τ k : Nat) : SchedContext :=
  { x.releaseReadyHead τ with boundThreadCode := k }

/-- The context rewrite keeps two contexts projecting the same: the release
reads the timer, which both runs pass in, and the refill fields, which the
projection keeps. -/
theorem project_bindContextWrite_pair {x y : SchedContext} (τ k : Nat)
    (h : projectKernelObject ctx observer (.schedContext x) =
      projectKernelObject ctx observer (.schedContext y)) :
    projectKernelObject ctx observer (.schedContext (bindContextWrite x τ k)) =
      projectKernelObject ctx observer (.schedContext (bindContextWrite y τ k)) := by
  have e : ∀ z : SchedContext, projectKernelObject ctx observer (.schedContext (bindContextWrite z τ k)) =
      .schedContext { schedContextLinksErased (z.releaseReadyHead τ) with
        boundThreadCode := if threadWordShown ctx observer k then k else 0 } := fun _ => rfl
  rw [e, e, ← schedContextLinksErased_releaseReadyHead, ← schedContextLinksErased_releaseReadyHead, schedContextLinksErased_of_project h]

/-- ...and the released budget the placement reads is the same. -/
theorem bindContextWrite_budgetRemaining_pair {x y : SchedContext} (τ : Nat)
    (h : projectKernelObject ctx observer (.schedContext x) =
      projectKernelObject ctx observer (.schedContext y)) :
    (x.releaseReadyHead τ).budgetRemaining = (y.releaseReadyHead τ).budgetRemaining := by
  have e : ∀ z : SchedContext, (z.releaseReadyHead τ).budgetRemaining =
      (schedContextLinksErased (z.releaseReadyHead τ)).budgetRemaining := fun _ => rfl
  rw [e, e, ← schedContextLinksErased_releaseReadyHead, ← schedContextLinksErased_releaseReadyHead, schedContextLinksErased_of_project h]

/-- The bind's thread write, as `schedContextBindPerform` writes it. -/
def bindThreadWrite (w : Nat) (a : TCB) : TCB :=
  { a with scBindingScCode := w, scBindingOwnerCode := 0 }

/-- The bind's thread write, as an observer sees it written. -/
def bindThreadProjected (ctx : LabelingContext) (observer : IfObserver) (w : Nat) :
    KernelObject → KernelObject
  | .tcb r => .tcb
      { r with
        scBindingScCode := if scWordShown ctx observer w then w else 0,
        scBindingOwnerCode :=
          if scWordShown ctx observer w && threadWordShown ctx observer 0 then 0 else 0 }
  | o => o

/-- The thread's binding write keeps two threads projecting the same: it sets
the binding words to one value in both. -/
theorem project_bindThreadWrite_pair (w : Nat) (a b : TCB)
    (h : projectKernelObject ctx observer (.tcb a) = projectKernelObject ctx observer (.tcb b)) :
    projectKernelObject ctx observer (.tcb (bindThreadWrite w a)) =
      projectKernelObject ctx observer (.tcb (bindThreadWrite w b)) := by
  have e : ∀ z : TCB, projectKernelObject ctx observer (.tcb (bindThreadWrite w z)) =
      bindThreadProjected ctx observer w (projectKernelObject ctx observer (.tcb z)) := fun _ => rfl
  rw [e, e, h]

/-- The fields of a thread an observer that sees it reads, out of the projection. -/
theorem tcb_fields_of_project {a b : TCB}
    (h : projectKernelObject ctx observer (.tcb a) = projectKernelObject ctx observer (.tcb b)) :
    a.isRunnable = b.isRunnable ∧ a.cpuAffinity = b.cpuAffinity ∧
      (if scWordShown ctx observer a.scBindingScCode then a.scBindingScCode else 0) =
        (if scWordShown ctx observer b.scBindingScCode then b.scBindingScCode else 0) := by
  simp only [projectKernelObject, KernelObject.tcb.injEq] at h
  have h1 := congrArg TCB.isRunnable h
  have h2 := congrArg TCB.cpuAffinity h
  have h3 := congrArg TCB.scBindingScCode h
  exact ⟨h1, h2, h3⟩

/-- The context's thread word, as the projection shows it. -/
theorem sc_boundWord_of_project {x y : SchedContext}
    (h : projectKernelObject ctx observer (.schedContext x) =
      projectKernelObject ctx observer (.schedContext y)) :
    (if threadWordShown ctx observer x.boundThreadCode then x.boundThreadCode else 0) =
      (if threadWordShown ctx observer y.boundThreadCode then y.boundThreadCode else 0) := by
  simp only [projectKernelObject, KernelObject.schedContext.injEq] at h
  exact congrArg SchedContext.boundThreadCode h

/-- The notification's context word, as the projection shows it. -/
theorem ntfn_word_of_project {m₁ m₂ : Notification}
    (h : projectKernelObject ctx observer (.notification m₁) =
      projectKernelObject ctx observer (.notification m₂)) :
    (if scWordShown ctx observer m₁.schedContextCode then m₁.schedContextCode else 0) =
      (if scWordShown ctx observer m₂.schedContextCode then m₂.schedContextCode else 0) := by
  simp only [projectKernelObject, KernelObject.notification.injEq] at h
  exact congrArg Notification.schedContextCode h

/-! ### What two low-equivalent runs agree on of a thread the observer sees -/

/-- The core a thread is homed on. -/
theorem determineTargetCore_pair {s₁ s₂ : SystemState} (t : SeLe4n.ThreadId)
    (hL : lowEquivalent_smp ctx observer s₁ s₂)
    (hTo : objectObservable ctx observer t.toObjId = true) :
    determineTargetCore s₁ t = determineTargetCore s₂ t := by
  have hk := hL.slot hTo
  unfold determineTargetCore
  cases h₁ : s₁.getTcb? t with
  | some x₁ =>
    obtain ⟨x₂, hO₂, hP⟩ := tcb_of_projected_eq ((SystemState.getTcb?_eq_some_iff _ _ _).mp h₁) hk
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hO₂]; dsimp only
    rw [(tcb_fields_of_project hP).2.1]
  | none =>
    cases h₂ : s₂.getTcb? t with
    | some x₂ =>
      obtain ⟨x₁, hO₁, -⟩ := tcb_of_projected_eq ((SystemState.getTcb?_eq_some_iff _ _ _).mp h₂) hk.symm
      rw [← SystemState.getTcb?_eq_some_iff, h₁] at hO₁; cases hO₁
    | none => rfl

/-- Whether a thread has a TCB. -/
theorem getTcb?_isSome_pair {s₁ s₂ : SystemState} (t : SeLe4n.ThreadId)
    (hL : lowEquivalent_smp ctx observer s₁ s₂)
    (hTo : objectObservable ctx observer t.toObjId = true) :
    (s₁.getTcb? t).isSome = (s₂.getTcb? t).isSome := by
  have hk := hL.slot hTo
  cases h₁ : s₁.getTcb? t with
  | some x₁ =>
    obtain ⟨x₂, hO₂, -⟩ := tcb_of_projected_eq ((SystemState.getTcb?_eq_some_iff _ _ _).mp h₁) hk
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr hO₂]; rfl
  | none =>
    cases h₂ : s₂.getTcb? t with
    | some x₂ =>
      obtain ⟨x₁, hO₁, -⟩ := tcb_of_projected_eq ((SystemState.getTcb?_eq_some_iff _ _ _).mp h₂) hk.symm
      rw [← SystemState.getTcb?_eq_some_iff, h₁] at hO₁; cases hO₁
    | none => rfl

/-- Whether a thread is current on a core. -/
theorem current_eq_pair {s₁ s₂ : SystemState} (t : SeLe4n.ThreadId) (c : CoreId)
    (hL : lowEquivalent_smp ctx observer s₁ s₂) (hT : threadObservable ctx observer t = true) :
    (s₁.scheduler.currentOnCore c == some t) = (s₂.scheduler.currentOnCore c == some t) := by
  have e : projectCurrentOnCore ctx observer s₁ c = projectCurrentOnCore ctx observer s₂ c :=
    congrArg ObservableState.current (hL c)
  unfold projectCurrentOnCore at e
  cases h₁ : s₁.scheduler.currentOnCore c with
  | none =>
    cases h₂ : s₂.scheduler.currentOnCore c with
    | none => rfl
    | some u =>
      rw [h₁, h₂] at e
      by_cases hu : u = t
      · subst hu; simp [hT] at e
      · simp [hu]
  | some u =>
    cases h₂ : s₂.scheduler.currentOnCore c with
    | none =>
      rw [h₁, h₂] at e
      by_cases hu : u = t
      · subst hu; simp [hT] at e
      · simp [hu]
    | some v =>
      rw [h₁, h₂] at e
      by_cases hu : u = t <;> by_cases hv : v = t
      · subst hu; subst hv; rfl
      · subst hu; simp only [hT, if_true] at e; split at e <;> simp_all
      · subst hv; simp only [hT, if_true] at e; split at e <;> simp_all
      · have a : (u == t) = false := beq_eq_false_iff_ne.mpr hu
        have b : (v == t) = false := beq_eq_false_iff_ne.mpr hv
        simp [a, b]

/-- Whether a thread is queued on a core, where both runs' queues agree with
their threads (`runQueueRefined`). -/
theorem queuedOn_pair {s₁ s₂ : SystemState} (t : SeLe4n.ThreadId) (c : CoreId)
    (hL : lowEquivalent_smp ctx observer s₁ s₂) (hT : threadObservable ctx observer t = true)
    (hR₁ : s₁.runQueueRefined) (hR₂ : s₂.runQueueRefined) :
    s₁.queuedOn c t = s₂.queuedOn c t := by
  rw [(hR₁ c).queuedOn, (hR₂ c).queuedOn]
  have e := hL.runnable c
  unfold projectRunnableOnCore at e
  have m : ∀ s : SystemState, (s.scheduler.runQueueOnCore c).contains t = true ↔
      t ∈ (s.scheduler.runQueueOnCore c).toList.filter (threadObservable ctx observer) := fun s => by
    rw [List.mem_filter, RunQueue.mem_toList_iff_mem]; simp [hT]
  apply Bool.eq_iff_iff.mpr
  rw [m, m, e]

/-- Where a thread is placed. -/
theorem placedCoreOf?_pair {s₁ s₂ : SystemState} (t : SeLe4n.ThreadId)
    (hL : lowEquivalent_smp ctx observer s₁ s₂) (hT : threadObservable ctx observer t = true)
    (hR₁ : s₁.runQueueRefined) (hR₂ : s₂.runQueueRefined) :
    placedCoreOf? s₁ t = placedCoreOf? s₂ t := by
  unfold placedCoreOf?
  congr 1
  funext c
  rw [queuedOn_pair t c hL hT hR₁ hR₂, current_eq_pair t c hL hT]

/-- The enqueue's link test, read as queue membership: a thread with a TCB,
queued on the core or on none. -/
theorem runLinksAdmit_eq_queuedOn (s : SystemState) (c : CoreId) (t : SeLe4n.ThreadId) :
    s.runLinksAdmit c t = ((s.getTcb? t).isSome &&
      (s.queuedOn c t || !(SeLe4n.Kernel.Concurrency.allCores.any fun c' => s.queuedOn c' t))) := by
  cases h : s.getTcb? t with
  | none => unfold SystemState.runLinksAdmit; rw [h]; rfl
  | some x =>
    have hq : ∀ c' : CoreId, s.queuedOn c' t = (x.runCoreCode == c'.val + 1) := fun c' => by
      unfold SystemState.queuedOn; rw [h]
    unfold SystemState.runLinksAdmit; rw [h]
    simp only [hq, Option.isSome_some, Bool.true_and]
    have hAny : (SeLe4n.Kernel.Concurrency.allCores.any fun c' : CoreId => x.runCoreCode == c'.val + 1) =
        decide (0 < x.runCoreCode ∧ x.runCoreCode ≤ SeLe4n.Kernel.Concurrency.numCores) := by
      apply Bool.eq_iff_iff.mpr
      simp only [List.any_eq_true, beq_iff_eq, decide_eq_true_eq]
      constructor
      · rintro ⟨c', -, h⟩; omega
      · rintro ⟨h0, h1⟩
        exact ⟨⟨x.runCoreCode - 1, by omega⟩, SeLe4n.Kernel.Concurrency.mem_allCores _, by simp; omega⟩
    rw [hAny]
    by_cases h0 : x.runCoreCode = 0
    · simp [h0]
    · have a : (x.runCoreCode == 0) = false := by simpa using h0
      have b : decide (0 < x.runCoreCode) = true := by simp; omega
      by_cases h1 : SeLe4n.Kernel.Concurrency.numCores < x.runCoreCode
      · have d : decide (x.runCoreCode ≤ SeLe4n.Kernel.Concurrency.numCores) = false := by
          simp; omega
        simp [a, b, d, h1]
      · have d : decide (x.runCoreCode ≤ SeLe4n.Kernel.Concurrency.numCores) = true := by
          simp; omega
        simp [a, b, d, h1]

/-- Whether the enqueue is admitted. -/
theorem runEnqueueAdmits_pair {s₁ s₂ : SystemState} (t : SeLe4n.ThreadId) (c : CoreId)
    (hL : lowEquivalent_smp ctx observer s₁ s₂) (hT : threadObservable ctx observer t = true)
    (hTo : objectObservable ctx observer t.toObjId = true)
    (hR₁ : s₁.runQueueRefined) (hR₂ : s₂.runQueueRefined) :
    s₁.runEnqueueAdmits c t = s₂.runEnqueueAdmits c t := by
  unfold SystemState.runEnqueueAdmits
  rw [runLinksAdmit_eq_queuedOn, runLinksAdmit_eq_queuedOn, getTcb?_isSome_pair t hL hTo,
    queuedOn_pair t c hL hT hR₁ hR₂]
  simp only [queuedOn_pair t _ hL hT hR₁ hR₂]

/-! ### The bind's writes, in two runs -/

/-- The bind's two object writes keep the run-queue agreement and the thread. -/
theorem bindWrites_runQueueRefined_pair (st : SystemState) (id : SeLe4n.ObjId)
    (sc' : SchedContext) (pf : st.rewriteAdmissible id (.schedContext sc'))
    (t : SeLe4n.ThreadId) (w : Nat) (hInv : st.objects.invExt) (hR : st.runQueueRefined) :
    ((st.rewriteObject id (.schedContext sc') pf).updateTcb t (bindThreadWrite w)).runQueueRefined := by
  have hInv1 := SystemState.rewriteObject_preserves_objects_invExt st id _ pf hInv
  have hR1 : (st.rewriteObject id (.schedContext sc') pf).runQueueRefined :=
    SystemState.runQueueRefined_of_frame (st := st) (fun c x => by
      unfold SystemState.runLinkOn
      rw [SystemState.rewriteObject_schedContext_getTcb? st id sc' pf hInv]) rfl rfl hR
  exact SystemState.updateTcb_runQueueRefined hInv1 (fun _ _ => rfl) hR1

/-- The bind's writes over a context and a thread read. -/
def bindPerformBody (st : SystemState) (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId)
    (sc : SchedContext) (tcb : TCB)
    (pf : st.rewriteAdmissible vS.val
      (.schedContext (bindContextWrite sc st.machine.timer (SeLe4n.ThreadId.optCode (some vT.val))))) :
    SystemState :=
  let st2 := (st.rewriteObject vS.val _ pf).updateTcb vT.val
    (bindThreadWrite (SchedContextBinding.scCode (.bound ⟨vS.val.toNat⟩)))
  let home := determineTargetCore st2 vT.val
  let st3 := if SchedContextOps.bindPlacesParkedThread st2 vT.val tcb (sc.releaseReadyHead st.machine.timer) then
    (st2.runEnqueueOnCore home vT.val (resolveInsertPriority st2 vT.val)).markReschedulePendingOnCore home
  else st2
  st3.releasePlace home ⟨vS.val.toNat⟩

theorem schedContextBindPerform_eq_body {st : SystemState} {vS : SeLe4n.ValidObjId}
    {vT : SeLe4n.ValidThreadId} {sc : SchedContext} {tcb : TCB}
    (hS : st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) = some sc)
    (hT : st.getTcb? vT.val = some tcb) :
    ∃ pf, SchedContextOps.schedContextBindPerform st vS vT = bindPerformBody st vS vT sc tcb pf := by
  unfold SchedContextOps.schedContextBindPerform
  split
  · next h => rw [SystemState.getSchedContextWitnessed?_eq_some hS] at h; cases h
  · next sc' hSc' h =>
    rw [SystemState.getSchedContextWitnessed?_eq_some hS] at h
    cases h
    dsimp only
    split
    · next h => rw [hT] at h; cases h
    · next tcb' h =>
      rw [hT] at h; cases h
      exact ⟨SystemState.rewriteAdmissible_schedContext hSc' _, rfl⟩
/-- The bind's placement tail, in two runs of a thread the observer sees, the
runs agreeing on whether the thread is placed. -/
theorem bindTail_lowEquivalent_pair {a₁ a₂ : SystemState} (t : SeLe4n.ThreadId)
    (tcb₁ tcb₂ : TCB) (r₁ r₂ : SchedContext) (s : SeLe4n.SchedContextId)
    (hL : lowEquivalent_smp ctx observer a₁ a₂)
    (hR₁ : a₁.runQueueRefined) (hR₂ : a₂.runQueueRefined)
    (hT : threadObservable ctx observer t = true)
    (hTo : objectObservable ctx observer t.toObjId = true)
    (hb : SchedContextOps.bindPlacesParkedThread a₁ t tcb₁ r₁ =
      SchedContextOps.bindPlacesParkedThread a₂ t tcb₂ r₂) :
    lowEquivalent_smp ctx observer
      ((if SchedContextOps.bindPlacesParkedThread a₁ t tcb₁ r₁ then
          (a₁.runEnqueueOnCore (determineTargetCore a₁ t) t (resolveInsertPriority a₁ t)).markReschedulePendingOnCore
            (determineTargetCore a₁ t)
        else a₁).releasePlace (determineTargetCore a₁ t) s)
      ((if SchedContextOps.bindPlacesParkedThread a₂ t tcb₂ r₂ then
          (a₂.runEnqueueOnCore (determineTargetCore a₂ t) t (resolveInsertPriority a₂ t)).markReschedulePendingOnCore
            (determineTargetCore a₂ t)
        else a₂).releasePlace (determineTargetCore a₂ t) s) := by
  rw [← determineTargetCore_pair t hL hTo, ← hb]
  refine releasePlace_lowEquivalent_pair _ s ?_
  split
  · exact markReschedulePendingOnCore_lowEquivalent_pair _
      (runEnqueueOnCore_lowEquivalent_pair _ t _ _ hL
        (fun _ => runEnqueueAdmits_pair t _ hL hT hTo hR₁ hR₂))
  · exact hL

/-- What the admission reads: the context and the thread, stored. -/
theorem schedContextDonateAdmitted_stored {st : SystemState} {vS : SeLe4n.ValidObjId}
    {vT : SeLe4n.ValidThreadId} (h : SchedContextOps.schedContextDonateAdmitted st vS vT = true) :
    ∃ sc tcb, st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) = some sc ∧
      st.getTcb? vT.val = some tcb := by
  unfold SchedContextOps.schedContextDonateAdmitted at h
  cases hW : st.getSchedContextWitnessed? (SeLe4n.SchedContextId.ofObjId vS.val) with
  | none => rw [hW] at h; cases h
  | some w =>
    rw [hW] at h
    cases hT : st.getTcb? vT.val with
    | none => simp [hT] at h
    | some tcb => exact ⟨w.1, tcb, w.2, rfl⟩

/-- **The bind's writes, made in two runs**, of a context and a thread the
observer sees, both admitted (`schedContextDonateAdmitted`): the runs agree on
the timer the release reads. -/
theorem schedContextBindPerform_lowEquivalent_pair {s₁ s₂ : SystemState}
    (vS : SeLe4n.ValidObjId) (vT : SeLe4n.ValidThreadId)
    (hL : lowEquivalent_smp ctx observer s₁ s₂)
    (hI₁ : s₁.objects.invExt) (hI₂ : s₂.objects.invExt)
    (hR₁ : s₁.runQueueRefined) (hR₂ : s₂.runQueueRefined)
    (hτ : s₁.machine.timer = s₂.machine.timer)
    (hS : objectObservable ctx observer vS.val = true)
    (hT : threadObservable ctx observer vT.val = true)
    (hTo : objectObservable ctx observer vT.val.toObjId = true)
    (hA₁ : SchedContextOps.schedContextDonateAdmitted s₁ vS vT = true)
    (hA₂ : SchedContextOps.schedContextDonateAdmitted s₂ vS vT = true) :
    lowEquivalent_smp ctx observer (SchedContextOps.schedContextBindPerform s₁ vS vT)
      (SchedContextOps.schedContextBindPerform s₂ vS vT) := by
  obtain ⟨sc₁, tcb₁, hS₁, hT₁⟩ := schedContextDonateAdmitted_stored hA₁
  obtain ⟨sc₂, tcb₂, hS₂, hT₂⟩ := schedContextDonateAdmitted_stored hA₂
  obtain ⟨pf₁, e₁⟩ := schedContextBindPerform_eq_body hS₁ hT₁
  obtain ⟨pf₂, e₂⟩ := schedContextBindPerform_eq_body hS₂ hT₂
  rw [e₁, e₂]
  have hPS : projectKernelObject ctx observer (.schedContext sc₁) =
      projectKernelObject ctx observer (.schedContext sc₂) := by
    have h := hL.slot hS
    rw [show vS.val = (SeLe4n.SchedContextId.ofObjId vS.val).toObjId from rfl,
      (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS₁,
      (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hS₂] at h
    exact Option.some.inj h
  have hPT : projectKernelObject ctx observer (.tcb tcb₁) =
      projectKernelObject ctx observer (.tcb tcb₂) := by
    have h := hL.slot hTo
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mp hT₁,
      (SystemState.getTcb?_eq_some_iff _ _ _).mp hT₂] at h
    exact Option.some.inj h
  have L₁ := rewriteObject_lowEquivalent_pair (ctx := ctx) (observer := observer) vS.val _ _ pf₁ pf₂
    (fun _ => by rw [hτ]; exact project_bindContextWrite_pair _ _ hPS) hI₁ hI₂ hL
  have hJ₁ := SystemState.rewriteObject_preserves_objects_invExt _ _ _ pf₁ hI₁
  have hJ₂ := SystemState.rewriteObject_preserves_objects_invExt _ _ _ pf₂ hI₂
  have L₂ := updateTcb_lowEquivalent_pair vT.val
    (bindThreadWrite (SchedContextBinding.scCode (.bound ⟨vS.val.toNat⟩))) hJ₁ hJ₂
    (project_bindThreadWrite_pair _) L₁
  have hQ₁ := bindWrites_runQueueRefined_pair s₁ vS.val _ pf₁ vT.val
    (SchedContextBinding.scCode (.bound ⟨vS.val.toNat⟩)) hI₁ hR₁
  have hQ₂ := bindWrites_runQueueRefined_pair s₂ vS.val _ pf₂ vT.val
    (SchedContextBinding.scCode (.bound ⟨vS.val.toNat⟩)) hI₂ hR₂
  refine bindTail_lowEquivalent_pair vT.val tcb₁ tcb₂ _ _ _ L₂ hQ₁ hQ₂ hT hTo ?_
  have hF := tcb_fields_of_project hPT
  unfold SchedContextOps.bindPlacesParkedThread
  rw [placedCoreOf?_pair vT.val L₂ hT hQ₁ hQ₂, hF.1, hτ,
    bindContextWrite_budgetRemaining_pair _ hPS]
/-! ### The admission, in two runs -/

/-- The admission reads the context's thread word and the thread's context word. -/
theorem schedContextDonateAdmitted_eq_words (st : SystemState) (vS : SeLe4n.ValidObjId)
    (vT : SeLe4n.ValidThreadId) :
    SchedContextOps.schedContextDonateAdmitted st vS vT =
      (match (st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val)).map (·.boundThreadCode),
          (st.getTcb? vT.val).map (·.scBindingScCode) with
       | some b, some w => b == 0 && w == 0
       | _, _ => false) := by
  unfold SchedContextOps.schedContextDonateAdmitted
  obtain ⟨o, hS⟩ : ∃ o, st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) = o := ⟨_, rfl⟩
  cases o with
  | none => rw [SystemState.getSchedContextWitnessed?_eq_none hS]; dsimp only; rw [hS]; rfl
  | some sc =>
    rw [SystemState.getSchedContextWitnessed?_eq_some hS]
    dsimp only
    rw [hS]
    have hb : sc.boundThread.isSome = !(sc.boundThreadCode == 0) := by
      unfold SchedContext.boundThread; cases sc.boundThreadCode <;> rfl
    rw [hb]
    cases hT : st.getTcb? vT.val with
    | none => cases sc.boundThreadCode <;> rfl
    | some tcb =>
      simp only [Option.map_some]
      unfold TCB.schedContextBinding SeLe4n.Kernel.SchedContextBinding.ofCodes
      cases sc.boundThreadCode <;> cases tcb.scBindingScCode <;> cases tcb.scBindingOwnerCode <;> rfl

/-- Two stores that project the same at a key hold a context there in both or
in neither, and the two contexts project the same. -/
theorem sc_of_projected_eq {o₂ : Option KernelObject} {k : SeLe4n.ObjId} {s₁ : SystemState}
    {x₁ : SchedContext} (h : s₁.objects[k]? = some (.schedContext x₁))
    (hO : (s₁.objects[k]?).map (projectKernelObject ctx observer) =
      o₂.map (projectKernelObject ctx observer)) :
    ∃ x₂, o₂ = some (.schedContext x₂) ∧
      projectKernelObject ctx observer (.schedContext x₁) =
        projectKernelObject ctx observer (.schedContext x₂) := by
  rw [h] at hO
  cases o₂ with
  | none => cases hO
  | some y =>
    simp only [Option.map_some, Option.some.injEq] at hO
    have hT := congrArg KernelObject.objectType hO
    rw [projectKernelObject_objectType, projectKernelObject_objectType] at hT
    cases y <;> simp [KernelObject.objectType] at hT
    exact ⟨_, rfl, hO⟩

/-- A word each run shows wherever it is set agrees between the runs. -/
theorem optWord_pair {α : Type} {o₁ o₂ : Option α} (w : α → Nat) (P : Nat → Bool)
    (hShape : o₁.isSome = o₂.isSome)
    (hProj : ∀ a₁ a₂, o₁ = some a₁ → o₂ = some a₂ →
      (if P (w a₁) then w a₁ else 0) = (if P (w a₂) then w a₂ else 0))
    (h₁ : ∀ a, o₁ = some a → w a ≠ 0 → P (w a) = true)
    (h₂ : ∀ a, o₂ = some a → w a ≠ 0 → P (w a) = true) :
    o₁.map w = o₂.map w := by
  cases o₁ with
  | none => cases o₂ with
    | none => rfl
    | some _ => cases hShape
  | some a₁ => cases o₂ with
    | none => cases hShape
    | some a₂ =>
      exact congrArg some (shownWord_eq (hProj a₁ a₂ rfl rfl) (h₁ a₁ rfl) (h₂ a₂ rfl))

/-- **Two runs with equal binding labels agree on the admission** of a context
and a thread the observer sees. -/
theorem schedContextDonateAdmitted_pair {s₁ s₂ : SystemState} (vS : SeLe4n.ValidObjId)
    (vT : SeLe4n.ValidThreadId) (hL : lowEquivalent_smp ctx observer s₁ s₂)
    (hB₁ : bindingLabelsEqual ctx s₁) (hB₂ : bindingLabelsEqual ctx s₂)
    (hS : objectObservable ctx observer vS.val = true)
    (hT : threadObservable ctx observer vT.val = true)
    (hTo : objectObservable ctx observer vT.val.toObjId = true) :
    SchedContextOps.schedContextDonateAdmitted s₁ vS vT =
      SchedContextOps.schedContextDonateAdmitted s₂ vS vT := by
  rw [schedContextDonateAdmitted_eq_words, schedContextDonateAdmitted_eq_words]
  have hSc : ∀ (st : SystemState), bindingLabelsEqual ctx st → ∀ sc,
      st.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) = some sc →
      sc.boundThreadCode ≠ 0 → threadWordShown ctx observer sc.boundThreadCode = true := by
    intro st hB sc h hne
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
    have e := hB.2.1 _ sc ⟨k⟩ ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp h) hk
    rw [hk, show k.succ = (SeLe4n.ThreadId.mk k).val + 1 from rfl, threadWordShown_val_succ]
    unfold threadObservable; rw [e]; exact hS
  have hTc : ∀ (st : SystemState), bindingLabelsEqual ctx st → ∀ tcb,
      st.getTcb? vT.val = some tcb →
      tcb.scBindingScCode ≠ 0 → scWordShown ctx observer tcb.scBindingScCode = true := by
    intro st hB tcb h hne
    obtain ⟨k, hk⟩ := Nat.exists_eq_succ_of_ne_zero hne
    have e := hB.1 _ tcb ⟨k⟩ ((SystemState.getTcb?_eq_some_iff _ _ _).mp h) hk
    rw [hk, show k.succ = (SeLe4n.SchedContextId.mk k).val + 1 from rfl, scWordShown_val_succ]
    unfold objectObservable; rw [← e]; exact hT
  have hkS := hL.slot hS
  have hkT := hL.slot hTo
  have vSc : (s₁.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val)).map (·.boundThreadCode) =
      (s₂.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val)).map (·.boundThreadCode) := by
    refine optWord_pair _ (threadWordShown ctx observer) ?_ ?_ (hSc s₁ hB₁) (hSc s₂ hB₂)
    · cases h₁ : s₁.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
      | some x₁ =>
        obtain ⟨x₂, h₂, -⟩ := sc_of_projected_eq ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp h₁) hkS
        rw [(SystemState.getSchedContext?_eq_some_iff _ _ _).mpr h₂]; rfl
      | none =>
        cases h₂ : s₂.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
        | none => rfl
        | some x₂ =>
          obtain ⟨x₁, h₁', -⟩ := sc_of_projected_eq
            ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp h₂) hkS.symm
          have e := (SystemState.getSchedContext?_eq_some_iff s₁
            (SeLe4n.SchedContextId.ofObjId vS.val) x₁).mpr h₁'
          rw [h₁] at e; cases e
    · intro a₁ a₂ h₁ h₂
      obtain ⟨x₂, h₂', hP⟩ := sc_of_projected_eq ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp h₁) hkS
      have e := (SystemState.getSchedContext?_eq_some_iff s₂
        (SeLe4n.SchedContextId.ofObjId vS.val) x₂).mpr h₂'
      rw [h₂] at e; cases e
      exact sc_boundWord_of_project hP
  have vTc : (s₁.getTcb? vT.val).map (·.scBindingScCode) =
      (s₂.getTcb? vT.val).map (·.scBindingScCode) := by
    refine optWord_pair _ (scWordShown ctx observer) (getTcb?_isSome_pair _ hL hTo) ?_
      (hTc s₁ hB₁) (hTc s₂ hB₂)
    intro a₁ a₂ h₁ h₂
    obtain ⟨x₂, h₂', hP⟩ := tcb_of_projected_eq ((SystemState.getTcb?_eq_some_iff _ _ _).mp h₁) hkT
    rw [← SystemState.getTcb?_eq_some_iff, h₂] at h₂'; cases h₂'
    exact (tcb_fields_of_project hP).2.2
  rw [vSc, vTc]

/-! ### The decision, in two runs -/

/-- With no context the lend changes nothing. -/
theorem maybeDonateSchedContext_of_no_context {st : SystemState}
    {n : SeLe4n.ObjId} {t : SeLe4n.ThreadId} (hC : notificationContext? st n = none) :
    maybeDonateSchedContext st n t = st := by
  unfold maybeDonateSchedContext
  unfold notificationContext? at hC
  cases hN : st.getNotification? n with
  | none => rfl
  | some m =>
    rw [hN] at hC
    simp only [Option.bind_some] at hC
    simp only [hC]

/-- With one, it is the lend over that context. -/
theorem maybeDonateSchedContext_of_context {st : SystemState}
    {n : SeLe4n.ObjId} {t : SeLe4n.ThreadId} {c : SeLe4n.SchedContextId}
    (hC : notificationContext? st n = some c) :
    maybeDonateSchedContext st n t =
      match c.toObjId.toValid?, t.toValid? with
      | some vS, some vT =>
        if SchedContextOps.schedContextDonateAdmitted st vS vT then
          SchedContextOps.schedContextBindPerform st vS vT
        else st
      | _, _ => st := by
  unfold maybeDonateSchedContext
  unfold notificationContext? at hC
  cases hN : st.getNotification? n with
  | none => rw [hN] at hC; cases hC
  | some m =>
    rw [hN] at hC
    simp only [Option.bind_some] at hC
    simp only [hC]
    rfl

/-- **The decision transfers**: where one run's notification, seen by an
observer that sees the thread, lends a context labelled as the thread, the
other's lends the same one. -/
theorem notificationContext?_pair {s₁ s₂ : SystemState} {n : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} {c : SeLe4n.SchedContextId}
    (hL : lowEquivalent_smp ctx observer s₁ s₂) (hB₁ : bindingLabelsEqual ctx s₁)
    (hT : threadObservable ctx observer t = true)
    (hC : notificationContext? s₁ n = some c)
    (hE : ctx.objectLabelOf c.toObjId = ctx.threadLabelOf t) :
    notificationContext? s₂ n = some c := by
  unfold notificationContext? at hC ⊢
  cases hN₁ : s₁.getNotification? n with
  | none => rw [hN₁] at hC; cases hC
  | some m₁ =>
    rw [hN₁] at hC
    simp only [Option.bind_some] at hC
    have hW₁ : m₁.schedContextCode = c.val + 1 := by
      have := congrArg SeLe4n.SchedContextId.optCode hC
      simpa [Notification.schedContext] using this
    have hO₁ := (SystemState.getNotification?_eq_some_iff _ _ _).mp hN₁
    have hCo : objectObservable ctx observer c.toObjId = true := by
      unfold objectObservable; rw [hE]; exact hT
    have hNo : objectObservable ctx observer n = true := by
      unfold objectObservable; rw [hB₁.2.2.1 n m₁ c hO₁ hW₁]; exact hCo
    have hk := hL.slot hNo
    rw [hO₁] at hk
    cases hO₂ : s₂.objects[n]? with
    | none => rw [hO₂] at hk; cases hk
    | some y =>
      rw [hO₂] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      have hTy := congrArg KernelObject.objectType hk
      rw [projectKernelObject_objectType, projectKernelObject_objectType] at hTy
      cases y <;> simp [KernelObject.objectType] at hTy
      rename_i m₂
      have hw := ntfn_word_of_project hk
      rw [hW₁, scWordShown_val_succ, hCo, if_pos rfl] at hw
      have hW₂ : m₂.schedContextCode = c.val + 1 := by
        by_cases hs : scWordShown ctx observer m₂.schedContextCode = true
        · rw [if_pos hs] at hw; exact hw.symm
        · rw [if_neg hs] at hw; cases hw
      rw [(SystemState.getNotification?_eq_some_iff _ _ _).mpr hO₂]
      simp only [Option.bind_some, Notification.schedContext, hW₂]
      rfl

/-! ### The lend, in two runs -/

private theorem objId_toValid?_val {o : SeLe4n.ObjId} {v : SeLe4n.ValidObjId}
    (h : o.toValid? = some v) : v.val = o := by
  unfold SeLe4n.ObjId.toValid? at h
  split at h
  · cases h
  · cases h; rfl

/-- **The notification lend to a thread labelled as the notification, made in
two low-equivalent runs, leaves them low-equivalent**, for every observer: both
runs hold equal binding labels (`bindingLabelsEqual`), keep their run queues
agreeing with their threads (`runQueueRefined`) and agree on the timer the
context's release reads; each thread carries its own TCB's label
(`threadObjectLabelsEqual`).  The thread's label equation with the notification
is a fact of the labelling, the same in both runs. -/
theorem maybeDonateSchedContext_lowEquivalent_pair {s₁ s₂ : SystemState}
    (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId)
    (hL : lowEquivalent_smp ctx observer s₁ s₂)
    (hI₁ : s₁.objects.invExt) (hI₂ : s₂.objects.invExt)
    (hR₁ : s₁.runQueueRefined) (hR₂ : s₂.runQueueRefined)
    (hτ : s₁.machine.timer = s₂.machine.timer)
    (hB₁ : bindingLabelsEqual ctx s₁) (hB₂ : bindingLabelsEqual ctx s₂)
    (hTO : threadObjectLabelsEqual ctx) (hTN : ctx.threadLabelOf t = ctx.objectLabelOf n) :
    lowEquivalent_smp ctx observer (maybeDonateSchedContext s₁ n t)
      (maybeDonateSchedContext s₂ n t) := by
  have hToEq : objectObservable ctx observer t.toObjId = threadObservable ctx observer t := by
    unfold objectObservable threadObservable; rw [hTO t]
  have hE : ∀ {s : SystemState} {c : SeLe4n.SchedContextId}, bindingLabelsEqual ctx s →
      notificationContext? s n = some c → ctx.objectLabelOf c.toObjId = ctx.threadLabelOf t :=
    fun hB hC => (bindingLabelsEqual.notificationContext hB hC).symm.trans hTN.symm
  cases hT : threadObservable ctx observer t with
  | false =>
    have hTo : objectObservable ctx observer t.toObjId = false := hToEq.trans hT
    exact lowEquivalent_smp_trans (maybeDonateSchedContext_lowEquivalent_hidden s₁ n t hI₁ hB₁ hTN hT hTo)
      (lowEquivalent_smp_trans hL (lowEquivalent_smp_symm
        (maybeDonateSchedContext_lowEquivalent_hidden s₂ n t hI₂ hB₂ hTN hT hTo)))
  | true =>
    have hTo : objectObservable ctx observer t.toObjId = true := hToEq.trans hT
    cases hC₁ : notificationContext? s₁ n with
    | some c =>
      have hEc := hE hB₁ hC₁
      have hC₂ := notificationContext?_pair hL hB₁ hT hC₁ hEc
      rw [maybeDonateSchedContext_of_context hC₁, maybeDonateSchedContext_of_context hC₂]
      cases hvS : c.toObjId.toValid? with
      | none => exact hL
      | some vS =>
        cases hvT : t.toValid? with
        | none => exact hL
        | some vT =>
          dsimp only
          have eS := objId_toValid?_val hvS
          have eT := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hvT
          have hS : objectObservable ctx observer vS.val = true := by
            rw [eS]; unfold objectObservable; rw [hEc]; exact hT
          have hT' : threadObservable ctx observer vT.val = true := by rw [eT]; exact hT
          have hTo' : objectObservable ctx observer vT.val.toObjId = true := by rw [eT]; exact hTo
          rw [schedContextDonateAdmitted_pair vS vT hL hB₁ hB₂ hS hT' hTo']
          cases hA : SchedContextOps.schedContextDonateAdmitted s₂ vS vT with
          | false => exact hL
          | true =>
            have hA₁ := (schedContextDonateAdmitted_pair vS vT hL hB₁ hB₂ hS hT' hTo').trans hA
            exact schedContextBindPerform_lowEquivalent_pair vS vT hL hI₁ hI₂ hR₁ hR₂ hτ hS hT'
              hTo' hA₁ hA
    | none =>
      have hC₂ : notificationContext? s₂ n = none := by
        cases h₂ : notificationContext? s₂ n with
        | none => rfl
        | some c =>
          have := notificationContext?_pair (lowEquivalent_smp_symm hL) hB₂ hT h₂ (hE hB₂ h₂)
          rw [hC₁] at this; cases this
      rw [maybeDonateSchedContext_of_no_context hC₁, maybeDonateSchedContext_of_no_context hC₂]
      exact hL

/-- **Over a deployment's labelling**: the labelling hypothesis is discharged,
leaving equal binding labels in both runs, the run-queue agreement, the timer and
the thread's label equation with the notification. -/
theorem maybeDonateSchedContext_lowEquivalent_pair_deployment
    (d : DeploymentLabeling) {observer : IfObserver} {s₁ s₂ : SystemState}
    (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId)
    (hL : lowEquivalent_smp (deploymentLabelingContext d) observer s₁ s₂)
    (hI₁ : s₁.objects.invExt) (hI₂ : s₂.objects.invExt)
    (hR₁ : s₁.runQueueRefined) (hR₂ : s₂.runQueueRefined)
    (hτ : s₁.machine.timer = s₂.machine.timer)
    (hB₁ : bindingLabelsEqual (deploymentLabelingContext d) s₁)
    (hB₂ : bindingLabelsEqual (deploymentLabelingContext d) s₂)
    (hTN : (deploymentLabelingContext d).threadLabelOf t =
      (deploymentLabelingContext d).objectLabelOf n) :
    lowEquivalent_smp (deploymentLabelingContext d) observer
      (maybeDonateSchedContext s₁ n t) (maybeDonateSchedContext s₂ n t) :=
  maybeDonateSchedContext_lowEquivalent_pair n t hL hI₁ hI₂ hR₁ hR₂ hτ hB₁ hB₂
    (deploymentLabelingContext_threadObjectLabelsEqual d) hTN

end NotificationLendTwoRun

end SeLe4n.Kernel
