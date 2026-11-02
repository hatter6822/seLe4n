/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.OffCoreContextMatches

/-!
# Every other core's bank matches its current thread after the timer entry

WS-ZA ZA6.28.  The timer entry's tick writes the saved registers of no thread
current on another core: the clock advance and the diagnostic clear write no
object, the replenishment drain writes scheduling contexts, release links and
run-queue links, the charge rewrites the ticking core's current thread with its
registers, and the timeout pass writes only the thread the exhausted context is
bound to, which is the ticking core's current thread itself; the scheduling
point and the domain step save only the ticking core's outgoing thread.  With
the banks' cross-core frame (`stepCovers`), every other core's bank keeps
matching its current thread (`perCoreTimerTickEntryState_preserves_contextMatchesCurrentOffCore`).
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)
open SeLe4n.Kernel.PriorityInheritance
open SeLe4n.Model.SystemState (RunQueueStage)

/-! ## The drain -/

/-- One due replenishment writes no saved register: the refill rewrites a
scheduling context, the wake writes run-queue links, and the key hook writes
flags. -/
theorem processOneReplenishmentOnCore_savedRegs (st : SystemState) (c : CoreId)
    (scId : SeLe4n.SchedContextId) (now : Nat) (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    (processOneReplenishmentOnCore st c scId now).savedRegs t = st.savedRegs t := by
  have hR : (refillSchedContext st scId now).savedRegs t = st.savedRegs t := by
    unfold SystemState.savedRegs; rw [refillSchedContext_getTcb?_eq st scId now hInv]
  have hRI := refillSchedContext_preserves_objects_invExt st scId now hInv
  unfold processOneReplenishmentOnCore
  rw [show (markRefillKeyChange st (refillWakeOnCore st c scId now) scId).savedRegs t =
      (refillWakeOnCore st c scId now).savedRegs t by
    unfold SystemState.savedRegs SystemState.getTcb?; rw [markRefillKeyChange_objects]]
  unfold refillWakeOnCore
  dsimp only
  split
  · rename_i w _
    split
    · exact hR
    · have hW := (savedRegsUnwritten.of_wakeThread (refillSchedContext st scId now) w c hRI).savedRegs_eq t
      exact (show _ = (wakeThread (refillSchedContext st scId now) w c).1.savedRegs t from rfl).trans
        (hW.trans hR)
  · exact hR

/-- **The drain writes no saved register.** -/
theorem processReplenishmentsDueOnCore_savedRegs (st : SystemState) (c : CoreId) (now : Nat)
    (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    (processReplenishmentsDueOnCore st c now).savedRegs t = st.savedRegs t := by
  simp only [processReplenishmentsDueOnCore]
  refine (drainDueOnCore_induction
    (fun s => s.objects.invExt ∧ s.savedRegs t = st.savedRegs t) c now
    (fun s scId h => ⟨processOneReplenishmentOnCore_preserves_objects_invExt s c scId now h.1,
      (processOneReplenishmentOnCore_savedRegs s c scId now h.1 t).trans h.2⟩)
    (fun s scId h => ⟨SystemState.releasePlace_objects_invExt s c scId h.1, by
      refine Eq.trans ?_ h.2
      unfold SystemState.savedRegs
      rw [(SystemState.releasePlace_agree s c scId).getTcb? t]⟩)
    _ st ⟨hInv, rfl⟩).2

/-- The prepared tick state writes no saved register. -/
theorem timerTickOnCorePrepared_savedRegs (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (t : SeLe4n.ThreadId) :
    (timerTickOnCorePrepared st c).savedRegs t = st.savedRegs t := by
  unfold timerTickOnCorePrepared
  exact processReplenishmentsDueOnCore_savedRegs
    { st with scheduler := st.scheduler.setLastTimeoutErrorsOnCore c [] } c _ hInv t

/-! ## The timeout pass -/

namespace savedRegsKeptExcept

variable {W : SeLe4n.ThreadId → Prop}

/-- A store of any object over a thread in `W`. -/
theorem storeObject_written {st st' : SystemState} {w : SeLe4n.ThreadId} {obj : KernelObject}
    (hInv : st.objects.invExt) (hW : W w) (h : storeObject w.toObjId obj st = .ok ((), st')) :
    savedRegsKeptExcept W st st' := fun t ht => by
  have hne : t.toObjId ≠ w.toObjId := fun e => ht (SeLe4n.ThreadId.toObjId_injective _ _ e ▸ hW)
  unfold SystemState.savedRegs SystemState.getTcb?
  rw [storeObject_objects_ne st st' w.toObjId t.toObjId obj hne hInv h]

/-- The boost's object write rewrites one boost code. -/
theorem of_pipBoostWrite (st : SystemState) (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (pipBoostWrite st tid) := by
  unfold pipBoostWrite
  split
  · rename_i tcb h _
    dsimp only
    split
    · exact .refl _
    · exact .rewriteObject_tcb _ hInv ((SystemState.getTcb?_eq_some_iff _ _ _).mp h) rfl
  · exact .refl _

/-- A boost update writes a boost code and run-queue links. -/
theorem of_updatePipBoostOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : savedRegsKeptExcept W st (updatePipBoostOnCore st c tid) :=
  (of_pipBoostWrite st tid hInv).trans (.of_runLinks (updatePipBoostOnCore_objectsAgreeOffRunLinks st c tid))

/-- The priority-inheritance revert writes boost codes and run-queue links. -/
theorem of_revertPriorityInheritance (fuel : Nat) :
    ∀ (st : SystemState) (tid : SeLe4n.ThreadId), st.objects.invExt →
      savedRegsKeptExcept W st (revertPriorityInheritance st tid fuel) := by
  induction fuel with
  | zero => intro st _ _; exact .refl _
  | succ fuel ih =>
    intro st tid hInv
    have h1 : savedRegsKeptExcept W st (updatePipBoost st tid) :=
      of_updatePipBoostOnCore st Concurrency.bootCoreId tid hInv
    have hI1 := updatePipBoost_preserves_objects_invExt st tid hInv
    simp only [revertPriorityInheritance]
    split
    · exact h1.trans (ih _ _ hI1)
    · exact h1

end savedRegsKeptExcept

/-- **A thread's timeout writes that thread alone**: the queue removal writes
links, the abort stores the thread itself, the wake and the reply-waiter unlink
write links, and the revert writes boost codes. -/
theorem timeoutThread_savedRegsKeptExcept {epId : SeLe4n.ObjId} {isRecvQ : Bool}
    {tid : SeLe4n.ThreadId} {ec : CoreId} {st : SystemState}
    {r : SystemState × Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : timeoutThread epId isRecvQ tid ec st = .ok r) :
    savedRegsKeptExcept (· = tid) st r.1 := by
  unfold timeoutThread at h
  split at h
  · cases h
  · rename_i st2 hAbort
    have hI2 := abortPendingIpcOnEndpoint_preserves_objects_invExt _ _ _ _ _ hInv hAbort
    have hA : savedRegsKeptExcept (· = tid) st st2 := by
      obtain ⟨st1, tcb1, hR, -, hS⟩ := abortPendingIpcOnEndpoint_shape hAbort
      exact (savedRegsKeptExcept.of_map (endpointQueueRemove_map_frame TCB.registerContext
        (fun _ _ _ _ => rfl) hInv hR)).trans
        (.storeObject_written (endpointQueueRemove_preserves_objects_invExt _ _ _ _ _ hInv hR) rfl hS)
    have hW : savedRegsKeptExcept (· = tid) st2 (wakeThread st2 tid ec).1 :=
      (savedRegsUnwritten.of_wakeThread st2 tid ec hI2).kept
    have hIW := wakeThread_preserves_objects_invExt st2 tid ec hI2
    dsimp only at h
    split at h
    · rename_i serverId _
      cases h
      exact (hA.trans hW).trans
        ((savedRegsUnwritten.of_unlinkReplyWaiter _ tid serverId hIW).kept.trans
          (savedRegsKeptExcept.of_revertPriorityInheritance _ _ serverId
            (SystemState.unlinkReplyWaiter_objects_invExt _ _ _ hIW)))
    · cases h
      exact hA.trans hW

/-- **The timeout pass writes the context's bound thread alone.** -/
theorem timeoutBlockedThreads_savedRegsKeptExcept (st : SystemState)
    (scId : SeLe4n.SchedContextId) (ec : CoreId) (hInv : st.objects.invExt) :
    savedRegsKeptExcept (fun t => ∃ sc, st.getSchedContext? scId = some sc ∧ sc.boundThread = some t)
      st (timeoutBlockedThreads st scId ec).1 := by
  unfold timeoutBlockedThreads
  split
  · rename_i sc hS
    split
    · rename_i t hB
      unfold timeoutBlockedThreadStep
      dsimp only
      split
      · split
        · split
          · rename_i r hT
            exact (timeoutThread_savedRegsKeptExcept hInv hT).mono fun x (hx : x = t) => ⟨sc, hS, hx ▸ hB⟩
          · exact .refl _
        · exact .refl _
      · exact .refl _
    · exact .refl _
  · exact .refl _

/-- The timeout pass moves no core's current thread. -/
theorem timeoutBlockedThreads_currentOnCore (st : SystemState) (scId : SeLe4n.SchedContextId)
    (ec d : CoreId) :
    (timeoutBlockedThreads st scId ec).1.scheduler.currentOnCore d = st.scheduler.currentOnCore d := by
  unfold timeoutBlockedThreads
  split
  · split
    · unfold timeoutBlockedThreadStep
      dsimp only
      split
      · split
        · split
          · rename_i r hT
            exact timeoutThread_currentOnCore_eq _ _ _ _ _ r d hT
          · rfl
        · rfl
      · rfl
    · rfl
  · rfl

/-! ## The charge -/

/-- The spend writes no saved register: a scheduling context, its release
place and the run queue's links. -/
theorem spendBudgetOnCore_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} (st : SystemState)
    (c : CoreId) (tid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId) (sc : SchedContext)
    (hSc : st.getSchedContext? scId = some sc) (start ticks : Nat) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (spendBudgetOnCore st c tid scId sc hSc start ticks) := by
  unfold spendBudgetOnCore
  dsimp only
  refine savedRegsKeptExcept.trans ?_
    (.of_runLinks (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _))
  refine savedRegsKeptExcept.trans ?_ (replenishOnCore_savedRegsKeptExcept _ _ _)
  exact savedRegsKeptExcept.rewriteObject_notTcb _ hInv (fun x hx => by
    rw [(SystemState.getSchedContext?_eq_some_iff st _ sc).mp hSc] at hx; cases hx)
    (fun x hx => by cases hx)

/-- The spend keeps the charged context's bound thread. -/
theorem spendBudgetOnCore_boundThread (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (start ticks : Nat) (hInv : st.objects.invExt) :
    ∃ sc', (spendBudgetOnCore st c tid scId sc hSc start ticks).getSchedContext? scId = some sc' ∧
      sc'.boundThread = sc.boundThread := by
  unfold spendBudgetOnCore
  dsimp only
  have h1 := SystemState.rewriteObject_schedContext_getSchedContext?_self st scId
    (cbsUpdateDeadline (sc.chargeBudget start ticks st.machine.timer) st.machine.timer true)
    (SystemState.rewriteAdmissible_schedContext hSc _) hInv
  have h2 := replenishOnCore_boundThread (st.rewriteObject scId.toObjId
    (.schedContext (cbsUpdateDeadline (sc.chargeBudget start ticks st.machine.timer)
      st.machine.timer true)) (SystemState.rewriteAdmissible_schedContext hSc _)) c scId scId
  rw [h1] at h2
  generalize hR : replenishOnCore _ c scId = R at h2
  cases e : R.getSchedContext? scId with
  | none => rw [e] at h2; cases h2
  | some sc2 =>
    rw [e] at h2
    refine ⟨sc2, ?_, (Option.some.inj h2).trans (chargedSchedContext_boundThread sc _ _ _)⟩
    exact (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
      ((SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks R c tid _).get_of_not_tcb
        (fun _ e => KernelObject.noConfusion e) ((SystemState.getSchedContext?_eq_some_iff _ _ _).mp e))

/-- **The exhausting charge writes the charged thread alone**: the spend writes
no saved register, and the timeout pass visits the charged context's bound
thread, which the binding pair has the charged thread be. -/
theorem budgetExhaustOnCore_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (preKey : SeLe4n.Priority × SeLe4n.Deadline × SeLe4n.DomainId)
    (scId : SchedContextId) (sc : SchedContext) (hSc : st.getSchedContext? scId = some sc)
    (ticks : Nat) (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st)
    (hBindId : tcb.schedContextBinding.scId? = some scId) :
    savedRegsKeptExcept (· = tid) st (budgetExhaustOnCore st c tid preKey scId sc hSc ticks) := by
  have hBound : sc.boundThread = some tid := by
    obtain ⟨sc0, hS0, hB0⟩ := hBi tid tcb scId ((SystemState.getTcb?_eq_some_iff _ _ _).mp hTcb)
      hBindId
    have h0 := (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr hS0
    rw [hSc] at h0; cases h0; exact hB0
  have hSp := spendBudgetOnCore_savedRegsKeptExcept (W := (· = tid)) st c tid scId sc hSc
    (st.machine.timer - ticks) ticks hInv
  have hSpI := spendBudgetOnCore_objects_invExt st c tid _ sc hSc (st.machine.timer - ticks) ticks hInv
  obtain ⟨sc', hs', hb'⟩ := spendBudgetOnCore_boundThread st c tid scId sc hSc
    (st.machine.timer - ticks) ticks hInv
  unfold budgetExhaustOnCore
  dsimp only
  generalize spendBudgetOnCore st c tid scId sc hSc (st.machine.timer - ticks) ticks = S at hSp hSpI hs'
  refine (hSp.trans (.of_objects_eq (markKeyChangeFor_objects S tid preKey))).trans ?_
  refine savedRegsKeptExcept.trans ?_ (.of_objects_eq rfl)
  refine (timeoutBlockedThreads_savedRegsKeptExcept _ scId c
    (by rw [markKeyChangeFor_objects]; exact hSpI)).mono ?_
  rintro t ⟨x, hx, hxb⟩
  have hG : (markKeyChangeFor S tid preKey).getSchedContext? scId = S.getSchedContext? scId := by
    unfold SystemState.getSchedContext?; rw [markKeyChangeFor_objects]
  rw [hG, hs'] at hx
  cases hx
  rw [hb', hBound] at hxb
  exact (Option.some.inj hxb).symm

/-- **The charge writes the charged thread alone**: the unbound arms rewrite
its time slice, the bound arm that leaves budget rewrites its context, and the
exhausting arm writes it alone (`budgetExhaustOnCore_savedRegsKeptExcept`). -/
theorem timerTickBudgetOnCore_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st) :
    savedRegsKeptExcept (· = tid) st (timerTickBudgetOnCore st c tid tcb hTcb).1 := by
  have hO := (SystemState.getTcb?_eq_some_iff st tid tcb).mp hTcb
  unfold timerTickBudgetOnCore
  split
  · split
    · unfold sliceExpireOnCore
      dsimp only
      refine savedRegsKeptExcept.trans ?_
        (.of_runLinks (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _))
      exact savedRegsKeptExcept.rewriteObject_tcb (SystemState.rewriteAdmissible_tcb hTcb _) hInv hO rfl
    · exact .rewriteObject_tcb (SystemState.rewriteAdmissible_tcb hTcb _) hInv hO rfl
  all_goals
    rename_i hBind
    split
    · rename_i sc hSc _
      dsimp only
      split
      · exact budgetExhaustOnCore_savedRegsKeptExcept st c tid tcb hTcb _ _ sc hSc 1 hInv hBi
          (by rw [hBind]; rfl)
      · exact .rewriteObject_notTcb (SystemState.rewriteAdmissible_schedContext hSc _) hInv
          (fun x hx => by
            rw [(SystemState.getSchedContext?_eq_some_iff st _ sc).mp hSc] at hx; cases hx)
          (fun x hx => by cases hx)
    · exact .refl _

/-- **The charge moves no core's current thread.** -/
theorem timerTickBudgetOnCore_currentOnCore (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) (d : CoreId) :
    (timerTickBudgetOnCore st c tid tcb hTcb).1.scheduler.currentOnCore d =
      st.scheduler.currentOnCore d := by
  unfold timerTickBudgetOnCore
  split
  · split
    · simp [sliceExpireOnCore, SystemState.rewriteObject_scheduler]
    · simp [SystemState.rewriteObject_scheduler]
  all_goals
    split
    · dsimp only
      split
      · unfold budgetExhaustOnCore
        simp only [markRescheduleTargets_currentOnCore, SchedulerState.setLastTimeoutErrorsOnCore_currentOnCore,
          timeoutBlockedThreads_currentOnCore, markKeyChangeFor_currentOnCore]
        simp [spendBudgetOnCore, replenishOnCore_currentOnCore, SystemState.rewriteObject_scheduler]
      · simp [SystemState.rewriteObject_scheduler]
    · rfl

/-! ## The tick, the domain step and the entry -/

/-- A scheduling point on a state whose current thread on `c` is the tick's. -/
private theorem rescheduleIfPendingOnCore_savedRegsKeptExcept {st s : SystemState} {c : CoreId}
    (hK : savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st s)
    (hs : s.objects.invExt) (hcur : s.scheduler.currentOnCore c = st.scheduler.currentOnCore c) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st
      (rescheduleIfPendingOnCore s c) := by
  unfold rescheduleIfPendingOnCore
  split
  · exact hK.trans ((handleRescheduleOnCoreState_savedRegsKeptExcept s c hs).mono
      fun t h => by rw [← hcur]; exact h)
  · exact hK

/-- **The tick writes the ticking core's current thread alone**: the drain
writes no saved register, the charge writes the charged thread, current on the
ticking core, and the scheduling point saves that same thread. -/
theorem timerTickOnCore_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) (hBi : schedContextBindingBidirectional st) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st (timerTickOnCore st c) := by
  have hP := timerTickOnCorePrepared_savedRegs st c hInv
  have hPInv := timerTickOnCorePrepared_preserves_objects_invExt st c hInv
  have hPBi := (timerTickOnCorePrepared_stepCovers st c hInv hBi).2
  have hPcur : (timerTickOnCorePrepared st c).scheduler.currentOnCore c =
      st.scheduler.currentOnCore c := by
    unfold timerTickOnCorePrepared
    rw [processReplenishmentsDueOnCore_currentOnCore_eq]
    simp
  have hPK : savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st
      (timerTickOnCorePrepared st c) := .of_eq hP
  have hCharge : ∀ tid tcb (hTcb : (timerTickOnCorePrepared st c).getTcb? tid = some tcb) st3 b,
      (timerTickOnCorePrepared st c).scheduler.currentOnCore c = some tid →
      timerTickBudgetOnCore (timerTickOnCorePrepared st c) c tid tcb hTcb = (st3, b) →
      savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st st3 ∧
        st3.objects.invExt ∧ st3.scheduler.currentOnCore c = st.scheduler.currentOnCore c := by
    intro tid tcb hTcb st3 b hCur hb
    have hK := timerTickBudgetOnCore_savedRegsKeptExcept _ c tid tcb hTcb hPInv hPBi
    have hC := timerTickBudgetOnCore_currentOnCore _ c tid tcb hTcb c
    rw [hb] at hK hC
    refine ⟨hPK.trans (hK.mono fun t (ht : t = tid) => by rw [← hPcur, ht]; exact hCur),
      timerTickBudgetOnCore_preserves_objects_invExt _ c tid tcb st3 b hPInv hb, hC.trans hPcur⟩
  rcases timerTickOnCore_cases st c with ⟨_, h⟩ | ⟨_, _, _, h⟩ | ⟨tid, tcb, hTcb, st3, hCur, hb, h⟩ |
      ⟨tid, tcb, hTcb, st3, hCur, hb, h⟩ <;> rw [h]
  · exact rescheduleIfPendingOnCore_savedRegsKeptExcept hPK hPInv hPcur
  · exact rescheduleIfPendingOnCore_savedRegsKeptExcept hPK hPInv hPcur
  · obtain ⟨hK, hI, hC⟩ := hCharge tid tcb hTcb st3 true hCur hb
    exact hK.trans ((scheduleEffectiveOnCore_savedRegsKeptExcept hI
      (scheduleEffectiveOnCore_eq_state st3 c)).mono fun t ht => by rw [← hC]; exact ht)
  · obtain ⟨hK, hI, hC⟩ := hCharge tid tcb hTcb st3 false hCur hb
    exact rescheduleIfPendingOnCore_savedRegsKeptExcept hK hI hC

/-- **The domain switch writes the outgoing thread alone** and leaves the core
idle or as it was. -/
theorem switchDomainOnCoreState_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st
        (switchDomainOnCoreState st c) ∧
      ∀ t, (switchDomainOnCoreState st c).scheduler.currentOnCore c = some t →
        st.scheduler.currentOnCore c = some t := by
  unfold switchDomainOnCoreState
  split
  · exact ⟨.refl _, fun _ h => h⟩
  · dsimp only
    split
    · exact ⟨.refl _, fun _ h => h⟩
    · refine ⟨((saveOutgoingContextOnCore_savedRegsKeptExcept st c hInv).trans
        (.of_runLinks (requeueOutgoingOnCore_objectsAgreeOffRunLinks st c))).trans
        (.of_objects_eq rfl), fun t h => ?_⟩
      simp at h

/-- **The domain step writes the outgoing thread alone**: the boundary's switch
saves it, and the scheduling point after it saves the thread current then,
the same one or none. -/
theorem scheduleDomainOnCoreState_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st
      (scheduleDomainOnCoreState st c) := by
  unfold scheduleDomainOnCoreState
  split
  · exact .refl _
  · split
    · obtain ⟨hK, hC⟩ := switchDomainOnCoreState_savedRegsKeptExcept st c hInv
      exact hK.trans ((scheduleEffectiveOnCore_savedRegsKeptExcept
        (switchDomainOnCore_preserves_objects_invExt st c _ hInv (switchDomainOnCore_eq_state st c))
        (scheduleEffectiveOnCore_eq_state _ c)).mono hC)
    · exact .of_objects_eq rfl

/-- **The timer step writes the saved registers of no thread current on another
core**: the clock advance writes none, the tick and the domain step each write
the ticking core's current thread at their start, which no other core runs
(`currentsUnique` before the tick, and after it through the run-queue
agreement the tick keeps). -/
theorem perCoreTimerTickPost_currentSavedRegsKeptOffCore (S : SystemState) (c : CoreId)
    (hInv : S.objects.invExt) (hR : S.runQueueRefined) (hRef : S.releaseQueueRefined)
    (hD : S.currentDequeuedUnique) (hBi : schedContextBindingBidirectional S)
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore S d) :
    currentSavedRegsKeptOffCore c S (perCoreTimerTickPost S c) := by
  have hClk : RunQueueStage S (tickClockedState S c) := by
    unfold tickClockedState; split
    · exact RunQueueStage.of_frame rfl rfl rfl
    · exact RunQueueStage.refl _
  have hKInv : (tickClockedState S c).objects.invExt := by rw [tickClockedState_objects]; exact hInv
  have hKRef : (tickClockedState S c).releaseQueueRefined := by
    unfold tickClockedState; split <;> exact hRef
  have hKBi : schedContextBindingBidirectional (tickClockedState S c) := by
    unfold tickClockedState; split <;> exact hBi
  have hKAff : ∀ d, replenishQueueAffinityConsistentOnCore (tickClockedState S c) d := by
    unfold tickClockedState; split <;> exact hAff
  have hKD : (tickClockedState S c).currentDequeuedUnique :=
    SystemState.currentDequeuedUniqueExcept_of_eq (st := S)
      (by rw [tickClockedState_scheduler])
      (fun c t => by unfold SystemState.runLinkOn SystemState.getTcb?; rw [tickClockedState_objects])
      (SystemState.StateMono.of_objects (tickClockedState_objects _ _)) hD
  have hCovT := timerTickOnCore_stepCovers _ c hKInv hKBi hKD
  have hTInv := timerTickOnCore_preserves_objects_invExt _ c hKInv
  have hCovD := scheduleDomainOnCoreState_stepCovers c _ hTInv
  have Stg := hClk.entry.trans (timerTickOnCore_runQueueEntryStage _ c
    (timerTickOnCorePrepared_currentContextPlaceableOnCore _ c hKInv hKRef hKD hKBi hKAff))
  have hUT := currentsUnique_of_dequeuedUnique (Stg.2 hInv hR (Stg.1.links hInv hR).2 hD)
  have h0 : currentSavedRegsKeptOffCore c S (tickClockedState S c) :=
    currentSavedRegsKeptOffCore_of_eq fun t => by
      unfold SystemState.savedRegs SystemState.getTcb?; rw [tickClockedState_objects]
  have h1 := currentSavedRegsKeptOffCore_of_current
    (timerTickOnCore_savedRegsKeptExcept _ c hKInv hKBi) (currentsUnique_of_dequeuedUnique hKD)
    hCovT.currentKept
  have h2 := currentSavedRegsKeptOffCore_of_current
    (scheduleDomainOnCoreState_savedRegsKeptExcept _ c hTInv) hUT hCovD.currentKept
  exact currentSavedRegsKeptOffCore_trans (currentSavedRegsKeptOffCore_trans h0 h1 hCovT.currentKept)
    h2 hCovD.currentKept

section
attribute [local irreducible] contextMatchesCurrentOnCore

/-- WS-ZA ZA6.28: **the timer entry keeps every other core's bank match**: the
save, the timer step (`perCoreTimerTickStep_stepCovers`,
`perCoreTimerTickPost_currentSavedRegsKeptOffCore`), the settle and the
activation.  The tick reads the placement invariants at the saved state, as its
run-queue agreement does (`perCoreTimerTickEntryState_runQueueEntryStage`). -/
theorem perCoreTimerTickEntryState_preserves_contextMatchesCurrentOffCore (coreId : UInt64)
    (c : CoreId) (hc : Concurrency.coreIdOfUInt64? coreId = some c)
    (frame : Option Architecture.InFlightContext) (st : SystemState) (E : EntryPremises st)
    (hRT : st.residentsHaveTcbs) (hBNR : st.blockedNotResident)
    (hN : st.currentNotResidentElsewhere)
    (hRef : (Concurrency.saveCapturedTrapFrameAt st coreId frame).releaseQueueRefined)
    (hBi : schedContextBindingBidirectional (Concurrency.saveCapturedTrapFrameAt st coreId frame))
    (hAff : ∀ d, replenishQueueAffinityConsistentOnCore
      (Concurrency.saveCapturedTrapFrameAt st coreId frame) d)
    (d : CoreId) (hd : d ≠ c) (h : contextMatchesCurrentOnCore st d) :
    contextMatchesCurrentOnCore (Architecture.clearIcacheMaintenance
      (Architecture.clearPhysicalWrites (activateThreadAt (PriorityInheritance.settleResidencyAt
        ((timerTickBracket coreId).run
          (Concurrency.saveCapturedTrapFrameAt st coreId frame)).2 coreId) coreId))) d := by
  obtain ⟨hlt, rfl⟩ := coreIdOfUInt64?_some hc
  have hAt : Concurrency.saveCapturedTrapFrameAt st coreId frame =
      Architecture.saveCapturedTrapFrame st ⟨coreId.toNat, hlt⟩ frame := by
    simp [Concurrency.saveCapturedTrapFrameAt, hc]
  have hSc := saveCapturedTrapFrame_contextMatchesCurrentOffCore st _ frame E.objInv
    (currentsUnique_of_dequeuedUnique E.dequeued) hN d hd h
  obtain ⟨ES, -, -, -⟩ := saveCapturedTrapFrame_carriesPremises st ⟨coreId.toNat, hlt⟩
    frame E hRT hBNR hN
  have StAll := perCoreTimerTickEntryState_runQueueEntryStage coreId frame st
    (hAt ▸ ES.objInv) hRef (hAt ▸ ES.dequeued) hBi hAff
  have hUf := currentsUnique_of_dequeuedUnique
    (StAll.2 E.objInv E.refined (StAll.1.links E.objInv E.refined).2 E.dequeued)
  rw [hAt] at hRef hBi hAff
  simp only [activateThreadAt, PriorityInheritance.settleResidencyAt,
    Concurrency.saveCapturedTrapFrameAt, hc] at hUf ⊢
  generalize Architecture.saveCapturedTrapFrame st ⟨coreId.toNat, hlt⟩ frame = S
    at hSc ES hRef hBi hAff hUf
  have hP : ((timerTickBracket coreId).run S).2 = perCoreTimerTickPost S ⟨coreId.toNat, hlt⟩ := by
    rw [timerTickBracket_run, perCoreTimerTickStepWithClockAdvance_state,
      perCoreTimerTickStep_valid_core S coreId hlt]
  rw [hP] at hUf ⊢
  have hCov := perCoreTimerTickStep_stepCovers S coreId hlt ES.objInv hBi ES.dequeued
  rw [perCoreTimerTickStep_valid_core S coreId hlt] at hCov
  have hS := perCoreTimerTickPost_currentSavedRegsKeptOffCore S ⟨coreId.toNat, hlt⟩ ES.objInv
    ES.refined hRef ES.dequeued hBi hAff
  have hI : (perCoreTimerTickPost S ⟨coreId.toNat, hlt⟩).objects.invExt :=
    scheduleDomainOnCore_preserves_objects_invExt _ ⟨coreId.toNat, hlt⟩ _
      (timerTickOnCore_preserves_objects_invExt _ _ (by rw [tickClockedState_objects]; exact ES.objInv))
      (scheduleDomainOnCore_eq_state _ _)
  exact contextMatchesCurrentOnCore_clearLedgers
    (settleThenActivateOnCore_contextMatchesCurrentOffCore hCov hS hI
      (hUf.of_scheduler (by simp [Architecture.clearIcacheMaintenance,
        Architecture.clearPhysicalWrites])) d hd hSc)

end

end SeLe4n.Kernel
