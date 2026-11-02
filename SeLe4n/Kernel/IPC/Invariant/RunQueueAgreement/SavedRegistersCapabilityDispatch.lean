/-
Copyright (c) 2026 seLe4n contributors. All rights reserved.
Released under GPL-3.0-or-later license as described in the file LICENSE.
-/
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.SavedRegistersFinalise

/-!
# The saved-register census over the capability-only dispatch

WS-ZA ZA6.25.  The capability-only dispatch's TCB and scheduling-context arms,
and then the whole dispatch (`dispatchCapabilityOnly_savedRegsKeptOffCore`).

Each arm is read as the threads it writes (`savedRegsWrittenFree`, at the
entry's start), so the census follows from the step's own cross-core frames:

* **The scheduling point.**  The executing core's reschedule
  (`handleRescheduleOnCoreState`) saves the core's outgoing thread alone
  (`handleRescheduleOnCoreState_savedRegsKeptExcept`).  Nothing before it in an
  arm makes a thread current on the executing core (each prior step keeps or
  clears that core's slot), so the outgoing thread is the caller, which no
  other core holds (`offCoreFree_of_current`).
* **The suspend's restore.**  The suspend's teardown restores its victim with
  the cancellation frame only when the victim was blocked in IPC at the entry's
  start, so current nowhere and resident nowhere (`offCoreFree_of_blocked`).
* **The resume.**  Its fault retire writes the restart frame only into a thread
  no core holds (`retirePendingFaultForResume_savedRegsKeptOffCore`); the rest
  of the resume writes no saved register but the scheduling point's.
* **`setConsumed`.**  The Consumed invocation writes the caller's first message
  register, and the caller is the executing core's current thread.
* **`completeYieldFrom`.**  No TCB or scheduling-context arm completes a yield
  outside a finalisation: the suspend cancels its victim's link
  (`cancelYieldTo`), which writes no register.  The completions a finalisation
  runs write a yield-linked thread, which no core holds
  (`yieldLinkedNotResident`); they reach this dispatch through the final delete
  and revoke and the space change's zombie passes, ZA6.24's
  `finaliseCensusChain`.
* **The space change.**  The zombie passes are that chain; the slot copies
  write no saved register, and their retires remove only threads no core holds.

Every other arm writes no saved register.
-/

namespace SeLe4n.Kernel
open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId)

/-! ### A core's own slot -/

/-- A core other than `e` (`numCores` is four), off which a frame or a census
reads core `e` as another core's. -/
def otherCore (e : CoreId) : CoreId :=
  if e.val = 0 then ⟨1, by decide⟩ else ⟨0, by decide⟩

theorem ne_otherCore (e : CoreId) : e ≠ otherCore e := by
  unfold otherCore
  split
  · rename_i h; intro he; rw [he] at h; cases h
  · rename_i h; intro he; rw [he] at h; exact h rfl

/-- **Core `c`'s current slot is kept or cleared** from `pre` to `post`. -/
def currentKeptOnCore (c : CoreId) (pre post : SystemState) : Prop :=
  ∀ t, post.scheduler.currentOnCore c = some t → pre.scheduler.currentOnCore c = some t

namespace currentKeptOnCore

variable {c : CoreId}

theorem refl (st : SystemState) : currentKeptOnCore c st st := fun _ h => h

theorem trans {a b d : SystemState} (h₁ : currentKeptOnCore c a b) (h₂ : currentKeptOnCore c b d) :
    currentKeptOnCore c a d := fun t h => h₁ t (h₂ t h)

theorem of_eq {pre post : SystemState}
    (h : post.scheduler.currentOnCore c = pre.scheduler.currentOnCore c) :
    currentKeptOnCore c pre post := fun _ ht => h ▸ ht

/-- **A frame off every core keeps every core's slot**: there is a second core
(`numCores` is four), off which the frame reads core `c`. -/
theorem of_offCore {pre post : SystemState} (h : ∀ e, currentKeptOffCore e pre post) :
    currentKeptOnCore c pre post := fun t ht =>
  h (otherCore c) c (ne_otherCore c) t ht

/-- A step every core's coverage holds of. -/
theorem of_stepCovers {pre post : SystemState} (h : ∀ e, stepCovers e pre post) :
    currentKeptOnCore c pre post :=
  of_offCore fun e => (h e).currentKept

end currentKeptOnCore

/-! ### The scheduling point -/

namespace savedRegsKeptExcept

variable {W : SeLe4n.ThreadId → Prop}

/-- A write of run-queue links and the scheduler alone. -/
theorem of_runLinks_eq {pre post : SystemState}
    (h : ∀ x, (post.getTcb? x).map TCB.withoutRunLinks = (pre.getTcb? x).map TCB.withoutRunLinks) :
    savedRegsKeptExcept W pre post := fun t _ =>
  TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.registerContext (h t)

end savedRegsKeptExcept

/-- **The preemption saves core `c`'s current thread alone**: the outgoing
thread's context save, then its re-enqueue, which writes run-queue links. -/
theorem preemptCurrentOnCore_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (incoming : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st
      (preemptCurrentOnCore st c incoming) := fun t ht =>
  TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.registerContext
    (preemptCurrentOnCore_getTcb?_ne_current st c incoming t hInv ht)

/-- The decision with nothing dispatched: an out-of-domain incumbent's
preemption, or nothing, then the flag cleared. -/
theorem rescheduleNoCandidateOnCore_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st
      (rescheduleNoCandidateOnCore st c) := by
  unfold rescheduleNoCandidateOnCore dropCurrentOnCore
  split
  · exact (preemptCurrentOnCore_savedRegsKeptExcept st c _ hInv).trans (.of_objects_eq rfl)
  · exact .of_objects_eq rfl

/-- WS-ZA ZA6.25: **the scheduling point saves the core's outgoing thread
alone**: the preemption writes core `c`'s current thread, and the dequeue and
the incoming restore write run-queue links and the core's bank. -/
theorem handleRescheduleOnCoreState_savedRegsKeptExcept (st : SystemState) (c : CoreId)
    (hInv : st.objects.invExt) :
    savedRegsKeptExcept (fun t => st.scheduler.currentOnCore c = some t) st
      (handleRescheduleOnCoreState st c) := by
  unfold handleRescheduleOnCoreState
  split
  · exact rescheduleNoCandidateOnCore_savedRegsKeptExcept st c hInv
  · dsimp only
    split
    · split
      · split
        · exact ((preemptCurrentOnCore_savedRegsKeptExcept st c _ hInv).trans (.of_runLinks (SystemState.runRemoveOnCore_objectsAgreeOffRunLinks _ c _))).trans
            (.of_objects_eq (restoreIncomingContextOnCoreUnlessCurrent_objects _ c _))
        · exact rescheduleNoCandidateOnCore_savedRegsKeptExcept st c hInv
      · exact rescheduleNoCandidateOnCore_savedRegsKeptExcept st c hInv
    · exact .of_objects_eq rfl

/-- **The scheduling point writes only threads free at `base`**, given the
core's current thread is. -/
theorem handleRescheduleSgiOnCore_savedRegsWrittenFree {e : CoreId} {base s s' : SystemState}
    (hInv : s.objects.invExt)
    (hFree : ∀ t, s.scheduler.currentOnCore e = some t → offCoreFree e base t)
    (h : handleRescheduleSgiOnCore s e = .ok s') : savedRegsWrittenFree e base s s' := by
  rw [handleRescheduleSgiOnCore_eq_state] at h
  cases h
  exact .of_kept (handleRescheduleOnCoreState_savedRegsKeptExcept s e hInv) hFree

/-! ### One slot written -/

namespace savedRegsKeptExcept

variable {W : SeLe4n.ThreadId → Prop}

/-- **One slot written**: every other slot kept, and the written one holds no
TCB on either side or a TCB on both with the same saved registers. -/
theorem of_oneSlot {pre post : SystemState} (k : SeLe4n.ObjId)
    (hO : ∀ k', k' ≠ k → post.objects[k']? = pre.objects[k']?)
    (hk : ((∀ x : TCB, pre.objects[k]? ≠ some (.tcb x)) ∧ ∀ x : TCB, post.objects[k]? ≠ some (.tcb x)) ∨
      ∃ x y : TCB, pre.objects[k]? = some (.tcb x) ∧ post.objects[k]? = some (.tcb y) ∧
        y.registerContext = x.registerContext) :
    savedRegsKeptExcept W pre post :=
  of_slotsTcb fun k' => by
    by_cases h : k' = k
    · subst h; exact .inr hk
    · exact .inl (hO k' h)

/-- A thread stored over itself with its saved registers. -/
theorem storeObject_tcb {pre post : SystemState} {k : SeLe4n.ObjId} {x y : TCB}
    (hInv : pre.objects.invExt) (hPre : pre.objects[k]? = some (.tcb x))
    (hS : storeObject k (.tcb y) pre = .ok ((), post)) (hr : y.registerContext = x.registerContext) :
    savedRegsKeptExcept W pre post :=
  of_oneSlot k (fun k' h => storeObject_objects_ne pre post k k' _ h hInv hS)
    (.inr ⟨x, y, hPre, storeObject_objects_eq' pre k _ _ hInv hS, hr⟩)

/-- An object that is no thread stored over one that is none. -/
theorem storeObject_notTcb {pre post : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (hInv : pre.objects.invExt) (hPre : ∀ x : TCB, pre.objects[k]? ≠ some (.tcb x))
    (hS : storeObject k obj pre = .ok ((), post)) (hObj : ∀ x : TCB, obj ≠ .tcb x) :
    savedRegsKeptExcept W pre post :=
  of_oneSlot k (fun k' h => storeObject_objects_ne pre post k k' _ h hInv hS)
    (.inl ⟨hPre, fun x hx => hObj x (by
      rw [storeObject_objects_eq' pre k _ _ hInv hS] at hx; exact Option.some.inj hx)⟩)

/-- A thread rewritten in place with its saved registers. -/
theorem rewriteObject_tcb {st : SystemState} {k : SeLe4n.ObjId} {x y : TCB}
    (h : st.rewriteAdmissible k (.tcb y)) (hInv : st.objects.invExt)
    (hPre : st.objects[k]? = some (.tcb x)) (hr : y.registerContext = x.registerContext) :
    savedRegsKeptExcept W st (st.rewriteObject k (.tcb y) h) :=
  of_oneSlot k (fun k' hk => SystemState.rewriteObject_objects_ne st k k' _ h (Ne.symm hk) hInv)
    (.inr ⟨x, y, hPre, SystemState.rewriteObject_objects_self st k _ h hInv, hr⟩)

/-- An object that is no thread rewritten in place over one that is none. -/
theorem rewriteObject_notTcb {st : SystemState} {k : SeLe4n.ObjId} {obj : KernelObject}
    (h : st.rewriteAdmissible k obj) (hInv : st.objects.invExt)
    (hPre : ∀ x : TCB, st.objects[k]? ≠ some (.tcb x)) (hObj : ∀ x : TCB, obj ≠ .tcb x) :
    savedRegsKeptExcept W st (st.rewriteObject k obj h) :=
  of_oneSlot k (fun k' hk => SystemState.rewriteObject_objects_ne st k k' _ h (Ne.symm hk) hInv)
    (.inl ⟨hPre, fun x hx => hObj x (by
      rw [SystemState.rewriteObject_objects_self st k _ h hInv] at hx; exact Option.some.inj hx)⟩)

end savedRegsKeptExcept

/-! ### The arms that write no saved register -/

/-- The notification bind writes a notification and the bound thread's binding
code. -/
theorem bindNotification_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {nid : SeLe4n.ObjId} {tcbId : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : bindNotification nid tcbId st = .ok ((), st')) : savedRegsKeptExcept W st st' := by
  unfold bindNotification at h
  split at h
  · rename_i ntfn hN
    split at h
    · cases h
    · rename_i tcb hT
      split at h
      · cases h
      · split at h
        · cases h
        · rename_i st1 hS1
          split at h
          · cases h
          · rename_i st2 hS2
            cases h
            have hNraw := (SystemState.getNotification?_eq_some_iff st nid ntfn).mp hN
            have hTraw := lookupTcb_some_objects st tcbId tcb hT
            have hI1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS1
            have hNe : tcbId.toObjId ≠ nid := fun e => by rw [e, hNraw] at hTraw; cases hTraw
            have k1 : savedRegsKeptExcept W st st1 :=
              .storeObject_notTcb hInv (fun x hx => by rw [hNraw] at hx; cases hx) hS1
                (fun x hx => by cases hx)
            have hT1 : st1.objects[tcbId.toObjId]? = some (.tcb tcb) := by
              rw [storeObject_objects_ne st st1 nid _ _ hNe hInv hS1]; exact hTraw
            exact k1.trans (.storeObject_tcb hI1 hT1 hS2 rfl)
  · split at h <;> cases h

namespace savedRegsKeptExcept

variable {W : SeLe4n.ThreadId → Prop}

/-- A write of contexts' release-queue fields alone. -/
theorem of_releaseLinks {pre post : SystemState} (h : post.objectsAgreeOffReleaseLinks pre) :
    savedRegsKeptExcept W pre post := fun t _ => by
  unfold SystemState.savedRegs
  cases hP : pre.getTcb? t with
  | some x =>
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr (h.get_of_not_sc (fun _ e => KernelObject.noConfusion e)
      ((SystemState.getTcb?_eq_some_iff _ _ _).mp hP))]
  | none =>
    cases hQ : post.getTcb? t with
    | none => rfl
    | some y =>
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr (h.symm.get_of_not_sc
        (fun _ e => KernelObject.noConfusion e) ((SystemState.getTcb?_eq_some_iff _ _ _).mp hQ))] at hP
      cases hP

/-- The boost's re-walk from a waiter: nothing, or one propagation. -/
theorem of_repropagateFromWaiter (st : SystemState) (tid : SeLe4n.ThreadId) (ec : CoreId)
    (fuel : Nat) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (PriorityInheritance.repropagateFromWaiter st tid ec fuel) := by
  rcases PriorityInheritance.repropagateFromWaiter_cases st tid ec fuel with h | ⟨srv, -, h⟩
  · rw [h]; exact refl st
  · rw [h]; exact of_propagatePipChainCrossCore st srv ec fuel hInv

end savedRegsKeptExcept

/-- The notification unbind writes the thread's binding code and a
notification. -/
theorem unbindNotification_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {tcbId : SeLe4n.ThreadId} (hInv : st.objects.invExt)
    (h : unbindNotification tcbId st = .ok ((), st')) : savedRegsKeptExcept W st st' := by
  unfold unbindNotification at h
  split at h
  · cases h
  · rename_i tcb hT
    have hTraw := lookupTcb_some_objects st tcbId tcb hT
    split at h
    · cases h
    · split at h
      · cases h
      · rename_i st1 hS1
        have k1 : savedRegsKeptExcept W st st1 := .storeObject_tcb hInv hTraw hS1 rfl
        have hI1 := storeObject_preserves_objects_invExt st st1 _ _ hInv hS1
        split at h
        · rename_i ntfn hN
          split at h
          · cases h
          · rename_i st2 hS2
            cases h
            exact k1.trans (.storeObject_notTcb hI1 (fun x hx => by
              rw [(SystemState.getNotification?_eq_some_iff st1 _ ntfn).mp hN] at hx; cases hx) hS2
              (fun x hx => by cases hx))
        · cases h; exact k1

/-- The IPC-buffer write stores the thread with its buffer address alone. -/
theorem setIPCBufferOp_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {addr : SeLe4n.VAddr} (hInv : st.objects.invExt)
    (h : Architecture.IpcBufferValidation.setIPCBufferOp st vtid addr = .ok st') :
    savedRegsKeptExcept W st st' := by
  unfold Architecture.IpcBufferValidation.setIPCBufferOp at h
  split at h
  · cases h
  · split at h
    · rename_i tcb hT
      dsimp only at h
      split at h
      · rename_i hS
        cases h
        exact .storeObject_tcb hInv ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hS rfl
      · cases h
    · cases h

/-- The fault-handler install rewrites the thread with its handler alone. -/
theorem setThreadFaultHandlerOp_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop}
    {st st' : SystemState} {vtid : SeLe4n.ValidThreadId} {cptr : SeLe4n.CPtr}
    (hInv : st.objects.invExt) (h : setThreadFaultHandlerOp st vtid cptr = .ok st') :
    savedRegsKeptExcept W st st' := by
  unfold setThreadFaultHandlerOp at h
  split at h
  · cases h
  · rename_i tcb hT _
    split at h
    · cases h
    · cases h
      unfold installFaultHandler
      exact .rewriteObject_tcb _ hInv ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) rfl

/-- The affinity change rewrites the moved thread's affinity and run-queue
links, and no other thread's TCB but its links. -/
theorem setThreadCpuAffinityWithMigration_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop}
    {st st' : SystemState} {tid : SeLe4n.ThreadId} {affinity : Option CoreId} {ec : CoreId}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : setThreadCpuAffinityWithMigration st tid affinity ec = .ok (st', sgi?)) :
    savedRegsKeptExcept W st st' := fun u _ => by
  obtain ⟨tcb, hT, -, -, -, hNe, hTv, -, -, -⟩ := setThreadCpuAffinityWithMigration_placement hInv h
  unfold SystemState.savedRegs
  by_cases hu : u = tid
  · subst hu
    rw [TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.registerContext
      (b := some { tcb with cpuAffinity := affinity }) hTv, hT]
    rfl
  · exact TCB.map_proj_eq_of_map_withoutRunLinks_eq _ (hNe u hu)

/-- The configure's propagation into its bound thread: the thread's priority and
domain rewritten in place, and its bucket re-keyed. -/
theorem schedContextConfigureBoundPropagate_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop}
    (stStored : SystemState) (scId : SeLe4n.SchedContextId) (boundTid : SeLe4n.ThreadId)
    (boundTcb : TCB) (hBound : stStored.getTcb? boundTid = some boundTcb) (priority domain : Nat)
    (hInv : stStored.objects.invExt) :
    savedRegsKeptExcept W stStored
      (SchedContextOps.schedContextConfigureBoundPropagate stStored scId boundTid boundTcb hBound
        priority domain) := by
  unfold SchedContextOps.schedContextConfigureBoundPropagate
  have hP : ∀ s : SystemState, savedRegsKeptExcept W stStored s → s.objects.invExt →
      savedRegsKeptExcept W stStored (match s.getTcbWitnessed? boundTid with
        | some ⟨currentTcb, hCurrent⟩ =>
          if currentTcb.domain.val = domain ∨
             ¬ SchedContextOps.schedContextConfigurePropagates boundTcb scId then s
          else s.rewriteObject boundTid.toObjId (KernelObject.tcb { currentTcb with domain := ⟨domain⟩ })
            (SystemState.rewriteAdmissible_tcb hCurrent _)
        | none => s) := fun s k hI => by
    split
    · rename_i currentTcb hCurrent _
      split
      · exact k
      · exact k.trans (.rewriteObject_tcb _ hI ((SystemState.getTcb?_eq_some_iff _ _ _).mp hCurrent) rfl)
    · exact k
  apply hP
  · split
    · exact .refl _
    · dsimp only
      have k1 := savedRegsKeptExcept.rewriteObject_tcb (W := W)
        (SystemState.rewriteAdmissible_tcb hBound { boundTcb with priority := ⟨priority⟩ }) hInv
        ((SystemState.getTcb?_eq_some_iff _ _ _).mp hBound) rfl
      split
      · exact k1.trans (.of_runLinks (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks _ _ _ _))
      · exact k1
  · split
    · exact hInv
    · dsimp only
      have hI1 := SystemState.rewriteObject_preserves_objects_invExt stStored boundTid.toObjId _
        (SystemState.rewriteAdmissible_tcb hBound { boundTcb with priority := ⟨priority⟩ }) hInv
      split
      · exact SystemState.runRequeueOnCore_objects_invExt _ _ _ _ hI1
      · exact hI1

/-- **The configure writes no saved register**: the replenishment purge and the
release placement write release fields, the store a context over a context,
and the bound thread's propagation, key hooks, boost re-walk and resume tail
priority, domain, run-queue links and boost codes. -/
theorem schedContextConfigure_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop}
    {st st' : SystemState} {vScId : SeLe4n.ValidObjId} {budget period priority deadline domain : Nat}
    (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextConfigure vScId budget period priority deadline domain st =
      .ok ((), st')) : savedRegsKeptExcept W st st' := by
  unfold SchedContextOps.schedContextConfigure at h
  split at h
  · cases h
  · split at h
    · rename_i sc hSc
      dsimp only at h
      split at h
      · have hO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
        simp only [SeLe4n.SchedContextId.toObjId_ofObjId] at hO
        have hA := SchedContextOps.purgeReplenishment_agree st ⟨vScId.val.toNat⟩
        have k1 : savedRegsKeptExcept W st
            (SchedContextOps.purgeReplenishment st ⟨vScId.val.toNat⟩) := .of_releaseLinks hA
        have hI1 := SchedContextOps.purgeReplenishment_objects_invExt st ⟨vScId.val.toNat⟩ hInv
        split at h
        · cases h
        · rename_i st0 hS
          have k2 : savedRegsKeptExcept W st st0 := k1.trans (.storeObject_notTcb hI1
            (fun x hx => by
              have := hA.symm.get_of_not_sc (fun _ e => KernelObject.noConfusion e) hx
              rw [hO] at this; cases this) hS (fun x hx => by cases hx))
          have hI2 := storeObject_preserves_objects_invExt _ st0 _ _ hI1 hS
          split at h
          · cases h; exact k2
          · rename_i boundTid _
            have k3 := k2.trans (.of_releaseLinks (SystemState.releasePlace_agree st0
              (determineTargetCore st boundTid) ⟨vScId.val.toNat⟩))
            have hI3 := SystemState.releasePlace_objects_invExt st0 (determineTargetCore st boundTid)
              ⟨vScId.val.toNat⟩ hI2
            split at h
            · rename_i boundTcb hBound _
              cases h
              have k4 := k3.trans (schedContextConfigureBoundPropagate_savedRegsKeptExcept _
                ⟨vScId.val.toNat⟩ _ _ hBound priority domain hI3)
              have hI4 := SchedContextOps.schedContextConfigureBoundPropagate_preserves_objects_invExt
                _ ⟨vScId.val.toNat⟩ _ _ hBound priority domain hI3
              have hI5 : (markKeyChangeFor (markCandidacyGainFor
                  (SchedContextOps.schedContextConfigureBoundPropagate _ ⟨vScId.val.toNat⟩ boundTid boundTcb
                    hBound priority domain) boundTid (hasSufficientBudget st boundTcb)) boundTid
                  (effectiveSchedParams st boundTcb)).objects.invExt := by
                rw [markKeyChangeFor_objects, markCandidacyGainFor_objects]; exact hI4
              exact ((k4.trans (.of_objects_eq (by rw [markKeyChangeFor_objects,
                markCandidacyGainFor_objects]))).trans (.of_repropagateFromWaiter _ boundTid
                (determineTargetCore st boundTid) st.objectIndex.length hI5)).trans
                (.of_runLinks (SchedContextOps.configureResumeBound_objectsAgreeOffRunLinks _ _ _))
            · cases h; exact k3
      · cases h
    · cases h

/-- **The configure through a control writes no saved register**: the move of
its bound thread to the control's core, then the configure. -/
theorem schedControlConfigure_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop}
    {st st' : SystemState} {core : CoreId} {vScId : SeLe4n.ValidObjId}
    {budget period priority deadline domain : Nat} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedControlConfigure core vScId budget period priority deadline domain st =
      .ok ((), st')) : savedRegsKeptExcept W st st' := by
  rcases SchedContextOps.schedControlConfigure_ok_cases h with h | ⟨_, _, _, _, -, -, -, hM, h⟩
  · exact schedContextConfigure_savedRegsKeptExcept hInv h
  · exact (setThreadCpuAffinityWithMigration_savedRegsKeptExcept hInv hM).trans
      (schedContextConfigure_savedRegsKeptExcept
        (setThreadCpuAffinityWithMigration_preserves_objects_invExt _ _ _ _ hInv _ hM) h)

/-- **The bind writes no saved register**: a context over a context, the bound
thread's binding codes and priority, its bucket and the key hooks, and the
release placement. -/
theorem schedContextBind_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop}
    {st st' : SystemState} {vScId : SeLe4n.ValidObjId} {vThreadId : SeLe4n.ValidThreadId}
    (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextBind vScId vThreadId st = .ok ((), st')) :
    savedRegsKeptExcept W st st' := by
  unfold SchedContextOps.schedContextBind at h
  split at h
  · rename_i sc hSc _
    split at h
    · cases h
    split at h
    · cases h
    split at h
    · rename_i tcb hT
      split at h
      · cases h
      split at h
      · cases h
      split at h
      · cases h
        have hO : st.objects[vScId.val]? = some (.schedContext sc) :=
          (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
        refine savedRegsKeptExcept.trans ?_ (.of_releaseLinks (SystemState.releasePlace_agree _ _ _))
        refine savedRegsKeptExcept.trans ?_ (.of_objects_eq (markKeyChangeFor_objects _ _ _))
        split
        · refine savedRegsKeptExcept.trans ?_
            (.of_runLinks (SystemState.runRequeueOnCore_objectsAgreeOffRunLinks _ _ _ _))
          refine savedRegsKeptExcept.trans ?_ (.updateTcb _ _ _ ?_ (fun _ => rfl))
          · exact .rewriteObject_notTcb _ hInv (fun x hx => by rw [hO] at hx; cases hx)
              (fun x hx => by cases hx)
          · exact SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hInv
        · split
          · refine savedRegsKeptExcept.trans ?_
              (.of_objects_eq (SystemState.markReschedulePendingOnCore_objects _ _))
            refine savedRegsKeptExcept.trans ?_
              (.of_runLinks (SystemState.runEnqueueOnCore_objectsAgreeOffRunLinks _ _ _ _))
            refine savedRegsKeptExcept.trans ?_ (.updateTcb _ _ _ ?_ (fun _ => rfl))
            · exact .rewriteObject_notTcb _ hInv (fun x hx => by rw [hO] at hx; cases hx)
                (fun x hx => by cases hx)
            · exact SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hInv
          · refine savedRegsKeptExcept.trans ?_ (.updateTcb _ _ _ ?_ (fun _ => rfl))
            · exact .rewriteObject_notTcb _ hInv (fun x hx => by rw [hO] at hx; cases hx)
                (fun x hx => by cases hx)
            · exact SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hInv
      all_goals cases h
    · cases h
  · cases h

/-- **The unbind writes no saved register**: a context over a context, the
thread's binding codes, its bucket, the replenishment purge and the key hooks;
the running core's slot is cleared in the scheduler alone. -/
theorem schedContextUnbind_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop}
    {st st' : SystemState} {vScId : SeLe4n.ValidObjId} (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextUnbind vScId st = .ok ((), st')) :
    savedRegsKeptExcept W st st' := by
  unfold SchedContextOps.schedContextUnbind at h
  split at h
  · rename_i sc hSc _
    have hO : st.objects[vScId.val]? = some (.schedContext sc) :=
      (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
    split at h
    · cases h
    · split at h
      · split at h
        · cases h
        · cases h
          refine savedRegsKeptExcept.trans ?_ (.of_objects_eq (markKeyChangeFor_objects _ _ _))
          refine savedRegsKeptExcept.trans ?_ (.of_objects_eq (markCandidacyGainFor_objects _ _ _))
          refine savedRegsKeptExcept.trans ?_ (.of_releaseLinks (SchedContextOps.purgeReplenishment_agree _ _))
          refine savedRegsKeptExcept.trans ?_
            (.of_runLinks (SchedContextOps.schedContextUnbindQueueStage_objectsAgreeOffRunLinks _ _ _ _ _))
          refine savedRegsKeptExcept.trans ?_ (.updateTcb _ _ _ ?_ (fun _ => rfl))
          · exact savedRegsKeptExcept.trans (.of_objects_eq rfl) (.rewriteObject_notTcb _ hInv
              (fun x hx => by rw [hO] at hx; cases hx) (fun x hx => by cases hx))
          · exact SystemState.rewriteObject_preserves_objects_invExt _ _ _ _ hInv
      · cases h
        refine savedRegsKeptExcept.trans ?_ (.of_releaseLinks (SchedContextOps.purgeReplenishment_agree _ _))
        exact .rewriteObject_notTcb _ hInv (fun x hx => by rw [hO] at hx; cases hx)
          (fun x hx => by cases hx)
  · cases h

/-- **A prefix the executing core's scheduling point ends**: the prefix writes
only threads free at `base` and keeps or clears the core's slot, so the outgoing
thread the point saves was the core's current thread at the prefix's start. -/
theorem savedRegsWrittenFree_schedPoint {e : CoreId} {base s0 s s' : SystemState}
    (hW : savedRegsWrittenFree e base s0 s) (hInv : s.objects.invExt)
    (hK : currentKeptOnCore e s0 s)
    (hFree : ∀ t, s0.scheduler.currentOnCore e = some t → offCoreFree e base t)
    (h : s' = s ∨ handleRescheduleSgiOnCore s e = .ok s') : savedRegsWrittenFree e base s0 s' := by
  rcases h with rfl | h
  · exact hW
  · exact hW.trans (handleRescheduleSgiOnCore_savedRegsWrittenFree hInv
      (fun t ht => hFree t (hK t ht)) h)

/-- The caller is the executing core's current thread, which no other core
holds. -/
theorem offCoreFree_of_currentOn {e : CoreId} {st : SystemState} (hU : currentsUnique st)
    (hN : st.currentNotResidentElsewhere) :
    ∀ t, st.scheduler.currentOnCore e = some t → offCoreFree e st t :=
  fun _ ht => offCoreFree_of_current ht hU hN

/-- WS-ZA ZA6.28: **what a scheduling arm does before its scheduling point**: it
writes only threads free of every core at `base`, keeps or clears the executing
core's slot, writes not that core's bank, and ends in no scheduling point or in
the core's reschedule.  The census (`SchedPointPrefix.writtenFree`) and the
executing core's bank agreement both read it. -/
structure SchedPointPrefix (e : CoreId) (base st s st' : SystemState) : Prop where
  writes : ∀ e', savedRegsWrittenFree e' base st s
  current : currentKeptOnCore e st s
  bank : s.machine.regsOnCore e = st.machine.regsOnCore e
  inv : s.objects.invExt
  point : st' = s ∨ handleRescheduleSgiOnCore s e = .ok st'

/-- A prefix that writes no saved register, at any `base`. -/
theorem SchedPointPrefix.of_kept {e : CoreId} {base st s st' : SystemState}
    (k : savedRegsKeptExcept (fun _ => False) st s) (hK : currentKeptOnCore e st s)
    (hB : s.machine.regsOnCore e = st.machine.regsOnCore e) (hI : s.objects.invExt)
    (hP : st' = s ∨ handleRescheduleSgiOnCore s e = .ok st') : SchedPointPrefix e base st s st' :=
  ⟨fun _ => .of_kept k fun _ h => h.elim, hK, hB, hI, hP⟩

/-- A step that writes no saved register, the executing core's slot or its bank,
ahead of a prefix. -/
theorem SchedPointPrefix.cons {e : CoreId} {base st₀ st s st' : SystemState}
    (k : savedRegsKeptExcept (fun _ => False) st₀ st) (hK : currentKeptOnCore e st₀ st)
    (hB : st.machine.regsOnCore e = st₀.machine.regsOnCore e) (P : SchedPointPrefix e base st s st') :
    SchedPointPrefix e base st₀ s st' :=
  ⟨fun e' => (savedRegsWrittenFree.of_kept k fun _ h => h.elim).trans (P.writes e'),
    hK.trans P.current, P.bank.trans hB, P.inv, P.point⟩

/-- **The census of a scheduling arm**: the prefix's, then the scheduling point's
save of the core's current thread, which the prefix found there. -/
theorem SchedPointPrefix.writtenFree {e : CoreId} {base st s st' : SystemState}
    (P : SchedPointPrefix e base st s st')
    (hFree : ∀ t, st.scheduler.currentOnCore e = some t → offCoreFree e base t) :
    savedRegsWrittenFree e base st st' :=
  savedRegsWrittenFree_schedPoint (P.writes e) P.inv P.current hFree P.point

/-- WS-ZA ZA6.28: **the unbind on the executing core** writes no saved register,
slot or bank before its scheduling point. -/
theorem schedContextUnbindOnCore_schedPointPrefix {e : CoreId} {base st st' : SystemState}
    {vScId : SeLe4n.ValidObjId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : SchedContextOps.schedContextUnbindOnCore vScId e st = .ok (st', sgi?)) :
    ∃ s, SchedPointPrefix e base st s st' := by
  unfold SchedContextOps.schedContextUnbindOnCore at h
  split at h
  · cases h
  · rename_i stU hUn
    have C := fun e' => schedContextUnbind_stepCovers st stU vScId e' hInv hUn
    exact ⟨stU, .of_kept (schedContextUnbind_savedRegsKeptExcept hInv hUn)
      (.of_stepCovers fun e' => (C e').1) ((C (otherCore e)).1.banksKept e (ne_otherCore e))
      (C e).2 (SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases _ _ _ _ _ _ h)⟩

/-- WS-ZA ZA6.25: **the unbind on the executing core** writes no saved register
but its scheduling point's. -/
theorem schedContextUnbindOnCore_savedRegsWrittenFree {e : CoreId} {st st' : SystemState}
    {vScId : SeLe4n.ValidObjId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt) (hU : currentsUnique st) (hN : st.currentNotResidentElsewhere)
    (h : SchedContextOps.schedContextUnbindOnCore vScId e st = .ok (st', sgi?)) :
    savedRegsWrittenFree e st st st' := by
  obtain ⟨_, P⟩ := schedContextUnbindOnCore_schedPointPrefix (base := st) hInv h
  exact P.writtenFree (offCoreFree_of_currentOn hU hN)

/-! ### The priority arms -/

/-- The priority write: the bound context's band and the thread's priority. -/
theorem updatePrioritySource_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (p : SeLe4n.Priority) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) := by
  unfold SchedContext.PriorityManagement.updatePrioritySource
  split
  · exact (savedRegsKeptExcept.updateSchedContext st _ _ hInv).trans (.updateTcb _ tid _
      (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv) (fun _ => rfl))
  · exact .updateTcb st tid _ hInv (fun _ => rfl)

/-- The bucket re-key writes run-queue links and the scheduler alone. -/
theorem migrateRunQueueBucketOnCore_machine (st : SystemState) (tid : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (h : CoreId) :
    (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore st tid p h).machine =
      st.machine := by
  unfold SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
  split <;> simp

/-- WS-ZA ZA6.28: **a priority change writes no saved register, slot or bank
before its scheduling point**: the priority write, the bucket re-key, the key
hook and the boost re-walk write priorities, run-queue links and boost codes. -/
theorem applyPriorityChangeOnCore_schedPointPrefix {e : CoreId} {base st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {p : SeLe4n.Priority} {b : Bool}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.applyPriorityChangeOnCore st tid tcb p e b = .ok (st', sgi?)) :
    ∃ s, SchedPointPrefix e base st s st' := by
  unfold SchedContext.PriorityManagement.applyPriorityChangeOnCore at h
  have hI1 := SchedContext.PriorityManagement.updatePrioritySource_preserves_objects_invExt st tid tcb p hInv
  have hI2 := SchedContext.PriorityManagement.migrateRunQueueBucketOnCore_objects_invExt _ tid p
    (determineTargetCore st tid) hI1
  have hI3 : (markKeyChangeFor (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
      (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) tid p
      (determineTargetCore st tid)) tid (effectiveSchedParams st tcb)).objects.invExt := by
    rw [markKeyChangeFor_objects]; exact hI2
  have k : savedRegsKeptExcept (fun _ => False) st (PriorityInheritance.repropagateFromWaiter
      (markKeyChangeFor (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore
        (SchedContext.PriorityManagement.updatePrioritySource st tid tcb p) tid p
        (determineTargetCore st tid)) tid (effectiveSchedParams st tcb)) tid e st.objectIndex.length) :=
    (((updatePrioritySource_savedRegsKeptExcept st tid tcb p hInv).trans
      (.of_runLinks (SchedContext.PriorityManagement.migrateRunQueueBucketOnCore_objectsAgreeOffRunLinks
        _ _ _ _))).trans (.of_objects_eq (markKeyChangeFor_objects _ _ _))).trans
      (.of_repropagateFromWaiter _ tid e _ hI3)
  have C := fun e' => (PriorityInheritance.repropagateFromWaiter_preserves
    (fun s => stepCovers e' _ s ∧ s.objects.invExt) _ tid e st.objectIndex.length
    (fun server _ => propagatePipChainCrossCore_stepCovers e' e _ _ server hI3)
    ⟨stepCovers_refl e' _, hI3⟩).1
  obtain ⟨objs, hU⟩ := SchedContext.PriorityManagement.updatePrioritySource_only_modifies_objects st tid tcb p
  refine ⟨_, .of_kept k ((currentKeptOnCore.of_eq ?_).trans (.of_stepCovers C))
    (((C (otherCore e)).banksKept e (ne_otherCore e)).trans ?_)
    (PriorityInheritance.repropagateFromWaiter_preserves_objects_invExt _ tid e _ hI3)
    (SchedContext.PriorityManagement.priorityRescheduleOnCore_state_cases _ _ _ _ _ _ h)⟩
  · rw [markKeyChangeFor_currentOnCore, migrateRunQueueBucketOnCore_currentOnCore, hU]
  · rw [markKeyChangeFor_machine, migrateRunQueueBucketOnCore_machine, hU]

/-- WS-ZA ZA6.25: **a priority change writes no saved register but its
scheduling point's**. -/
theorem applyPriorityChangeOnCore_savedRegsWrittenFree {e : CoreId} {base st st' : SystemState}
    {tid : SeLe4n.ThreadId} {tcb : TCB} {p : SeLe4n.Priority} {b : Bool}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (hFree : ∀ t, st.scheduler.currentOnCore e = some t → offCoreFree e base t)
    (h : SchedContext.PriorityManagement.applyPriorityChangeOnCore st tid tcb p e b = .ok (st', sgi?)) :
    savedRegsWrittenFree e base st st' := by
  obtain ⟨_, P⟩ := applyPriorityChangeOnCore_schedPointPrefix (base := base) hInv h
  exact P.writtenFree hFree

/-- WS-ZA ZA6.28: **the priority write's prefix**: the checks read, then the
priority change's. -/
theorem setPriorityOnCore_schedPointPrefix {e : CoreId} {base st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid p e =
      .ok (st', sgi?)) : ∃ s, SchedPointPrefix e base st s st' := by
  unfold SchedContext.PriorityManagement.setPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · exact applyPriorityChangeOnCore_schedPointPrefix hInv h
      · cases h
  · cases h

/-- WS-ZA ZA6.25: **the priority write writes no saved register but its
scheduling point's**. -/
theorem setPriorityOnCore_savedRegsWrittenFree {e : CoreId} {st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (hU : currentsUnique st) (hN : st.currentNotResidentElsewhere)
    (h : SchedContext.PriorityManagement.setPriorityOnCore st vCallerTid vTargetTid p e =
      .ok (st', sgi?)) : savedRegsWrittenFree e st st st' := by
  obtain ⟨_, P⟩ := setPriorityOnCore_schedPointPrefix (base := st) hInv h
  exact P.writtenFree (offCoreFree_of_currentOn hU hN)

/-- WS-ZA ZA6.28: **the ceiling write's prefix**: the ceiling is the target's
slot rewritten with its saved registers, and a ceiling that bites is a priority
change. -/
theorem setMCPriorityOnCore_schedPointPrefix {e : CoreId} {base st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (h : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid p e =
      .ok (st', sgi?)) : ∃ s, SchedPointPrefix e base st s st' := by
  unfold SchedContext.PriorityManagement.setMCPriorityOnCore at h
  split at h
  · split at h
    · cases h
    · split at h
      · rename_i targetTcb hTarget _
        have hPre := (SystemState.getTcb?_eq_some_iff st vTargetTid.val targetTcb).mp hTarget
        have hAd := SystemState.rewriteAdmissible_tcb hTarget { targetTcb with maxControlledPriority := p }
        have k : savedRegsKeptExcept (fun _ => False) st
            (st.rewriteObject vTargetTid.val.toObjId (.tcb { targetTcb with maxControlledPriority := p }) hAd) :=
          .rewriteObject_tcb hAd hInv hPre rfl
        have hI := SystemState.rewriteObject_preserves_objects_invExt st _ _ hAd hInv
        have hK : currentKeptOnCore e st
            (st.rewriteObject vTargetTid.val.toObjId (.tcb { targetTcb with maxControlledPriority := p }) hAd) :=
          .of_eq (by rw [SystemState.rewriteObject_scheduler])
        have hB : (st.rewriteObject vTargetTid.val.toObjId
            (.tcb { targetTcb with maxControlledPriority := p }) hAd).machine.regsOnCore e =
              st.machine.regsOnCore e := by rw [SystemState.rewriteObject_machine]
        dsimp only at h
        split at h
        · obtain ⟨s, P⟩ := applyPriorityChangeOnCore_schedPointPrefix (base := base) hI h
          exact ⟨s, .cons k hK hB P⟩
        · cases h; exact ⟨_, .of_kept k hK hB hI (.inl rfl)⟩
      · cases h
  · cases h

/-- WS-ZA ZA6.25: **the ceiling write writes no saved register but its
scheduling point's**. -/
theorem setMCPriorityOnCore_savedRegsWrittenFree {e : CoreId} {st st' : SystemState}
    {vCallerTid vTargetTid : SeLe4n.ValidThreadId} {p : SeLe4n.Priority}
    {sgi? : Option (CoreId × Concurrency.SgiKind)} (hInv : st.objects.invExt)
    (hU : currentsUnique st) (hN : st.currentNotResidentElsewhere)
    (h : SchedContext.PriorityManagement.setMCPriorityOnCore st vCallerTid vTargetTid p e =
      .ok (st', sgi?)) : savedRegsWrittenFree e st st st' := by
  obtain ⟨_, P⟩ := setMCPriorityOnCore_schedPointPrefix (base := st) hInv h
  exact P.writtenFree (offCoreFree_of_currentOn hU hN)

/-! ### The Consumed invocation -/

/-- WS-ZA ZA6.25: **the Consumed invocation writes the caller's saved registers
alone**: its consumed time lands in the caller's first message register, and the
caller is the executing core's current thread. -/
theorem schedContextConsumedOnCore_savedRegsWrittenFree {e : CoreId} {st st' : SystemState}
    {s : SeLe4n.SchedContextId} (hInv : st.objects.invExt) (hU : currentsUnique st)
    (hN : st.currentNotResidentElsewhere) (h : schedContextConsumedOnCore s e st = .ok st') :
    savedRegsWrittenFree e st st st' := by
  obtain ⟨caller, hCur, rfl⟩ := schedContextConsumedOnCore_ok h
  refine savedRegsWrittenFree.of_kept (W := (· = caller)) ?_
    (fun _ ht => ht ▸ offCoreFree_of_currentOn hU hN caller hCur)
  unfold setConsumed
  split
  · exact (savedRegsKeptExcept.updateSchedContext st _ _ hInv).trans
      (.updateTcb_written _ caller _ (SystemState.updateSchedContext_preserves_objects_invExt _ _ _ hInv) rfl)
  · exact .of_objects_eq rfl

/-! ### The resume -/

/-- The resume's restore: the IPC clear, the state and boost write, keeping the
thread's own register window (`restoreToReady` stages nothing). -/
theorem resumeReadyMidState_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} (st : SystemState)
    (tid : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    savedRegsKeptExcept W st (Lifecycle.Suspend.resumeReadyMidState st tid) :=
  (show savedRegsKeptExcept W st (Lifecycle.Suspend.restoreToReady st tid) from
    savedRegsKeptExcept.updateTcb st tid _ hInv (fun _ => rfl)).trans
    (.updateTcb _ tid _ (PriorityInheritance.restoreToReady_objects_invExt st tid hInv) (fun _ => rfl))

/-- WS-ZA ZA6.28: **the resume writes no saved register, slot or bank before
its scheduling point**: the restore keeps the resumed thread's window, the key
hook writes no object, the enqueue writes run-queue links, and every core's slot
is kept up to the local reschedule. -/
theorem resumeThreadOnCore_schedPointPrefix {e : CoreId} {base st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (h : Lifecycle.Suspend.resumeThreadOnCore st vtid e = .ok (st', sgi?)) :
    ∃ s, SchedPointPrefix e base st s st' := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at h
  dsimp only [] at h
  split at h
  · split at h
    · cases h
    have hMid := PriorityInheritance.resumeReadyMidState_objects_invExt st vtid.val hInv
    have h1Inv : (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val)
        vtid.val).objects.invExt := by rw [markKeyChangeFrom_objects]; exact hMid
    have k : savedRegsKeptExcept (fun _ => False) st (enqueueRunnableOnCore
        (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val) vtid.val)
        (determineTargetCore st vtid.val) vtid.val) :=
      ((resumeReadyMidState_savedRegsKeptExcept st vtid.val hInv).trans
        (.of_objects_eq (markKeyChangeFrom_objects _ _ _))).trans
        (fun t _ => savedRegs_enqueueRunnableOnCore _ _ _ h1Inv t)
    have hK : currentKeptOnCore e st (enqueueRunnableOnCore
        (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val) vtid.val)
        (determineTargetCore st vtid.val) vtid.val) :=
      (currentKeptOnCore.of_eq (by
        rw [markKeyChangeFrom_currentOnCore, PriorityInheritance.resumeReadyMidState_scheduler_eq])).trans
        (.of_offCore fun e' => enqueueRunnableOnCore_currentKept e' _ _ _)
    have hB : (enqueueRunnableOnCore
        (markKeyChangeFrom st (Lifecycle.Suspend.resumeReadyMidState st vtid.val) vtid.val)
        (determineTargetCore st vtid.val) vtid.val).machine.regsOnCore e =
          st.machine.regsOnCore e := by
      rw [enqueueRunnableOnCore_machine_eq, markKeyChangeFrom_machine,
        PriorityInheritance.resumeReadyMidState_machine_eq]
    have h2Inv := enqueueRunnableOnCore_preserves_objects_invExt _
      (determineTargetCore st vtid.val) vtid.val h1Inv
    split at h
    · split at h
      · rename_i st4 hH
        cases h
        exact ⟨_, .of_kept k hK hB h2Inv (.inr hH)⟩
      · cases h
    · cases h
      exact ⟨_, .of_kept k hK hB h2Inv (.inl rfl)⟩
  · cases h

/-- WS-ZA ZA6.25: **the resume writes no saved register but its scheduling
point's**. -/
theorem resumeThreadOnCore_savedRegsWrittenFree {e : CoreId} {base st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt)
    (hFree : ∀ t, st.scheduler.currentOnCore e = some t → offCoreFree e base t)
    (h : Lifecycle.Suspend.resumeThreadOnCore st vtid e = .ok (st', sgi?)) :
    savedRegsWrittenFree e base st st' := by
  obtain ⟨_, P⟩ := resumeThreadOnCore_schedPointPrefix (base := base) hInv h
  exact P.writtenFree hFree

/-- A resume that succeeds found its target suspended. -/
theorem resumeThreadOnCore_inactive {st st' : SystemState} {vtid : SeLe4n.ValidThreadId}
    {e : CoreId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : Lifecycle.Suspend.resumeThreadOnCore st vtid e = .ok (st', sgi?)) :
    ∃ tcb, st.getTcb? vtid.val = some tcb ∧ tcb.threadState = .Inactive := by
  unfold Lifecycle.Suspend.resumeThreadOnCore at h
  dsimp only [] at h
  split at h
  · rename_i tcb hT
    split at h
    · cases h
    · rename_i hS
      exact ⟨tcb, hT, by simpa [bne_iff_ne, ne_eq] using hS⟩
  · cases h

/-- WS-ZA ZA6.25: **the resume writes the saved registers of no thread another
core holds.**  Its fault retire writes the restart frame of a suspended thread,
which no core runs (a current thread is active, `currentActive`), and only when
no core holds it resident (`retirePendingFaultForResume_savedRegsKeptOffCore`);
the resume itself writes no saved register but its scheduling point's. -/
theorem tcbResume_savedRegsKeptOffCore {e : CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt) (hR : st.runQueueRefined) (hD : st.currentDequeuedUnique)
    (hN : st.currentNotResidentElsewhere)
    (h : Lifecycle.Suspend.resumeThreadOnCore (retirePendingFaultForResume st vtid.val) vtid e =
      .ok (st', sgi?)) : savedRegsKeptOffCore e st st' := by
  have hSch := retirePendingFaultForResume_scheduler_eq st vtid.val
  have hMach := retirePendingFaultForResume_machine st vtid.val
  have hInv1 := retirePendingFaultForResume_preserves_objects_invExt st vtid.val hInv
  have hStage := retirePendingFaultForResume_runQueueStage st vtid.val
  have hD1 := hStage.2.1 none hInv hR (hStage.1 hInv hR).2 hD
  obtain ⟨tcb, hT, hIn⟩ := resumeThreadOnCore_inactive h
  have hCur : ∀ d, d ≠ e → st.scheduler.currentOnCore d ≠ some vtid.val := fun d _ hd => by
    obtain ⟨x, hx, hA⟩ := hD1.currentActive d vtid.val (by rw [hSch]; exact hd)
    rw [hT] at hx; cases hx; exact hA hIn
  have hFree : ∀ t, (retirePendingFaultForResume st vtid.val).scheduler.currentOnCore e = some t →
      offCoreFree e (retirePendingFaultForResume st vtid.val) t := fun t ht => by
    have hF := offCoreFree_of_currentOn (currentsUnique_of_dequeuedUnique hD) hN t (by rw [← hSch]; exact ht)
    unfold offCoreFree at hF ⊢; rw [hSch, hMach]; exact hF
  have C := (resumeThreadOnCore_stepCovers _ st' vtid e sgi? hInv1 h).1
  exact savedRegsKeptOffCore_trans_stepCovers (retirePendingFaultForResume_savedRegsKeptOffCore hInv hCur)
    ((resumeThreadOnCore_savedRegsWrittenFree hInv1 hFree h).census C.currentKept C.residentKept) C

/-! ### The suspend -/

namespace savedRegsKeptExcept

variable {W : SeLe4n.ThreadId → Prop}

/-- The reclaim's extra steps over the cancellation write run-queue links and
release fields alone. -/
theorem of_cancelIpcBlockingReclaimed (st : SystemState) (v : SeLe4n.ThreadId) (tcb : TCB) :
    savedRegsKeptExcept W (Lifecycle.Suspend.cancelIpcBlocking st v tcb)
      (cancelIpcBlockingReclaimed v tcb st) :=
  of_map fun x => by
    rw [← TCB.map_proj_eq_of_map_withoutRunLinks_eq TCB.registerContext
      (cancelIpcBlockingReclaimed_getTcb? v tcb st x)]

/-- A donated context handed back writes binding codes alone. -/
theorem of_cleanupDonatedSchedContext {st st' : SystemState} {v : SeLe4n.ThreadId}
    (hInv : st.objects.invExt) (h : cleanupDonatedSchedContext st v = .ok st') :
    savedRegsKeptExcept W st st' := by
  unfold cleanupDonatedSchedContext at h
  split at h
  · cases h; exact .refl _
  · split at h
    · obtain ⟨newOwner?, _, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose h
      exact of_map fun x => returnDonatedSchedContext_getTcb?_map_eq TCB.registerContext
        (fun _ _ _ => rfl) _ st' _ _ _ hInv newOwner? hPop x
    · cases h; exact .refl _

end savedRegsKeptExcept

/-- The donated-context return writes binding codes and release links alone. -/
theorem cancelDonatedDonationOnCore_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop}
    {st st' : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB} (hInv : st.objects.invExt)
    (h : cancelDonatedDonationOnCore st t tcb = .ok st') : savedRegsKeptExcept W st st' := by
  unfold cancelDonatedDonationOnCore at h
  split at h
  · split at h
    · cases h
    · rename_i sMid hC
      cases h
      exact (savedRegsKeptExcept.of_cleanupDonatedSchedContext hInv hC).trans
        (.of_releaseLinks (migrateSchedContextReplenishment_agree _ _ _ _))
  · cases h

/-- WS-ZA ZA6.25: **the suspend's cancellation writes the victim alone, and only
when it was blocked**, so then no core runs it or holds it resident
(`offCoreFree_of_blocked`); a ready victim's cancellation writes no thread. -/
theorem cancelIpcBlockingReclaimed_savedRegsWrittenFree {e : CoreId} {st : SystemState}
    {v : SeLe4n.ThreadId} {tcb : TCB} (hInv : st.objects.invExt) (hB : blockedCurrentNowhere st)
    (hBN : st.blockedNotResident) (hT : st.getTcb? v = some tcb) :
    savedRegsWrittenFree e st st (cancelIpcBlockingReclaimed v tcb st) := by
  by_cases hS : tcb.ipcState = .ready
  · refine .of_kept (W := fun _ => False)
      ((savedRegsKeptExcept.of_objects_eq ?_).trans (.of_cancelIpcBlockingReclaimed st v tcb))
      (fun _ h => h.elim)
    simp only [Lifecycle.Suspend.cancelIpcBlocking, hS]
  · exact .of_kept ((cancelIpcBlocking_savedRegsKeptExcept st v tcb hInv).trans
      (.of_cancelIpcBlockingReclaimed st v tcb)) (fun _ ht => ht ▸ offCoreFree_of_blocked hB hBN hT hS)

/-- A suspend's scheduling point is the identity or the executing core's
reschedule. -/
theorem suspendRescheduleOnCore_state_cases {st st' : SystemState} {runningCore e : CoreId}
    {wc ld : Bool} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (h : Lifecycle.Suspend.suspendRescheduleOnCore st runningCore e wc ld = .ok (st', sgi?)) :
    st' = st ∨ handleRescheduleSgiOnCore st e = .ok st' := by
  unfold Lifecycle.Suspend.suspendRescheduleOnCore at h
  repeat' split at h
  all_goals first
    | (cases h; done)
    | (cases h; exact .inl rfl)
    | (rename_i st4 hH; cases h; exact .inr hH)

/-- WS-ZA ZA6.28: **the suspend's prefix writes no saved register but a blocked
victim's, and not the executing core's slot or bank.**  The cancellation writes the victim only when it
was blocked (`cancelIpcBlockingReclaimed_savedRegsWrittenFree`); the boost
revert, the donation cancel, the deschedule, the state clears and the yield-link
cancel write boost codes, binding codes, run-queue and release links and state
fields; and none puts a thread in the executing core's slot, so the thread its
scheduling point saves was the core's current thread at the entry. -/
theorem suspendThreadOnCore_schedPointPrefix {e : CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt) (hB : blockedCurrentNowhere st) (hBN : st.blockedNotResident)
    (h : Lifecycle.Suspend.suspendThreadOnCore st vtid e = .ok (st', sgi?)) :
    ∃ s, SchedPointPrefix e st st s st' := by
  unfold Lifecycle.Suspend.suspendThreadOnCore at h
  dsimp only [] at h
  split at h
  · rename_i tcb hT
    split at h
    · cases h
    have hW1 := fun e' => cancelIpcBlockingReclaimed_savedRegsWrittenFree (e := e') hInv hB hBN hT
    have hK1 : currentKeptOnCore e st (cancelIpcBlockingReclaimed vtid.val tcb st) :=
      .of_stepCovers fun e' => cancelIpcBlockingReclaimed_stepCovers e' st vtid.val tcb hInv
    have hB1 : (cancelIpcBlockingReclaimed vtid.val tcb st).machine.regsOnCore e =
        st.machine.regsOnCore e :=
      (cancelIpcBlockingReclaimed_stepCovers (otherCore e) st vtid.val tcb hInv).banksKept e
        (ne_otherCore e)
    have h1Inv : (cancelIpcBlockingReclaimed vtid.val tcb st).objects.invExt :=
      cancelIpcBlockingReclaimed_objects_invExt vtid.val tcb st
        (Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt st vtid.val tcb hInv)
    cases hBS : PriorityInheritance.blockingServer st vtid.val
    case' none =>
      rw [hBS] at h
      dsimp only at h
      generalize cancelIpcBlockingReclaimed vtid.val tcb st = s2 at h hW1 hK1 hB1 h1Inv
    case' some srv =>
      rw [hBS] at h
      dsimp only at h
      have hc := fun e' => propagatePipChainCrossCore_stepCovers e' e
        (cancelIpcBlockingReclaimed vtid.val tcb st).objectIndex.length _ srv h1Inv
      replace hW1 := fun e' => (hW1 e').trans (.of_kept (W := fun _ => False)
        (.of_propagatePipChainCrossCore _ srv e
          (cancelIpcBlockingReclaimed vtid.val tcb st).objectIndex.length h1Inv) (fun _ h => h.elim))
      replace hK1 := hK1.trans (.of_stepCovers fun e' => (hc e').1)
      replace hB1 := ((hc (otherCore e)).1.banksKept e (ne_otherCore e)).trans hB1
      replace h1Inv := (hc e).2
      clear hc
      generalize (PriorityInheritance.propagatePipChainCrossCore
        (cancelIpcBlockingReclaimed vtid.val tcb st) srv e).1 = s2 at h hW1 hK1 hB1 h1Inv
    all_goals
      split at h
      · cases h
      rename_i s3 hDon
      obtain ⟨k3, hK3, hB3, h3Inv⟩ : savedRegsKeptExcept (fun _ => False) s2 s3 ∧
          currentKeptOnCore e s2 s3 ∧ s3.machine.regsOnCore e = s2.machine.regsOnCore e ∧
          s3.objects.invExt := by
        split at hDon
        · cases hDon; exact ⟨.refl _, .refl _, rfl, h1Inv⟩
        · exact ⟨cancelBoundDonationOnCore_savedRegsKeptExcept h1Inv hDon,
            .of_stepCovers fun e' => (cancelBoundDonationOnCore_stepCovers e' h1Inv hDon).1,
            (cancelBoundDonationOnCore_stepCovers (otherCore e) h1Inv hDon).1.banksKept e
              (ne_otherCore e),
            (cancelBoundDonationOnCore_stepCovers e h1Inv hDon).2⟩
        · exact ⟨cancelDonatedDonationOnCore_savedRegsKeptExcept h1Inv hDon,
            .of_stepCovers fun e' => (cancelDonatedDonationOnCore_stepCovers e' h1Inv hDon).1,
            (cancelDonatedDonationOnCore_stepCovers (otherCore e) h1Inv hDon).1.banksKept e
              (ne_otherCore e),
            (cancelDonatedDonationOnCore_stepCovers e h1Inv hDon).2⟩
      have h4Inv : (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)).objects.invExt :=
        descheduleAt_objects_invExt _ _ _ h3Inv
      have h5Inv : (Lifecycle.Suspend.clearPendingStateValid
          (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) vtid).objects.invExt :=
        SystemState.updateTcb_preserves_objects_invExt _ _ _ h4Inv
      have h6Inv := SystemState.updateTcb_preserves_objects_invExt _ vtid.val
        (fun t => { t with threadState := .Inactive }) h5Inv
      have h6bInv := SystemState.cancelYieldTo_preserves_objects_invExt _ vtid.val h6Inv
      have k : savedRegsKeptExcept (fun _ => False) s2 (cancelYieldTo
          ((Lifecycle.Suspend.clearPendingStateValid
            (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) vtid).updateTcb vtid.val
            fun t => { t with threadState := .Inactive }) vtid.val) :=
        (((k3.trans (.of_runLinks (by
          unfold descheduleAt
          split
          · exact removeRunnableOnCore_objectsAgreeOffRunLinks _ _ _
          · exact .refl _))).trans
          (show savedRegsKeptExcept _ (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val))
            (Lifecycle.Suspend.clearPendingStateValid
              (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) vtid) from
            .updateTcb _ vtid.val _ h4Inv (fun _ => rfl))).trans
          (.updateTcb _ vtid.val (fun t => { t with threadState := .Inactive }) h5Inv (fun _ => rfl))).trans
          (cancelYieldTo_savedRegsKeptExcept _ vtid.val h6Inv)
      have hK : currentKeptOnCore e st (cancelYieldTo
          ((Lifecycle.Suspend.clearPendingStateValid
            (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) vtid).updateTcb vtid.val
            fun t => { t with threadState := .Inactive }) vtid.val) :=
        ((hK1.trans hK3).trans (.of_stepCovers fun e' =>
          descheduleAt_stepCovers e' s3 vtid.val (placedCoreOf? st vtid.val))).trans
          (.of_eq (by
            rw [SystemState.cancelYieldTo_scheduler, SystemState.updateTcb_scheduler]
            unfold Lifecycle.Suspend.clearPendingStateValid Lifecycle.Suspend.clearPendingState
            rw [SystemState.updateTcb_scheduler]))
      have hBk : (cancelYieldTo
          ((Lifecycle.Suspend.clearPendingStateValid
            (descheduleAt s3 vtid.val (placedCoreOf? st vtid.val)) vtid).updateTcb vtid.val
            fun t => { t with threadState := .Inactive }) vtid.val).machine.regsOnCore e =
            st.machine.regsOnCore e := by
        refine Eq.trans ?_ (((descheduleAt_stepCovers (otherCore e) s3 vtid.val
          (placedCoreOf? st vtid.val)).banksKept e (ne_otherCore e)).trans (hB3.trans hB1))
        rw [SystemState.cancelYieldTo_machine, SystemState.updateTcb_machine]
        unfold Lifecycle.Suspend.clearPendingStateValid Lifecycle.Suspend.clearPendingState
        rw [SystemState.updateTcb_machine]
      exact ⟨_, fun e' => (hW1 e').trans (.of_kept k (fun _ h => h.elim)), hK, hBk, h6bInv,
        suspendRescheduleOnCore_state_cases h⟩
  · cases h

/-- WS-ZA ZA6.25: **the suspend writes no saved register but a blocked victim's
and its scheduling point's**: its prefix (`suspendThreadOnCore_schedPointPrefix`),
then the scheduling point's save of the core's current thread at the entry. -/
theorem suspendThreadOnCore_savedRegsWrittenFree {e : CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {sgi? : Option (CoreId × Concurrency.SgiKind)}
    (hInv : st.objects.invExt) (hU : currentsUnique st) (hN : st.currentNotResidentElsewhere)
    (hB : blockedCurrentNowhere st) (hBN : st.blockedNotResident)
    (h : Lifecycle.Suspend.suspendThreadOnCore st vtid e = .ok (st', sgi?)) :
    savedRegsWrittenFree e st st st' := by
  obtain ⟨_, P⟩ := suspendThreadOnCore_schedPointPrefix hInv hB hBN h
  exact P.writtenFree (offCoreFree_of_currentOn hU hN)

/-! ### The space change -/

/-- The thread-slot store keeps the scheduler. -/
theorem storeTcbWith_scheduler (st : SystemState) (id : SeLe4n.ObjId) (f : TCB → TCB) :
    (st.storeTcbWith id f).scheduler = st.scheduler := by
  unfold SystemState.storeTcbWith
  split
  · split
    · rfl
    · split
      · rename_i h; exact storeObject_scheduler_eq _ _ _ _ h
      · rfl
  · rfl

/-- A thread slot's copy keeps the scheduler. -/
theorem threadSlotCopied_scheduler (st : SystemState) (tid : SeLe4n.ThreadId) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    (threadSlotCopied st tid slot srcCNode srcSlot rights).scheduler = st.scheduler := by
  rcases threadSlotCopied_cases st tid slot srcCNode srcSlot rights with ⟨-, e⟩ | ⟨cap, -, e⟩ <;>
    rw [e] <;>
    simp [threadSlotCleared, storeTcbWith_scheduler, SystemState.updateTcb_scheduler]

/-- **A thread slot's copy writes no saved register**: the thread's own slot
cells and every derivation link, nothing else. -/
theorem threadSlotCopied_savedRegsKeptExcept {W : SeLe4n.ThreadId → Prop} {st : SystemState}
    {tid : SeLe4n.ThreadId} {t : TCB} (hInv : st.objects.invExt) (hT : st.getTcb? tid = some t)
    (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    savedRegsKeptExcept W st (threadSlotCopied st tid slot srcCNode srcSlot rights) := by
  obtain ⟨hO, t', hT', hw⟩ := threadSlotCopied_frame hInv hT slot srcCNode srcSlot rights
  refine savedRegsKeptExcept.of_slotsTcb fun k => ?_
  by_cases hk : k = tid.toObjId
  · subst hk
    refine .inr (.inr ⟨t, t', (SystemState.getTcb?_eq_some_iff _ _ _).mp hT,
      (SystemState.getTcb?_eq_some_iff _ _ _).mp hT', ?_⟩)
    have := TCB.proj_eq_of_withoutLinks_eq TCB.registerContext hw
    revert this
    split <;> exact id
  · rcases hO k hk with e | ⟨_, _, ha, hb, _⟩ | ⟨x, y, ha, hb, hw'⟩
    · exact .inl e
    · exact .inr (.inl ⟨fun x hx => (by rw [ha] at hx; cases hx), fun x hx => (by rw [hb] at hx; cases hx)⟩)
    · exact .inr (.inr ⟨x, y, ha, hb, TCB.proj_eq_of_withoutLinks_eq TCB.registerContext hw'⟩)

/-- WS-ZA ZA6.25: **a thread slot set writes the saved registers only of a
thread its retire removes**, which no core holds (`retireFinalObject_savedRegs`);
the slot set keeps the scheduler and the machine. -/
theorem threadSlotSet_savedRegs {e ec : CoreId} {st : SystemState} {tid : SeLe4n.ThreadId}
    {t : TCB} (hInv : st.objects.invExt) (hT : st.getTcb? tid = some t) (slot : SeLe4n.Slot)
    (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) (u : SeLe4n.ThreadId) :
    (threadSlotSet ec st tid slot srcCNode srcSlot rights).savedRegs u = st.savedRegs u ∨
      offCoreFree e st u := by
  unfold threadSlotSet
  have hI := (threadSlotCopied_tcb hInv hT slot srcCNode srcSlot rights).2
  have k := threadSlotCopied_savedRegsKeptExcept (W := fun _ => False) hInv hT slot srcCNode srcSlot
    rights u id
  rcases retireFinalObject_savedRegs e ec (slotRetireTarget st tid.toObjId slot)
      (recorderFor st (slotRetireTarget st tid.toObjId slot) tid.toObjId slot) _ hI u with r | r
  · exact .inl (r.trans k)
  · refine .inr fun d hd => ?_
    have := r d hd
    rwa [threadSlotCopied_scheduler, threadSlotCopied_machine] at this

/-- A thread slot set keeps the scheduler and the machine. -/
theorem threadSlotSet_scheduler_machine (ec : CoreId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (slot : SeLe4n.Slot) (srcCNode : SeLe4n.ObjId) (srcSlot : SeLe4n.Slot) (rights : AccessRightSet) :
    (threadSlotSet ec st tid slot srcCNode srcSlot rights).scheduler = st.scheduler ∧
      (threadSlotSet ec st tid slot srcCNode srcSlot rights).machine = st.machine := by
  unfold threadSlotSet
  obtain ⟨-, hs, hm⟩ := retireFinalObject_fields ec (slotRetireTarget st tid.toObjId slot)
    (recorderFor st (slotRetireTarget st tid.toObjId slot) tid.toObjId slot)
    (threadSlotCopied st tid slot srcCNode srcSlot rights)
  exact ⟨hs.trans (threadSlotCopied_scheduler _ _ _ _ _ _),
    hm.trans (threadSlotCopied_machine _ _ _ _ _ _)⟩

/-- WS-ZA ZA6.25: **a space change writes the saved registers only of threads no
core holds after it**: each slot set writes only a thread its retire removes,
and neither moves the scheduler or the machine. -/
theorem copyThreadSpaces_savedRegs {e ec : CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} (hInv : st.objects.invExt)
    (h : copyThreadSpaces ec st vtid cnSrc vrSrc = .ok st') (u : SeLe4n.ThreadId) :
    st'.savedRegs u = st.savedRegs u ∨ offCoreFree e st' u := by
  obtain ⟨tcb, hT, -, -, hCn, -, rfl⟩ := copyThreadSpaces_ok h
  obtain ⟨cnCap, -, hCL, -⟩ := cspaceRootSourceAdmitted_spec hCn
  obtain ⟨t1, hT1⟩ := Option.isSome_iff_exists.mp
    (threadSlotSet_getTcb? ec hInv hT (slot := TCB.cspaceRootSlot) (by decide)
      cnSrc.cnode cnSrc.slot TCB.cspaceRootRights hCL)
  have hI1 : (threadSlotSet ec st vtid.val TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot
      TCB.cspaceRootRights).objects.invExt := by
    unfold threadSlotSet
    exact (retireFinalObject_frame ec _ _ _ (threadSlotCopied_tcb hInv hT TCB.cspaceRootSlot
      cnSrc.cnode cnSrc.slot TCB.cspaceRootRights).2).1
  obtain ⟨hs1, hm1⟩ := threadSlotSet_scheduler_machine ec st vtid.val TCB.cspaceRootSlot
    cnSrc.cnode cnSrc.slot TCB.cspaceRootRights
  obtain ⟨hs2, hm2⟩ := threadSlotSet_scheduler_machine ec
    (threadSlotSet ec st vtid.val TCB.cspaceRootSlot cnSrc.cnode cnSrc.slot TCB.cspaceRootRights)
    vtid.val TCB.vspaceRootSlot vrSrc.cnode vrSrc.slot TCB.vspaceRootRights
  unfold copyThreadSpacesPerform
  rcases threadSlotSet_savedRegs (e := e) (ec := ec) hI1 hT1 TCB.vspaceRootSlot vrSrc.cnode
      vrSrc.slot TCB.vspaceRootRights u with r2 | r2
  · rcases threadSlotSet_savedRegs (e := e) (ec := ec) hInv hT TCB.cspaceRootSlot cnSrc.cnode
        cnSrc.slot TCB.cspaceRootRights u with r1 | r1
    · exact .inl (r2.trans r1)
    · right; unfold offCoreFree at r1 ⊢; rw [hs2, hm2, hs1, hm1]; exact r1
  · right; unfold offCoreFree at r2 ⊢; rw [hs2, hm2]; exact r2

/-- WS-ZA ZA6.25: **the space change through the zombie delete writes the saved
registers of no thread another core holds**: the zombie passes are a delete
chain (`finaliseCensusChain`), and the plain space change writes only threads no
core holds after it (`copyThreadSpaces_savedRegs`). -/
theorem copyThreadSpacesZombie_savedRegsKeptOffCore {e ec : CoreId} {st st' : SystemState}
    {vtid : SeLe4n.ValidThreadId} {cnSrc vrSrc : CSpaceAddr} (B : FinaliseCensusBase st)
    (hB : finalisingDeleteBundle st) (h : copyThreadSpacesZombie ec st vtid cnSrc vrSrc = .ok st') :
    savedRegsKeptOffCore e st st' := by
  rcases copyThreadSpacesZombie_cases h with h1 | ⟨n, s, hR, rfl | h2⟩
  · intro d hd t ht
    rcases copyThreadSpaces_savedRegs (e := e) B.objInv h1 t with w | w
    · exact w
    · exfalso
      rcases ht with x | x
      · exact (w d hd).1 x
      · exact (w d hd).2 x
  · exact (hR.chain.closed (finaliseCensusChain e st) (fun _ _ _ hQ hD => hQ.delete B hD)
      (fun d _ hQ => hQ.finalise B d) (.start hB)).2.2
  · have Q := hR.chain.closed (finaliseCensusChain e st) (fun _ _ _ hQ hD => hQ.delete B hD)
      (fun d _ hQ => hQ.finalise B d) (.start hB)
    have C := (copyThreadSpaces_stepCovers e ec s st' vtid cnSrc vrSrc Q.1.2.1.2.1 Q.1.2.1.1 Q.1.2.2 h2).1
    exact savedRegsKeptOffCore_extend Q.2.2 C (stepCovers_trans Q.1.1 C)
      (fun t => (copyThreadSpaces_savedRegs (e := e) Q.1.2.1.2.1 h2 t).imp_right .inr)

/-! ### Over the dispatch -/

/-- WS-ZA ZA6.25: **the capability-only dispatch writes the saved registers of
no thread another core holds**, every arm.  The final delete and revoke write
only threads free at the entry's start or released from every core
(`cspaceDeleteSlotZombie_savedRegsKeptOffCore`,
`cspaceRevokeCdtFinalising_savedRegsKeptOffCore`), and so does the space change
(`copyThreadSpacesZombie_savedRegsKeptOffCore`); the resume's fault retire
writes a thread no core runs or holds (`tcbResume_savedRegsKeptOffCore`); the
unbind, the Consumed invocation, the suspend and the priority arms write the
caller, a blocked victim or their scheduling point's outgoing thread, each free
at the entry's start (`*_savedRegsWrittenFree`, read through
`savedRegsWrittenFree.census`); the service query writes the caller alone; and
every other arm keeps every saved context (`savedRegsKept`,
`*_savedRegsKeptExcept`).  The coverage relation's frames are the step's
(`stepCovers.currentKept`, `stepCovers.residentKept`). -/
theorem dispatchCapabilityOnly_savedRegsKeptOffCore {decoded : SyscallDecodeResult}
    {cap : Capability} {tid : SeLe4n.ThreadId} {ec : CoreId} {k : Kernel Unit}
    {st st' : SystemState} (P : SyscallArmPremises st ec tid) (hRT : st.residentsHaveTcbs)
    (hN : st.currentNotResidentElsewhere) (hB : finalisingDeleteBundle st)
    (hBNR : st.blockedNotResident) (hYA : st.yieldLinksAgree) (hYN : st.yieldLinkedNotResident)
    (hK : dispatchCapabilityOnly decoded cap tid ec = some k) (h : k st = .ok ((), st'))
    (hCK : currentKeptOffCore ec st st') (hRK : residentKeptOffCore ec st st') :
    savedRegsKeptOffCore ec st st' := by
  have hInv := P.objInv
  have hU := currentsUnique_of_dequeuedUnique P.dequeued
  have B : FinaliseCensusBase st :=
    ⟨P.objInv, P.refined, P.toEntryPremises.blocked, hBNR, hYA, hYN⟩
  have hF : savedRegsKept st st' → savedRegsKeptOffCore ec st st' := fun hS =>
    savedRegsKeptOffCore_of_savedRegsKept hS P.dequeued hRT hCK hRK
  have hW : savedRegsWrittenFree ec st st st' → savedRegsKeptOffCore ec st st' := fun w =>
    w.census hCK hRK
  have hX : savedRegsKeptExcept (fun _ => False) st st' → savedRegsKeptOffCore ec st st' := fun x =>
    hW (.of_kept x (fun _ h => h.elim))
  clear hCK hRK
  unfold dispatchCapabilityOnly at hK
  cases hId : decoded.syscallId <;> rw [hId] at hK <;> simp only [Option.some.injEq,
    reduceCtorEq] at hK
  all_goals subst hK
  all_goals cases hT : cap.target <;> rw [hT] at h <;> dsimp only at h
  all_goals first | (cases h; done) | skip
  all_goals (repeat' split at h)
  all_goals first | (cases h; done) | skip
  all_goals first
    | exact cspaceDeleteSlotZombie_savedRegsKeptOffCore B hB h
    | exact cspaceRevokeCdtFinalising_savedRegsKeptOffCore B hB h
    | exact hF (mintReplyCapWithCdt_savedRegsKept hInv h)
    | exact hF (untypedResetFromCap_savedRegsKept hInv h)
    | exact hF (untypedRetypeFromCap_savedRegsKept hInv h)
    | exact hF (vspaceMapFromFrameCap_savedRegsKept hInv h)
    | exact hF (vspaceUnmapPageWithShootdownAndIcacheBroadcast_savedRegsKept hInv h)
    | exact hF (vspaceUnifyInstructionPage_savedRegsKept h)
    | exact hF (pageTableMap_savedRegsKept hInv h)
    | exact hF (pageTableUnmap_savedRegsKept hInv h)
    | exact hF (revokeServiceByRecordedRegistration_savedRegsKept hInv h)
    | exact hX (schedControlConfigure_savedRegsKeptExcept hInv h)
    | exact hX (schedContextBind_savedRegsKeptExcept hInv h)
    | exact hX (bindNotification_savedRegsKeptExcept hInv h)
    | (cases h; rename_i hS
       first
        | (rw [lookupServiceByRecordedRegistration_preserves_state _ _ _ _ hS]
           exact writeReturnFrameToTcb_savedRegsKeptOffCore _ hInv P.current hU hN)
        | exact hW (schedContextUnbindOnCore_savedRegsWrittenFree hInv hU hN hS)
        | exact hW (schedContextConsumedOnCore_savedRegsWrittenFree hInv hU hN hS)
        | exact hX (unbindNotification_savedRegsKeptExcept hInv hS)
        | exact hW (suspendThreadOnCore_savedRegsWrittenFree hInv hU hN P.toEntryPremises.blocked
            hBNR hS)
        | exact tcbResume_savedRegsKeptOffCore hInv P.refined P.dequeued hN hS
        | exact hW (setPriorityOnCore_savedRegsWrittenFree hInv hU hN hS)
        | exact hW (setMCPriorityOnCore_savedRegsWrittenFree hInv hU hN hS)
        | exact hX (setThreadCpuAffinityWithMigration_savedRegsKeptExcept hInv hS)
        | exact hX (setIPCBufferOp_savedRegsKeptExcept hInv hS)
        | exact hX (setThreadFaultHandlerOp_savedRegsKeptExcept hInv hS)
        | exact copyThreadSpacesZombie_savedRegsKeptOffCore B hB hS)
