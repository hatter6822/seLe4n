/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Invariant.FinaliseWaiterCompletion
import SeLe4n.Kernel.IPC.Invariant.RunQueueAgreement.Capability

/-!
# What a thread's finalisation keeps of the thread

WS-ZA ZA5.4 part 26: what `finaliseThread_quiesces` reads along the thread
finalisation's steps.

* `tcbProjKept g s' s`: every thread keeps `g` of its TCB across a step, with
  its instances for each kind of write (`updateTcb`, `modifyObject`, the
  notification unbind, the endpoint cancel, the waiter frames).
* `runCodeBounded`: a thread's run-core code names a core or none.  Every write
  of it is a dequeue (zero) or an enqueue on a core; nothing else moves it.
* `finaliseCarried`: the finalisation's invariant, the run queues' agreement,
  `FinaliseFrameAny` and `runCodeBounded`, carried by every step class
  (`CancelAllFrame`'s), so it holds on every state between the steps.
* What each step does to the finalised thread: the notification unbind clears
  its binding code (`finaliseThreadUnbindNotification_self`); the cancel leaves
  it ready off every endpoint queue with its binding code and id kept
  (`finaliseThreadCancel_quiets`, over `TCB.cancelKey`); the suspend marks it
  `.Inactive` on no core (`finaliseThreadSuspend_quiets`); the context unbind
  clears its binding and nothing else (`finaliseThreadUnbindSchedContext_self`).
* `noWaiter_of_servers`: a step that keeps every thread's blocking server keeps
  a server waited on by nothing (`finaliseThreadSuspend_servers`).
* `readyThread_unlinked`: the invariant reads every other link off a ready
  thread nothing waits on.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open SeLe4n.Kernel.Concurrency (CoreId numCores)

-- ============================================================================
-- A projection of every thread kept
-- ============================================================================

/-- **Every thread keeps `g` of its TCB**, and holds a TCB exactly where it did.
`SystemState.RunCoresAgree` is the run-core code's instance. -/
def tcbProjKept {α : Type} (g : TCB → α) (s' s : SystemState) : Prop :=
  ∀ y : SeLe4n.ThreadId, (s'.getTcb? y).map g = (s.getTcb? y).map g

namespace tcbProjKept

variable {α : Type} {g : TCB → α}

theorem refl (s : SystemState) : tcbProjKept g s s := fun _ => rfl

theorem trans {a b c : SystemState} (h₂ : tcbProjKept g c b) (h₁ : tcbProjKept g b a) :
    tcbProjKept g c a := fun y => (h₂ y).trans (h₁ y)

theorem of_objects {s s' : SystemState} (h : s'.objects = s.objects) : tcbProjKept g s' s :=
  fun y => by unfold SystemState.getTcb?; rw [h]

/-- A TCB update keeping `g` keeps it of every thread. -/
theorem updateTcb (s : SystemState) (w : SeLe4n.ThreadId) {f : TCB → TCB}
    (hInv : s.objects.invExt) (hf : ∀ t, g (f t) = g t) : tcbProjKept g (s.updateTcb w f) s := by
  intro y
  by_cases h : w.toObjId = y.toObjId
  · cases SeLe4n.ThreadId.toObjId_injective w y h
    rw [SystemState.updateTcb_getTcb?_self s w f hInv]
    cases s.getTcb? w <;> simp [hf]
  · rw [SystemState.updateTcb_getTcb?_ne s w f hInv y h]

/-- An object update that leaves every TCB a TCB as it is, and makes no TCB of
another object, keeps every thread. -/
theorem modifyObject (s : SystemState) (k : SeLe4n.ObjId) {f : KernelObject → KernelObject}
    (hInv : s.objects.invExt) (hT : ∀ t, f (.tcb t) = .tcb t)
    (hN : ∀ o, (∀ t, o ≠ .tcb t) → ∀ t, f o ≠ .tcb t) : tcbProjKept g (s.modifyObject k f) s := by
  intro y
  have e : (s.modifyObject k f).getTcb? y = s.getTcb? y := by
    unfold SystemState.getTcb?
    rw [modifyObject_objects_getElem hInv]
    by_cases hk : k = y.toObjId
    · rw [if_pos hk]
      subst hk
      cases hO : s.objects[y.toObjId]? with
      | none => rfl
      | some o =>
        simp only [Option.map_some]
        by_cases ht : ∃ t, o = .tcb t
        · obtain ⟨t, rfl⟩ := ht; rw [hT]
        · have hno : ∀ t, o ≠ .tcb t := fun t e => ht ⟨t, e⟩
          have hfo := hN o hno
          cases hf : f o <;> cases o <;> first | exact (hno _ rfl).elim | exact (hfo _ hf).elim | rfl
    · rw [if_neg hk]
  rw [e]

/-- The unbind keeps every thread but its bound-notification code. -/
theorem storeUnbindNotification (s : SystemState) (t : SeLe4n.ThreadId) (n : SeLe4n.ObjId)
    (hInv : s.objects.invExt) (hg : ∀ u : TCB, g { u with boundNotificationCode := 0 } = g u) :
    tcbProjKept g (SeLe4n.Kernel.storeUnbindNotification s t n) s := by
  unfold SeLe4n.Kernel.storeUnbindNotification
  exact (modifyObject _ n (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv)
    (fun _ => rfl) (fun o ho t' => by
      cases o with
      | tcb w => exact (ho w rfl).elim
      | notification _ => intro hc; cases hc
      | _ => exact ho t')).trans
    (updateTcb s t hInv hg)

/-- **The endpoint cancel, split at its last two writes**: the queue removal's
neighbour and endpoint writes (which keep every thread but its queue links),
then the cancelled thread taken off the queue and made a cancelled waiter. -/
theorem storeEndpointBlockedCancelled_split (s : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (t : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) (hInv : s.objects.invExt)
    (hP : ∀ r u : TCB, g (queueUnlinkPredecessor r u) = g u)
    (hS : ∀ r u : TCB, g (queueUnlinkSuccessor r u) = g u) :
    ∃ X : SystemState, X.objects.invExt ∧ tcbProjKept g X s ∧
      SeLe4n.Kernel.storeEndpointBlockedCancelled s e q t ep tcb =
        (X.updateTcb t tcbOffQueue).updateTcb t cancelledEndpointWaiterTcb := by
  have hMod : ∀ (S : SystemState) (f : KernelObject → KernelObject), S.objects.invExt →
      (∀ u, f (.tcb u) = .tcb u) → (∀ o, (∀ u, o ≠ .tcb u) → ∀ u, f o ≠ .tcb u) →
      tcbProjKept g (S.modifyObject e f) S ∧ (S.modifyObject e f).objects.invExt :=
    fun S f hI hT hN => ⟨modifyObject S e hI hT hN, modifyObject_preserves_objects_invExt hI⟩
  have hEnd : ∀ (b : Bool) (h tl : Nat) (o : KernelObject), (∀ u, o ≠ .tcb u) →
      ∀ u, endsSetEndpoint b h tl o ≠ .tcb u := by
    intro b h tl o ho u
    cases o with
    | tcb w => exact (ho w rfl).elim
    | endpoint _ => intro hc; cases hc
    | _ => exact ho u
  have hHead : ∀ (b : Bool) (c : Nat) (o : KernelObject), (∀ u, o ≠ .tcb u) →
      ∀ u, headAdvancedEndpoint b c o ≠ .tcb u := by
    intro b c o ho u
    cases o with
    | tcb w => exact (ho w rfl).elim
    | endpoint _ => intro hc; cases hc
    | _ => exact ho u
  have fin : ∀ (S : SystemState) (b : Bool) (h tl : Nat), tcbProjKept g S s → S.objects.invExt →
      ∃ X : SystemState, X.objects.invExt ∧ tcbProjKept g X s ∧
        ((S.modifyObject e (endsSetEndpoint b h tl)).updateTcb t tcbOffQueue).updateTcb t
          cancelledEndpointWaiterTcb =
        (X.updateTcb t tcbOffQueue).updateTcb t cancelledEndpointWaiterTcb := by
    intro S b h tl k i
    obtain ⟨k3, i3⟩ := hMod S (endsSetEndpoint b h tl) i (fun _ => rfl) (hEnd b h tl)
    exact ⟨_, i3, k3.trans k, rfl⟩
  have h1 : tcbProjKept g (match tcb.queuePPrev with
      | some .endpointHead => s.modifyObject e (headAdvancedEndpoint q tcb.queueNextCode)
      | some (.tcbNext p) => s.updateTcb p (queueUnlinkPredecessor tcb)
      | none => s) s ∧ (match tcb.queuePPrev with
      | some .endpointHead => s.modifyObject e (headAdvancedEndpoint q tcb.queueNextCode)
      | some (.tcbNext p) => s.updateTcb p (queueUnlinkPredecessor tcb)
      | none => s).objects.invExt := by
    split
    · exact hMod s _ hInv (fun _ => rfl) (hHead q _)
    · exact ⟨updateTcb s _ hInv (hP tcb), SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv⟩
    · exact ⟨refl s, hInv⟩
  have h2 : ∀ S : SystemState, tcbProjKept g S s → S.objects.invExt →
      tcbProjKept g (match tcb.queueNext with
        | some n => S.updateTcb n (queueUnlinkSuccessor tcb)
        | none => S) s ∧ (match tcb.queueNext with
        | some n => S.updateTcb n (queueUnlinkSuccessor tcb)
        | none => S).objects.invExt := by
    intro S k i
    split
    · exact ⟨(updateTcb S _ i (hS tcb)).trans k, SystemState.updateTcb_preserves_objects_invExt _ _ _ i⟩
    · exact ⟨k, i⟩
  have h3 := h2 _ h1.1 h1.2
  exact fin _ q _ _ h3.1 h3.2

/-- The endpoint cancel keeps every thread but its queue links and the
cancelled thread's IPC fields. -/
theorem storeEndpointBlockedCancelled (s : SystemState) (e : SeLe4n.ObjId) (q : Bool)
    (t : SeLe4n.ThreadId) (ep : Endpoint) (tcb : TCB) (hInv : s.objects.invExt)
    (hP : ∀ r u : TCB, g (queueUnlinkPredecessor r u) = g u)
    (hS : ∀ r u : TCB, g (queueUnlinkSuccessor r u) = g u)
    (hO : ∀ u : TCB, g (tcbOffQueue u) = g u) (hC : ∀ u : TCB, g (cancelledEndpointWaiterTcb u) = g u) :
    tcbProjKept g (SeLe4n.Kernel.storeEndpointBlockedCancelled s e q t ep tcb) s := by
  obtain ⟨X, i, k, hEq⟩ := storeEndpointBlockedCancelled_split s e q t ep tcb hInv hP hS
  rw [hEq]
  exact (updateTcb _ t (SystemState.updateTcb_preserves_objects_invExt _ t tcbOffQueue i) hC).trans
    ((updateTcb _ t i hO).trans k)

/-- A kept projection is kept of a thread present on the earlier state. -/
theorem get {s s' : SystemState} (h : tcbProjKept g s' s) {y : SeLe4n.ThreadId} {t : TCB}
    (hY : s.getTcb? y = some t) : ∃ t', s'.getTcb? y = some t' ∧ g t' = g t := by
  have e := h y
  rw [hY] at e
  cases hs : s'.getTcb? y with
  | none => rw [hs] at e; cases e
  | some t' =>
    rw [hs] at e
    simp only [Option.map_some, Option.some.injEq] at e
    exact ⟨t', rfl, e⟩

/-- **A step keeps `g` of every thread** when it keeps `g` of every TCB it finds
and makes no TCB where there was none. -/
theorem of_fwd_bwd {s s' : SystemState}
    (hF : ∀ (k : SeLe4n.ObjId) (t0 : TCB), s.objects[k]? = some (.tcb t0) →
      ∃ t', s'.objects[k]? = some (.tcb t') ∧ g t' = g t0)
    (hB : ∀ (k : SeLe4n.ObjId) (t' : TCB), s'.objects[k]? = some (.tcb t') →
      ∃ t0, s.objects[k]? = some (.tcb t0)) : tcbProjKept g s' s := by
  intro y
  cases hs : s.getTcb? y with
  | some t =>
    obtain ⟨t', h', e⟩ := hF _ t ((SystemState.getTcb?_eq_some_iff _ _ _).mp hs)
    rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h']
    simp only [Option.map_some, e]
  | none =>
    cases hs' : s'.getTcb? y with
    | none => rfl
    | some t' =>
      obtain ⟨t0, h0⟩ := hB _ t' ((SystemState.getTcb?_eq_some_iff _ _ _).mp hs')
      rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h0] at hs; cases hs

/-- A step agreeing off the run-queue links keeps what they do not hold. -/
theorem of_agreeOffRunLinks {s s' : SystemState} (h : SystemState.objectsAgreeOffRunLinks s' s)
    (hg : ∀ u, g u.withoutRunLinks = g u) : tcbProjKept g s' s :=
  of_fwd_bwd (fun _ _ hk => by
      obtain ⟨t', h', e⟩ := h.get_tcb hk
      exact ⟨t', h', by rw [← hg t', e, hg]⟩)
    (fun _ _ hk => by obtain ⟨t0, h0, -⟩ := h.get_tcb' hk; exact ⟨t0, h0⟩)

/-- ...and one agreeing off the release-queue links keeps every thread. -/
theorem of_agreeOffReleaseLinks {s s' : SystemState}
    (h : SystemState.objectsAgreeOffReleaseLinks s' s) : tcbProjKept g s' s :=
  fun y => by rw [h.getTcb? y]

/-- ...and one agreeing off the reply-waiter links. -/
theorem of_agreeOffReplyLinks {s s' : SystemState}
    (h : SystemState.objectsAgreeOffReplyLinks s' s) (hg : ∀ u, g u.withoutReplyLinks = g u) :
    tcbProjKept g s' s :=
  of_fwd_bwd (fun _ _ hk => by
      obtain ⟨t', h', e⟩ := h.get_tcb hk
      exact ⟨t', h', by rw [← hg t', e, hg]⟩)
    (fun _ _ hk => by obtain ⟨t0, h0, -⟩ := h.get_tcb' hk; exact ⟨t0, h0⟩)

/-- A frame excluding no thread keeps whatever its key determines. -/
theorem of_waiterFrame {s s' : SystemState} (h : WaiterFrame s s' (fun _ => False))
    (hg : ∀ u v, TCB.waiterKeyEq u v → g u = g v) : tcbProjKept g s' s := by
  intro y
  cases hs : s.getTcb? y with
  | some t =>
    obtain ⟨t', h', k, -⟩ := h.fwd y t id hs
    rw [h']; simp only [Option.map_some, hg _ _ k]
  | none =>
    cases hs' : s'.getTcb? y with
    | none => rfl
    | some t' =>
      obtain ⟨t0, h0, -⟩ := h.bwd y t' id hs'
      rw [h0] at hs; cases hs

/-- **The cancelled caller's donation return keeps every thread but its binding
codes.** -/
theorem returnDonationToCancelledCaller (s : SystemState) (w : SeLe4n.ThreadId) (t : TCB)
    (hInv : s.objects.invExt)
    (hg : ∀ (u : TCB) (c o : Nat), g { u with scBindingScCode := c, scBindingOwnerCode := o } = g u) :
    tcbProjKept g (Lifecycle.Suspend.returnDonationToCancelledCaller s w t) s := by
  unfold Lifecycle.Suspend.returnDonationToCancelledCaller
  split
  · rename_i scId holder _ _ _
    split
    · rename_i st' hOk
      obtain ⟨n, -, hPop⟩ := returnDonatedSchedContextResolved_ok_decompose hOk
      refine of_fwd_bwd (fun k t0 hk => ?_) (fun k t' hk => ?_)
      · obtain ⟨t', h', c, o, e⟩ :=
          returnDonatedSchedContext_tcb_rewrite _ st' holder scId w hInv n hPop k t0 hk
        exact ⟨t', h', by rw [e, hg]⟩
      · obtain ⟨t0, h0, -⟩ :=
          returnDonatedSchedContext_tcb_rewrite_backward _ st' holder scId w n hInv hPop k t' hk
        exact ⟨t0, h0⟩
    · exact refl _
  · exact refl _

/-- **A consume of `w`'s reply link keeps every thread but its reply code.** -/
theorem consumeReplyLink (s : SystemState) (w : SeLe4n.ThreadId) (t : TCB)
    (hInv : s.objects.invExt) (hg : ∀ u : TCB, g { u with replyObjectCode := 0 } = g u) :
    tcbProjKept g (Lifecycle.Suspend.consumeReplyLink s w t) s := by
  unfold Lifecycle.Suspend.consumeReplyLink
  split
  · exact refl _
  · rename_i rid _
    have hStep := SystemState.consumeCallerReply_eq_link s w rid
    refine of_fwd_bwd (fun k t0 hk => ?_) (fun k t' hk => ?_)
    · by_cases hkw : k = w.toObjId
      · subst hkw
        exact ⟨_, SystemState.consumeCallerReply_tcb_caller s _ w rid hInv hStep t0 hk, hg t0⟩
      · exact ⟨t0, SystemState.consumeCallerReply_tcb_other s _ w rid hInv hStep k t0 hkw hk, rfl⟩
    · obtain ⟨t0, h0, -⟩ := SystemState.consumeCallerReply_tcb_forward s _ w rid hInv hStep k t' hk
      exact ⟨t0, h0⟩

/-- **The last write of `x`'s TCB** names what is stored there. -/
theorem _root_.SeLe4n.Model.SystemState.updateTcb_getTcb?_self_some {S : SystemState}
    {x : SeLe4n.ThreadId} {F : TCB → TCB} (hInv : S.objects.invExt) {w : TCB}
    (h : (S.updateTcb x F).getTcb? x = some w) : ∃ u, S.getTcb? x = some u ∧ w = F u := by
  rw [SystemState.updateTcb_getTcb?_self S x F hInv] at h
  cases hS : S.getTcb? x with
  | none => rw [hS] at h; cases h
  | some u => rw [hS] at h; cases h; exact ⟨u, rfl, rfl⟩

end tcbProjKept

-- ============================================================================
-- A run-core code names a core or none
-- ============================================================================

/-- **The run-core code of `y` names a core or none**: zero (on no queue) or a
core's index plus one. -/
def runCodeBounded (s : SystemState) (y : SeLe4n.ThreadId) : Prop :=
  ∀ t, s.getTcb? y = some t → t.runCoreCode ≤ numCores

namespace runCodeBounded

/-- A step keeping every run-core code keeps the bound. -/
theorem of_runCoresAgree {s s' : SystemState} {y : SeLe4n.ThreadId}
    (h : SystemState.RunCoresAgree s' s) (hb : runCodeBounded s y) : runCodeBounded s' y := by
  intro t' ht'
  have e := h y
  rw [ht'] at e
  cases hs : s.getTcb? y with
  | none => rw [hs] at e; cases e
  | some t =>
    rw [hs] at e
    simp only [Option.map_some, Option.some.injEq] at e
    rw [e]; exact hb t hs

/-- A thread queued on a core has a bounded code. -/
theorem of_queuedOn {s : SystemState} {y : SeLe4n.ThreadId} {c : CoreId}
    (h : s.queuedOn c y = true) : runCodeBounded s y := by
  intro t ht
  unfold SystemState.queuedOn at h
  rw [ht] at h
  simp only [beq_iff_eq] at h
  rw [h]; exact c.isLt

/-- A bounded code of a thread queued on no core is zero. -/
theorem eq_zero {s : SystemState} {y : SeLe4n.ThreadId} {t : TCB} (hb : runCodeBounded s y)
    (ht : s.getTcb? y = some t) (hq : ∀ c : CoreId, s.queuedOn c y = false) :
    t.runCoreCode = 0 := by
  have hle := hb t ht
  cases hc : t.runCoreCode with
  | zero => rfl
  | succ k =>
    have hk : k < numCores := by omega
    have := hq ⟨k, hk⟩
    unfold SystemState.queuedOn at this
    rw [ht] at this
    simp [hc] at this

/-- **A dequeue keeps every run-core code bounded**: the dequeued thread's code
goes to zero or stays, and no other thread's moves. -/
theorem runRemoveOnCore (s : SystemState) (c : CoreId) (w y : SeLe4n.ThreadId)
    (hb : runCodeBounded s y) : runCodeBounded (s.runRemoveOnCore c w) y := by
  by_cases hy : y = w
  · subst hy
    have hO := SystemState.runRemoveOnCore_objects s c y
    split at hO
    · intro t' ht'
      rw [SystemState.getTcb?_frame hO] at ht'
      unfold SystemState.runUnlinkLinks at ht'
      rw [SystemState.mapTcbInPlace_getTcb?_self] at ht'
      cases hm : (((((s.updateTcbAtCode (s.runLinkOn c y).prev
          (fun z => { z with runNextCode := (s.runLinkOn c y).next })).updateTcbAtCode
          (s.runLinkOn c y).next (fun z => { z with runPrevCode := (s.runLinkOn c y).prev })).updateTcbAtCode
          (s.runLinkOn c y).bucketPrev
          (fun z => { z with runBucketNextCode := (s.runLinkOn c y).bucketNext })).updateTcbAtCode
          (s.runLinkOn c y).bucketNext
          (fun z => { z with runBucketPrevCode := (s.runLinkOn c y).bucketPrev })).getTcb? y) with
      | none => rw [hm] at ht'; cases ht'
      | some tm =>
        rw [hm] at ht'
        simp only [Option.map_some, Option.some.injEq] at ht'
        subst ht'
        show 0 ≤ numCores
        exact Nat.zero_le _
    · exact of_runCoresAgree (SystemState.RunCoresAgree.of_objects hO) hb
  · intro t' ht'
    have e := SystemState.runRemoveOnCore_runCoreCode_ne s c w y hy
    rw [ht'] at e
    cases hs : s.getTcb? y with
    | none => rw [hs] at e; cases e
    | some t =>
      rw [hs] at e
      simp only [Option.map_some, Option.some.injEq] at e
      rw [e]; exact hb t hs

/-- ...and so does a deschedule wherever the thread is placed. -/
theorem descheduleAtPlacement (s : SystemState) (w y : SeLe4n.ThreadId)
    (hb : runCodeBounded s y) : runCodeBounded (SeLe4n.Kernel.descheduleAtPlacement s w) y := by
  unfold SeLe4n.Kernel.descheduleAtPlacement descheduleAt
  split
  · rename_i c _
    intro t' ht'
    exact runRemoveOnCore s c w y hb t' ht'
  · exact hb

/-- **A requeue keeps every run-core code bounded**: the requeued thread is left
queued on the core, and no other thread's code moves. -/
theorem runRequeueOnCore (S : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) (y : SeLe4n.ThreadId) (hb : runCodeBounded S y) :
    runCodeBounded (S.runRequeueOnCore c t p) y := by
  intro t' ht'
  by_cases hyt : y = t
  · subst hyt
    have hS : (S.getTcb? y).isSome = true := by
      have h1 := SystemState.runEnqueueAdmitted_getTcb?_isSome (S.runRemoveOnCore c y) c y y p
      have h2 := SystemState.runRemoveOnCore_getTcb?_isSome S c y y
      have h3 : (S.runRequeueOnCore c y p).getTcb? y =
          ((S.runRemoveOnCore c y).runEnqueueAdmitted c y p).getTcb? y := by
        unfold SystemState.getTcb?; rw [SystemState.runRequeueOnCore_objects]
      rw [← h2, ← h1, ← h3, ht']; rfl
    have hq := SystemState.runRequeueOnCore_queuedOn S c y p c y
    rw [if_pos rfl, hS] at hq
    simp only [decide_true, Bool.and_self] at hq
    exact of_queuedOn hq t' ht'
  · have hM := SystemState.runRequeueOnCore_runCoreCode_ne S c t y p hyt
    rw [ht'] at hM
    cases h1 : S.getTcb? y with
    | none => rw [h1] at hM; cases hM
    | some t1 =>
      rw [h1] at hM
      simp only [Option.map_some, Option.some.injEq] at hM
      rw [hM]; exact hb t1 h1

/-- **A boost keeps every run-core code bounded**: its write keeps the holder's
code, and its re-key leaves the holder queued on the core it was on. -/
theorem updatePipBoostOnCore (s : SystemState) (c : CoreId) (tid y : SeLe4n.ThreadId)
    (hInv : s.objects.invExt) (hb : runCodeBounded s y) :
    runCodeBounded (PriorityInheritance.updatePipBoostOnCore s c tid) y := by
  have hMark : ∀ (S : SystemState) k, runCodeBounded S y → runCodeBounded (markKeyChangeFor S tid k) y :=
    fun S k h t ht => h t (by unfold SystemState.getTcb? at ht ⊢; rwa [markKeyChangeFor_objects] at ht)
  cases hTid : s.getTcb? tid with
  | none =>
    unfold PriorityInheritance.updatePipBoostOnCore
    rw [SystemState.getTcbWitnessed?_eq_none hTid]
    exact hb
  | some tcb =>
    have hRw : ∀ (new : TCB) (hA : s.rewriteAdmissible tid.toObjId (.tcb new)),
        new.runCoreCode = tcb.runCoreCode →
        runCodeBounded (s.rewriteObject tid.toObjId (.tcb new) hA) y := by
      intro new hA hNew t' ht'
      by_cases hy : tid.toObjId = y.toObjId
      · have hyt : y = tid :=
          Classical.byContradiction fun hne => threadId_toObjId_ne hne hy
        subst hyt
        have hSelf := SystemState.rewriteObject_objects_self _ _ _ hA hInv
        have e : (s.rewriteObject y.toObjId (.tcb new) hA).getTcb? y = some new :=
          (SystemState.getTcb?_eq_some_iff _ _ _).mpr hSelf
        rw [e] at ht'; cases ht'
        rw [hNew]; exact hb tcb hTid
      · rw [SystemState.rewriteObject_getTcb?_ne _ _ _ hA hInv y hy] at ht'
        exact hb t' ht'
    unfold PriorityInheritance.updatePipBoostOnCore
    simp only [SystemState.getTcbWitnessed?_eq_some hTid]
    split
    · exact hb
    · split
      · split
        · exact hMark _ _ (runRequeueOnCore _ c tid _ y (hRw _ _ rfl))
        · exact hMark _ _ (hRw _ _ rfl)
      · exact hMark _ _ (hRw _ _ rfl)

/-- ...and so does the whole chain walk, by induction on the fuel. -/
theorem propagate (ec : CoreId) :
    ∀ (fuel : Nat) (s : SystemState) (tid y : SeLe4n.ThreadId), s.objects.invExt →
      runCodeBounded s y →
      runCodeBounded (PriorityInheritance.propagatePipChainCrossCore s tid ec fuel).1 y
  | 0, _, _, _, _, hb => hb
  | n + 1, s, tid, y, hInv, hb => by
    rw [PriorityInheritance.propagatePipChainCrossCore_step]
    have hB := PriorityInheritance.pipBoostWithWake_preserves_objects_invExt s tid ec hInv
    have h1 := updatePipBoostOnCore s (determineTargetCore s tid) tid y hInv hb
    simp only
    split
    · exact propagate ec n _ _ y hB h1
    · exact h1

end runCodeBounded

-- ============================================================================
-- What every step of a thread's finalisation carries
-- ============================================================================

/-- **What every step of a thread's finalisation keeps**, from the state `st` it
started on: the finalisation's invariant, a kernel entry's worth of run-queue
steps, a kind-keeping write, and the run-core code of `y` bounded. -/
def finaliseCarried (st : SystemState) (y : SeLe4n.ThreadId) (s : SystemState) : Prop :=
  finaliseStepInvariant s ∧ SystemState.RunQueueEntryStage st s ∧ FinaliseFrameAny st s ∧
    runCodeBounded s y

namespace finaliseCarried

variable (st : SystemState) (y : SeLe4n.ThreadId)

theorem start (hI : finaliseStepInvariant st) (hB : runCodeBounded st y) :
    finaliseCarried st y st :=
  ⟨hI, ⟨SystemState.RunQueueLinkStage.refl st, fun _ _ _ d => d⟩, .refl hI.2.1, hB⟩

theorem unbindStep : FinaliseUnbindStep (finaliseCarried st y) :=
  fun n s ntfn t ⟨hI, hR, hF, hB⟩ hN hBt hCode hIn =>
    ⟨(finaliseStepInvariant.unbind hI hN hCode hIn).1,
      finaliseUnbindStep_runQueueEntryStage st n s ntfn t hR hN hBt hCode hIn,
      FinaliseFrameAny.unbindStep st n s ntfn t hF hN hBt hCode hIn,
      runCodeBounded.of_runCoresAgree
        (tcbProjKept.storeUnbindNotification s t n hI.2.1 (fun _ => rfl)) hB⟩

theorem notificationCancelStep : FinaliseNotificationCancelStep (finaliseCarried st y) :=
  fun s n t tcb ntfn ⟨hI, hR, hF, hB⟩ hT hIpc hN hC =>
    ⟨(finaliseStepInvariant.cancel hI hT hIpc hN hC).1,
      finaliseNotificationCancelStep_runQueueEntryStage st s n t tcb ntfn hR hT hIpc hN hC,
      FinaliseFrameAny.notificationCancelStep st s n t tcb ntfn hF hT hIpc hN hC,
      runCodeBounded.of_runCoresAgree (cancelIpcBlocking_runCoresAgree s t tcb hI.2.1) hB⟩

theorem endpointCancelStep : FinaliseEndpointCancelStep (finaliseCarried st y) :=
  fun s e q t ep tcb ⟨hI, hR, hF, hB⟩ hT hE hC =>
    ⟨(finaliseStepInvariant.endpointBlockedCancel hI hT hE hC).1,
      finaliseEndpointCancelStep_runQueueEntryStage st s e q t ep tcb hR hT hE hC,
      FinaliseFrameAny.endpointCancelStep st s e q t ep tcb hF hT hE hC,
      runCodeBounded.of_runCoresAgree
        (tcbProjKept.storeEndpointBlockedCancelled s e q t ep tcb hI.2.1 (fun _ _ => rfl)
          (fun _ _ => rfl) (fun _ => rfl) (fun _ => rfl)) hB⟩

theorem suspendStep : FinaliseSuspendStep (finaliseCarried st y) :=
  fun s t tcb ⟨hI, hR, hF, hB⟩ hT hS hO hIn hId =>
    ⟨(finaliseStepInvariant.suspend hI hT hS hO hIn hId).1,
      finaliseSuspendStep_runQueueEntryStage st s t tcb hR hT hS hO hIn hId,
      FinaliseFrameAny.suspendStep st s t tcb hF hT hS hO hIn hId,
      runCodeBounded.of_runCoresAgree
        (tcbProjKept.updateTcb _ t (descheduleAtPlacement_preserves_objects_invExt s t hI.2.1)
          (fun _ => rfl)) (runCodeBounded.descheduleAtPlacement s t y hB)⟩

theorem releaseStep : FinaliseReleaseStep (finaliseCarried st y) :=
  fun s t ⟨hI, hR, hF, hB⟩ =>
    ⟨(finaliseStepInvariant.releaseCores t hI).1,
      finaliseReleaseStep_runQueueEntryStage st s t hR,
      FinaliseFrameAny.releaseStep st s t hF,
      runCodeBounded.of_runCoresAgree
        (SystemState.RunCoresAgree.of_objects (finaliseThreadReleaseCores_objects s t)) hB⟩

theorem scReleaseStep : FinaliseScReleaseStep (finaliseCarried st y) :=
  fun s s' t tcb sc x ⟨hI, hR, hF, hB⟩ hT hS hSc hBd hOk =>
    ⟨(finaliseStepInvariant.release hI hT hS hSc hBd hOk).1,
      finaliseScReleaseStep_runQueueEntryStage st s s' t tcb sc x hR hT hS hSc hBd hOk,
      FinaliseFrameAny.scReleaseStep st s s' t tcb sc x hF hT hS hSc hBd hOk,
      runCodeBounded.of_runCoresAgree (cancelBoundDonationOnCore_runCoresAgree hI.2.1 hOk) hB⟩

/-- WS-ZA ZA6.6: the yield steps — the suspend's cancel and the unbind's
completion — carry it: each keeps the invariant (`finaliseStepInvariant.yieldStep`),
is a run-queue stage, a finalisation frame, and keeps every run-core code. -/
theorem yieldStep : FinaliseYieldStep (finaliseCarried st y) :=
  ⟨fun s t ⟨hI, hR, hF, hB⟩ =>
    ⟨(hI.yieldStep (cancelYieldTo_preserves_ipcInvariantFull s t hI.2.1 hI.1)
        (ReachFieldFrame.cancelYieldTo s t hI.2.1) (FinaliseFrame.cancelYieldTo s t hI.2.1)).1,
      hR.trans (SystemState.cancelYieldTo_runQueueStage s t).entry,
      (FinaliseFrameAny.yieldStep st).cancel s t hF,
      runCodeBounded.of_runCoresAgree
        (SystemState.cancelYieldTo_objectsAgreeOffYield s t hI.2.1).runCoresAgree hB⟩,
   fun s c ⟨hI, hR, hF, hB⟩ =>
    ⟨(hI.yieldStep (completeYieldFrom_preserves_ipcInvariantFull s c hI.2.1 hI.1)
        (ReachFieldFrame.completeYieldFrom s c hI.2.1)
        (FinaliseFrame.completeYieldFrom s c hI.2.1)).1,
      hR.trans (SystemState.completeYieldFrom_runQueueStage s c).entry,
      (FinaliseFrameAny.yieldStep st).complete s c hF,
      runCodeBounded.of_runCoresAgree
        (SystemState.completeYieldFrom_objectsAgreeOffYield s c hI.2.1).runCoresAgree hB⟩⟩

theorem replyStep : FinaliseReplyStep (finaliseCarried st y) := by
  intro s x r c t ⟨hI, hR, hF, hB⟩ hX hC hT hG
  refine ⟨(hI.reply hX hC hT hG).1, finaliseReplyStep_runQueueEntryStage st s x r c t hR hX hC hT hG,
    FinaliseFrameAny.replyStep st s x r c t hF hX hC hT hG, ?_⟩
  have hM : runCodeBounded (cancelIpcBlockingMigrated c t s) y :=
    runCodeBounded.of_runCoresAgree (SystemState.RunCoresAgree.trans
      (fun y => by rw [(cancelIpcBlockingMigrated_agree c t s).getTcb? y])
      (cancelIpcBlocking_runCoresAgree s c t hI.2.1)) hB
  have hMI : (cancelIpcBlockingMigrated c t s).objects.invExt := by
    exact cancelIpcBlockingMigrated_objects_invExt c t s
      (Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt s c t hI.2.1)
  have hD : runCodeBounded (cancelIpcBlockingReclaimed c t s) y ∧
      (cancelIpcBlockingReclaimed c t s).objects.invExt := by
    unfold cancelIpcBlockingReclaimed descheduleUnboundHolder
    split
    · exact ⟨hM, hMI⟩
    · exact ⟨runCodeBounded.descheduleAtPlacement _ _ y hM,
        descheduleAtPlacement_preserves_objects_invExt _ _ hMI⟩
  unfold finaliseReplyRevert
  split
  · exact runCodeBounded.propagate _ _ _ _ y hD.2 hD.1
  · exact hD.1

end finaliseCarried

-- ============================================================================
-- What each step writes of the finalised thread
-- ============================================================================

/-- **An object update keeping every TCB keeps every thread's TCB.** -/
theorem getTcb?_modifyObject_of_keeps (s : SystemState) (k : SeLe4n.ObjId)
    {f : KernelObject → KernelObject} (hInv : s.objects.invExt) (hT : ∀ t, f (.tcb t) = .tcb t)
    (hN : ∀ o, (∀ t, o ≠ .tcb t) → ∀ t, f o ≠ .tcb t) (y : SeLe4n.ThreadId) :
    (s.modifyObject k f).getTcb? y = s.getTcb? y := by
  have h := tcbProjKept.modifyObject (g := id) s k hInv hT hN y
  simpa only [Option.map_id, id] using h

/-- **The notification unbind clears the thread's bound-notification code and
writes nothing else of it.** -/
theorem finaliseThreadUnbindNotification_self {s : SystemState} {x : SeLe4n.ThreadId} {tx : TCB}
    (hInv : s.objects.invExt) (hX : s.getTcb? x = some tx) :
    (finaliseThreadUnbindNotification s x).getTcb? x = some { tx with boundNotificationCode := 0 } := by
  have hc : boundNotificationCodeOf s x = tx.boundNotificationCode := by
    unfold boundNotificationCodeOf; rw [hX]
  unfold finaliseThreadUnbindNotification
  dsimp only
  rw [hc]
  by_cases h0 : tx.boundNotificationCode = 0
  · rw [if_pos (by rw [h0]; rfl), hX]
    cases tx; simp only at h0; subst h0; rfl
  · rw [if_neg (by simpa only [beq_iff_eq] using h0)]
    unfold storeUnbindNotification
    rw [getTcb?_modifyObject_of_keeps _ _ (SystemState.updateTcb_preserves_objects_invExt _ _ _ hInv)
      (fun _ => rfl) (fun o ho t' => by
        cases o with
        | tcb w => exact (ho w rfl).elim
        | notification _ => intro hc; cases hc
        | _ => exact ho t'),
      SystemState.updateTcb_getTcb?_self s x _ hInv, hX]
    rfl

-- ============================================================================
-- The cancel quiets the finalised thread
-- ============================================================================

/-- **A thread's bound-notification code and id**, the two fields no step of the
finalisation after the notification unbind writes. -/
def _root_.SeLe4n.Model.TCB.bindKey (t : TCB) : Nat × SeLe4n.ThreadId := (t.boundNotificationCode, t.tid)

/-- **What the finalisation's cancel leaves of a thread**, compared: its two IPC
codes, its endpoint-queue links, its bound-notification code and its id. -/
def _root_.SeLe4n.Model.TCB.cancelKey (t : TCB) : Nat × Nat × Nat × Nat × Nat × Nat × SeLe4n.ThreadId :=
  (t.ipcObjectCode, t.ipcStateCode, t.queueNextCode, t.queuePrevCode, t.queuePPrevCode,
    t.boundNotificationCode, t.tid)

/-- **The key of a thread the cancel has quieted**: ready, linked into no
endpoint queue, with the bound-notification code and id `b` names. -/
def _root_.SeLe4n.Model.TCB.quietKey (b : Nat × SeLe4n.ThreadId) : Nat × Nat × Nat × Nat × Nat × Nat × SeLe4n.ThreadId :=
  (0, 0, 0, 0, 0, b.1, b.2)

/-- **The notification cancel, split at its last write**: the notification, the
waiter's links and its neighbours' links (which keep every thread's
bound-notification code and id), then the waiter restored. -/
theorem storeNotificationBlockedCancelled_split (s : SystemState) (n : SeLe4n.ObjId)
    (t : SeLe4n.ThreadId) (isHead : Bool) (prev next : Option SeLe4n.ThreadId)
    (hInv : s.objects.invExt) :
    ∃ Y : SystemState, Y.objects.invExt ∧ tcbProjKept TCB.bindKey Y s ∧
      storeNotificationBlockedCancelled s n t isHead prev next =
        Lifecycle.Suspend.restoreToReadyCancelled Y t := by
  have hM : (s.modifyObject n (cancelledNotificationObject isHead prev next)).objects.invExt :=
    modifyObject_preserves_objects_invExt hInv
  have kM : tcbProjKept TCB.bindKey (s.modifyObject n (cancelledNotificationObject isHead prev next)) s :=
    tcbProjKept.modifyObject s n hInv (fun _ => rfl) (fun o ho u => by
      cases o with
      | tcb w => exact (ho w rfl).elim
      | notification _ => intro hc; cases hc
      | _ => exact ho u)
  unfold storeNotificationBlockedCancelled
  generalize s.modifyObject n (cancelledNotificationObject isHead prev next) = S0 at hM kM ⊢
  have hC : (clearNtfnLinks S0 t).objects.invExt :=
    SystemState.updateTcb_preserves_objects_invExt _ _ _ hM
  have kC : tcbProjKept TCB.bindKey (clearNtfnLinks S0 t) s := by
    unfold clearNtfnLinks
    refine (tcbProjKept.updateTcb S0 t hM ?_).trans kM
    intro _; rfl
  have up : ∀ (S : SystemState) (w : SeLe4n.ThreadId) (f : TCB → TCB),
      (∀ u, TCB.bindKey (f u) = TCB.bindKey u) →
      S.objects.invExt ∧ tcbProjKept TCB.bindKey S s →
      (S.updateTcb w f).objects.invExt ∧ tcbProjKept TCB.bindKey (S.updateTcb w f) s :=
    fun S w f hf h => ⟨SystemState.updateTcb_preserves_objects_invExt _ _ _ h.1,
      (tcbProjKept.updateTcb S w h.1 hf).trans h.2⟩
  have hU : ∀ p' nx : Option SeLe4n.ThreadId,
      (unlinkNtfnNeighbours (clearNtfnLinks S0 t) p' nx).objects.invExt ∧
        tcbProjKept TCB.bindKey (unlinkNtfnNeighbours (clearNtfnLinks S0 t) p' nx) s := by
    intro p' nx
    cases p' <;> cases nx <;> unfold unlinkNtfnNeighbours <;> dsimp only
    · exact ⟨hC, kC⟩
    · exact up _ _ _ (fun _ => rfl) ⟨hC, kC⟩
    · exact up _ _ _ (fun _ => rfl) ⟨hC, kC⟩
    · exact up _ _ _ (fun _ => rfl) (up _ _ _ (fun _ => rfl) ⟨hC, kC⟩)
  exact ⟨_, (hU _ _).1, (hU _ _).2, rfl⟩

/-- **A cancelled endpoint waiter is quiet**: on a state the admission's
endpoint clause admits, the cancel leaves the thread ready and off every
endpoint queue, with its bound-notification code and id. -/
theorem cancelEndpointBlocked_quiets {s : SystemState} {e : SeLe4n.ObjId} {q : Bool}
    {x : SeLe4n.ThreadId} {t1 : TCB} (hInv : s.objects.invExt) (hX : s.getTcb? x = some t1)
    (hA : endpointCancelAdmitted s e q x t1 = true) :
    ∃ t2, (cancelEndpointBlocked s e q x t1).getTcb? x = some t2 ∧
      t2.cancelKey = TCB.quietKey t1.bindKey := by
  unfold endpointCancelAdmitted at hA
  have hM := ((Bool.and_eq_true _ _).mp hA).2
  unfold cancelEndpointBlocked
  cases hE : s.getEndpoint? e with
  | none => rw [hE] at hM; cases hM
  | some ep =>
    rw [hE] at hM
    dsimp only at hM ⊢
    rw [if_pos hM]
    obtain ⟨X, i, k, hEq⟩ := tcbProjKept.storeEndpointBlockedCancelled_split (g := TCB.bindKey)
      s e q x ep t1 hInv (fun _ _ => rfl) (fun _ _ => rfl)
    rw [hEq]
    obtain ⟨u, hu, ku⟩ := k.get hX
    have i1 := SystemState.updateTcb_preserves_objects_invExt X x tcbOffQueue i
    rw [SystemState.updateTcb_getTcb?_self _ x _ i1, SystemState.updateTcb_getTcb?_self _ x _ i, hu]
    refine ⟨_, rfl, ?_⟩
    show TCB.quietKey u.bindKey = _
    rw [ku]

/-- **A cancelled notification waiter is quiet.** -/
theorem cancelIpcBlocking_notification_quiets {s : SystemState} {n : SeLe4n.ObjId}
    {ntfn : Notification} {x : SeLe4n.ThreadId} {t1 : TCB} (hInv : s.objects.invExt)
    (hN : s.getNotification? n = some ntfn) (hX : s.getTcb? x = some t1)
    (hB : t1.ipcState = .blockedOnNotification n) :
    ∃ t2, (Lifecycle.Suspend.cancelIpcBlocking s x t1).getTcb? x = some t2 ∧
      t2.cancelKey = TCB.quietKey t1.bindKey := by
  rw [cancelIpcBlocking_notification_inPlace hN hX hB]
  obtain ⟨Y, i, k, hEq⟩ := storeNotificationBlockedCancelled_split s n x _ _ _ hInv
  rw [hEq]
  obtain ⟨u, hu, ku⟩ := k.get hX
  unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
  rw [SystemState.updateTcb_getTcb?_self _ x _ i, hu]
  refine ⟨_, rfl, ?_⟩
  show TCB.quietKey u.bindKey = _
  rw [ku]

/-- **A finalised thread's own reply cancel quiets it**: on a state the
admission's reply clause admits, the reply removal (the donation return, the
splice, the restore, the consume and the unlink, a head reply's reclaim, and the
boost revert) leaves it ready and off every endpoint queue, with its
bound-notification code and id. -/
theorem finaliseReplyCallerCancel_quiets {s : SystemState} {x : SeLe4n.ThreadId} {t1 : TCB}
    (hInv : s.objects.invExt) (hX : s.getTcb? x = some t1)
    (hA : replyCallerCancelAdmitted s x t1 = true) :
    ∃ t2, (finaliseReplyCallerCancel s x t1).getTcb? x = some t2 ∧
      t2.cancelKey = TCB.quietKey t1.bindKey := by
  unfold replyCallerCancelAdmitted at hA
  unfold finaliseReplyCallerCancel
  split at hA
  · rename_i r hR
    rw [if_pos hA]
    have hG := ((Bool.and_eq_true _ _).mp ((Bool.and_eq_true _ _).mp hA).1).2
    obtain ⟨-, -, -, -, ⟨ep, rt, hB⟩, -⟩ := replyCallerFinalisable_parts hG
    have hCI := Lifecycle.Suspend.cancelIpcBlocking_preserves_objects_invExt s x t1 hInv
    have hC : ∃ t2, (Lifecycle.Suspend.cancelIpcBlocking s x t1).getTcb? x = some t2 ∧
        t2.cancelKey = TCB.quietKey t1.bindKey := by
      rw [cancelIpcBlocking_replyArm_unfold s x t1 hB]
      have i1 := Lifecycle.Suspend.returnDonationToCancelledCaller_preserves_objects_invExt s x t1 hInv
      have k1 := tcbProjKept.returnDonationToCancelledCaller (g := TCB.bindKey) s x t1 hInv
        (fun _ _ _ => rfl)
      generalize Lifecycle.Suspend.returnDonationToCancelledCaller s x t1 = S1 at i1 k1
      have i2 := spliceThreadReplyFrameOut_preserves_objects_invExt S1 t1 i1
      have k2 : tcbProjKept TCB.bindKey (spliceThreadReplyFrameOut S1 t1) s := fun y => by
        rw [spliceThreadReplyFrameOut_getTcb?_eq S1 t1 i1 y]; exact k1 y
      generalize spliceThreadReplyFrameOut S1 t1 = S2 at i2 k2
      obtain ⟨u, hu, ku⟩ := k2.get hX
      have i3 := Lifecycle.Suspend.restoreToReadyCancelled_invExt S2 x i2
      obtain ⟨w3, hx3, e3⟩ : ∃ w3, (Lifecycle.Suspend.restoreToReadyCancelled S2 x).getTcb? x =
          some w3 ∧ w3.cancelKey = TCB.quietKey u.bindKey := by
        refine ⟨(u.restoredToReady).withReturnFrame Architecture.cancelledIpcFrame, ?_, rfl⟩
        unfold Lifecycle.Suspend.restoreToReadyCancelled Lifecycle.Suspend.restoreToReadyStaging
        rw [SystemState.updateTcb_getTcb?_self _ _ _ i2, hu]
        rfl
      generalize Lifecycle.Suspend.restoreToReadyCancelled S2 x = S3 at i3 hx3
      have k4 := tcbProjKept.consumeReplyLink (g := TCB.cancelKey) S3 x t1 i3 (fun _ => rfl)
      have k5 := tcbProjKept.of_agreeOffReplyLinks (g := TCB.cancelKey)
        (SystemState.unlinkReplyWaiterOpt_objectsAgreeOffReplyLinks
          (Lifecycle.Suspend.consumeReplyLink S3 x t1) x t1.blockingServer?) (fun _ => rfl)
      obtain ⟨w, hw, kw⟩ := (k5.trans k4).get hx3
      exact ⟨w, hw, by rw [kw, e3, ku]⟩
    obtain ⟨t2, h2, k2⟩ := hC
    have hF : tcbProjKept TCB.cancelKey (finaliseReplyCancel s r x t1)
          (Lifecycle.Suspend.cancelIpcBlocking s x t1) ∧
        (finaliseReplyCancel s r x t1).objects.invExt := by
      unfold finaliseReplyCancel
      split
      · refine ⟨(tcbProjKept.of_agreeOffRunLinks
          (cancelIpcBlockingReclaimed_objectsAgreeOffRunLinks x t1 s) (fun _ => rfl)).trans
          (tcbProjKept.of_agreeOffReleaseLinks (cancelIpcBlockingMigrated_agree x t1 s)), ?_⟩
        have hMI : (cancelIpcBlockingMigrated x t1 s).objects.invExt := by
          exact cancelIpcBlockingMigrated_objects_invExt x t1 s hCI
        unfold cancelIpcBlockingReclaimed descheduleUnboundHolder
        split
        · exact hMI
        · exact descheduleAtPlacement_preserves_objects_invExt _ _ hMI
      · exact ⟨tcbProjKept.refl _, hCI⟩
    have hRv := tcbProjKept.of_waiterFrame (g := TCB.cancelKey)
      (finaliseReplyRevert_frame _ hF.2 t1.blockingServer? (fun _ => False)).1
      (fun u v k => by
        obtain ⟨a1, a2, -, a4, a5, -, a7, a8, a9⟩ := k
        simp only [TCB.cancelKey, a1, a2, a4, a5, a7, a8, a9])
    obtain ⟨t3, h3, k3⟩ := (hRv.trans hF.1).get h2
    exact ⟨t3, h3, k3.trans k2⟩
  · cases hA

/-- **The finalisation's cancel quiets the thread** (WS-ZA ZA5.4 part 26): on a
state the admission's IPC clause admits (`threadIpcCancelAdmitted`), the thread
is left ready and linked into no endpoint queue, with its bound-notification code
and id, whatever it was blocked on. -/
theorem finaliseThreadCancel_quiets {s : SystemState} {x : SeLe4n.ThreadId} {t1 : TCB}
    (hInv : s.objects.invExt) (hX : s.getTcb? x = some t1)
    (hA : threadIpcCancelAdmitted s x t1 = true) :
    ∃ t2, (finaliseThreadCancel s x).getTcb? x = some t2 ∧
      t2.cancelKey = TCB.quietKey t1.bindKey := by
  unfold threadIpcCancelAdmitted at hA
  unfold finaliseThreadCancel
  rw [hX]
  dsimp only
  have hI : t1.ipcState = ThreadIpcState.ofCodes t1.ipcObjectCode t1.ipcStateCode := rfl
  rcases hc : t1.ipcStateCode with _ | _ | _ | _ | k
  · rw [hc] at hA
    cases ho : t1.ipcObjectCode with
    | zero =>
      have hR : t1.ipcState = .ready := by rw [hI, hc, ho]; rfl
      rw [hR]
      simp only [ho, beq_self_eq_true, if_true, Bool.and_eq_true, beq_iff_eq] at hA
      obtain ⟨⟨⟨⟨⟨hN, hP⟩, hPP⟩, -⟩, -⟩, -⟩ := hA
      exact ⟨t1, hX, by simp only [TCB.cancelKey, TCB.quietKey, TCB.bindKey, hc, ho, hN, hP, hPP]⟩
    | succ o =>
      have hR : t1.ipcState = .blockedOnSend ⟨o⟩ := by rw [hI, hc, ho]; rfl
      rw [hR]
      simp only [ho, Nat.add_sub_cancel, Nat.succ_ne_zero, beq_iff_eq, if_false] at hA
      exact cancelEndpointBlocked_quiets hInv hX hA
  · have hR : t1.ipcState = .blockedOnReceive ⟨t1.ipcObjectCode⟩ := by rw [hI, hc]; rfl
    rw [hR]
    rw [hc] at hA
    exact cancelEndpointBlocked_quiets hInv hX hA
  · have hR : t1.ipcState = .blockedOnNotification ⟨t1.ipcObjectCode⟩ := by rw [hI, hc]; rfl
    rw [hR]
    rw [hc] at hA
    dsimp only at hA ⊢
    cases hN : s.getNotification? ⟨t1.ipcObjectCode⟩ with
    | none => rw [hN] at hA; simp at hA
    | some ntfn =>
      rw [hN] at hA
      dsimp only at hA ⊢
      have hC := ((Bool.and_eq_true _ _).mp hA).2
      rw [if_pos hC]
      exact cancelIpcBlocking_notification_quiets hInv hN hX hR
  · have hR : t1.ipcState = .blockedOnCall ⟨t1.ipcObjectCode⟩ := by rw [hI, hc]; rfl
    rw [hR]
    rw [hc] at hA
    exact cancelEndpointBlocked_quiets hInv hX hA
  · have hR : t1.ipcState = .blockedOnReply ⟨t1.ipcObjectCode⟩ (SeLe4n.ThreadId.ofOptCode k) := by
      rw [hI, hc]; rfl
    rw [hR]
    rw [hc] at hA
    exact finaliseReplyCallerCancel_quiets hInv hX hA

-- ============================================================================
-- The suspend takes the quiet thread off the scheduler
-- ============================================================================

/-- **Between scheduling points a thread is placed on at most one core**: queued
on one core (its core code names one), or current on one, never both
(`currentDequeuedUnique`). -/
theorem currentDequeuedUnique.placedOnce {s : SystemState} (h : s.currentDequeuedUnique)
    (x : SeLe4n.ThreadId) (c c' : CoreId) :
    (s.queuedOn c x = true ∨ s.scheduler.currentOnCore c = some x) →
    (s.queuedOn c' x = true ∨ s.scheduler.currentOnCore c' = some x) → c = c' := by
  have hq : ∀ a b : CoreId, s.queuedOn a x = true → s.queuedOn b x = true → a = b := by
    intro a b ha hb
    unfold SystemState.queuedOn at ha hb
    cases hT : s.getTcb? x with
    | none => rw [hT] at ha; cases ha
    | some t =>
      rw [hT] at ha hb
      simp only [beq_iff_eq] at ha hb
      exact Fin.ext (by omega)
  rintro (h1 | h1) (h2 | h2)
  · exact hq c c' h1 h2
  · rw [h.not_queued h2 c] at h1; cases h1
  · rw [h.not_queued h1 c'] at h2; cases h2
  · exact ((h.current c x h1).2.1 c' h2).symm

/-- **The suspend leaves the quiet thread suspended and on no core**: marked
`.Inactive` with no message, its core code zero and current nowhere, its cancel
key kept.  When the guard fires the deschedule takes it off its one placement
(`descheduleAtPlacement_unplaced`); when it does not, the thread is already
suspended with no message, so it is neither queued nor current
(`currentDequeuedUnique`). -/
theorem finaliseThreadSuspend_quiets {s : SystemState} {x : SeLe4n.ThreadId} {t4 : TCB}
    (hInv : s.objects.invExt) (hCD : s.currentDequeuedUnique) (hB : runCodeBounded s x)
    (hX : s.getTcb? x = some t4) (hS : t4.ipcStateCode = 0) (hO : t4.ipcObjectCode = 0)
    (hId : isIdleThreadId x = false) :
    ∃ t5, (finaliseThreadSuspend s x).getTcb? x = some t5 ∧ t5.cancelKey = t4.cancelKey ∧
      t5.threadState = .Inactive ∧ t5.pendingMessage = none ∧ t5.runCoreCode = 0 ∧
      ∀ c, (finaliseThreadSuspend s x).scheduler.currentOnCore c ≠ some x := by
  unfold finaliseThreadSuspend
  rw [hX]
  dsimp only
  by_cases hG : (t4.threadState != .Inactive || t4.pendingMessage.isSome) = true
  · rw [if_pos (by simp only [hS, hO, hId, hG, beq_self_eq_true, Bool.and_self, Bool.not_false])]
    have hU := (placedCoreOf?_none_iff _ _).mp
      (descheduleAtPlacement_unplaced s x (currentDequeuedUnique.placedOnce hCD x))
    have iD := descheduleAtPlacement_preserves_objects_invExt s x hInv
    have kD := tcbProjKept.of_agreeOffRunLinks (g := TCB.cancelKey)
      (descheduleAtPlacement_objectsAgreeOffRunLinks s x) (fun _ => rfl)
    obtain ⟨u, hu, ku⟩ := kD.get hX
    have hz := runCodeBounded.eq_zero (runCodeBounded.descheduleAtPlacement s x x hB) hu
      (fun c => (hU c).1)
    refine ⟨finalisedSuspendMark u, ?_, ku, rfl, rfl, hz, fun c => ?_⟩
    · rw [SystemState.updateTcb_getTcb?_self _ _ _ iD, hu]; rfl
    · rw [SystemState.updateTcb_scheduler]; exact (hU c).2
  · rw [if_neg (by simp only [hG, Bool.and_false, Bool.false_and, Bool.false_eq_true,
      not_false_eq_true])]
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq, not_or, Decidable.not_not,
      Option.isSome_iff_ne_none] at hG
    obtain ⟨hIn, hM⟩ := hG
    have hNR : ¬ s.runnable x := by
      rintro ⟨t, ht, -, hR⟩
      rw [hX] at ht; cases ht; exact hR hIn
    have hQ : ∀ c : CoreId, s.queuedOn c x = false := fun c => by
      cases hq : s.queuedOn c x
      · rfl
      · exact absurd (hCD.queuedRunnable c x hq) hNR
    refine ⟨t4, hX, rfl, hIn, hM, runCodeBounded.eq_zero hB hX hQ, fun c hc => ?_⟩
    exact hNR (hCD.runnable hc)

-- ============================================================================
-- What the invariant says of a ready thread nothing waits on
-- ============================================================================

/-- **A ready thread nothing waits on holds no link the invariant ties to a
blocked state**: linked into no notification queue
(`notificationWaiterConsistent`), into no reply-waiter queue and heading none
(`replyWaitersConsistent`), holding no reply link (`replyCallerLinkage`), no
stashed reply (`pendingReceiveReplyWellFormed`) and no timeout budget
(`blockedThreadTimeoutConsistent`). -/
theorem readyThread_unlinked {s : SystemState} {x : SeLe4n.ThreadId} {t : TCB}
    (h : finaliseStepInvariant s) (hX : s.getTcb? x = some t) (hS : t.ipcStateCode = 0)
    (hO : t.ipcObjectCode = 0) (hW : ∀ v, ¬ ReplyViews.waiterOf s.replyViews v x) :
    t.ntfnNextCode = 0 ∧ t.ntfnPrevCode = 0 ∧ t.replyWaiterNextCode = 0 ∧
      t.replyWaiterPrevCode = 0 ∧ t.replyWaitersHeadCode = 0 ∧ t.replyObjectCode = 0 ∧
      t.pendingReceiveReplyCode = 0 ∧ t.timeoutBudget = none := by
  have hR : t.ipcState = .ready := by
    show ThreadIpcState.ofCodes t.ipcObjectCode t.ipcStateCode = _
    rw [hS, hO]; rfl
  have hTo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hX
  obtain ⟨hFull, -, hNtfn, hRw, -, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, hTB, -, -, -, -, hLink, hPend, -, -, -⟩ := hFull
  have hN := hNtfn.2.2.2.2 x t hTo (fun oid e => by rw [hR] at e; cases e)
  have hSrv : t.blockingServer? = none := by unfold TCB.blockingServer?; rw [hR]
  have hV := SystemState.replyViews_of_tcb hTo
  have hPN := hRw.2.2.1 x t.replyView hV hSrv
  obtain ⟨l, hCh, -, -, hMem⟩ := hRw.1 x t.replyView hV
  have hl : l = [] := by
    cases l with
    | nil => rfl
    | cons w _ => exact absurd ((hMem w).mp (List.mem_cons_self ..)) (hW w)
  subst hl
  have hHd : t.replyWaitersHeadCode = 0 := (SeLe4n.ThreadId.ofOptCode_eq_none_iff _).mp hCh
  have hRO : t.replyObjectCode = 0 := by
    cases hc : t.replyObjectCode with
    | zero => rfl
    | succ k =>
      have hr : t.replyObject = some ⟨k⟩ := by unfold TCB.replyObject; rw [hc]; rfl
      obtain ⟨r, hr', hcl⟩ := hLink.1.1 x t ⟨k⟩ hTo hr
      obtain ⟨t', ht', -, ep, rt, hB⟩ := hLink.1.2 ⟨k⟩ r x hr' hcl
      rw [hTo] at ht'; cases ht'; rw [hR] at hB; cases hB
  have hPR : t.pendingReceiveReplyCode = 0 := by
    cases hc : t.pendingReceiveReplyCode with
    | zero => rfl
    | succ k =>
      have hp : t.pendingReceiveReply = some ⟨k⟩ := by unfold TCB.pendingReceiveReply; rw [hc]; rfl
      obtain ⟨⟨ep, hB⟩, -⟩ := hPend.1 x t ⟨k⟩ hX hp
      rw [hR] at hB; cases hB
  have hT : t.timeoutBudget = none := by
    cases hb : t.timeoutBudget with
    | none => rfl
    | some sc =>
      have := (hTB x t sc hTo hb).2
      rw [hR] at this; exact this.elim
  exact ⟨(SeLe4n.ThreadId.ofOptCode_eq_none_iff _).mp hN.2,
    (SeLe4n.ThreadId.ofOptCode_eq_none_iff _).mp hN.1, hPN.2, hPN.1, hHd, hRO, hPR, hT⟩

-- ============================================================================
-- The context unbind clears the binding
-- ============================================================================

/-- **The finalisation's context unbind clears the thread's binding and nothing
else**: on a thread on no core whose binding names no owner and, when it names a
context, a context bound back to it, the unbind leaves the thread with no
binding, every other thread, every core's current slot and the machine as they
were. -/
theorem finaliseThreadUnbindSchedContext_self {s : SystemState} {x : SeLe4n.ThreadId} {t : TCB}
    (hInv : s.objects.invExt) (hX : s.getTcb? x = some t) (hRun : t.runCoreCode = 0)
    (hHeld : threadHeldOnSomeCore s x = false) (hOwn : t.scBindingOwnerCode = 0)
    (hBd : t.scBindingScCode ≠ 0 → ∃ sc, s.getSchedContext? ⟨t.scBindingScCode - 1⟩ = some sc ∧
      sc.boundThreadCode = x.val + 1) :
    (finaliseThreadUnbindSchedContext s x).getTcb? x =
        some { t with scBindingScCode := 0, scBindingOwnerCode := 0 } ∧
      (∀ y : SeLe4n.ThreadId, y.toObjId ≠ x.toObjId →
        (finaliseThreadUnbindSchedContext s x).getTcb? y = s.getTcb? y) ∧
      (∀ c, (finaliseThreadUnbindSchedContext s x).scheduler.currentOnCore c =
        s.scheduler.currentOnCore c) ∧
      (finaliseThreadUnbindSchedContext s x).machine = s.machine := by
  unfold finaliseThreadUnbindSchedContext
  rw [hX]
  dsimp only
  by_cases h0 : t.scBindingScCode = 0
  · rw [if_neg (by simp [h0])]
    refine ⟨?_, fun _ _ => rfl, fun _ => rfl, rfl⟩
    rw [hX]
    cases t
    simp only at h0 hOwn
    subst h0; subst hOwn; rfl
  · obtain ⟨sc, hSc, hB⟩ := hBd h0
    rw [if_pos (by simp [h0, hOwn, hRun, hHeld, hSc, hB])]
    have hBind := schedContextBinding_of_codes' h0 hOwn
    rw [cancelDonationArmOnCore_of_bound s x t _ hBind]
    have hOk := cancelBoundDonationOnCore_of_bound s x t _ hBind
    rw [hOk]
    dsimp only
    obtain ⟨g1, g2⟩ := cancelBoundDonationOnCore_getTcb? s _ x t _ hBind hInv hOk
    refine ⟨by rw [g1, hX]; rfl, g2,
      fun c => (cancelBoundDonationOnCore_runQueue_current_eq s _ x t c hOk).2,
      cancelBoundDonationOnCore_machine_eq s _ x t hOk⟩

/-- **The suspend keeps every thread's blocking server**: the deschedule writes
run-queue links, the mark the thread's run state and message. -/
theorem finaliseThreadSuspend_servers (s : SystemState) (x : SeLe4n.ThreadId)
    (hInv : s.objects.invExt) : tcbProjKept TCB.blockingServer? (finaliseThreadSuspend s x) s := by
  unfold finaliseThreadSuspend
  split
  · split
    · exact (tcbProjKept.updateTcb (f := finalisedSuspendMark) _ x
        (descheduleAtPlacement_preserves_objects_invExt s x hInv)
        (fun _ => rfl)).trans (tcbProjKept.of_agreeOffRunLinks (g := TCB.blockingServer?)
          (descheduleAtPlacement_objectsAgreeOffRunLinks s x) (fun _ => rfl))
    · exact tcbProjKept.refl s
  · exact tcbProjKept.refl s

/-- A step keeping every thread's blocking server keeps a server waited on by
nothing. -/
theorem noWaiter_of_servers {s s' : SystemState} {x : SeLe4n.ThreadId}
    (h : tcbProjKept TCB.blockingServer? s' s) (hW : ∀ v, ¬ ReplyViews.waiterOf s.replyViews v x) :
    ∀ v, ¬ ReplyViews.waiterOf s'.replyViews v x := by
  intro v hv
  obtain ⟨tv, htv, hsv⟩ := waiterOf_iff.mp hv
  have e := h v
  rw [htv] at e
  cases hs : s.getTcb? v with
  | none => rw [hs] at e; cases e
  | some t0 =>
    rw [hs] at e
    simp only [Option.map_some, Option.some.injEq] at e
    exact hW v (waiterOf_iff.mpr ⟨t0, hs, e ▸ hsv⟩)

end SeLe4n.Kernel
