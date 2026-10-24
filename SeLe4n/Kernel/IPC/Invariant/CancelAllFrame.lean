/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.CancelAll
import SeLe4n.Kernel.Lifecycle.Operations.CleanupPreservation
import SeLe4n.Kernel.Architecture.PageTeardownClears

/-!
# What a final delete's finalisation writes

WS-ZA ZA5.4 part 23: `finaliseFinalObject` (`IPC/Operations/CancelAll.lean`)
cancels an endpoint's or a notification's waiters and unbinds a notification
before the retire.  This module states what those writes are, once, for every
consumer:

* **The walks' induction** (`cancelEndpointQueue_closed`,
  `cancelNotificationQueue_closed`, `finaliseFinalObject_closed`): a property
  every step keeps holds after the whole finalisation, whatever the fuel.
* **The write frame** (`FinaliseFrame`): only the object store, the
  scheduler and the cores' FP/SIMD-owner and residency records change (a
  finalised thread is released by every core, WS-ZA ZA5.4 part 24), the object
  table stays well formed, and every key either
  keeps its object or holds a thread, an endpoint or a notification before and
  after, of the same kind and with the same capability slots.  So no CNode, no
  untyped, no VSpace root and no page table is written
  (`FinaliseFrame.kind`, `FinaliseFrame.roots_iff`), and the teardown's
  well-formedness carries across the finalisation
  (`finaliseFinalObject_preserves_teardownWellFormed`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

-- ============================================================================
-- §1  The walks' induction
-- ============================================================================

/-- **A property every endpoint cancel keeps holds after the walk.** -/
theorem cancelEndpointQueue_closed (P : SystemState → Prop) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool)
    (hStep : ∀ (s : SystemState) (ep : Endpoint) (t : SeLe4n.ThreadId) (tcb : TCB), P s →
      s.getEndpoint? endpointId = some ep → (endpointWaitQueue ep isReceiveQ).head = some t →
      s.getTcb? t = some tcb → endpointWaiterCancellable s endpointId t tcb = true →
      P (storeEndpointWaiterCancelled s endpointId isReceiveQ t tcb.queueNext)) :
    ∀ (fuel : Nat) (st : SystemState), P st →
      P (cancelEndpointQueue endpointId isReceiveQ fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ fuel ih =>
    intro st h
    simp only [cancelEndpointQueue]
    split
    · next ep hE =>
      split
      · next t hH =>
        split
        · next tcb hT =>
          split
          · next hC => exact ih _ (hStep st ep t tcb h hE hH hT hC)
          · exact h
        · exact h
      · exact h
    · exact h

/-- **A property every notification cancel keeps holds after the walk.** -/
theorem cancelNotificationQueue_closed (P : SystemState → Prop) (notificationId : SeLe4n.ObjId)
    (hStep : ∀ (s : SystemState) (n : Notification) (t : SeLe4n.ThreadId) (tcb : TCB), P s →
      s.getNotification? notificationId = some n → n.waitHead = some t →
      s.getTcb? t = some tcb → notificationWaiterCancellable s notificationId t tcb = true →
      P (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t)) :
    ∀ (fuel : Nat) (st : SystemState), P st →
      P (cancelNotificationQueue notificationId fuel st) := by
  intro fuel
  induction fuel with
  | zero => intro st h; exact h
  | succ fuel ih =>
    intro st h
    simp only [cancelNotificationQueue]
    split
    · next n hN =>
      split
      · next t hH =>
        split
        · next tcb hT =>
          split
          · next hC => exact ih _ (hStep st n t tcb h hN hH hT hC)
          · exact h
        · exact h
      · exact h
    · exact h

/-- **A property the unbind keeps holds after `unbindMaybeNotification`.** -/
theorem unbindMaybeNotification_closed (P : SystemState → Prop) (notificationId : SeLe4n.ObjId)
    (hStep : ∀ (s : SystemState) (n : Notification) (t : SeLe4n.ThreadId), P s →
      s.getNotification? notificationId = some n → n.boundTCB = some t →
      boundNotificationCodeOf s t = notificationId.val + 1 →
      unbindNotificationInPlace s t = true →
      P (storeUnbindNotification s t notificationId))
    (st : SystemState) (h : P st) : P (unbindMaybeNotification notificationId st) := by
  unfold unbindMaybeNotification
  split
  · next n hN =>
    split
    · next t hB =>
      split
      · next hC =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hC
        exact hStep st n t h hN hB hC.1 hC.2
      · exact h
    · exact h
  · exact h

/-- **The reservation-unbind step a thread's or a context's finalisation takes**:
a `.bound` thread, queued and held nowhere, whose context is bound back to it,
unbound by the destroy cleanup's reservation arm (`cancelDonationArmOnCore`). -/
def FinaliseScUnbindStep (P : SystemState → Prop) : Prop :=
  ∀ (s s' : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB) (sc : SchedContext), P s →
    s.getTcb? t = some tcb → tcb.scBindingScCode ≠ 0 → tcb.scBindingOwnerCode = 0 →
    tcb.runCoreCode = 0 → threadHeldOnSomeCore s t = false →
    ipcCodesIdleAllowed tcb.ipcObjectCode tcb.ipcStateCode = true →
    s.getSchedContext? ⟨tcb.scBindingScCode - 1⟩ = some sc → sc.boundThreadCode = t.val + 1 →
    cancelDonationArmOnCore s t tcb = .ok s' → P s'

/-- **The cancel step a thread's finalisation takes**: the head waiter of a
notification leaves its queue, and is not woken (`cancelIpcBlocking`). -/
def FinaliseCancelStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (n : SeLe4n.ObjId) (t : SeLe4n.ThreadId) (tcb : TCB) (ntfn : Notification),
    P s → s.getTcb? t = some tcb → tcb.ipcState = .blockedOnNotification n →
    s.getNotification? n = some ntfn → ntfn.waitHead = some t →
    notificationWaiterCancellable s n t tcb = true →
    P (Lifecycle.Suspend.cancelIpcBlocking s t tcb)

/-- **The suspend step a thread's finalisation takes**: a ready thread that is
not suspended and is no core's idle thread leaves the scheduler where the state
places it (`descheduleAtPlacement`) and is marked `.Inactive`. -/
def FinaliseSuspendStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB), P s → s.getTcb? t = some tcb →
    tcb.ipcStateCode = 0 → tcb.ipcObjectCode = 0 → tcb.threadState ≠ .Inactive →
    isIdleThreadId t = false →
    P ((descheduleAtPlacement s t).updateTcb t (fun t => { t with threadState := .Inactive }))

/-- **The release step a thread's finalisation takes**: no core holds the thread
as its FP/SIMD owner or its resident (`finaliseThreadReleaseCores`). -/
def FinaliseReleaseStep (P : SystemState → Prop) : Prop :=
  ∀ (s : SystemState) (t : SeLe4n.ThreadId), P s → P (finaliseThreadReleaseCores s t)

/-- **The notification-unbind step**: as `unbindMaybeNotification_closed` asks. -/
def FinaliseUnbindStep (P : SystemState → Prop) : Prop :=
  ∀ (notificationId : SeLe4n.ObjId) (s : SystemState) (n : Notification)
    (t : SeLe4n.ThreadId), P s →
    s.getNotification? notificationId = some n → n.boundTCB = some t →
    boundNotificationCodeOf s t = notificationId.val + 1 →
    unbindNotificationInPlace s t = true →
    P (storeUnbindNotification s t notificationId)

/-- **An IPC state `ipcCodesIdleAllowed` admits is one an unbound thread may
idle in.** -/
theorem passiveServerIdleAllowed_of_codes {tcb : TCB}
    (h : ipcCodesIdleAllowed tcb.ipcObjectCode tcb.ipcStateCode = true) :
    passiveServerIdleAllowed tcb.ipcState := by
  unfold ipcCodesIdleAllowed at h
  unfold TCB.ipcState ThreadIpcState.ofCodes passiveServerIdleAllowed
  generalize tcb.ipcObjectCode = o at h ⊢
  generalize tcb.ipcStateCode = c at h ⊢
  match c, o with
  | 0, 0 => exact Or.inl rfl
  | 0, _ + 1 => simp at h
  | 1, _ => exact Or.inr (Or.inl ⟨_, Or.inl rfl⟩)
  | 2, _ => exact Or.inr (Or.inl ⟨_, Or.inr rfl⟩)
  | 3, _ => simp at h
  | _ + 4, _ => exact Or.inr (Or.inr ⟨_, _, rfl⟩)

/-- A thread code `t + 1` decodes to `t`. -/
theorem threadOfOptCode_succ (t : SeLe4n.ThreadId) :
    SeLe4n.ThreadId.ofOptCode (t.val + 1) = some t := by
  have := SeLe4n.ThreadId.ofOptCode_optCode (some t)
  exact this

/-- **A property the thread finalisation's steps keep holds after it.** -/
theorem finaliseThread_closed (P : SystemState → Prop) (hUnbind : FinaliseUnbindStep P)
    (hSc : FinaliseScUnbindStep P) (hCancel : FinaliseCancelStep P)
    (hSuspend : FinaliseSuspendStep P) (hRelease : FinaliseReleaseStep P)
    (x : SeLe4n.ObjId) (st : SystemState) (h : P st) :
    P (finaliseThread x st) := by
  rw [finaliseThread_eq]
  split
  · generalize hTid : (⟨x.val⟩ : SeLe4n.ThreadId) = tid
    -- The notification unbind.
    have h1 : P (finaliseThreadUnbindNotification st tid) := by
      unfold finaliseThreadUnbindNotification
      dsimp only
      split
      · exact h
      · rename_i hc
        split
        · rename_i n hN
          split
          · rename_i hB
            simp only [Bool.and_eq_true, beq_iff_eq] at hB hc
            refine hUnbind _ st n tid h hN ?_ ?_ hB.2
            · unfold Notification.boundTCB; rw [hB.1]; exact threadOfOptCode_succ tid
            · simp only [SeLe4n.ObjId.val]; omega
          · exact h
        · exact h
    -- The cancel.
    have h2 : P (finaliseThreadCancel (finaliseThreadUnbindNotification st tid) tid) := by
      generalize finaliseThreadUnbindNotification st tid = s at h1 ⊢
      unfold finaliseThreadCancel
      split
      · rename_i t hT
        split
        · rename_i n hI
          split
          · rename_i ntfn hN
            split
            · rename_i hG
              simp only [Bool.and_eq_true, beq_iff_eq] at hG
              exact hCancel s n tid t ntfn h1 hT hI hN hG.1 hG.2
            · exact h1
          · exact h1
        · exact h1
      · exact h1
    -- The suspend.
    have h3 : P (finaliseThreadSuspend
        (finaliseThreadCancel (finaliseThreadUnbindNotification st tid) tid) tid) := by
      generalize finaliseThreadCancel _ tid = s at h2 ⊢
      unfold finaliseThreadSuspend
      split
      · rename_i t hT
        split
        · rename_i hG
          simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hG
          obtain ⟨⟨⟨hS, hO⟩, hI⟩, hId⟩ := hG
          exact hSuspend s tid t h2 hT hS hO hI hId
        · exact h2
      · exact h2
    -- The release.
    have h4 := hRelease _ tid h3
    -- The reservation unbind.
    generalize finaliseThreadReleaseCores _ tid = s at h4 ⊢
    unfold finaliseThreadUnbindSchedContext
    split
    · rename_i t hT
      cases hM : s.getSchedContext? ⟨t.scBindingScCode - 1⟩ with
      | none => simp only [hM, Bool.and_false, Bool.false_eq_true, ↓reduceIte]; exact h4
      | some sc =>
        simp only [hM]
        split
        · rename_i hG
          simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq, Bool.not_eq_true'] at hG
          obtain ⟨⟨⟨⟨⟨hS, hO⟩, hR⟩, hH⟩, hA⟩, hM'⟩ := hG
          split
          · rename_i s' hOk
            exact hSc s s' tid t sc h4 hT hS hO hR hH hA hM hM' hOk
          · exact h4
        · exact h4
    · exact h4
  · exact h

/-- **A property the reservation unbind keeps holds after the
scheduling-context finalisation.** -/
theorem finaliseSchedContext_closed (P : SystemState → Prop) (hSc : FinaliseScUnbindStep P)
    (x : SeLe4n.ObjId) (st : SystemState) (h : P st) : P (finaliseSchedContext x st) := by
  rw [finaliseSchedContext_eq]
  split
  · unfold finaliseSchedContextUnbind
    split
    · rename_i sc hX
      split
      · exact h
      · rename_i hB0
        dsimp only
        split
        · rename_i t hT
          split
          · rename_i hG
            simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true'] at hG
            obtain ⟨⟨⟨⟨hS, hO⟩, hR⟩, hH⟩, hA⟩ := hG
            split
            · rename_i s' hOk
              refine hSc st s' _ t sc h hT (by omega) hO hR hH hA ?_ ?_ hOk
              · rw [hS, Nat.add_sub_cancel]
                have hO : st.objects[x]? = some (.schedContext sc) := by rw [← hX]; simp
                unfold SystemState.getSchedContext?
                rw [show (⟨x.val⟩ : SeLe4n.SchedContextId).toObjId = x from rfl, hO]
              · simp only [beq_iff_eq] at hB0
                show _ = _ - 1 + 1; omega
            · exact h
          · exact h
        · exact h
    · exact h
  · exact h

/-- **A property every cancel, unbind and suspend keeps holds after the
finalisation.** -/
theorem finaliseFinalObject_closed (P : SystemState → Prop)
    (hEp : ∀ (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool) (s : SystemState) (ep : Endpoint)
      (t : SeLe4n.ThreadId) (tcb : TCB), P s →
      s.getEndpoint? endpointId = some ep → (endpointWaitQueue ep isReceiveQ).head = some t →
      s.getTcb? t = some tcb → endpointWaiterCancellable s endpointId t tcb = true →
      P (storeEndpointWaiterCancelled s endpointId isReceiveQ t tcb.queueNext))
    (hNtfn : ∀ (notificationId : SeLe4n.ObjId) (s : SystemState) (n : Notification)
      (t : SeLe4n.ThreadId) (tcb : TCB), P s →
      s.getNotification? notificationId = some n → n.waitHead = some t →
      s.getTcb? t = some tcb → notificationWaiterCancellable s notificationId t tcb = true →
      P (wakeCancelledWaiter (Lifecycle.Suspend.cancelIpcBlocking s t tcb) t))
    (hUnbind : FinaliseUnbindStep P) (hSc : FinaliseScUnbindStep P)
    (hCancel : FinaliseCancelStep P) (hSuspend : FinaliseSuspendStep P)
    (hRelease : FinaliseReleaseStep P)
    (target : Nat) (st : SystemState) (h : P st) : P (finaliseFinalObject target st) := by
  unfold finaliseFinalObject
  split
  · exact h
  dsimp only
  split
  · split
    · exact cancelEndpointQueue_closed P _ true (hEp _ true) _ _
        (cancelEndpointQueue_closed P _ false (hEp _ false) _ _ h)
    · exact cancelNotificationQueue_closed P _ (hNtfn _) _ _
        (unbindMaybeNotification_closed P _ (hUnbind _) st h)
    · exact finaliseThread_closed P hUnbind hSc hCancel hSuspend hRelease _ st h
    · exact finaliseSchedContext_closed P hSc _ st h
    · exact h
  · exact h

-- ============================================================================
-- §2  The write frame
-- ============================================================================

/-- **An object a finalisation may write**: a thread, an endpoint, a
notification or a scheduling context. -/
def finaliseWritable (o : KernelObject) : Prop :=
  o.objectType = .tcb ∨ o.objectType = .endpoint ∨ o.objectType = .notification ∨
    o.objectType = .schedContext

theorem finaliseWritable.untyped {o : KernelObject} (h : finaliseWritable o) :
    o.untyped? = none := by
  cases o <;> simp_all [finaliseWritable, KernelObject.objectType, KernelObject.untyped?]

theorem finaliseWritable.not_cnode {o : KernelObject} (h : finaliseWritable o) :
    o.objectType ≠ .cnode := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

theorem finaliseWritable.not_vspaceRoot {o : KernelObject} (h : finaliseWritable o) :
    o.objectType ≠ .vspaceRoot := by
  rcases h with h | h | h | h <;> rw [h] <;> decide

theorem finaliseWritable_tcb (t : TCB) : finaliseWritable (.tcb t) := Or.inl rfl

theorem finaliseWritable_schedContext (sc : SchedContext) :
    finaliseWritable (.schedContext sc) := Or.inr (Or.inr (Or.inr rfl))

/-- **What a finalisation writes, key by key**: each key keeps its object, or
holds a thread, an endpoint, a notification or a scheduling context before and
after, of the same kind, with the same capability slots and, for a context, the
same reply-stack head. -/
def finaliseWrite (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ∃ pre post : KernelObject, st.objects[oid]? = some pre ∧ st'.objects[oid]? = some post ∧
      post.objectType = pre.objectType ∧ post.tcbSlots = pre.tcbSlots ∧
      schedContextStackHead? (some post) = schedContextStackHead? (some pre) ∧
      finaliseWritable pre

namespace finaliseWrite

theorem refl (st : SystemState) : finaliseWrite st st := fun _ => Or.inl rfl

theorem trans {a b c : SystemState} (h₁ : finaliseWrite a b) (h₂ : finaliseWrite b c) :
    finaliseWrite a c := by
  intro oid
  rcases h₁ oid with e₁ | ⟨p₁, q₁, hp₁, hq₁, ht₁, hs₁, hh₁, hw₁⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, ht₂, hs₂, hh₂, hw₂⟩
    · exact Or.inl (e₂.trans e₁)
    · exact Or.inr ⟨p₂, q₂, e₁ ▸ hp₂, hq₂, ht₂, hs₂, hh₂, hw₂⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, ht₂, hs₂, hh₂, hw₂⟩
    · exact Or.inr ⟨p₁, q₁, hp₁, e₂.trans hq₁, ht₁, hs₁, hh₁, hw₁⟩
    · rw [hq₁] at hp₂
      cases hp₂
      exact Or.inr ⟨p₁, q₂, hp₁, hq₂, ht₂.trans ht₁, hs₂.trans hs₁, hh₂.trans hh₁, hw₁⟩

/-- A finalisation write is kind-preserving: what it writes is no CNode, and
keeps its untyped record (none). -/
theorem kind {st st' : SystemState} (h : finaliseWrite st st') : kindPreservingWrite st st' := by
  intro oid
  rcases h oid with e | ⟨pre, post, hp, hq, ht, hs, -, hw⟩
  · exact Or.inl e
  · have hw' : finaliseWritable post := by unfold finaliseWritable; rw [ht]; exact hw
    exact Or.inr ⟨pre, post, hp, hq, ht, ht ▸ hw.not_cnode, hs, by
      rw [hw.untyped, hw'.untyped]⟩

/-- An object the finalisation may not write is kept where it is. -/
theorem keeps {st st' : SystemState} (h : finaliseWrite st st') {oid : SeLe4n.ObjId}
    {o : KernelObject} (hO : st.objects[oid]? = some o) (hN : ¬ finaliseWritable o) :
    st'.objects[oid]? = some o := by
  rcases h oid with e | ⟨pre, post, hp, -, -, -, -, hw⟩
  · rw [e]; exact hO
  · rw [hO] at hp; cases hp; exact absurd hw hN

/-- …and an object present after a finalisation that it may not write was there
before it. -/
theorem keeps' {st st' : SystemState} (h : finaliseWrite st st') {oid : SeLe4n.ObjId}
    {o : KernelObject} (hO : st'.objects[oid]? = some o) (hN : ¬ finaliseWritable o) :
    st.objects[oid]? = some o := by
  rcases h oid with e | ⟨pre, post, hp, hq, ht, -, -, hw⟩
  · rw [← e]; exact hO
  · rw [hO] at hq; cases hq
    exact absurd (by unfold finaliseWritable; rw [ht]; exact hw) hN

/-- **The finalisation writes no VSpace root.** -/
theorem roots_iff {st st' : SystemState} (h : finaliseWrite st st') (oid : SeLe4n.ObjId)
    (r : VSpaceRoot) :
    st'.objects[oid]? = some (.vspaceRoot r) ↔ st.objects[oid]? = some (.vspaceRoot r) := by
  have hN : ¬ finaliseWritable (.vspaceRoot r) := fun hw => hw.not_vspaceRoot rfl
  exact ⟨fun hO => h.keeps' hO hN, fun hO => h.keeps hO hN⟩

/-- **A write that keeps the kinds and every object it may not write is a
finalisation write.** -/
theorem of_kind_keeps {st st' : SystemState} (hK : kindPreservingWrite st st')
    (hT : ∀ (oid : SeLe4n.ObjId) (o : KernelObject), st.objects[oid]? = some o →
      ¬ finaliseWritable o → st'.objects[oid]? = some o)
    (hH : ∀ (oid : SeLe4n.ObjId), schedContextStackHead? st'.objects[oid]? =
      schedContextStackHead? st.objects[oid]?) :
    finaliseWrite st st' := by
  intro oid
  rcases hK oid with e | ⟨pre, post, hp, hq, ht, -, hs, -⟩
  · exact Or.inl e
  · by_cases hw : finaliseWritable pre
    · have := hH oid; rw [hp, hq] at this
      exact Or.inr ⟨pre, post, hp, hq, ht, hs, this, hw⟩
    · exact Or.inl ((hT oid pre hp hw).trans hp.symm)

/-- **A store of a finalisation-writable object's like at its own key.** -/
theorem of_insert {st st' : SystemState} {k : SeLe4n.ObjId} {o o' : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k o')
    (hPre : st.objects[k]? = some o) (hW : finaliseWritable o)
    (hT : o'.objectType = o.objectType) (hS : o'.tcbSlots = o.tcbSlots)
    (hH : schedContextStackHead? (some o') = schedContextStackHead? (some o) := by
      first | rfl | simp [schedContextStackHead?]) :
    finaliseWrite st st' := by
  intro oid
  rw [hO]
  by_cases e : oid = k
  · subst e
    exact Or.inr ⟨o, o', hPre, RobinHood.RHTable.getElem?_insert_self st.objects oid o' hInv,
      hT, hS, hH, hW⟩
  · exact Or.inl (RobinHood.RHTable.getElem?_insert_ne st.objects k oid o'
      (by intro h; exact e (eq_of_beq h).symm) hInv)

/-- **Writes off the run-queue links are finalisation writes**: they rewrite
threads only, keeping their slots. -/
theorem of_agreeOffRunLinks {st st' : SystemState} (h : st'.objectsAgreeOffRunLinks st) :
    finaliseWrite st st' := by
  intro oid
  rcases h.pointwise oid with e | ⟨t, t', ht, ht'⟩
  · exact Or.inl e
  · obtain ⟨t'', ht'', hE⟩ := h.get_tcb ht
    rw [ht'] at ht''
    cases ht''
    refine Or.inr ⟨.tcb t, .tcb t', ht, ht', rfl, ?_, rfl, finaliseWritable_tcb t⟩
    simp only [KernelObject.tcbSlots,
      TCB.proj_eq_of_withoutRunLinks_eq (·.spaceCells) hE,
      TCB.proj_eq_of_withoutRunLinks_eq (·.spaceLinks) hE]

/-- **A notification-queue unlink is a finalisation write**: it rewrites
notifications and threads' notification links. -/
theorem of_ntfnUnlinkReach {st st' : SystemState} (h : ntfnUnlinkReach st st') :
    finaliseWrite st st' := by
  intro oid
  rcases h.2 oid with e | ⟨n, n', hn, hn', -⟩ | ⟨t, t', ht, ht', ⟨np, nn, rfl⟩⟩
  · exact Or.inl e
  · exact Or.inr ⟨.notification n, .notification n', hn, hn', rfl, rfl, rfl,
      Or.inr (Or.inr (Or.inl rfl))⟩
  · exact Or.inr ⟨.tcb t, .tcb _, ht, ht', rfl, rfl, rfl, finaliseWritable_tcb t⟩

end finaliseWrite

/-- **`st'` is `st` with at most its object store, its scheduler and the cores'
FP/SIMD-owner and residency records rewritten** — what a finalisation writes,
once a finalised thread is released by every core (`finaliseThreadReleaseCores`):
every other machine field, every register bank and the memory are `st`'s. -/
def onlyObjectsSchedulerCoreHoldsDiffer (st' st : SystemState) : Prop :=
  st' = { st with objects := st'.objects, scheduler := st'.scheduler,
                  machine := { st.machine with fpOwner := st'.machine.fpOwner,
                                               residentCode := st'.machine.residentCode } }

namespace onlyObjectsSchedulerCoreHoldsDiffer

theorem refl (st : SystemState) : onlyObjectsSchedulerCoreHoldsDiffer st st := rfl

theorem trans {a b c : SystemState} (h₂ : onlyObjectsSchedulerCoreHoldsDiffer c b)
    (h₁ : onlyObjectsSchedulerCoreHoldsDiffer b a) : onlyObjectsSchedulerCoreHoldsDiffer c a := by
  unfold onlyObjectsSchedulerCoreHoldsDiffer at *
  calc c = { b with objects := c.objects, scheduler := c.scheduler,
                    machine := { b.machine with fpOwner := c.machine.fpOwner,
                                                residentCode := c.machine.residentCode } } := h₂
    _ = _ := by rw [h₁]

theorem of_onlyObjectsSchedulerDiffer {st st' : SystemState}
    (h : SystemState.onlyObjectsSchedulerDiffer st' st) : onlyObjectsSchedulerCoreHoldsDiffer st' st := by
  unfold onlyObjectsSchedulerCoreHoldsDiffer
  unfold SystemState.onlyObjectsSchedulerDiffer at h
  rw [h]

theorem cdt {st st' : SystemState} (h : onlyObjectsSchedulerCoreHoldsDiffer st' st) :
    st'.cdt = st.cdt := by
  have e := congrArg SystemState.cdt h; exact e

theorem asidTable {st st' : SystemState} (h : onlyObjectsSchedulerCoreHoldsDiffer st' st) :
    st'.asidTable = st.asidTable := by
  have e := congrArg SystemState.asidTable h; exact e

/-- The release writes the two records alone. -/
theorem releaseCores (st : SystemState) (t : SeLe4n.ThreadId) :
    onlyObjectsSchedulerCoreHoldsDiffer (finaliseThreadReleaseCores st t) st := by
  unfold onlyObjectsSchedulerCoreHoldsDiffer finaliseThreadReleaseCores
  simp only []
  rw [MachineState.releaseThread, MachineState.releaseThreadOnCores_fields]

end onlyObjectsSchedulerCoreHoldsDiffer

/-- **What a finalisation's step leaves**: only the object store, the scheduler
and the cores' hold records changed, the object table well formed, and a
finalisation write. -/
structure FinaliseFrame (st st' : SystemState) : Prop where
  rest : onlyObjectsSchedulerCoreHoldsDiffer st' st
  invExt : st'.objects.invExt
  write : finaliseWrite st st'

namespace FinaliseFrame

theorem refl {st : SystemState} (hInv : st.objects.invExt) : FinaliseFrame st st :=
  ⟨.refl st, hInv, .refl st⟩

theorem trans {a b c : SystemState} (h₁ : FinaliseFrame a b) (h₂ : FinaliseFrame b c) :
    FinaliseFrame a c :=
  ⟨h₂.rest.trans h₁.rest, h₂.invExt, h₁.write.trans h₂.write⟩

theorem kind {st st' : SystemState} (h : FinaliseFrame st st') : kindPreservingWrite st st' :=
  h.write.kind

theorem asidTable {st st' : SystemState} (h : FinaliseFrame st st') :
    st'.asidTable = st.asidTable := h.rest.asidTable

theorem cdt {st st' : SystemState} (h : FinaliseFrame st st') : st'.cdt = st.cdt := h.rest.cdt

/-- **The finalisation keeps the teardown's well-formedness, and only shrinks
the roots** — it keeps every root. -/
theorem preserves_teardownWellFormed {st st' : SystemState} (h : FinaliseFrame st st')
    (hW : teardownWellFormed st) :
    teardownWellFormed st' ∧
      vspaceRootsShrink st st' := by
  refine ⟨teardownWellFormed_of_roots_eq h.invExt h.asidTable
    (h.write.roots_iff) hW, fun oid r' hR => ⟨r', (h.write.roots_iff oid r').1 hR, rfl,
      fun _ _ hm => hm, fun _ _ he => he, fun _ hs => hs⟩⟩

/-- **The finalisation keeps every slot's capability**: it writes no CNode, and
a thread it writes keeps its space slots. -/
theorem slotCapAt {st st' : SystemState} (h : FinaliseFrame st st') (r : SlotRef) :
    st'.slotCapAt r = st.slotCapAt r := by
  rw [SystemState.slotCapAt_eq_bind, SystemState.slotCapAt_eq_bind]
  rcases h.write r.cnode with e | ⟨pre, post, hp, hq, ht, hs, -, hw⟩
  · rw [e]
  · rw [hp, hq]
    simp only [Option.bind_some,
      (KernelObject.slots_eq_of_tcbSlots ht (ht ▸ hw.not_cnode) hs).1]

/-- **The finalisation keeps every untyped record.** -/
theorem getUntyped? {st st' : SystemState} (h : FinaliseFrame st st') :
    st'.getUntyped? = st.getUntyped? :=
  funext fun o => by
    rw [SystemState.getUntyped?_eq_bind, SystemState.getUntyped?_eq_bind]; exact h.kind.untyped o

end FinaliseFrame

-- ============================================================================
-- §3  Each step's frame
-- ============================================================================

namespace FinaliseFrame

/-- A thread rewritten in its slot, its capability slots kept. -/
theorem updateTcb (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB)
    (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).spaceCells = x.spaceCells ∧ (f x).spaceLinks = x.spaceLinks := by
      intro _; exact ⟨rfl, rfl⟩) :
    FinaliseFrame st (st.updateTcb t f) := by
  cases hG : st.getTcb? t with
  | none => rw [SystemState.updateTcb_eq_self_of_none hG]; exact .refl hInv
  | some x =>
    rw [SystemState.updateTcb_eq_of_some hG]
    exact ⟨rfl, RHTable_insert_preserves_invExt _ _ _ hInv,
      finaliseWrite.of_insert hInv rfl ((SystemState.getTcb?_eq_some_iff st t x).mp hG)
        (finaliseWritable_tcb x) rfl (by simp only [KernelObject.tcbSlots, (hf x).1, (hf x).2])⟩

/-- An object rewritten in its slot by an update that keeps every object, or
keeps a writable one's kind and slots. -/
theorem modifyObject (st : SystemState) (k : SeLe4n.ObjId) (f : KernelObject → KernelObject)
    (hInv : st.objects.invExt)
    (hf : ∀ o, f o = o ∨ ((f o).objectType = o.objectType ∧ (f o).tcbSlots = o.tcbSlots ∧
      schedContextStackHead? (some (f o)) = schedContextStackHead? (some o) ∧
      finaliseWritable o)) :
    FinaliseFrame st (st.modifyObject k f) := by
  unfold SystemState.modifyObject
  cases hG : st.objects[k]? with
  | none =>
    have e : st.objects.modify k f = st.objects := by
      unfold RobinHood.RHTable.modify; rw [← RHTable_getElem?_eq_get?, hG]
    rw [e]; exact .refl hInv
  | some o =>
    rw [RobinHood.RHTable.modify_of_get? hG]
    refine ⟨rfl, RHTable_insert_preserves_invExt _ _ _ hInv, ?_⟩
    rcases hf o with e | ⟨hT, hS, hH, hW⟩
    · rw [e]
      intro oid
      left
      show (st.objects.insert k o)[oid]? = st.objects[oid]?
      by_cases h : oid = k
      · subst h; exact (RobinHood.RHTable.getElem?_insert_self st.objects oid o hInv).trans hG.symm
      · exact RobinHood.RHTable.getElem?_insert_ne st.objects k oid o
          (by intro h'; exact h (eq_of_beq h').symm) hInv
    · exact finaliseWrite.of_insert hInv rfl hG hW hT hS hH

/-- The wake: a run-queue insert and the `.ready` mark, on threads only. -/
theorem enqueueRunnableOnCore (st : SystemState) (c : Concurrency.CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.enqueueRunnableOnCore st c t) := by
  refine ⟨.of_onlyObjectsSchedulerDiffer (enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c t),
    enqueueRunnableOnCore_preserves_objects_invExt st c t hInv, ?_⟩
  cases hT : st.getTcb? t with
  | none =>
    simp only [SeLe4n.Kernel.enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_none hT]
    exact .refl _
  | some tcb =>
    cases hD : wakeDeclines st c t with
    | true =>
      simp only [SeLe4n.Kernel.enqueueRunnableOnCore, SystemState.getTcbWitnessed?_eq_some hT, hD,
        if_true]
      exact .refl _
    | false =>
      exact (finaliseWrite.of_insert
        (st' := { st with objects := st.objects.insert t.toObjId (.tcb (tcb.setIpcState .ready)) })
        hInv rfl ((SystemState.getTcb?_eq_some_iff st t tcb).mp hT) (finaliseWritable_tcb tcb)
        rfl rfl).trans
        (finaliseWrite.of_agreeOffRunLinks (enqueueRunnableOnCore_objectsAgree_marked st c t tcb hT hD))

theorem wakeCancelledWaiter (st : SystemState) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.wakeCancelledWaiter st t) :=
  enqueueRunnableOnCore st _ t hInv

/-- The pop of an endpoint queue's head, each write in its slot. -/
theorem storePopHead (st : SystemState) (endpointId : SeLe4n.ObjId) (isReceiveQ : Bool)
    (head : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.storePopHead st endpointId isReceiveQ head next) := by
  have h1 := modifyObject st endpointId (popEndpoint isReceiveQ (SeLe4n.ThreadId.optCode next))
    hInv (fun o => by
      cases o with
      | endpoint e =>
        right
        simp only [popEndpoint]
        split <;> exact ⟨rfl, rfl, rfl, Or.inr (Or.inl rfl)⟩
      | _ => exact Or.inl rfl)
  cases next with
  | none =>
    simp only [SeLe4n.Kernel.storePopHead]
    exact h1.trans (updateTcb _ _ _ h1.invExt)
  | some n =>
    simp only [SeLe4n.Kernel.storePopHead]
    have h2 := h1.trans (updateTcb _ n tcbAsQueueHead h1.invExt)
    exact h2.trans (updateTcb _ _ _ h2.invExt)

/-- An endpoint waiter's cancel: the pop, the thread's IPC ended, the wake. -/
theorem storeEndpointWaiterCancelled (st : SystemState) (endpointId : SeLe4n.ObjId)
    (isReceiveQ : Bool) (t : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.storeEndpointWaiterCancelled st endpointId isReceiveQ t next) := by
  unfold SeLe4n.Kernel.storeEndpointWaiterCancelled
  have h1 := storePopHead st endpointId isReceiveQ t next hInv
  have h2 := h1.trans (updateTcb _ t cancelledEndpointWaiterTcb h1.invExt)
  exact h2.trans (wakeCancelledWaiter _ t h2.invExt)

/-- A notification waiter's cancel: it leaves the notification's queue and is
restored, staged with the cancellation frame. -/
theorem notificationCancel (st : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB)
    (n : SeLe4n.ObjId) (hInv : st.objects.invExt)
    (hB : tcb.ipcState = .blockedOnNotification n) :
    FinaliseFrame st (Lifecycle.Suspend.cancelIpcBlocking st t tcb) := by
  have hEq : Lifecycle.Suspend.cancelIpcBlocking st t tcb =
      Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue st t) t := by
    unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
  rw [hEq]
  have hR := removeFromNotificationWaitQueue_reach st t hInv
  have h1 : FinaliseFrame st (removeFromNotificationWaitQueue st t) := by
    obtain ⟨objs, e⟩ := removeFromNotificationWaitQueue_eq_objects st t
    exact ⟨by rw [e]; rfl, hR.1, finaliseWrite.of_ntfnUnlinkReach hR⟩
  exact h1.trans (updateTcb _ _ _ h1.invExt)

/-- The unbind, each side in its slot. -/
theorem storeUnbindNotification (st : SystemState) (t : SeLe4n.ThreadId) (n : SeLe4n.ObjId)
    (hInv : st.objects.invExt) :
    FinaliseFrame st (SeLe4n.Kernel.storeUnbindNotification st t n) := by
  unfold SeLe4n.Kernel.storeUnbindNotification
  have h1 := updateTcb st t (fun x => { x with boundNotificationCode := 0 }) hInv
  exact h1.trans (modifyObject _ n _ h1.invExt (fun o => by
    cases o with
    | notification m => exact Or.inr ⟨rfl, rfl, rfl, Or.inr (Or.inr (Or.inl rfl))⟩
    | _ => exact Or.inl rfl))

/-- A step that writes the scheduler alone. -/
theorem of_objects_eq {st st' : SystemState} (hR : SystemState.onlyObjectsSchedulerDiffer st' st)
    (hO : st'.objects = st.objects) (hInv : st.objects.invExt) : FinaliseFrame st st' :=
  ⟨.of_onlyObjectsSchedulerDiffer hR, hO ▸ hInv, fun oid => Or.inl (by rw [hO])⟩

/-- A scheduling context rewritten in its slot, its reply-stack head kept. -/
theorem updateSchedContext (st : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hInv : st.objects.invExt)
    (hf : ∀ x, (f x).scReply = x.scReply) :
    FinaliseFrame st (st.updateSchedContext scId f) := by
  cases hG : st.getSchedContext? scId with
  | none => rw [SystemState.updateSchedContext_eq_self_of_none hG]; exact .refl hInv
  | some x =>
    rw [SystemState.updateSchedContext_eq_of_some hG]
    exact ⟨rfl, RHTable_insert_preserves_invExt _ _ _ hInv,
      finaliseWrite.of_insert hInv rfl ((SystemState.getSchedContext?_eq_some_iff st scId x).mp hG)
        (finaliseWritable_schedContext x) rfl rfl (by simp [schedContextStackHead?, hf x])⟩

/-- The key hook rewrites the scheduler alone. -/
theorem markKeyChangeFrom (pre st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.markKeyChangeFrom pre st tid) :=
  let post := SeLe4n.Kernel.markKeyChangeFrom pre st tid
  of_objects_eq (markKeyChangeFrom_extract_frame
    (fun s : SystemState => ({ s with objects := post.objects, scheduler := post.scheduler } :
      SystemState)) pre st tid (fun _ _ => rfl))
    (markKeyChangeFrom_objects pre st tid) hInv

/-- **The reservation unbind**: the context's binding cleared, its replenishment
purged, the thread's binding cleared, the key hook. -/
theorem cancelBoundDonationOnCore {st st' : SystemState} {t : SeLe4n.ThreadId} {tcb : TCB}
    {c : Concurrency.CoreId} (hInv : st.objects.invExt)
    (h : SeLe4n.Kernel.cancelBoundDonationOnCore st t tcb c = .ok st') : FinaliseFrame st st' := by
  unfold SeLe4n.Kernel.cancelBoundDonationOnCore at h
  split at h
  · rename_i scId _
    injection h with h; subst h
    have h1 := updateSchedContext st scId
      (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
      hInv (fun _ => rfl)
    generalize st.updateSchedContext scId _ = st1 at h1 ⊢
    let sch := st1.scheduler.setReplenishQueueOnCore c
      (ReplenishQueue.remove (st1.scheduler.replenishQueueOnCore c) scId)
    have h2 := h1.trans (of_objects_eq (st' := { st1 with scheduler := sch }) rfl rfl h1.invExt)
    have h3 := h2.trans (updateTcb _ t
      (fun tcb' => { tcb' with scBindingScCode := 0, scBindingOwnerCode := 0 }) h2.invExt)
    exact h3.trans (markKeyChangeFrom _ _ t h3.invExt)
  · cases h

/-- **A deschedule where the state places the thread**: run-queue links and the
scheduler alone. -/
theorem descheduleAt (st : SystemState) (t : SeLe4n.ThreadId) (p : Option Concurrency.CoreId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.descheduleAt st t p) := by
  cases p with
  | none => exact .refl hInv
  | some c =>
    exact ⟨.of_onlyObjectsSchedulerDiffer (removeRunnableOnCore_onlyObjectsSchedulerDiffer st t c),
      removeRunnableOnCore_objects_invExt st t c hInv,
      finaliseWrite.of_agreeOffRunLinks (removeRunnableOnCore_objectsAgreeOffRunLinks st t c)⟩

/-- **A finalised thread's suspend**: the deschedule, then the `.Inactive` mark. -/
theorem suspend (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    FinaliseFrame st ((descheduleAtPlacement st t).updateTcb t (fun t => { t with threadState := .Inactive })) := by
  have h1 := descheduleAt st t (placedCoreOf? st t) hInv
  exact h1.trans (updateTcb _ t _ h1.invExt)

/-- **A finalised thread's release by every core**: the cores' hold records
alone. -/
theorem releaseCores (st : SystemState) (t : SeLe4n.ThreadId) (hInv : st.objects.invExt) :
    FinaliseFrame st (finaliseThreadReleaseCores st t) := by
  have hO := finaliseThreadReleaseCores_objects st t
  constructor
  · exact onlyObjectsSchedulerCoreHoldsDiffer.releaseCores st t
  · rw [hO]; exact hInv
  · intro oid; left; rw [hO]

/-- The reservation-unbind step, as the closure asks it. -/
theorem scUnbindStep (st : SystemState) : FinaliseScUnbindStep (FinaliseFrame st) := by
  intro s s' t tcb _ h _ hS hO _ _ _ _ _ hOk
  rw [cancelDonationArmOnCore_of_codes s t hS hO] at hOk
  exact h.trans (cancelBoundDonationOnCore h.invExt hOk)

end FinaliseFrame

/-- **What a notification waiter's cancel admits**: the waiter is no reserved
thread, is blocked on the notification, is linked into no endpoint queue, and a
cancel may wake it. -/
theorem notificationWaiterCancellable_parts {st : SystemState} {n : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : notificationWaiterCancellable st n t tcb = true) :
    ¬ t.isReserved ∧ tcb.ipcState = .blockedOnNotification n ∧ tcb.queuePrev = none ∧
      tcb.queueNext = none ∧ cancelledWaiterWakeable st t tcb = true := by
  simp only [notificationWaiterCancellable, Bool.and_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hR, hB⟩, hP⟩, hN⟩, hW⟩ := h
  refine ⟨by simp [hR], hB, ?_, ?_, hW⟩
  · simp [TCB.queuePrev, hP, SeLe4n.ThreadId.ofOptCode]
  · simp [TCB.queueNext, hN, SeLe4n.ThreadId.ofOptCode]

theorem notificationWaiterCancellable_blocked {st : SystemState} {n : SeLe4n.ObjId}
    {t : SeLe4n.ThreadId} {tcb : TCB} (h : notificationWaiterCancellable st n t tcb = true) :
    tcb.ipcState = .blockedOnNotification n :=
  (notificationWaiterCancellable_parts h).2.1

/-- **The finalisation's write frame.** -/
theorem finaliseFinalObject_frame (target : Nat) (st : SystemState) (hInv : st.objects.invExt) :
    FinaliseFrame st (finaliseFinalObject target st) :=
  finaliseFinalObject_closed (FinaliseFrame st)
    (fun _ _ _ _ _ _ h _ _ _ _ => h.trans (.storeEndpointWaiterCancelled _ _ _ _ _ h.invExt))
    (fun _ s _ t tcb h _ _ _ hC =>
      have h1 := h.trans (FinaliseFrame.notificationCancel s t tcb _ h.invExt
        (notificationWaiterCancellable_blocked hC))
      h1.trans (.wakeCancelledWaiter _ _ h1.invExt))
    (fun _ _ _ _ h _ _ _ _ => h.trans (.storeUnbindNotification _ _ _ h.invExt))
    (FinaliseFrame.scUnbindStep st)
    (fun s n t tcb _ h _ hI _ _ _ => h.trans (FinaliseFrame.notificationCancel s t tcb n h.invExt hI))
    (fun s t _ h _ _ _ _ _ => h.trans (FinaliseFrame.suspend s t h.invExt))
    (fun s t h => h.trans (FinaliseFrame.releaseCores s t h.invExt))
    target st (.refl hInv)

/-- **The finalisation writes only the object store and the scheduler**, on any
state. -/
theorem finaliseFinalObject_onlyObjectsSchedulerCoreHoldsDiffer (target : Nat) (st : SystemState) :
    onlyObjectsSchedulerCoreHoldsDiffer (finaliseFinalObject target st) st := by
  have hU : ∀ (s : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB),
      SystemState.onlyObjectsSchedulerDiffer (s.updateTcb t f) s := by
    intro s t f; unfold SystemState.updateTcb; split <;> rfl
  have hM : ∀ (s : SystemState) (k : SeLe4n.ObjId) (f : KernelObject → KernelObject),
      SystemState.onlyObjectsSchedulerDiffer (s.modifyObject k f) s := fun _ _ _ => rfl
  have hP : ∀ (s : SystemState) (e : SeLe4n.ObjId) (q : Bool) (h : SeLe4n.ThreadId)
      (n : Option SeLe4n.ThreadId),
      SystemState.onlyObjectsSchedulerDiffer (SeLe4n.Kernel.storePopHead s e q h n) s := by
    intro s e q h n
    cases n with
    | none => simp only [SeLe4n.Kernel.storePopHead]; exact (hU _ _ _).trans (hM _ _ _)
    | some m =>
      simp only [SeLe4n.Kernel.storePopHead]
      exact (hU _ _ _).trans ((hU _ _ _).trans (hM _ _ _))
  have hS : ∀ (s : SystemState) (k : SeLe4n.SchedContextId) (f : SchedContext → SchedContext),
      SystemState.onlyObjectsSchedulerDiffer (s.updateSchedContext k f) s := by
    intro s k f; unfold SystemState.updateSchedContext; split <;> rfl
  have hK : ∀ (pre s : SystemState) (t : SeLe4n.ThreadId),
      SystemState.onlyObjectsSchedulerDiffer (markKeyChangeFrom pre s t) s := by
    intro pre s t
    let post := markKeyChangeFrom pre s t
    exact markKeyChangeFrom_extract_frame
      (fun x : SystemState => ({ x with objects := post.objects, scheduler := post.scheduler } :
        SystemState)) pre s t (fun _ _ => rfl)
  have hNc : ∀ (s : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB) (n : SeLe4n.ObjId),
      tcb.ipcState = .blockedOnNotification n →
      SystemState.onlyObjectsSchedulerDiffer (Lifecycle.Suspend.cancelIpcBlocking s t tcb) s := by
    intro s t tcb n hB
    have hEq : Lifecycle.Suspend.cancelIpcBlocking s t tcb =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue s t) t := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [hB]
    rw [hEq]
    obtain ⟨objs, e⟩ := removeFromNotificationWaitQueue_eq_objects s t
    have hR : SystemState.onlyObjectsSchedulerDiffer (removeFromNotificationWaitQueue s t) s := by
      rw [e]; rfl
    exact (hU _ _ _).trans hR
  have hL : ∀ {s s' : SystemState}, SystemState.onlyObjectsSchedulerDiffer s' s →
      onlyObjectsSchedulerCoreHoldsDiffer s st → onlyObjectsSchedulerCoreHoldsDiffer s' st :=
    fun hX h => (onlyObjectsSchedulerCoreHoldsDiffer.of_onlyObjectsSchedulerDiffer hX).trans h
  refine finaliseFinalObject_closed (fun s => onlyObjectsSchedulerCoreHoldsDiffer s st)
    (fun _ _ s _ t _ h _ _ _ _ => ?_) (fun _ s _ t tcb h _ _ _ hC => ?_)
    (fun _ s _ t h _ _ _ _ => ?_) (fun s s' t tcb _ h _ hS' hO _ _ _ _ _ hOk => ?_)
    (fun s n t tcb _ h _ hI _ _ _ => hL (hNc s t tcb n hI) h)
    (fun s t _ h _ _ _ _ _ => hL ((hU _ t _).trans (descheduleAtPlacement_onlyObjectsSchedulerDiffer s t)) h)
    (fun s t h => (onlyObjectsSchedulerCoreHoldsDiffer.releaseCores s t).trans h) target st
    (.refl st)
  · unfold storeEndpointWaiterCancelled wakeCancelledWaiter
    exact hL ((enqueueRunnableOnCore_onlyObjectsSchedulerDiffer _ _ _).trans
      ((hU _ _ _).trans (hP _ _ _ _ _))) h
  · have hEq : Lifecycle.Suspend.cancelIpcBlocking s t tcb =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue s t) t := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [notificationWaiterCancellable_blocked hC]
    unfold wakeCancelledWaiter
    rw [hEq]
    obtain ⟨objs, e⟩ := removeFromNotificationWaitQueue_eq_objects s t
    have hR : SystemState.onlyObjectsSchedulerDiffer (removeFromNotificationWaitQueue s t) s := by
      rw [e]; rfl
    exact hL ((enqueueRunnableOnCore_onlyObjectsSchedulerDiffer _ _ _).trans
      ((hU _ _ _).trans hR)) h
  · unfold SeLe4n.Kernel.storeUnbindNotification
    exact hL ((hM _ _ _).trans (hU _ _ _)) h
  · rw [cancelDonationArmOnCore_of_codes s t hS' hO] at hOk
    unfold cancelBoundDonationOnCore at hOk
    split at hOk
    · rename_i scId _
      injection hOk with hOk; subst hOk
      have h1 := hS s scId
        (fun sc => { sc with boundThreadCode := 0, isActive := false, donationOrigin := none })
      generalize s.updateSchedContext scId _ = s1 at h1 ⊢
      let c := determineTargetCore s t
      let sch := s1.scheduler.setReplenishQueueOnCore c
        (ReplenishQueue.remove (s1.scheduler.replenishQueueOnCore c) scId)
      have h2 : SystemState.onlyObjectsSchedulerDiffer { s1 with scheduler := sch } s :=
        SystemState.onlyObjectsSchedulerDiffer.trans
          (show SystemState.onlyObjectsSchedulerDiffer { s1 with scheduler := sch } s1 from rfl) h1
      exact hL ((hK _ _ _).trans ((hU _ _ _).trans h2)) h
    · cases hOk

theorem finaliseFinalObject_cdt (target : Nat) (st : SystemState) :
    (finaliseFinalObject target st).cdt = st.cdt :=
  (finaliseFinalObject_onlyObjectsSchedulerCoreHoldsDiffer target st).cdt

/-- **The finalisation keeps the teardown's well-formedness and shrinks no
root.** -/
theorem finaliseFinalObject_preserves_teardownWellFormed (target : Nat) (st : SystemState)
    (hW : teardownWellFormed st) :
    teardownWellFormed (finaliseFinalObject target st) ∧
      vspaceRootsShrink st (finaliseFinalObject target st) :=
  (finaliseFinalObject_frame target st hW.1).preserves_teardownWellFormed hW

/-- **The retire after the finalisation keeps the teardown's well-formedness and
only shrinks the roots**: the finalisation's, then the retire's
(`retireFinalObject_preserves_teardownWellFormed`). -/
theorem retireFinalisedObject_preserves_teardownWellFormed (ec : Concurrency.CoreId)
    (target recorder : Nat) (st : SystemState) (hW : teardownWellFormed st) :
    teardownWellFormed (retireFinalisedObject ec target recorder st) ∧
      vspaceRootsShrink st (retireFinalisedObject ec target recorder st) := by
  obtain ⟨h1, s1⟩ := finaliseFinalObject_preserves_teardownWellFormed target st hW
  obtain ⟨h2, s2⟩ := retireFinalObject_preserves_teardownWellFormed ec target recorder _ h1
  exact ⟨h2, s1.trans s2⟩

end SeLe4n.Kernel
