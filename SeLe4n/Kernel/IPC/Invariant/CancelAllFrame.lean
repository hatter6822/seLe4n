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
* **The write frame** (`FinaliseFrame`): only the object store and the
  scheduler change, the object table stays well formed, and every key either
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

/-- **A property every cancel and the unbind keep holds after the
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
    (hUnbind : ∀ (notificationId : SeLe4n.ObjId) (s : SystemState) (n : Notification)
      (t : SeLe4n.ThreadId), P s →
      s.getNotification? notificationId = some n → n.boundTCB = some t →
      boundNotificationCodeOf s t = notificationId.val + 1 →
      unbindNotificationInPlace s t = true →
      P (storeUnbindNotification s t notificationId))
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
    · exact h
  · exact h

-- ============================================================================
-- §2  The write frame
-- ============================================================================

/-- **An object a finalisation may write**: a thread, an endpoint or a
notification. -/
def finaliseWritable (o : KernelObject) : Prop :=
  o.objectType = .tcb ∨ o.objectType = .endpoint ∨ o.objectType = .notification

theorem finaliseWritable.untyped {o : KernelObject} (h : finaliseWritable o) :
    o.untyped? = none := by
  cases o <;> simp_all [finaliseWritable, KernelObject.objectType, KernelObject.untyped?]

theorem finaliseWritable.not_cnode {o : KernelObject} (h : finaliseWritable o) :
    o.objectType ≠ .cnode := by
  rcases h with h | h | h <;> rw [h] <;> decide

theorem finaliseWritable.not_vspaceRoot {o : KernelObject} (h : finaliseWritable o) :
    o.objectType ≠ .vspaceRoot := by
  rcases h with h | h | h <;> rw [h] <;> decide

theorem finaliseWritable_tcb (t : TCB) : finaliseWritable (.tcb t) := Or.inl rfl

/-- **What a finalisation writes, key by key**: each key keeps its object, or
holds a thread, an endpoint or a notification before and after, of the same
kind and with the same capability slots. -/
def finaliseWrite (st st' : SystemState) : Prop :=
  ∀ oid : SeLe4n.ObjId, st'.objects[oid]? = st.objects[oid]? ∨
    ∃ pre post : KernelObject, st.objects[oid]? = some pre ∧ st'.objects[oid]? = some post ∧
      post.objectType = pre.objectType ∧ post.tcbSlots = pre.tcbSlots ∧ finaliseWritable pre

namespace finaliseWrite

theorem refl (st : SystemState) : finaliseWrite st st := fun _ => Or.inl rfl

theorem trans {a b c : SystemState} (h₁ : finaliseWrite a b) (h₂ : finaliseWrite b c) :
    finaliseWrite a c := by
  intro oid
  rcases h₁ oid with e₁ | ⟨p₁, q₁, hp₁, hq₁, ht₁, hs₁, hw₁⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, ht₂, hs₂, hw₂⟩
    · exact Or.inl (e₂.trans e₁)
    · exact Or.inr ⟨p₂, q₂, e₁ ▸ hp₂, hq₂, ht₂, hs₂, hw₂⟩
  · rcases h₂ oid with e₂ | ⟨p₂, q₂, hp₂, hq₂, ht₂, hs₂, hw₂⟩
    · exact Or.inr ⟨p₁, q₁, hp₁, e₂.trans hq₁, ht₁, hs₁, hw₁⟩
    · rw [hq₁] at hp₂
      cases hp₂
      exact Or.inr ⟨p₁, q₂, hp₁, hq₂, ht₂.trans ht₁, hs₂.trans hs₁, hw₁⟩

/-- A finalisation write is kind-preserving: what it writes is no CNode, and
keeps its untyped record (none). -/
theorem kind {st st' : SystemState} (h : finaliseWrite st st') : kindPreservingWrite st st' := by
  intro oid
  rcases h oid with e | ⟨pre, post, hp, hq, ht, hs, hw⟩
  · exact Or.inl e
  · have hw' : finaliseWritable post := by unfold finaliseWritable; rw [ht]; exact hw
    exact Or.inr ⟨pre, post, hp, hq, ht, ht ▸ hw.not_cnode, hs, by
      rw [hw.untyped, hw'.untyped]⟩

/-- An object the finalisation may not write is kept where it is. -/
theorem keeps {st st' : SystemState} (h : finaliseWrite st st') {oid : SeLe4n.ObjId}
    {o : KernelObject} (hO : st.objects[oid]? = some o) (hN : ¬ finaliseWritable o) :
    st'.objects[oid]? = some o := by
  rcases h oid with e | ⟨pre, post, hp, -, -, -, hw⟩
  · rw [e]; exact hO
  · rw [hO] at hp; cases hp; exact absurd hw hN

/-- …and an object present after a finalisation that it may not write was there
before it. -/
theorem keeps' {st st' : SystemState} (h : finaliseWrite st st') {oid : SeLe4n.ObjId}
    {o : KernelObject} (hO : st'.objects[oid]? = some o) (hN : ¬ finaliseWritable o) :
    st.objects[oid]? = some o := by
  rcases h oid with e | ⟨pre, post, hp, hq, ht, -, hw⟩
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
      ¬ finaliseWritable o → st'.objects[oid]? = some o) :
    finaliseWrite st st' := by
  intro oid
  rcases hK oid with e | ⟨pre, post, hp, hq, ht, -, hs, -⟩
  · exact Or.inl e
  · by_cases hw : finaliseWritable pre
    · exact Or.inr ⟨pre, post, hp, hq, ht, hs, hw⟩
    · exact Or.inl ((hT oid pre hp hw).trans hp.symm)

/-- **A store of a finalisation-writable object's like at its own key.** -/
theorem of_insert {st st' : SystemState} {k : SeLe4n.ObjId} {o o' : KernelObject}
    (hInv : st.objects.invExt) (hO : st'.objects = st.objects.insert k o')
    (hPre : st.objects[k]? = some o) (hW : finaliseWritable o)
    (hT : o'.objectType = o.objectType) (hS : o'.tcbSlots = o.tcbSlots) :
    finaliseWrite st st' := by
  intro oid
  rw [hO]
  by_cases e : oid = k
  · subst e
    exact Or.inr ⟨o, o', hPre, RobinHood.RHTable.getElem?_insert_self st.objects oid o' hInv,
      hT, hS, hW⟩
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
    refine Or.inr ⟨.tcb t, .tcb t', ht, ht', rfl, ?_, finaliseWritable_tcb t⟩
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
  · exact Or.inr ⟨.notification n, .notification n', hn, hn', rfl, rfl, Or.inr (Or.inr rfl)⟩
  · exact Or.inr ⟨.tcb t, .tcb _, ht, ht', rfl, rfl, finaliseWritable_tcb t⟩

end finaliseWrite

/-- **What a finalisation's step leaves**: only the object store and the
scheduler changed, the object table well formed, and a finalisation write. -/
structure FinaliseFrame (st st' : SystemState) : Prop where
  rest : SystemState.onlyObjectsSchedulerDiffer st' st
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

theorem scheduler_or {st st' : SystemState} (h : FinaliseFrame st st') :
    st' = { st with objects := st'.objects, scheduler := st'.scheduler } := h.rest

theorem asidTable {st st' : SystemState} (h : FinaliseFrame st st') :
    st'.asidTable = st.asidTable := by
  have e := congrArg SystemState.asidTable h.rest; exact e

theorem cdt {st st' : SystemState} (h : FinaliseFrame st st') : st'.cdt = st.cdt := by
  have e := congrArg SystemState.cdt h.rest; exact e

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
  rcases h.write r.cnode with e | ⟨pre, post, hp, hq, ht, hs, hw⟩
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
    rcases hf o with e | ⟨hT, hS, hW⟩
    · rw [e]
      intro oid
      left
      show (st.objects.insert k o)[oid]? = st.objects[oid]?
      by_cases h : oid = k
      · subst h; exact (RobinHood.RHTable.getElem?_insert_self st.objects oid o hInv).trans hG.symm
      · exact RobinHood.RHTable.getElem?_insert_ne st.objects k oid o
          (by intro h'; exact h (eq_of_beq h').symm) hInv
    · exact finaliseWrite.of_insert hInv rfl hG hW hT hS

/-- The wake: a run-queue insert and the `.ready` mark, on threads only. -/
theorem enqueueRunnableOnCore (st : SystemState) (c : Concurrency.CoreId) (t : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) : FinaliseFrame st (SeLe4n.Kernel.enqueueRunnableOnCore st c t) := by
  refine ⟨enqueueRunnableOnCore_onlyObjectsSchedulerDiffer st c t,
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
        split <;> exact ⟨rfl, rfl, Or.inr (Or.inl rfl)⟩
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
    | notification m => exact Or.inr ⟨rfl, rfl, Or.inr (Or.inr rfl)⟩
    | _ => exact Or.inl rfl))

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
    target st (.refl hInv)

/-- **The finalisation writes only the object store and the scheduler**, on any
state. -/
theorem finaliseFinalObject_onlyObjectsSchedulerDiffer (target : Nat) (st : SystemState) :
    SystemState.onlyObjectsSchedulerDiffer (finaliseFinalObject target st) st := by
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
  refine finaliseFinalObject_closed (fun s => SystemState.onlyObjectsSchedulerDiffer s st)
    (fun _ _ s _ t _ h _ _ _ _ => ?_) (fun _ s _ t tcb h _ _ _ hC => ?_)
    (fun _ s _ t h _ _ _ _ => ?_) target st (.refl st)
  · unfold storeEndpointWaiterCancelled wakeCancelledWaiter
    exact (enqueueRunnableOnCore_onlyObjectsSchedulerDiffer _ _ _).trans
      ((hU _ _ _).trans ((hP _ _ _ _ _).trans h))
  · have hEq : Lifecycle.Suspend.cancelIpcBlocking s t tcb =
        Lifecycle.Suspend.restoreToReadyCancelled (removeFromNotificationWaitQueue s t) t := by
      unfold Lifecycle.Suspend.cancelIpcBlocking; rw [notificationWaiterCancellable_blocked hC]
    unfold wakeCancelledWaiter
    rw [hEq]
    obtain ⟨objs, e⟩ := removeFromNotificationWaitQueue_eq_objects s t
    have hR : SystemState.onlyObjectsSchedulerDiffer (removeFromNotificationWaitQueue s t) s := by
      rw [e]; rfl
    exact (enqueueRunnableOnCore_onlyObjectsSchedulerDiffer _ _ _).trans
      ((hU _ _ _).trans (hR.trans h))
  · unfold SeLe4n.Kernel.storeUnbindNotification
    exact (hM _ _ _).trans ((hU _ _ _).trans h)

theorem finaliseFinalObject_cdt (target : Nat) (st : SystemState) :
    (finaliseFinalObject target st).cdt = st.cdt := by
  have e := congrArg SystemState.cdt (finaliseFinalObject_onlyObjectsSchedulerDiffer target st)
  exact e

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
