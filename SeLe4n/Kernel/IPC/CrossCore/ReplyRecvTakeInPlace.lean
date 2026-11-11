-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCapsDelivered
import SeLe4n.Kernel.IPC.CrossCore.EndpointReceiveInPlace

/-!
# The reply-receive whose receive leg meets a waiting sender, in place

seL4-MCS's `handleReplyRecv` runs `doReplyTransfer` and then `receiveIPC`; when
a sender is already queued on the endpoint, `receiveIPC` takes it at once: the
sender is dequeued, made ready and woken, and its message delivered to the
server.  This is the ordinary server loop under load.  The specification runs
the same order (`endpointReplyRecvAnsweringOnCore`): the reply leg, the
reply leg's transfer, then the receive leg's take (`receiveTake_inPlace`).

The take's guard reads the sender's message words (its badge, its fault flag),
which the run-queue frame of the reply leg erases (`TCB.withoutRunLinks`).  The
reply leg writes no such word, so this module states that frame
(`SystemState.objectsKeepSendCaps`), carries the take's guard across the reply
leg and its transfer (`receiveTakesInPlace_of_frame`), commutes the answered
caller's held message past the take (`storePopHead_msg`), and proves the
in-place performers equal to the specification
(`replyRecvOnCore_take_delivered`, `replyRecvOnCore_take_capsDelivered`).
-/

namespace SeLe4n.Model

/-- The four words a blocked sender's capability fills in (`TCB.setSendCap`),
the ones `TCB.withoutRunLinks` erases. -/
@[inline] def TCB.sendCapWords (t : TCB) : UInt64 × Bool × Bool × Bool :=
  (t.ipcBadge, t.ipcBadged, t.ipcCanGrant, t.ipcFaultSend)

/-- A thread's send-capability words; none for any other object. -/
def KernelObject.sendCapWords : KernelObject → Option (UInt64 × Bool × Bool × Bool)
  | .tcb t => some t.sendCapWords
  | _ => none

/-- An object rewrite that keeps every thread's send-capability words. -/
def KeepsSendCaps (F : KernelObject → KernelObject) : Prop :=
  ∀ o, (F o).sendCapWords = o.sendCapWords

/-- A TCB rewrite that keeps the send-capability words. -/
def TcbKeepsSendCaps (g : TCB → TCB) : Prop := ∀ t, (g t).sendCapWords = t.sendCapWords

theorem KeepsSendCaps.mapTcb {g : TCB → TCB} (hg : TcbKeepsSendCaps g) :
    KeepsSendCaps (KernelObject.mapTcb g) := by
  intro o; cases o <;> simp [KernelObject.mapTcb, KernelObject.sendCapWords, hg _]

end SeLe4n.Model

namespace SeLe4n.Model.SystemState

open SeLe4n.Kernel SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency (CoreId)

/-- `st'` holds `st`'s send-capability words at every key. -/
def objectsKeepSendCaps (st' st : SystemState) : Prop :=
  ∀ x : SeLe4n.ObjId,
    (st'.objects[x]?).map KernelObject.sendCapWords = (st.objects[x]?).map KernelObject.sendCapWords

namespace objectsKeepSendCaps

theorem refl (st : SystemState) : objectsKeepSendCaps st st := fun _ => rfl

theorem trans {a b c : SystemState} (h₂ : objectsKeepSendCaps c b) (h₁ : objectsKeepSendCaps b a) :
    objectsKeepSendCaps c a := fun x => (h₂ x).trans (h₁ x)

theorem of_objects_eq {a b : SystemState} (h : b.objects = a.objects) : objectsKeepSendCaps b a :=
  fun x => by rw [h]

theorem congr {a a' b b' : SystemState} (ha : a'.objects = a.objects)
    (hb : b'.objects = b.objects) (h : objectsKeepSendCaps a b) : objectsKeepSendCaps a' b' :=
  fun x => by rw [ha, hb]; exact h x

end objectsKeepSendCaps

theorem mapValueAt_keepsSendCaps (st : SystemState) (k : SeLe4n.ObjId)
    {F : KernelObject → KernelObject} (hF : KeepsSendCaps F) :
    objectsKeepSendCaps { st with objects := st.objects.mapValueAt k F } st := by
  intro x
  show ((st.objects.mapValueAt k F)[x]?).map _ = _
  simp only [RHTable_getElem?_eq_get?]
  rw [RHTable.get?_mapValueAt]
  split
  · cases st.objects.get? x with
    | none => rfl
    | some o => simp only [Option.map_some, hF o]
  · rfl

theorem mapTcbInPlace_keepsSendCaps (st : SystemState) (t : SeLe4n.ThreadId) {g : TCB → TCB}
    (hg : TcbKeepsSendCaps g) : objectsKeepSendCaps (st.mapTcbInPlace t g) st :=
  mapValueAt_keepsSendCaps st t.toObjId (KeepsSendCaps.mapTcb hg)

theorem updateTcbAtCode_keepsSendCaps (st : SystemState) (k : Nat) {g : TCB → TCB}
    (hg : TcbKeepsSendCaps g) : objectsKeepSendCaps (st.updateTcbAtCode k g) st := by
  unfold updateTcbAtCode; split
  · exact .refl _
  · exact mapTcbInPlace_keepsSendCaps _ _ hg

theorem updateTcb_keepsSendCaps (st : SystemState) (t : SeLe4n.ThreadId) {g : TCB → TCB}
    (hg : TcbKeepsSendCaps g) (hNo : st.objects.noResizeDue) :
    objectsKeepSendCaps (st.updateTcb t g) st := by
  rw [updateTcb_eq_mapTcbInPlace _ _ _ hNo]; exact mapTcbInPlace_keepsSendCaps _ _ hg

theorem modifyObject_keepsSendCaps (st : SystemState) (k : SeLe4n.ObjId)
    {F : KernelObject → KernelObject} (hF : KeepsSendCaps F) (hNo : st.objects.noResizeDue) :
    objectsKeepSendCaps (st.modifyObject k F) st := by
  rw [modifyObject_eq_mapValueAt _ _ _ hNo]; exact mapValueAt_keepsSendCaps st k hF

theorem runAppendLinks_keepsSendCaps (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : objectsKeepSendCaps (st.runAppendLinks c t p) st := by
  unfold runAppendLinks
  exact .trans (updateTcbAtCode_keepsSendCaps _ _ (fun _ => rfl))
    (.trans (updateTcbAtCode_keepsSendCaps _ _ (fun _ => rfl))
      (mapTcbInPlace_keepsSendCaps _ _ (fun _ => rfl)))

theorem runEnqueueAdmitted_keepsSendCaps (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (p : SeLe4n.Priority) : objectsKeepSendCaps (st.runEnqueueAdmitted c t p) st := by
  have h := runEnqueueAdmitted_objects st c t p
  split at h
  · exact .of_objects_eq h
  · exact .congr h rfl (runAppendLinks_keepsSendCaps st c t p)

theorem unlinkReplyWaiter_keepsSendCaps (st : SystemState) (w s : SeLe4n.ThreadId) :
    objectsKeepSendCaps (st.unlinkReplyWaiter w s) st := by
  unfold unlinkReplyWaiter; dsimp only
  exact .trans (mapTcbInPlace_keepsSendCaps _ _ (fun _ => rfl))
    (.trans (mapTcbInPlace_keepsSendCaps _ _ (fun _ => rfl))
      (.trans (updateTcbAtCode_keepsSendCaps _ _ (fun _ => rfl))
        (updateTcbAtCode_keepsSendCaps _ _ (fun _ => rfl))))

end SeLe4n.Model.SystemState

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-! ### The reply leg keeps every sender's message words -/

theorem enqueueRunnableOnCore_keepsSendCaps (st : SystemState) (c : CoreId) (t : SeLe4n.ThreadId)
    (hNo : st.objects.noResizeDue) :
    SystemState.objectsKeepSendCaps (enqueueRunnableOnCore st c t) st := by
  rw [enqueueRunnableOnCore_eq_impl]
  unfold enqueueRunnableOnCoreImpl
  split
  · dsimp only
    split
    · exact .refl _
    · exact .congr rfl rfl ((SystemState.runEnqueueAdmitted_keepsSendCaps _ c t _).trans
        (SystemState.modifyObject_keepsSendCaps _ _
          (fun o => by cases o <;> rfl) hNo))
  · exact .refl _

/-- **The reply's writes keep every thread's send-capability words**: they
write the caller's state, run-queue and reply-waiter links and the reply
object, never a sender's badge, grant or fault flag. -/
theorem storeReplyRendezvousReady_keepsSendCaps (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    SystemState.objectsKeepSendCaps (storeReplyRendezvousReady st c server rid) st := by
  unfold storeReplyRendezvousReady storeReplyLegReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _
    (determineTargetCore (st.updateTcb c receiverReady) c) c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  refine (SystemState.unlinkReplyWaiter_keepsSendCaps _ c server).trans
    ((SystemState.updateTcb_keepsSendCaps _ c ?_ hNo3).trans
      ((SystemState.modifyObject_keepsSendCaps _ _ ?_ hNo2).trans
        ((enqueueRunnableOnCore_keepsSendCaps _ _ c hNo1).trans
          (SystemState.updateTcb_keepsSendCaps _ c ?_ hNo))))
  · intro _; rfl
  · intro o; cases o <;> rfl
  · intro _; rfl

/-- **What a take reads of its sender, kept**: the queue successor, the IPC
state, the saved registers and the four send-capability words. -/
structure SenderWordsKept (t' t : TCB) : Prop where
  queueNext : t'.queueNextCode = t.queueNextCode
  ipcState : t'.ipcState = t.ipcState
  regs : t'.registerContext = t.registerContext
  badge : t'.ipcBadge = t.ipcBadge
  badged : t'.ipcBadged = t.ipcBadged
  faultSend : t'.ipcFaultSend = t.ipcFaultSend
  canGrant : t'.ipcCanGrant = t.ipcCanGrant

theorem SenderWordsKept.trans {a b c : TCB} (h₂ : SenderWordsKept c b) (h₁ : SenderWordsKept b a) :
    SenderWordsKept c a :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2, h₂.3.trans h₁.3, h₂.4.trans h₁.4, h₂.5.trans h₁.5,
    h₂.6.trans h₁.6, h₂.7.trans h₁.7⟩

/-- Two TCBs that agree off the run-queue links and on their send-capability
words keep every word a take reads. -/
theorem SenderWordsKept.of_withoutRunLinks {t t' : TCB}
    (h : t'.withoutRunLinks = t.withoutRunLinks) (hw : t'.sendCapWords = t.sendCapWords) :
    SenderWordsKept t' t := by
  have e := TCB.eq_withRunLinks_of_withoutRunLinks_eq h
  simp only [TCB.sendCapWords, Prod.mk.injEq] at hw
  obtain ⟨h1, h2, h3, h4⟩ := hw
  rw [e]
  exact ⟨rfl, rfl, rfl, h1, h2, h4, h3⟩

/-- Two TCBs that agree off their derivation links keep every word a take
reads. -/
theorem SenderWordsKept.of_withoutLinks {t t' : TCB} (h : t'.withoutLinks = t.withoutLinks) :
    SenderWordsKept t' t := by
  have f : ∀ {α : Type} (g : TCB → α), (∀ u : TCB, g u.withoutLinks = g u) → g t' = g t :=
    fun g hg => by rw [← hg t', ← hg t, h]
  exact ⟨f TCB.queueNextCode (fun _ => rfl), f TCB.ipcState (fun _ => rfl),
    f TCB.registerContext (fun _ => rfl), f TCB.ipcBadge (fun _ => rfl),
    f TCB.ipcBadged (fun _ => rfl), f TCB.ipcFaultSend (fun _ => rfl),
    f TCB.ipcCanGrant (fun _ => rfl)⟩

/-! ### The take's guard across a frame -/

/-- **The take's in-place guard carries over** to a state with every key found
where it was, every key holding an object of the same kind and every thread
still a thread, the sender's queue successor and state as they were. -/
theorem receiveTakesInPlace_of_frame {s s' : SystemState} (epId : SeLe4n.ObjId)
    (tid sid : SeLe4n.ThreadId) (t t' : TCB)
    (hK : s'.objectsKeepFinds s)
    (hV : ∀ x, s'.getObjectType? x = s.getObjectType? x)
    (hTcb : ∀ p : SeLe4n.ThreadId, (s.getTcb? p).isSome = true → (s'.getTcb? p).isSome = true)
    (hQ : t'.queueNextCode = t.queueNextCode) (hIpc : t'.ipcState = t.ipcState)
    (h : receiveTakesInPlace s epId tid sid t = true) :
    receiveTakesInPlace s' epId tid sid t' = true := by
  have hS : ∀ {id ty}, storeLeavesIndexAndTypes s id ty = true →
      storeLeavesIndexAndTypes s' id ty = true :=
    fun h => storeLeavesIndexAndTypes_of_frame hV h
  have hQ' : t'.queueNext = t.queueNext := by simp only [TCB.queueNext, hQ]
  unfold receiveTakesInPlace sendWakesInPlace at h ⊢
  rw [hQ', hIpc]
  simp only [Bool.and_eq_true] at h ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, b1⟩, b2⟩, b3⟩, b4⟩, b5⟩, b6⟩, b7⟩ := h
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, hS a2⟩, (hK _).trans a3⟩, hS a4⟩, (hK _).trans a5⟩, ?_⟩, b1⟩, b2⟩, b3⟩,
    hS b4⟩, (hK _).trans b5⟩, hTcb _ b6⟩, b7⟩
  revert a6
  cases t.queueNext with
  | none => exact id
  | some n =>
    simp only [Bool.and_eq_true]
    rintro ⟨⟨⟨⟨c1, c2⟩, c3⟩, c4⟩, c5⟩
    exact ⟨⟨⟨⟨c1, c2⟩, hS c3⟩, (hK _).trans c4⟩, hTcb _ c5⟩

/-- **The take's guard across the reply leg**: on the state the reply leaves
(the caller `c` woken holding `msg`, its reply object consumed), the endpoint is
as it was, the sender `s` is a thread keeping every word the take reads, and
the take's in-place guard, read on the pre-state, still holds. -/
theorem storeReplyRendezvous_takeGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hG : receiveTakesInPlace st epId tid s sTcb = true) :
    (storeReplyRendezvous st c tid rid msg).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (storeReplyRendezvous st c tid rid msg).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        receiveTakesInPlace (storeReplyRendezvous st c tid rid msg) epId tid s sTcb1 = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hSc' : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hSr : s.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hS; cases hS
  have hKS := storeReplyRendezvousReady_keepsSendCaps st c tid rid hNo
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
  generalize hS1 : storeReplyRendezvousReady st c tid rid = S1 at hKS
  have hAg := fun x hx hy => hS1 ▸ storeReplyRendezvousReady_agree st c tid rid ct hNo hTc hFC x hx hy
  have hHold : ∀ x, x ≠ c.toObjId →
      (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = S1.objects[x]? := fun x hx => by
    rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyRendezvousReady_keepsFinds st c tid rid hNo hFC
  obtain ⟨tc1, htc1, -⟩ := hS1 ▸ storeReplyRendezvousReady_caller st c tid rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyRendezvousReady_reply st c tid rid ct rp hNo hTc hFC hRp hRc
  have hAt : ∀ x, (x = c.toObjId ∧
        ∃ t, (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = some (.tcb t)) ∨
      (x = rid.toObjId ∧
        (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = some (.reply rp.consumed)) ∨
      ((S1.mapTcbInPlace c (holdMessage msg)).objects[x]?).map KernelObject.withoutRunLinks =
        (st.objects[x]?).map KernelObject.withoutRunLinks := by
    intro x
    by_cases hxc : x = c.toObjId
    · subst hxc
      left
      refine ⟨rfl, holdMessage msg tc1, ?_⟩
      rw [SystemState.objects_mapTcbInPlace, if_pos (beq_self_eq_true _), htc1]; rfl
    · by_cases hxr : x = rid.toObjId
      · subst hxr; right; left; rw [hHold _ hxc]; exact ⟨rfl, hR1⟩
      · right; right; rw [hHold _ hxc]; exact hAg x hxc hxr
  have hV : ∀ x, (S1.mapTcbInPlace c (holdMessage msg)).getObjectType? x = st.getObjectType? x := by
    intro x
    rcases hAt x with ⟨e, t, h⟩ | ⟨e, h⟩ | h
    · subst e; unfold SystemState.getObjectType?
      rw [h, (SystemState.getTcb?_eq_some_iff _ _ _).mp hTc]; rfl
    · subst e; unfold SystemState.getObjectType?; rw [h, hRp]; rfl
    · exact getObjectType?_of_view h
  have hKF : (S1.mapTcbInPlace c (holdMessage msg)).objectsKeepFinds st :=
    (SystemState.mapTcbInPlace_keepsFinds _ _ _).trans hK
  have hTcb : ∀ p : SeLe4n.ThreadId, (st.getTcb? p).isSome = true →
      ((S1.mapTcbInPlace c (holdMessage msg)).getTcb? p).isSome = true := by
    intro p hp
    obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
    have h1 := (SystemState.getTcb?_eq_some_iff _ _ _).mp ht
    rcases hAt p.toObjId with ⟨_, t', h⟩ | ⟨e, _⟩ | h
    · exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h⟩
    · rw [e, hRp] at h1; cases h1
    · obtain ⟨t', h', _⟩ := agreeAt_tcb h h1
      exact Option.isSome_iff_exists.mpr ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h'⟩
  obtain ⟨sTcb1, hS1o, e1⟩ := agreeAt_tcb (hAg _ hSc' hSr) hS
  have hw : sTcb1.sendCapWords = sTcb.sendCapWords := by
    have k := hKS s.toObjId
    rw [hS1o, hS] at k
    simpa [KernelObject.sendCapWords] using k
  have hKept := SenderWordsKept.of_withoutRunLinks e1 hw
  refine ⟨by rw [hHold _ hEc]; exact agreeAt_of_not_tcb (hAg _ hEc hEr) (fun _ e => by cases e) hE,
    sTcb1, by rw [hHold _ hSc']; exact hS1o, hKept, ?_⟩
  exact receiveTakesInPlace_of_frame epId tid s sTcb sTcb1 hKF hV hTcb hKept.queueNext
    hKept.ipcState hG

/-! ### The answered caller's held message, past the take -/

/-- **A pop commutes with a message-slot write**: it rewrites the endpoint's
queue ends and two threads' queue links, never a message slot. -/
theorem storePopHead_msg (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
    (μ : Option IpcMessage → Option IpcMessage) (π : Nat → Nat) (st : SystemState)
    (epId : SeLe4n.ObjId) (isReceiveQ : Bool) (head : SeLe4n.ThreadId)
    (next : Option SeLe4n.ThreadId) (hNo : st.objects.noResizeDue) :
    storePopHead (st.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) epId isReceiveQ head next =
      (storePopHead st epId isReceiveQ head next).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  have hF : ∀ o, popEndpoint isReceiveQ (ThreadId.optCode next)
      (KernelObject.mapTcb (TCB.withMessageSlots ρ μ π) o) =
      KernelObject.mapTcb (TCB.withMessageSlots ρ μ π)
        (popEndpoint isReceiveQ (ThreadId.optCode next) o) := fun o => by
    cases o <;> try rfl
    generalize ThreadId.optCode next = k
    cases isReceiveQ <;> cases k <;> rfl
  have h1 := modifyObject_noResizeDue st epId (popEndpoint isReceiveQ (ThreadId.optCode next)) hNo
  unfold storePopHead
  cases next with
  | none =>
    dsimp only
    rw [modifyObject_msg r ρ μ st epId _ hNo hF]
    exact updateTcb_msg r ρ μ π _ head tcbOffQueue h1 (fun _ _ => rfl)
  | some n =>
    dsimp only
    rw [modifyObject_msg r ρ μ st epId _ hNo hF,
      updateTcb_msg r ρ μ π _ n tcbAsQueueHead h1 (fun _ _ => rfl)]
    exact updateTcb_msg r ρ μ π _ head tcbOffQueue (updateTcb_noResizeDue _ _ _ h1) (fun _ _ => rfl)

/-- A frame write at one thread commutes with an in-place TCB write at another,
its fallback holding a message at the first. -/
theorem writeDeliveredFrameIfReady_mapTcbInPlace (X : SystemState) (c r : SeLe4n.ThreadId)
    (f : Architecture.SyscallReturnFrame) (g h : TCB → TCB) (hNe : c ≠ r) :
    writeDeliveredFrameIfReady (X.mapTcbInPlace r g) c f
        (fun _ => (X.mapTcbInPlace r g).mapTcbInPlace c h) =
      (writeDeliveredFrameIfReady X c f (fun _ => X.mapTcbInPlace c h)).mapTcbInPlace r g := by
  have hNe' : r.toObjId ≠ c.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  unfold writeDeliveredFrameIfReady
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe']
  cases X.getTcb? c with
  | none => rfl
  | some t =>
    dsimp only
    split
    · exact SystemState.mapTcbInPlace_swap X _ _ (fun h => absurd h hNe)
    · exact SystemState.mapTcbInPlace_swap X _ _ (fun h => absurd h hNe)

/-! ### The reply-receive whose receive leg takes a waiting sender -/

/-- **The reply-receive meeting a waiting sender, its reply leg transferring**:
under the reply's guard, a reply leg whose transfer answers `(summary, S2)` on
the state the reply leaves, and on `S2` a sender `s` at the head of the send
queue blocked by a routed capability-free send, not delivering a fault, whose
take writes only its slots, the composite is the reply's writes, the transfer,
the take (`receiveTake_inPlace`), the server's priority walk, the caller staged
with the transfer's report and the sender's completion staged. -/
theorem replyRecvOnCore_take_transfer (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true)
    (hH : ep.sendQ.head = some s)
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyTransferCaps st tid c grant (storeReplyRendezvous st c tid rid msg) =
      .ok (summary, S2))
    (hE2 : S2.objects[epId]? = some (.endpoint ep)) {sTcb2 : TCB}
    (hT2 : S2.objects[s.toObjId]? = some (.tcb sTcb2))
    (hG2 : receiveTakesInPlace S2 epId tid s sTcb2 = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
      sTcb2.registerContext 32 = .send capAddr mi)
    (hF : sTcb2.ipcFaultSend = false) :
    endpointReplyRecvOnCore epId tid rid c msg grant core st =
      .ok ({ results := #[] }, Architecture.stageWokenSendCompletion
        (Architecture.stageDeliveredMessage
          (PriorityInheritance.propagatePipChainCrossCore
            ((wakeThread ((storePopHead S2 epId false s sTcb2.queueNext).updateTcb s
                receiverReady) s core).1.updateTcb tid
              (callReceiverTcb (blockedSenderMessage (storePopHead S2 epId false s sTcb2.queueNext)
                s sTcb2))) tid core).1 c summary.capInfo) (some s)) := by
  obtain ⟨hEq, hHead⟩ := replyOnCore_inPlace st tid c tid ct ep0 rid msg core hSz hT hIpc hRO hG
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRec : recordedReplyServer? st c = some tid := by
    simp only [recordedReplyServer?, hTc, hIpc]
  generalize hS1 : storeReplyRendezvous st c tid rid msg = S1 at hEq hHead hXf
  have hPop : replyRecvPopDonation rid c S1 = .ok (none, S1) := by
    unfold replyRecvPopDonation
    rw [replyFrameHeadHolder?_of_no_head _ _ hHead]
    simp only [popUnheldReplyHead_of_no_head _ _ _ _ hHead]
  have hXf' : replyRecvReplyTransfer none st tid c grant S1 = .ok (summary, S2) := hXf
  have hEp2 : S2.getEndpoint? epId = some ep := (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE2
  obtain ⟨hRecv, -, -⟩ := receiveTake_delivered S2 epId ep tid (some rid) core s sTcb2 capAddr mi
    hE2 hH hT2 hG2 hR hF
  have hNoCall := receiveTake_dequeuedNoCall S2 epId ep tid core s sTcb2
    (blockedSenderMessage (storePopHead S2 epId false s sTcb2.queueNext) s sTcb2) hE2 hH hT2 hG2
  unfold endpointReplyRecvOnCore endpointReplyRecvAnsweringOnCore
  simp only [hRec, Option.getD_some, hEq, hPop, hXf', hRecv, hEp2, Option.bind_some, hH]
  simp only [replyRecvPostReceiveDonation, hNoCall, Bool.false_eq_true, ↓reduceIte]
  simp [replyRecvAnswerCaller]

/-- The take's writes before the server's own frame: the sender popped, made
ready and woken, the server made ready, its priority walk, then the caller's
frame with the transfer's report (read from the server's saved registers `rf`)
and the sender's completion frame. -/
@[noinline] def replyRecvTakeLegs (capInfo : Nat) (Y : SystemState) (c tid s : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (nextCode : Nat) (core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) : SystemState :=
  let W := (wakeThread ((storePopHead Y epId false s (ThreadId.ofOptCode nextCode)).updateTcb s
    receiverReady) s core).1
  let Z := (PriorityInheritance.propagatePipChainCrossCore (W.updateTcb tid receiverReady) tid
    core).1
  Architecture.stageWokenSendCompletion (deliverReplyRecvCapsFrame capInfo Z c layout rf len badge)
    (some s)

/-- The server's own frame, its six words read from the sender's saved
registers before any write.  Out of line from the legs (`replyRecvTakeLegs`):
`rf` is the server's own register file, which the arm projects out of its TCB
and holds while it passes it on, so the arm releases it once the legs return and
this write finds it unshared and writes it in place rather than copying it. -/
@[noinline] def writeTakerFrame (X : SystemState) (tid : SeLe4n.ThreadId)
    (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  X.mapTcbInPlace tid (withFrameWords w0 w1 w2 w3 w4 w5)

theorem deliverReplyRecvCapsFrame_noResizeDue (capInfo : Nat) (Y : SystemState)
    (c : SeLe4n.ThreadId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) (hNo : Y.objects.noResizeDue) :
    (deliverReplyRecvCapsFrame capInfo Y c layout rf len badge).objects.noResizeDue := by
  unfold deliverReplyRecvCapsFrame writeDeliveredFrameIfReady holdReplyRecvBody
  split
  · split <;> exact hNo
  · exact hNo

theorem deliverReplyRecvCapsFrame_getTcb?_ne (capInfo : Nat) (Y : SystemState)
    (c t : SeLe4n.ThreadId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) (hNe : c.toObjId ≠ t.toObjId) :
    (deliverReplyRecvCapsFrame capInfo Y c layout rf len badge).getTcb? t = Y.getTcb? t := by
  unfold deliverReplyRecvCapsFrame writeDeliveredFrameIfReady holdReplyRecvBody
  split
  · split <;> exact SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe
  · rfl

theorem stageWokenSendCompletion_noResizeDue (X : SystemState) (s? : Option SeLe4n.ThreadId)
    (hNo : X.objects.noResizeDue) :
    (Architecture.stageWokenSendCompletion X s?).objects.noResizeDue := by
  unfold Architecture.stageWokenSendCompletion
  split
  · exact hNo
  · split
    · split
      · exact updateTcb_noResizeDue _ _ _ hNo
      · exact hNo
    · exact hNo

/-- **The take's tail stages the caller's held reply and the server's message
as frames**: on `Y` with the caller holding the reply (`S2`), where the take
runs in place for a sender blocked by a routed capability-free send, staging
the caller with the report, the woken sender's completion and the server's
message is the legs (`replyRecvTakeLegs`) and then the server's frame
(`writeTakerFrame`), its six words read from the sender's saved registers. -/
theorem replyRecvTakeFrame_staged (Y : SystemState) (c tid s : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (sTcb : TCB) (core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (capInfo : Nat) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hNo : Y.objects.noResizeDue) (hNe : tid ≠ c) (hSC : s ≠ c)
    (hSz4 : Architecture.regMessageLength layout len - 1 ≤ 4)
    (hE : (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })).objects[epId]? =
        some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })).objects[s.toObjId]? =
        some (.tcb sTcb))
    (hG : receiveTakesInPlace (Y.mapTcbInPlace c (holdMessage
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })) epId tid s sTcb
        = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    Architecture.stageDeliveredMessage (Architecture.stageWokenSendCompletion
        (Architecture.stageDeliveredMessage
          (PriorityInheritance.propagatePipChainCrossCore
            ((wakeThread ((storePopHead (Y.mapTcbInPlace c (holdMessage
                { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }))
                epId false s sTcb.queueNext).updateTcb s receiverReady) s core).1.updateTcb tid
              (callReceiverTcb (blockedSenderMessage (storePopHead (Y.mapTcbInPlace c (holdMessage
                { registers := Architecture.regReplyRecvBody layout rf len, badge := badge }))
                epId false s sTcb.queueNext) s sTcb))) tid core).1 c capInfo) (some s)) tid 0 =
      writeTakerFrame
        (replyRecvTakeLegs capInfo Y c tid s epId sTcb.queueNextCode core layout rf len badge) tid
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5 := by
  generalize hM : ({ registers := Architecture.regReplyRecvBody layout rf len, badge := badge } :
    IpcMessage) = m at hE hT hG
  generalize hS2 : Y.mapTcbInPlace c (holdMessage m) = S2 at hE hT hG
  have hG' := hG
  simp only [receiveTakesInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨hSG, _⟩, hRS⟩, hRN⟩, _⟩, _⟩, hRT⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨_, _⟩, _⟩, _⟩, hFH⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hRo := (SystemState.getTcb?_eq_some_iff _ _ _).mp hRTo
  have hNeER : epId ≠ tid.toObjId := fun h => by rw [h, hRo] at hE; cases hE
  have hNeSR : s.toObjId ≠ tid.toObjId := fun h =>
    hRS (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  have hNxR : ∀ n, sTcb.queueNext = some n → n.toObjId ≠ tid.toObjId := fun n hn h => by
    rw [hn] at hRN
    simp only [bne_iff_ne, ne_eq] at hRN
    exact hRN (SeLe4n.ThreadId.toObjId_injective _ _ h).symm
  obtain ⟨_, hFr⟩ := popHead_inPlace S2 epId false ep s sTcb hE
    (by simp only [Bool.false_eq_true, ↓reduceIte]; exact hH) hT hSG
  have hFH1 := (hFr.keepsFinds s.toObjId).trans hFH
  have hO1r := (hFr.other _ hNeER hNeSR hNxR).trans hRo
  have hT2s := updateTcb_getTcb?_self_of_findsInPlace receiverReady hFr.head_tcb hFH1
  have hA3 := enqueueRunnableOnCore_agree_of_findsInPlace
    ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady)
    (determineTargetCore ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady) s)
    s _ hT2s rfl (by rw [updateTcb_findsInPlace _ hFr.head_tcb hFH1]; exact hFH1)
  have hO2r := (updateTcb_get?_ne_of_findsInPlace receiverReady hFr.head_tcb hFH1 hNeSR).trans hO1r
  obtain ⟨rt3, hO3r, _⟩ := hA3.get_tcb hO2r
  have hW3r : (wakeThread ((storePopHead S2 epId false s sTcb.queueNext).updateTcb s receiverReady)
      s core).1.getTcb? tid = some rt3 := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hO3r
  have hMsg := (blockedSender_of_routedSend (storePopHead S2 epId false s sTcb.queueNext) s sTcb
    capAddr mi hR hF).2
  generalize blockedSenderMessage (storePopHead S2 epId false s sTcb.queueNext) s sTcb = msgS
    at hMsg
  subst hS2
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have hST : s ≠ tid := fun e => hRS e.symm
  have hNoPY := storePopHead_noResizeDue Y epId false s sTcb.queueNext hNo
  have hNoU := updateTcb_noResizeDue _ s receiverReady hNoPY
  have hNoWY := wakeThread_noResizeDue _ s core hNoU
  have hNoWr := updateTcb_noResizeDue _ tid receiverReady hNoWY
  have hNoZ := propagatePipChainCrossCore_noResizeDue _ tid core hNoWr
  have hNoZs : (SystemState.mapTcbInPlace (PriorityInheritance.propagatePipChainCrossCore
      ((wakeThread ((storePopHead Y epId false s sTcb.queueNext).updateTcb s receiverReady) s
        core).1.updateTcb tid receiverReady) tid core).1 tid (holdMessage msgS)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoZ
  have hNoD := deliverReplyRecvCapsFrame_noResizeDue capInfo _ c layout rf len badge hNoZ
  have hNoE := stageWokenSendCompletion_noResizeDue _ (some s) hNoD
  rw [storePopHead_msg c _ _ _ Y epId false s sTcb.queueNext hNo] at hW3r ⊢
  rw [updateTcb_msg c _ _ _ _ s receiverReady hNoPY (fun h => absurd h hSC)] at hW3r ⊢
  rw [wakeThread_msg c _ _ _ _ s core hNoU] at hW3r ⊢
  dsimp only at hW3r ⊢
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hCT] at hW3r
  unfold writeTakerFrame replyRecvTakeLegs
  dsimp only
  rw [← TCB.optCode_queueNext, SeLe4n.ThreadId.ofOptCode_optCode]
  generalize (wakeThread ((storePopHead Y epId false s sTcb.queueNext).updateTcb s receiverReady) s
    core).1 = W at hW3r hNoWY hNoWr hNoZ hNoZs hNoD hNoE ⊢
  have hNoWrc : ((W.updateTcb tid receiverReady).mapTcbInPlace c (holdMessage m)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoWr
  rw [updateTcb_msg c _ _ _ _ tid (callReceiverTcb msgS) hNoWY (fun h => absurd h hNe),
    SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, ← holdMessage_receiverReady,
    ← SystemState.mapTcbInPlace_mapTcbInPlace, ← SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY,
    SystemState.mapTcbInPlace_swap _ (holdMessage msgS) (holdMessage m)
      (fun h => absurd h (fun e => hNe e.symm)),
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoWrc,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoWr,
    SystemState.mapTcbInPlace_swap _ (holdMessage m) (holdMessage msgS) (fun h => absurd h hNe),
    stageDeliveredMessage_holdMessage_caps _ _ _ _ hNoZs
      (by rw [← hM, Architecture.regReplyRecvBody_size]; exact hSz4),
    writeDeliveredFrameIfReady_mapTcbInPlace _ c tid _ _ _ (fun e => hNe e.symm),
    ← hM, returnFrameOfMessage_regReplyRecvBody_caps]
  have hWr : (W.updateTcb tid receiverReady).getTcb? tid = some (receiverReady rt3) := by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hNoWY, SystemState.mapTcbInPlace_getTcb?_self,
      hW3r]; rfl
  obtain ⟨x, hX, hXs⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core hNoWr tid _ hWr
  generalize (PriorityInheritance.propagatePipChainCrossCore (W.updateTcb tid receiverReady) tid
    core).1 = Z at hX hNoZ hNoZs hNoD hNoE ⊢
  rw [show writeDeliveredFrameIfReady Z c (regReplyRecvFrameCaps layout rf len badge capInfo)
      (fun _ => Z.mapTcbInPlace c (holdMessage
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })) =
      deliverReplyRecvCapsFrame capInfo Z c layout rf len badge from rfl]
  have hDr := (deliverReplyRecvCapsFrame_getTcb?_ne capInfo Z c tid layout rf len badge hCT).trans hX
  generalize deliverReplyRecvCapsFrame capInfo Z c layout rf len badge = D at hDr hNoD hNoE ⊢
  have hEr := (stageWokenSendCompletion_getTcb?_ne D s tid hST hNoD).trans hDr
  have hSzS : msgS.registers.size ≤ 4 := by
    rw [hMsg]
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageWokenSendCompletion_msg D tid s _ _ _ hST hNoD,
    stageDeliveredMessage_holdMessage _ _ _ hNoE hSzS, hMsg,
    Architecture.returnFrameOfMessage_regMessageBody]
  unfold writeDeliveredFrameIfReady
  rw [hEr]
  dsimp only
  rw [if_pos (by rw [hXs]; rfl)]

theorem SenderWordsKept.ipcBadgeView {t' t : TCB} (h : SenderWordsKept t' t) :
    t'.ipcBadgeView = t.ipcBadgeView := by
  rw [TCB.ipcBadgeView_eq_opt, TCB.ipcBadgeView_eq_opt, h.badge, h.badged]

/-- **The reply-receive meeting a waiting sender, its reply transferring
nothing, delivered**: the reply's writes, the take, the server's priority walk,
then the caller's frame, the sender's completion and the server's frame, its six
words read from the sender's saved registers before any write. -/
@[noinline] def performReplyRecvTakeLegs (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  replyRecvTakeLegs 0 (storeReplyRendezvousReady st c tid rid) c tid s epId nextCode core layout
    rf len badge

/-- The inert take, the legs (`performReplyRecvTakeLegs`) and then the
server's frame (`writeTakerFrame`), each out of line so the arm releases the
server's register file between them. -/
@[inline] def performReplyRecvTakeDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) (w0 w1 w2 w3 w4 w5 : UInt64) : SystemState :=
  writeTakerFrame (performReplyRecvTakeLegs st c tid rid epId s nextCode core layout rf len badge)
    tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive meeting a waiting sender, its reply transferring
nothing, is the specification's**: under the reply's guard, a reply of at most
four words transferring no capability (`replyTransferInert`), and a sender `s`
at the head of the send queue blocked by a routed capability-free send, not
delivering a fault, whose take writes only its slots (every check read on the
pre-state), the checked arm's result is `performReplyRecvTakeDelivered`. -/
theorem replyRecvOnCore_take_delivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hSz4 : Architecture.regMessageLength layout len - 1 ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true) (hNe : tid ≠ c)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hInert : replyTransferInert st tid ct grant = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvTakeDelivered st c tid rid epId s sTcb.queueNextCode core layout rf
        len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5) := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.2
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hSz : ¬ (Architecture.regReplyRecvBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regReplyRecvBody_size]; unfold maxMessageRegisters; omega
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := storeReplyRendezvous_takeGuard st c tid rid
    { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } ct rp epId ep s
    sTcb hNo hT hFC hRp hE hS hSC hGt
  have hXf := replyTransferCaps_of_inert st tid c grant ct hTc hInert
    (storeReplyRendezvous st c tid rid
      { registers := Architecture.regReplyRecvBody layout rf len, badge := badge })
  have hR1 : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
      sTcb1.registerContext 32 = .send capAddr mi := by rw [hK.regs]; exact hR
  rw [replyRecvOnCore_take_transfer st epId tid c rid _ grant core ct ep0 ep s capAddr mi hSz hT
    hIpc hRO hG hH hXf hE1 hS1 hG1 hR1 (by rw [hK.faultSend]; exact hF)]
  dsimp only
  rw [CapTransferSummary.capInfo_empty]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hE1 hS1 hG1 ⊢
  rw [replyRecvTakeFrame_staged _ c tid s epId ep sTcb1 core layout rf len badge 0 capAddr mi
    (storeReplyRendezvousReady_noResizeDue st c tid rid hNo) hNe hSC hSz4 hE1 hH hS1 hG1 hR1
    (by rw [hK.faultSend]; exact hF), hK.queueNext, hK.regs, hK.ipcBadgeView]
  rfl

/-- **The take's guard across a capability transfer**: the transfer writes
CNode slots, derivation links and the receiver's IPC buffer, never an endpoint,
a sender's message words or a queue link, so the endpoint, the sender's words
and the take's in-place guard carry over (`transferFrame`). -/
theorem takeGuard_of_transferFrame {s' s : SystemState} (h : transferFrame s' s)
    {epId : SeLe4n.ObjId} {ep : Endpoint} {tid sid : SeLe4n.ThreadId} {sTcb : TCB}
    (hE : s.objects[epId]? = some (.endpoint ep))
    (hS : s.objects[sid.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace s epId tid sid sTcb = true) :
    s'.objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb', s'.objects[sid.toObjId]? = some (.tcb sTcb') ∧ SenderWordsKept sTcb' sTcb ∧
        receiveTakesInPlace s' epId tid sid sTcb' = true := by
  refine ⟨h.obj hE rfl (transferView_endpoint_back ep), ?_⟩
  obtain ⟨t', h1, e⟩ := h.tcb hS
  have hK := SenderWordsKept.of_withoutLinks e
  refine ⟨t', h1, hK, receiveTakesInPlace_of_frame epId tid sid sTcb t' h.2.2.1
    (getObjectType?_of_transferFrame h) ?_ hK.queueNext hK.ipcState hG⟩
  intro p hp
  have e := h.getTcb? p
  revert hp e
  cases s.getTcb? p <;> cases s'.getTcb? p <;> simp

/-- **The reply-receive meeting a waiting sender, its reply leg transferring,
delivered**: the reply's writes, the transfer in place on no endpoint, the take,
the server's priority walk, then the caller's frame with the transfer's report,
the sender's completion and the server's frame.  The replier and the caller
enter as the words the transfer reads of them, the sender as its successor and
the six words of its frame, all read before the reply's writes. -/
@[noinline] def performReplyRecvTakeCapsLegs (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  let X := storeReplyRendezvousReady st c tid rid
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    replyRecvTakeLegs (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X)
      c tid s epId nextCode core layout rf len badge

/-- The installing take, its legs (`performReplyRecvTakeCapsLegs`) and then the
server's frame (`writeTakerFrame`), each out of line so the arm releases the
server's register file between them. -/
@[inline] def performReplyRecvTakeCapsDelivered (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (core : CoreId) (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) (w0 w1 w2 w3 w4 w5 : UInt64)
    (sv : SeLe4n.ObjId) (sb : SeLe4n.VAddr) (sroot : SeLe4n.ObjId) (count : Nat)
    (rv : SeLe4n.ObjId) (rb : SeLe4n.VAddr) (rroot : SeLe4n.ObjId) : SystemState :=
  writeTakerFrame (performReplyRecvTakeCapsLegs st c tid rid epId s nextCode core layout rf len
    badge sv sb sroot count rv rb rroot) tid w0 w1 w2 w3 w4 w5

/-- **The reply-receive meeting a waiting sender, its reply leg transferring,
is the specification's**: under the guard of `replyRecvOnCore_take_delivered`
(its inert transfer replaced by a granting replier whose frame asks for `count`
capabilities, `hReq`) and the transfer's stores in place
(`replyTransferStoresInPlace`, read on the pre-state), the checked arm's result
is `performReplyRecvTakeCapsDelivered`. -/
theorem replyRecvOnCore_take_capsDelivered (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rp : Reply) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (stcb : TCB) (count : Nat)
    (hSz4 : Architecture.regMessageLength layout len - 1 ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true) (hNe : tid ≠ c)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hGt : receiveTakesInPlace st epId tid s sTcb = true)
    (hR : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
      sTcb.registerContext 32 = .send capAddr mi)
    (hF : sTcb.ipcFaultSend = false)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count)
    (hW : replyTransferStoresInPlace st c.toObjId stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot
      count ct.vspaceRoot ct.ipcBuffer ct.cspaceRoot = true) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvTakeCapsDelivered st c tid rid epId s sTcb.queueNextCode core layout
        rf len badge
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x0
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x1
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x2
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x3
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x4
        (Architecture.regMessageFrame SeLe4n.arm64DefaultLayout sTcb.registerContext mi.length
          sTcb.ipcBadgeView).x5
        stcb.vspaceRoot stcb.ipcBuffer stcb.cspaceRoot count ct.vspaceRoot ct.ipcBuffer
        ct.cspaceRoot) := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hFC : st.objects.findsInPlace c.toObjId = true := by
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG
    exact hG.1.1.1.2
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hSz : ¬ (Architecture.regReplyRecvBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regReplyRecvBody_size]; unfold maxMessageRegisters; omega
  obtain ⟨hE1, sTcb1, hS1o, hK1, hG1⟩ := storeReplyRendezvous_takeGuard st c tid rid
    { registers := Architecture.regReplyRecvBody layout rf len, badge := badge } ct rp epId ep s
    sTcb hNo hT hFC hRp hE hS hSC hGt
  generalize hMsg : ({ registers := Architecture.regReplyRecvBody layout rf len, badge := badge } :
    IpcMessage) = msg at hE1 hS1o hG1
  have hNoX := storeReplyRendezvousReady_noResizeDue st c tid rid hNo
  have hAX := ipcBufferReadsAgree_storeReplyRendezvousReady st c tid rid hNo
  obtain ⟨hIX, hLX⟩ := storeReplyRendezvousReady_fields st c tid rid hNo
  generalize hX : storeReplyRendezvousReady st c tid rid = X at hNoX hAX hIX hLX
  have hS1 : storeReplyRendezvous st c tid rid msg = X.mapTcbInPlace c (holdMessage msg) := by
    rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, hX]
  obtain ⟨sm, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 sm hNoX hT1
  have hXf : replyTransferCaps st tid c true (storeReplyRendezvous st c tid rid msg) =
      .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    unfold replyTransferCaps
    rw [hReq, hTgt, hS1, receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _)
      c _ _ _ X hNoX, hT1]
    rfl
  rw [hS1] at hE1 hS1o hG1
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAX)
    hIX hLX ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoX) c.toObjId stcb ct count hW
    (by rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X
      hNoX, hT1]; rfl)).1
  obtain ⟨hE2, sTcb2, hS2o, hK2, hG2⟩ := takeGuard_of_transferFrame hFr hE1 hS1o hG1
  have hK := hK2.trans hK1
  have hR2 : Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout
      sTcb2.registerContext 32 = .send capAddr mi := by rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  rw [replyRecvOnCore_take_transfer st epId tid c rid msg true core ct ep0 ep s capAddr mi
    (hMsg ▸ hSz) hT hIpc hRO hG hH hXf hE2 hS2o hG2 hR2 hF2]
  dsimp only
  subst hMsg
  rw [CapTransferSummary.capInfo_empty]
  rw [replyRecvTakeFrame_staged Y1 c tid s epId ep sTcb2 core layout rf len badge sm.capInfo capAddr
    mi hNoY hNe hSC hSz4 hE2 hH hS2o hG2 hR2 hF2, hK.queueNext, hK.regs, hK.ipcBadgeView]
  have hKl := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => replyRecvTakeLegs i Y c tid s epId sTcb.queueNextCode core layout rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hKl
  rw [hAX.frameCapRequestOf, hAX.capTargetOf, hT1] at hKl
  unfold performReplyRecvTakeCapsDelivered performReplyRecvTakeCapsLegs
  rw [hX]
  dsimp only
  rw [hKl]

end SeLe4n.Kernel
