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
import SeLe4n.Kernel.IPC.CrossCore.LongReplyRecvFrame
import SeLe4n.Kernel.IPC.CrossCore.FaultAnswerInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyUnheldPopFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyCapsReturnDelivered

/-!
# The frame a reply-receive's take runs in

seL4-MCS's `handleReplyRecv` runs `doReplyTransfer` and then `receiveIPC`; when
a sender is already queued on the endpoint, `receiveIPC` takes it at once.  The
take's guard reads the sender's message words (its badge, its fault flag), which
the run-queue frame of the reply leg erases (`TCB.withoutRunLinks`).  The reply
leg writes no such word, so this module states that frame
(`SystemState.objectsKeepSendCaps`, `SenderWordsKept`) and carries the take's
guard across every reply arm's leg, pop and transfer
(`storeReplyRendezvous_takeGuard`, `storeReplyLeg_takeGuard`,
`popUnheldSettled_takeGuard`, `takeGuard_of_transferFrame`,
`receiveReturnSchedContext_takeGuard`).  It also holds the writes the takes
share: the taker's frame (`writeTakerFrame`), the long delivery past another
thread's write (`deliverLongReplyRecvFrame_mapTcbInPlace`).  The fault answer
runs before the take (WS-SX SX32), so no take frame commutes past it.  The
composed take over every arm
and answer is `ReplyRecvTakeComposed`; the Call takes read the same frame.
-/

namespace SeLe4n.Model

/-- The five words a blocked sender's capability fills in (`TCB.setSendCap`),
the ones `TCB.withoutRunLinks` erases. -/
@[inline] def TCB.sendCapWords (t : TCB) : UInt64 × Bool × Bool × Bool × Bool :=
  (t.ipcBadge, t.ipcBadged, t.ipcCanGrant, t.ipcFaultSend, t.ipcCanGrantReply)

/-- A thread's send-capability words; none for any other object. -/
def KernelObject.sendCapWords : KernelObject → Option (UInt64 × Bool × Bool × Bool × Bool)
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
  canGrantReply : t'.ipcCanGrantReply = t.ipcCanGrantReply

theorem SenderWordsKept.trans {a b c : TCB} (h₂ : SenderWordsKept c b) (h₁ : SenderWordsKept b a) :
    SenderWordsKept c a :=
  ⟨h₂.1.trans h₁.1, h₂.2.trans h₁.2, h₂.3.trans h₁.3, h₂.4.trans h₁.4, h₂.5.trans h₁.5,
    h₂.6.trans h₁.6, h₂.7.trans h₁.7, h₂.8.trans h₁.8⟩

/-- Two TCBs that agree off the run-queue links and on their send-capability
words keep every word a take reads. -/
theorem SenderWordsKept.of_withoutRunLinks {t t' : TCB}
    (h : t'.withoutRunLinks = t.withoutRunLinks) (hw : t'.sendCapWords = t.sendCapWords) :
    SenderWordsKept t' t := by
  have e := TCB.eq_withRunLinks_of_withoutRunLinks_eq h
  simp only [TCB.sendCapWords, Prod.mk.injEq] at hw
  obtain ⟨h1, h2, h3, h4, h5⟩ := hw
  rw [e]
  exact ⟨rfl, rfl, rfl, h1, h2, h4, h3, h5⟩

/-- Two TCBs that agree off their derivation links keep every word a take
reads. -/
theorem SenderWordsKept.of_withoutLinks {t t' : TCB} (h : t'.withoutLinks = t.withoutLinks) :
    SenderWordsKept t' t := by
  have f : ∀ {α : Type} (g : TCB → α), (∀ u : TCB, g u.withoutLinks = g u) → g t' = g t :=
    fun g hg => by rw [← hg t', ← hg t, h]
  exact ⟨f TCB.queueNextCode (fun _ => rfl), f TCB.ipcState (fun _ => rfl),
    f TCB.registerContext (fun _ => rfl), f TCB.ipcBadge (fun _ => rfl),
    f TCB.ipcBadged (fun _ => rfl), f TCB.ipcFaultSend (fun _ => rfl),
    f TCB.ipcCanGrant (fun _ => rfl), f TCB.ipcCanGrantReply (fun _ => rfl)⟩

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

/-! ### The take's guard across the receive's return -/

/-- **The take's guard across the receive's return** (seL4-MCS `receiveIPC`'s
`maybeReturnSchedContext`): the return clears at most a thread's two binding
codes and rewrites a context, so the endpoint, the sender's words and the take's
in-place guard carry over. -/
theorem receiveReturnSchedContext_takeGuard (blocks : Bool) (S : SystemState)
    (tid : SeLe4n.ThreadId) (hNo : S.objects.noResizeDue)
    {epId : SeLe4n.ObjId} {ep : Endpoint} {sid : SeLe4n.ThreadId} {sTcb : TCB}
    (hE : S.objects[epId]? = some (.endpoint ep))
    (hS : S.objects[sid.toObjId]? = some (.tcb sTcb))
    (hG : receiveTakesInPlace S epId tid sid sTcb = true) :
    (receiveReturnSchedContext blocks S tid).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb', (receiveReturnSchedContext blocks S tid).objects[sid.toObjId]? =
          some (.tcb sTcb') ∧ SenderWordsKept sTcb' sTcb ∧
        receiveTakesInPlace (receiveReturnSchedContext blocks S tid) epId tid sid sTcb' = true := by
  have hAg := receiveReturnSchedContext_returnAgree blocks S tid hNo
  have hKF := receiveReturnSchedContext_keepsFinds blocks S tid hNo
  generalize receiveReturnSchedContext blocks S tid = S' at hAg hKF
  have hV : ∀ x, S'.getObjectType? x = S.getObjectType? x := by
    intro x
    unfold SystemState.getObjectType?
    rcases hAg x with e | ⟨o, o', h0, h1, r⟩
    · rw [e]
    · rw [h0, h1]
      rcases r with rfl | ⟨t, rfl, rfl⟩ | ⟨_, _, rfl, rfl⟩ <;> rfl
  have hTcb : ∀ (p : SeLe4n.ThreadId) (t : TCB), S.objects[p.toObjId]? = some (.tcb t) →
      ∃ t', S'.objects[p.toObjId]? = some (.tcb t') ∧
        (t' = t ∨ t' = { t with scBindingScCode := 0, scBindingOwnerCode := 0 }) := by
    intro p t h
    rcases hAg p.toObjId with e | ⟨o0, o', h0, h1, r⟩
    · exact ⟨t, by rw [e, h], Or.inl rfl⟩
    · rw [h] at h0; cases h0
      rcases r with rfl | ⟨t1, e1, rfl⟩ | ⟨_, _, e1, _⟩
      · exact ⟨t, h1, Or.inl rfl⟩
      · cases e1; exact ⟨_, h1, Or.inr rfl⟩
      · cases e1
  have hEp : S'.objects[epId]? = some (.endpoint ep) := by
    rcases hAg epId with e | ⟨o0, o', h0, h1, r⟩
    · rw [e, hE]
    · rw [hE] at h0; cases h0
      rcases r with rfl | ⟨_, e1, _⟩ | ⟨_, _, e1, _⟩
      · exact h1
      · cases e1
      · cases e1
  obtain ⟨t', h1, e⟩ := hTcb sid sTcb hS
  have hK : SenderWordsKept t' sTcb := by
    rcases e with rfl | rfl <;> exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  refine ⟨hEp, t', h1, hK, receiveTakesInPlace_of_frame epId tid sid sTcb t' hKF hV ?_
    hK.queueNext hK.ipcState hG⟩
  intro p hp
  obtain ⟨t, ht⟩ := Option.isSome_iff_exists.mp hp
  obtain ⟨t2, h2, _⟩ := hTcb p t ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht)
  rw [(SystemState.getTcb?_eq_some_iff _ _ _).mpr h2]
  rfl

/-! ### The taker's own frame -/

/-- The server's own frame, its six words read from the sender's saved
registers before any write.  Out of line from the legs (`ReplyRecvArm.takeLegs`):
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

theorem SenderWordsKept.ipcBadgeView {t' t : TCB} (h : SenderWordsKept t' t) :
    t'.ipcBadgeView = t.ipcBadgeView := by
  rw [TCB.ipcBadgeView_eq_opt, TCB.ipcBadgeView_eq_opt, h.badge, h.badged]

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

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-! ## The long delivery past another thread's write -/

theorem overflowSlotsFrom_congr {S S' : SystemState} (h : ipcWordReadsAgree S' S)
    (r : SeLe4n.ThreadId) : ∀ (i n : Nat), overflowSlotsFrom S' r i n = overflowSlotsFrom S r i n
  | _, 0 => rfl
  | i, n + 1 => by
    simp only [overflowSlotsFrom, h.overflowSlotOf r i, overflowSlotsFrom_congr h r (i + 1) n]

/-- **The overflow copy commutes past a TCB write that keeps every buffer
read**: the copy records machine writes, the TCB write rewrites one object. -/
theorem overflowCopyStore_mapTcbInPlace (r s t : SeLe4n.ThreadId) (g : TCB → TCB)
    (hg : ∀ x, (g x).spaceCells[2] = x.spaceCells[2] ∧ (g x).ipcBuffer = x.ipcBuffer) :
    ∀ (n i : Nat) (S : SystemState),
      overflowCopyStore (S.mapTcbInPlace t g) r s i n = (overflowCopyStore S r s i n).mapTcbInPlace t g
  | 0, _, _ => rfl
  | n + 1, i, S => by
    have hA := (ipcBufferReadsAgree_mapTcbInPlace S t g hg).words
    simp only [overflowCopyStore, hA.overflowSlotOf r i, hA.overflowWordAt s i]
    split
    · exact overflowCopyStore_mapTcbInPlace r s t g hg n (i + 1)
        (S.recordPhysicalWrite _)
    · rfl

/-- **The long delivery to `r` commutes past a write of another thread `t`
that keeps every buffer read.** -/
theorem deliverLongReplyRecvFrame_mapTcbInPlace (X : SystemState) (r s t : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (g : TCB → TCB)
    (hg : ∀ x, (g x).spaceCells[2] = x.spaceCells[2] ∧ (g x).ipcBuffer = x.ipcBuffer)
    (hNe : r ≠ t) :
    deliverLongReplyRecvFrame (X.mapTcbInPlace t g) r rf len s badge capInfo =
      (deliverLongReplyRecvFrame X r rf len s badge capInfo).mapTcbInPlace t g := by
  have hNe' : t.toObjId ≠ r.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  have hA := (ipcBufferReadsAgree_mapTcbInPlace X t g hg).words
  unfold deliverLongReplyRecvFrame deliverLongSendFrame
  rw [SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe']
  cases X.getTcb? r with
  | none => rfl
  | some x =>
    simp only []
    split
    · rw [overflowSlotsFrom_congr hA r 0 (len - 4),
        SystemState.mapTcbInPlace_swap _ g _ (fun e => absurd e hNe),
        overflowCopyStore_mapTcbInPlace r s t g hg]
    · unfold holdLongSendMessage longSendMessage
      rw [hA.overflowRegsFrom s 0 (len - 4),
        SystemState.mapTcbInPlace_swap _ g _ (fun e => absurd e hNe)]

/-- The overflow copy records machine writes only. -/
theorem overflowCopyStore_objects (r s : SeLe4n.ThreadId) :
    ∀ (n i : Nat) (S : SystemState), (overflowCopyStore S r s i n).objects = S.objects
  | 0, _, _ => rfl
  | n + 1, i, S => by
    simp only [overflowCopyStore]
    split
    · exact overflowCopyStore_objects r s n (i + 1) _
    · rfl

theorem deliverLongReplyRecvFrame_noResizeDue (X : SystemState) (r : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (s : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge)
    (capInfo : Nat) (hNo : X.objects.noResizeDue) :
    (deliverLongReplyRecvFrame X r rf len s badge capInfo).objects.noResizeDue := by
  unfold deliverLongReplyRecvFrame deliverLongSendFrame holdLongSendMessage
  split
  · split
    · rw [overflowCopyStore_objects]; exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo
    · exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo
  · exact hNo

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

theorem performFaultAnswer_noResizeDue (X : SystemState) (c : SeLe4n.ThreadId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (n off : Nat)
    (hNo : X.objects.noResizeDue) :
    (performFaultAnswer X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n
      off).objects.noResizeDue := by
  unfold performFaultAnswer applyFaultRestart faultAbandonOnCore
  split
  · exact updateTcb_noResizeDue _ _ _ hNo
  · split
    · exact updateTcb_noResizeDue _ _ _ (removeRunnableOnCore_noResizeDue _ _ _ hNo)
    · split
      · exact updateTcb_noResizeDue _ _ _ hNo
      · exact updateTcb_noResizeDue _ _ _ hNo

end SeLe4n.Kernel

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section UnlinkedTakeGuard

/-- **The reply leg alone keeps every thread's send-capability words**:
`storeReplyRendezvousReady_keepsSendCaps` without the unlink. -/
theorem storeReplyLegReady_keepsSendCaps (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    SystemState.objectsKeepSendCaps (storeReplyLegReady st c rid) st := by
  unfold storeReplyLegReady
  dsimp only
  have hNo1 := updateTcb_noResizeDue st c receiverReady hNo
  have hNo2 := enqueueRunnableOnCore_noResizeDue _
    (determineTargetCore (st.updateTcb c receiverReady) c) c hNo1
  have hNo3 := modifyObject_noResizeDue _ rid.toObjId replyConsumedObject hNo2
  refine (SystemState.updateTcb_keepsSendCaps _ c ?_ hNo3).trans
      ((SystemState.modifyObject_keepsSendCaps _ _ ?_ hNo2).trans
        ((enqueueRunnableOnCore_keepsSendCaps _ _ c hNo1).trans
          (SystemState.updateTcb_keepsSendCaps _ c ?_ hNo)))
  · intro _; rfl
  · intro o; cases o <;> rfl
  · intro _; rfl

/-- **The take's guard across the reply leg alone** (no server's reply waiters
to leave): `storeReplyRendezvous_takeGuard` for `storeReplyLeg`. -/
theorem storeReplyLeg_takeGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hG : receiveTakesInPlace st epId tid s sTcb = true) :
    (storeReplyLeg st c rid msg).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (storeReplyLeg st c rid msg).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        receiveTakesInPlace (storeReplyLeg st c rid msg) epId tid s sTcb1 = true := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hRc : rid.toObjId ≠ c.toObjId := fun e => by rw [e, hT] at hRp; cases hRp
  have hEc : epId ≠ c.toObjId := fun e => by rw [e, hT] at hE; cases hE
  have hEr : epId ≠ rid.toObjId := fun e => by rw [e, hRp] at hE; cases hE
  have hSc' : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  have hSr : s.toObjId ≠ rid.toObjId := fun e => by rw [e, hRp] at hS; cases hS
  have hKS := storeReplyLegReady_keepsSendCaps st c rid hNo
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo]
  generalize hS1 : storeReplyLegReady st c rid = S1 at hKS
  have hAg := fun x hx hy => hS1 ▸ storeReplyLegReady_agree st c rid ct hNo hTc hFC x hx hy
  have hHold : ∀ x, x ≠ c.toObjId →
      (S1.mapTcbInPlace c (holdMessage msg)).objects[x]? = S1.objects[x]? := fun x hx => by
    rw [SystemState.objects_mapTcbInPlace, if_neg (fun h => hx (beq_iff_eq.mp h).symm)]
  have hK : S1.objectsKeepFinds st := hS1 ▸ storeReplyLegReady_keepsFinds st c rid hNo hFC
  obtain ⟨tc1, htc1, -⟩ := hS1 ▸ storeReplyLegReady_callerView st c rid ct hNo hTc hFC hRc
  have hR1 : S1.objects[rid.toObjId]? = some (.reply rp.consumed) :=
    hS1 ▸ storeReplyLegReady_reply st c rid ct rp hNo hTc hFC hRp hRc
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

end UnlinkedTakeGuard

section UnheldTakeGuard

/-- **The take's guard across a pop that leaves the sender's slot alone**: a
step writing only what a pop writes (`popFrame`), the sender's object found
unchanged, keeps the endpoint and the take's in-place guard. -/
theorem takeGuard_of_popFrame {P T : SystemState} (hF : popFrame P T)
    {epId : SeLe4n.ObjId} {ep : Endpoint} {tid sid : SeLe4n.ThreadId} {sTcb : TCB}
    (hE : T.objects[epId]? = some (.endpoint ep))
    (hG : receiveTakesInPlace T epId tid sid sTcb = true) :
    P.objects[epId]? = some (.endpoint ep) ∧ receiveTakesInPlace P epId tid sid sTcb = true :=
  ⟨popAgreeAt_endpoint (hF.2.2.2 epId) hE,
    receiveTakesInPlace_of_frame epId tid sid sTcb sTcb hF.2.2.1
      (fun x => getObjectType?_of_popAgree (hF.2.2.2 x))
      (fun _ hp => getTcb?_isSome_of_popAgree (hF.2.2.2 _) hp) rfl rfl hG⟩

/-- **The take's guard across the reply leg, the unheld pop and its settle**:
on the state they leave, the endpoint is as it was, the sender a thread keeping
every word the take reads, and the take's in-place guard, read on the
pre-state, still holds.  The pop and the settle write the caller's binding, the
reply stack's links and the context, never the sender's slot. -/
theorem popUnheldSettled_takeGuard (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (scId : SeLe4n.SchedContextId) (home : CoreId)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hNo : st.objects.noResizeDue)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hFC : st.objects.findsInPlace c.toObjId = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hG : receiveTakesInPlace st epId tid s sTcb = true) :
    (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
        (storeReplyLeg st c rid msg) c scId) home scId).objects[epId]? = some (.endpoint ep) ∧
      ∃ sTcb1, (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
          (storeReplyLeg st c rid msg) c scId) home scId).objects[s.toObjId]? = some (.tcb sTcb1) ∧
        SenderWordsKept sTcb1 sTcb ∧
        receiveTakesInPlace (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
          (storeReplyLeg st c rid msg) c scId) home scId) epId tid s sTcb1 = true := by
  have hSc' : s.toObjId ≠ c.toObjId := fun e => hSC (SeLe4n.ThreadId.toObjId_injective _ _ e)
  obtain ⟨hE1, sTcb1, hS1, hK, hG1⟩ := storeReplyLeg_takeGuard st c tid rid msg ct rp epId ep s
    sTcb hNo hT hFC hRp hE hS hSC hG
  have hNoT := storeReplyLeg_noResizeDue st c rid msg hNo
  generalize storeReplyLeg st c rid msg = T at hE1 hS1 hG1 hNoT
  have hPt := returnUnheldSchedContextInPlace_tcbAt T c scId hNoT hSc' hS1
  have hFr := returnUnheldSchedContextInPlace_popFrame T c scId hNoT
  generalize returnUnheldSchedContextInPlace T c scId = Rr at hPt hFr
  have hPt' := releaseAgreeAt_of_not_sc (SchedContextOps.settleReturnedContext_agree Rr home scId)
    hPt (fun _ e => by cases e)
  have hF := (settleReturnedContext_popFrame Rr home scId).trans hFr
  obtain ⟨hEP, hGP⟩ := takeGuard_of_popFrame hF hE1 hG1
  exact ⟨hEP, sTcb1, hPt', hK, hGP⟩

end UnheldTakeGuard

end SeLe4n.Kernel
