/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeComposed
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvUnlinkedCallTakeInPlace

/-!
# The reply-receive whose receive leg takes a queued caller, composed over its reply arm

WS-SX SX27.  A reply-receive whose receive leg meets a caller queued by a
`Call` runs, whatever the reply's arm, the arm's reply leg and pop
(`ReplyRecvArm`, as the blocking receive and the Send take run them), the reply
leg's transfer, the server's context return on its bound notification, the take
(the caller popped, blocked on the reply through the same reply object and
queued on the server's reply waiters, the server handed its message), the
rendezvous donation (seL4-MCS `receiveIPC` → `reply_push (canDonate)`: the
caller's context lent to a server holding none, nothing lent to a server that
holds one), and the server's priority walk.  The holder's deschedule of the
post-receive half is the identity on every arm here: the only arm whose pop
returns a context (the donated arm) returns it from the server itself, and the
server is the one the new call's context goes to.

The arm's reply leg and pop are joined to the specification once per arm
(`ReplyRecvArm.legPop`), the take after them once for every arm
(`replyRecvAnsweringOnCore_callTake_of_pop`); the take's guard is carried
across the arm's reply leg and pop (`ReplyRecvArm.callTakeGuard`), the reply
leg's transfer and the receive's context return once.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency
open Architecture.RegisterDecode

/-- **An in-place take of a queued caller lends nothing, as the specification
runs it**: the receive dequeued a call, and the rendezvous donation is the
identity (`receiveCallTakesInPlace`'s `callDonatesNothing`). -/
theorem receiveCallTake_lendsNothing (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (core : CoreId)
    (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallTakesInPlace st endpointId receiver s sTcb rid = true) :
    rendezvousDequeuedCall (receiveCallTakeState st endpointId s sTcb receiver rid) s = true ∧
      applyRendezvousCallDonation (receiveCallTakeState st endpointId s sTcb receiver rid)
        receiver s = .ok (receiveCallTakeState st endpointId s sTcb receiver rid) := by
  obtain ⟨_, hIpc, hBs, hBr⟩ :=
    receiveCallTake_inPlace st endpointId ep receiver rid core s sTcb hE hH hT
      (receiveCallTakesReplyInPlace_of_inPlace hG)
  have hG' := receiveCallTakesReplyInPlace_of_inPlace hG
  simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hG'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, _⟩, hRT⟩, _⟩, _⟩ := hG'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, _⟩, _⟩, _⟩, _⟩ := hSG'
  obtain ⟨rt, hRTo⟩ := Option.isSome_iff_exists.mp hRT
  have hDN := receiveCallTakesInPlace_lendsNothing hG hRTo
  have hTs : st.getTcb? s = some sTcb := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨x, hx, hxI⟩ := Option.map_eq_some_iff.mp hIpc
  have hCall : rendezvousDequeuedCall (receiveCallTakeState st endpointId s sTcb receiver rid)
      s = true := by
    unfold rendezvousDequeuedCall
    simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte, hx, hxI]
  obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff s).mpr hSRes)
  obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff receiver).mpr hRRes)
  have hNone : callDonationSchedContext? (receiveCallTakeState st endpointId s sTcb receiver rid)
      s receiver = none := by
    rw [callDonationSchedContext?_congr (s := st) hBs hBr, callDonationSchedContext?_eq_bindings]
    simp only [lookupTcb, hRRes, hSRes, Bool.false_eq_true, ↓reduceIte, hRTo, hTs,
      Option.map_some]
    revert hDN
    unfold callDonatesNothing
    cases rt.schedContextBinding <;> cases sTcb.schedContextBinding <;>
      simp [donationOfBindings, SchedContextBinding.scId?]
  have h := applyReceiveRendezvousDonation_of_no_donation
    (receiveCallTakeState st endpointId s sTcb receiver rid) receiver s sv rv hsv hrv hNone
  unfold applyReceiveRendezvousDonation at h
  simp only [hCall, ↓reduceIte] at h
  exact ⟨hCall, h⟩

namespace ReplyRecvArm

/-- Whether the arm's Call take lends the taken caller's context to the server:
every arm's pop leaves the server holding no context but the held arm's, which
keeps the one its reply heads, so its take lends nothing. -/
@[inline] def callLends : ReplyRecvArm → Bool
  | .held => false
  | _ => true

/-- **The Call take's in-place guard on the state the receive runs on**: the
take and the donation (`receiveCallDonatesInPlace`) where the arm lends, the
take lending nothing (`receiveCallTakesInPlace`) where it does not. -/
def CallReady (arm : ReplyRecvArm) (Q : SystemState) (epId : SeLe4n.ObjId)
    (tid s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) : Prop :=
  if arm.callLends then receiveCallDonatesInPlace Q epId tid s sTcb rid = true
  else receiveCallTakesInPlace Q epId tid s sTcb rid = true

/-- The rendezvous donation, in place: the taken caller `s`'s context `scS`
lent to the server where the arm lends, nothing otherwise. -/
@[inline] def callLend (arm : ReplyRecvArm) (X : SystemState) (s tid : SeLe4n.ThreadId)
    (scS : SeLe4n.SchedContextId) (donorHome doneeHome : CoreId) : SystemState :=
  if arm.callLends then lendSchedContextInPlace X s tid scS donorHome doneeHome else X

/-- **The post-receive half after a take that dequeued a `Call`** is the
rendezvous donation to the server and the server's priority walk: the holder's
deschedule is the identity, the donated arm's holder being the server itself. -/
theorem postReceive_call (arm : ReplyRecvArm) (scId : SeLe4n.SchedContextId)
    (tid s : SeLe4n.ThreadId) (core : CoreId) (X Y : SystemState)
    (hC : rendezvousDequeuedCall X s = true)
    (hD : applyRendezvousCallDonation X tid s = .ok Y) :
    replyRecvPostReceiveDonation tid tid s core (arm.returned scId tid) X =
      .ok ((), (PriorityInheritance.propagatePipChainCrossCore Y tid core).1) := by
  cases arm <;> simp [replyRecvPostReceiveDonation, returned, replyRecvHolderDeschedule, hC, hD]

/-- **The receive leg's take of a queued caller, over the arm**: under the
arm's guard on the state the receive runs on, the receive takes the caller
(`receiveCallTakeState`), dequeues a call, and the rendezvous donation is the
arm's lend of the caller's context, read on that state. -/
theorem callTake_receive (arm : ReplyRecvArm) (Q : SystemState) (epId : SeLe4n.ObjId)
    (ep : Endpoint) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (core : CoreId)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : Q.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : Q.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : arm.CallReady Q epId tid s sTcb rid) (hF : sTcb.ipcFaultSend = false)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .call capAddr mi) :
    endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
        (receiveCallTakeState Q epId s sTcb tid rid, .ok (s, { results := #[] }, none)) ∧
      rendezvousDequeuedCall (receiveCallTakeState Q epId s sTcb tid rid) s = true ∧
      applyRendezvousCallDonation (receiveCallTakeState Q epId s sTcb tid rid) tid s =
        .ok (arm.callLend (receiveCallTakeState Q epId s sTcb tid rid) s tid
          ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore Q s) (determineTargetCore Q tid)) := by
  unfold CallReady at hG
  unfold callLend
  cases hL : arm.callLends
  · simp only [hL, Bool.false_eq_true, ↓reduceIte] at hG ⊢
    obtain ⟨hRecv, -, -⟩ := receiveCallTake_delivered Q epId ep tid rid core s sTcb capAddr mi
      hE hH hT hG hF hR
    exact ⟨hRecv, receiveCallTake_lendsNothing Q epId ep tid rid core s sTcb hE hH hT hG⟩
  · simp only [hL, ↓reduceIte] at hG ⊢
    obtain ⟨hRecv, -, -, hCallT, hDonE⟩ := receiveCallDonatingTake_delivered Q epId ep tid rid
      core s sTcb capAddr mi hE hH hT hG hF hR
    exact ⟨hRecv, hCallT, applyRendezvousCallDonation_lendInPlace hDonE⟩

end ReplyRecvArm

/-- **The take of a queued caller after the arm's reply leg and pop is the
specification's**, for every arm and answer: once the reply leg answers `S1`,
the pop hands back the arm's `returned` on `P`, and the reply leg's transfer
answers `(summary, S2)`, a receive on the state the server's context return
leaves that takes a caller (`R`) whose rendezvous donation answers `Y` runs the
post-receive half as the donation and the server's priority walk, then the
caller's answer. -/
theorem replyRecvAnsweringOnCore_callTake_of_pop (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} (answer : Option Architecture.FaultReplyOutcome)
    (st : SystemState) (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (msg : IpcMessage) (grant : Bool) (core : CoreId) (s : SeLe4n.ThreadId)
    {S1 P : SystemState} {x : Option (CoreId × SgiKind)}
    (hRecS : (recordedReplyServer? st c).getD tid = tid)
    (hEq : endpointReplyOnCore tid c msg core st = (S1, .ok x))
    (hPop : replyRecvPopDonation rid c S1 = .ok (arm.returned scId tid, P))
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyRecvReplyTransfer answer st tid c grant P = .ok (summary, S2))
    {R Y : SystemState}
    (hRecv : endpointReceiveDualWithCapsOnCore epId tid (some rid) core
      (receiveReturnSchedContext true S2 tid) = (R, .ok (s, { results := #[] }, none)))
    (hC : rendezvousDequeuedCall R s = true)
    (hD : applyRendezvousCallDonation R tid s = .ok Y) :
    endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
      .ok ({ results := #[] }, replyRecvAnswerCaller answer
        (PriorityInheritance.propagatePipChainCrossCore Y tid core).1 c summary.capInfo) := by
  unfold endpointReplyRecvAnsweringOnCore
  simp only [hRecS, hEq, hPop, hXf, hRecv, ReplyRecvArm.postReceive_call arm scId tid s core R Y hC hD]
  simp [applyReceiveLegPipHandoff]

/-! ### The Call take's guard across the reply leg's transfer -/

/-- A read of one object that sees it as the transfer leaves it (a CNode as
nothing, a thread off its derivation links) is kept by the transfer. -/
theorem transferFrame.bindView {s' s : SystemState} (h : transferFrame s' s) {α : Type}
    (g : KernelObject → Option α) (hg : ∀ o, g o = (transferView o).bind g) (x : SeLe4n.ObjId) :
    (s'.objects[x]?).bind g = (s.objects[x]?).bind g := by
  have e := congrArg (fun v => (v.bind id).bind g) (h.2.2.2 x)
  have k : ∀ v : Option KernelObject, v.bind g = ((v.map transferView).bind id).bind g := by
    intro v; cases v with
    | none => rfl
    | some o => show g o = (transferView o).bind g; exact hg o
  rw [k (s'.objects[x]?), k (s.objects[x]?)]; exact e

theorem transferFrame.getReply? {s' s : SystemState} (h : transferFrame s' s)
    (r : SeLe4n.ReplyId) : s'.getReply? r = s.getReply? r := by
  have gS : ∀ (S : SystemState), S.getReply? r = (S.objects[r.toObjId]?).bind
      (fun o => match o with | .reply m => some m | _ => none) := by
    intro S; unfold SystemState.getReply?
    cases S.objects[r.toObjId]? with
    | none => rfl
    | some o => cases o <;> rfl
  rw [gS, gS]
  exact h.bindView _ (fun o => by cases o <;> rfl) _

theorem transferFrame.getSchedContext? {s' s : SystemState} (h : transferFrame s' s)
    (q : SeLe4n.SchedContextId) : s'.getSchedContext? q = s.getSchedContext? q := by
  have gS : ∀ (S : SystemState), S.getSchedContext? q = (S.objects[q.toObjId]?).bind
      (fun o => match o with | .schedContext m => some m | _ => none) := by
    intro S; unfold SystemState.getSchedContext?
    cases S.objects[q.toObjId]? with
    | none => rfl
    | some o => cases o <;> rfl
  rw [gS, gS]
  exact h.bindView _ (fun o => by cases o <;> rfl) _

theorem transferFrame.getNotification? {s' s : SystemState} (h : transferFrame s' s)
    (n : SeLe4n.ObjId) : s'.getNotification? n = s.getNotification? n := by
  have gN : ∀ (S : SystemState), S.getNotification? n = (S.objects[n]?).bind
      (fun o => match o with | .notification m => some m | _ => none) := by
    intro S; unfold SystemState.getNotification?
    cases S.objects[n]? with
    | none => rfl
    | some o => cases o <;> rfl
  rw [gN, gN]
  exact h.bindView _ (fun o => by cases o <;> rfl) _

/-- A thread as the transfer leaves it: its derivation links aside, as it was. -/
theorem transferFrame.getTcb?_some {s' s : SystemState} (h : transferFrame s' s)
    {x : SeLe4n.ThreadId} {t : TCB} (ht : s.getTcb? x = some t) :
    ∃ t', s'.getTcb? x = some t' ∧ t'.withoutLinks = t.withoutLinks := by
  obtain ⟨t', h1, e⟩ := h.tcb ((SystemState.getTcb?_eq_some_iff _ _ _).mp ht)
  exact ⟨t', (SystemState.getTcb?_eq_some_iff _ _ _).mpr h1, e⟩

theorem determineTargetCore_of_transferFrame {s' s : SystemState} (h : transferFrame s' s)
    (x : SeLe4n.ThreadId) : determineTargetCore s' x = determineTargetCore s x := by
  have e := h.getTcb? x
  unfold determineTargetCore
  cases h1 : s.getTcb? x with
  | none =>
    rw [h1] at e
    cases h2 : s'.getTcb? x with
    | none => rfl
    | some _ => rw [h2] at e; cases e
  | some t =>
    rw [h1] at e
    cases h2 : s'.getTcb? x with
    | none => rw [h2] at e; cases e
    | some t' =>
      rw [h2] at e
      have := congrArg TCB.cpuAffinity (Option.some.inj e)
      simp only [TCB.withoutLinks] at this
      simp only [this]

/-- **The caller's context, ready to be donated, across the transfer**: it reads
the caller's binding, the context, its reply and their slots, none of which the
transfer writes. -/
theorem callerContextReady_of_transferFrame {s' s : SystemState} (h : transferFrame s' s)
    (caller : SeLe4n.ThreadId) (t t' : TCB) (rid : SeLe4n.ReplyId)
    (hB : t'.scBindingScCode = t.scBindingScCode)
    (hC : callerContextReady s caller t rid = true) :
    callerContextReady s' caller t' rid = true := by
  unfold callerContextReady at hC ⊢
  rw [hB]
  cases hk : t.scBindingScCode with
  | zero => rw [hk] at hC; exact hC
  | succ k =>
    rw [hk] at hC
    simp only [h.getSchedContext?, Bool.and_eq_true] at hC ⊢
    obtain ⟨⟨a1, a2⟩, a3⟩ := hC
    refine ⟨⟨h.leaves a1, (h.2.2.1 _).trans a2⟩, ?_⟩
    cases hsc : s.getSchedContext? ⟨k⟩ with
    | none => rw [hsc] at a3; cases a3
    | some sc =>
      rw [hsc] at a3
      dsimp only at a3 ⊢
      simp only [Bool.and_eq_true] at a3 ⊢
      obtain ⟨b0, b⟩ := a3
      refine ⟨b0, ?_⟩
      revert b
      cases sc.scReply with
      | none => exact id
      | some old =>
        dsimp only
        simp only [Bool.and_eq_true, h.getReply?]
        rintro ⟨⟨⟨b1, b2⟩, b3⟩, b4⟩
        exact ⟨⟨⟨b1, h.leaves b2⟩, (h.2.2.1 _).trans b3⟩, b4⟩

/-- **The receive's return guard across the transfer**: it reads the receiver's
notification, that notification's context, the context's thread and the
receiver's binding, none of which the transfer writes. -/
theorem receiveReturnFires_of_transferFrame {s' s : SystemState} (h : transferFrame s' s)
    (tid : SeLe4n.ThreadId) : receiveReturnFires true s' tid = receiveReturnFires true s tid := by
  have e := h.getTcb? tid
  unfold receiveReturnFires
  cases h1 : s.getTcb? tid with
  | none =>
    rw [h1] at e
    cases h2 : s'.getTcb? tid with
    | none => rfl
    | some _ => rw [h2] at e; cases e
  | some t =>
    rw [h1] at e
    cases h2 : s'.getTcb? tid with
    | none => rw [h2] at e; cases e
    | some t' =>
      rw [h2] at e
      have e' := Option.some.inj e
      have hBN : t'.boundNotificationCode = t.boundNotificationCode := by
        have := congrArg TCB.boundNotificationCode e'; exact this
      have hS1 : t'.scBindingScCode = t.scBindingScCode := by
        have := congrArg TCB.scBindingScCode e'; exact this
      have hO1 : t'.scBindingOwnerCode = t.scBindingOwnerCode := by
        have := congrArg TCB.scBindingOwnerCode e'; exact this
      simp only [hBN]
      rw [signalReturnGuard_congr (st := s) (st' := s') (by rw [h.getNotification?])
        (fun q => by rw [h.getSchedContext?]) (by rw [h1, h2]; simp only [Option.map_some,
          TCB.schedContextBinding, hS1, hO1])]

/-- What the transfer keeps of a thread it leaves off its links. -/
theorem withoutLinks_fields {t t' : TCB} (e : t'.withoutLinks = t.withoutLinks) :
    t'.scBindingScCode = t.scBindingScCode ∧ t'.scBindingOwnerCode = t.scBindingOwnerCode ∧
      t'.replyObjectCode = t.replyObjectCode ∧ t'.boundNotificationCode = t.boundNotificationCode := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · have := congrArg TCB.scBindingScCode e; exact this
  · have := congrArg TCB.scBindingOwnerCode e; exact this
  · have := congrArg TCB.replyObjectCode e; exact this
  · have := congrArg TCB.boundNotificationCode e; exact this

/-- **The take of a queued caller, its slots read, across the transfer.** -/
theorem receiveCallTakesReplyInPlace_of_transferFrame {s' s : SystemState} (h : transferFrame s' s)
    (epId : SeLe4n.ObjId) (tid sid : SeLe4n.ThreadId) (t t' : TCB) (rid : SeLe4n.ReplyId)
    (hK : SenderWordsKept t' t) (hRO : t'.replyObjectCode = t.replyObjectCode)
    (hG : receiveCallTakesReplyInPlace s epId tid sid t rid = true) :
    receiveCallTakesReplyInPlace s' epId tid sid t' rid = true := by
  have hV := getObjectType?_of_transferFrame h
  have hTcb : ∀ p : SeLe4n.ThreadId, (s.getTcb? p).isSome = true → (s'.getTcb? p).isSome = true := by
    intro p hp
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨x', hx', -⟩ := h.getTcb?_some hx
    rw [hx']; rfl
  have hQ' : t'.queueNext = t.queueNext := by simp only [TCB.queueNext, hK.queueNext]
  have hRO' : t'.replyObject = t.replyObject := by simp only [TCB.replyObject, hRO]
  unfold receiveCallTakesReplyInPlace at hG ⊢
  rw [hQ', hRO', hK.ipcState, hK.canGrant, hK.canGrantReply, h.getReply?]
  simp only [Bool.and_eq_true] at hG ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩ := hG
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sendWakesInPlace_of_frame epId sid t.queueNext h.2.2.1 hV hTcb a1, a2⟩, a3⟩,
    ?_⟩, h.leaves a5⟩, (h.2.2.1 _).trans a6⟩, h.leaves a7⟩, (h.2.2.1 _).trans a8⟩, a9⟩,
    hTcb _ a10⟩, a11⟩, a12⟩
  revert a4
  cases t.queueNext with
  | none => exact id
  | some n => exact id

/-- **The take lending nothing, across the transfer.** -/
theorem receiveCallTakesInPlace_of_transferFrame {s' s : SystemState} (h : transferFrame s' s)
    (epId : SeLe4n.ObjId) (tid sid : SeLe4n.ThreadId) (t t' : TCB) (rid : SeLe4n.ReplyId)
    (hK : SenderWordsKept t' t) (e : t'.withoutLinks = t.withoutLinks)
    (hG : receiveCallTakesInPlace s epId tid sid t rid = true) :
    receiveCallTakesInPlace s' epId tid sid t' rid = true := by
  have hV := getObjectType?_of_transferFrame h
  have hTcb : ∀ p : SeLe4n.ThreadId, (s.getTcb? p).isSome = true → (s'.getTcb? p).isSome = true := by
    intro p hp
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.mp hp
    obtain ⟨x', hx', -⟩ := h.getTcb?_some hx
    rw [hx']; rfl
  obtain ⟨hB, hO, hRO, -⟩ := withoutLinks_fields e
  have hQ' : t'.queueNext = t.queueNext := by simp only [TCB.queueNext, hK.queueNext]
  have hRO' : t'.replyObject = t.replyObject := by simp only [TCB.replyObject, hRO]
  unfold receiveCallTakesInPlace at hG ⊢
  rw [hQ', hRO', hK.ipcState, hK.canGrant, hK.canGrantReply, h.getReply?]
  simp only [Bool.and_eq_true] at hG ⊢
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a1, a2⟩, a3⟩, a4⟩, a5⟩, a6⟩, a7⟩, a8⟩, a9⟩, a10⟩, a11⟩, a12⟩ := hG
  refine ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨sendWakesInPlace_of_frame epId sid t.queueNext h.2.2.1 hV hTcb a1, a2⟩, a3⟩,
    ?_⟩, h.leaves a5⟩, (h.2.2.1 _).trans a6⟩, h.leaves a7⟩, (h.2.2.1 _).trans a8⟩, a9⟩,
    ?_⟩, a11⟩, a12⟩
  · revert a4
    cases t.queueNext with
    | none => exact id
    | some n => exact id
  · revert a10
    cases h1 : s.getTcb? tid with
    | none => intro x; cases x
    | some rt =>
      obtain ⟨rt', h2, e2⟩ := h.getTcb?_some h1
      rw [h2]
      obtain ⟨hB2, hO2, -, -⟩ := withoutLinks_fields e2
      dsimp only
      simp only [callDonatesNothing, TCB.schedContextBinding, hB, hO, hB2, hO2]
      exact id

/-! ### The Call take's guard through the transfer and the receive's return -/

/-- **A lending take's guard, read before the receive's return, through the
transfer and the return**: on the state the return leaves, the endpoint is as
it was, the queued caller a thread keeping every word the take reads, its
binding and its home, the server its home, and the take's and the donation's
in-place guard holds (`receiveReturnSchedContext_callDonationGuard`). -/
theorem callDonationGuard_through {P S2 : SystemState} (hFr : transferFrame S2 P)
    (hNo2 : S2.objects.noResizeDue) {epId : SeLe4n.ObjId} {ep : Endpoint}
    {tid s : SeLe4n.ThreadId} {sTcbP rtP : TCB} {rid : SeLe4n.ReplyId}
    (hE : P.objects[epId]? = some (.endpoint ep)) (hS : P.objects[s.toObjId]? = some (.tcb sTcbP))
    (hTk : receiveCallTakesReplyInPlace P epId tid s sTcbP rid = true)
    (hCx : callerContextReady P s sTcbP rid = true) (hRt : P.getTcb? tid = some rtP)
    (hOr : rtP.scBindingScCode = 0 ∨ receiveReturnFires true P tid = true) :
    ∃ sTcb2, (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep) ∧
      (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2) ∧
      SenderWordsKept sTcb2 sTcbP ∧ sTcb2.scBindingScCode = sTcbP.scBindingScCode ∧
      determineTargetCore (receiveReturnSchedContext true S2 tid) s = determineTargetCore P s ∧
      determineTargetCore (receiveReturnSchedContext true S2 tid) tid = determineTargetCore P tid ∧
      receiveCallDonatesInPlace (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid =
        true := by
  have hE2 := hFr.obj hE rfl (transferView_endpoint_back ep)
  obtain ⟨sTcb2, hS2, e⟩ := hFr.tcb hS
  have hK := SenderWordsKept.of_withoutLinks e
  obtain ⟨hB, -, hRO, -⟩ := withoutLinks_fields e
  have hTk2 := receiveCallTakesReplyInPlace_of_transferFrame hFr epId tid s sTcbP sTcb2 rid hK hRO hTk
  have hCx2 := callerContextReady_of_transferFrame hFr s sTcbP sTcb2 rid hB hCx
  obtain ⟨rt2, hRt2, e2⟩ := hFr.getTcb?_some hRt
  obtain ⟨hB2, -, -, -⟩ := withoutLinks_fields e2
  have hOr2 : rt2.scBindingScCode = 0 ∨ receiveReturnFires true S2 tid = true := by
    rw [hB2, receiveReturnFires_of_transferFrame hFr]; exact hOr
  obtain ⟨hEQ, hSQ, hDs, hDt, hGQ⟩ := receiveReturnSchedContext_callDonationGuard S2 epId ep tid s
    sTcb2 rid rt2 hNo2 hE2 hS2 hTk2 hCx2 hRt2 hOr2
  exact ⟨sTcb2, hEQ, hSQ, hK, hB, hDs.trans (determineTargetCore_of_transferFrame hFr s),
    hDt.trans (determineTargetCore_of_transferFrame hFr tid), hGQ⟩

/-- A lending take's guard read after the pop is read before the receive's
return, the server holding no context. -/
theorem receiveCallDonatesInPlace_pre {P : SystemState} {epId : SeLe4n.ObjId}
    {tid s : SeLe4n.ThreadId} {sTcb : TCB} {rid : SeLe4n.ReplyId}
    (h : receiveCallDonatesInPlace P epId tid s sTcb rid = true) :
    receiveCallTakesReplyInPlace P epId tid s sTcb rid = true ∧
      callerContextReady P s sTcb rid = true ∧
      ∃ rt, P.getTcb? tid = some rt ∧
        (rt.scBindingScCode = 0 ∨ receiveReturnFires true P tid = true) := by
  unfold receiveCallDonatesInPlace at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases hT : P.getTcb? tid with
  | none => rw [hT] at h2; cases h2
  | some rt =>
    rw [hT] at h2
    simp only [callDonationReady_eq_callerContextReady, Bool.and_eq_true, beq_iff_eq] at h2
    exact ⟨h1, h2.2, rt, rfl, Or.inl h2.1⟩

/-- **The held arm's take, lending nothing, through the transfer and the
receive's return**: a server bound to no notification returns nothing. -/
theorem callTakeGuard_through {P S2 : SystemState} (hFr : transferFrame S2 P)
    {epId : SeLe4n.ObjId} {ep : Endpoint} {tid s : SeLe4n.ThreadId} {sTcbP rtP : TCB}
    {rid : SeLe4n.ReplyId}
    (hE : P.objects[epId]? = some (.endpoint ep)) (hS : P.objects[s.toObjId]? = some (.tcb sTcbP))
    (hG : receiveCallTakesInPlace P epId tid s sTcbP rid = true)
    (hRt : P.getTcb? tid = some rtP) (hBN : rtP.boundNotificationCode = 0) :
    ∃ sTcb2, (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep) ∧
      (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2) ∧
      SenderWordsKept sTcb2 sTcbP ∧ sTcb2.scBindingScCode = sTcbP.scBindingScCode ∧
      determineTargetCore (receiveReturnSchedContext true S2 tid) s = determineTargetCore P s ∧
      determineTargetCore (receiveReturnSchedContext true S2 tid) tid = determineTargetCore P tid ∧
      receiveCallTakesInPlace (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid =
        true := by
  obtain ⟨rt2, hRt2, e2⟩ := hFr.getTcb?_some hRt
  obtain ⟨-, -, -, hBN2⟩ := withoutLinks_fields e2
  have hQ : receiveReturnSchedContext true S2 tid = S2 := by
    unfold receiveReturnSchedContext
    simp only [↓reduceIte, hRt2, hBN2, hBN]
  rw [hQ]
  have hE2 := hFr.obj hE rfl (transferView_endpoint_back ep)
  obtain ⟨sTcb2, hS2, e⟩ := hFr.tcb hS
  have hK := SenderWordsKept.of_withoutLinks e
  obtain ⟨hB, -, -, -⟩ := withoutLinks_fields e
  exact ⟨sTcb2, hE2, hS2, hK, hB, determineTargetCore_of_transferFrame hFr s,
    determineTargetCore_of_transferFrame hFr tid,
    receiveCallTakesInPlace_of_transferFrame hFr epId tid s sTcbP sTcb2 rid hK e hG⟩

/-- **What the arm's Call take asks of the pre-state**, beyond its reply leg's
guard: the take and the donation read past the reply leg (the arms that pop
nothing), past the pop (the donated and unheld arms, the unheld server holding
no context), or the take lending nothing past the held pop, its server bound to
no notification, so the receive's return takes nothing back from it. -/
def ReplyRecvArm.CallAdmits : ReplyRecvArm → SystemState → SeLe4n.ObjId → SeLe4n.ThreadId →
    SeLe4n.ThreadId → TCB → SeLe4n.ReplyId → Prop
  | .rendezvous, st, epId, tid, s, sTcb, rid => receiveCallDonatesPastReply st epId tid s sTcb rid = true
  | .unlinked, st, epId, tid, s, sTcb, rid => receiveCallDonatesPastReply st epId tid s sTcb rid = true
  | .donated, st, epId, tid, s, sTcb, rid =>
      receiveCallDonatesPastPop st epId tid s sTcb rid (replyHeadContextCode st rid) = true
  | .unheld, st, epId, tid, s, sTcb, rid =>
      receiveCallDonatesPastPop st epId tid s sTcb rid (replyHeadContextCode st rid) = true ∧
        ∃ rt, st.getTcb? tid = some rt ∧ rt.scBindingScCode = 0
  | .held, st, epId, tid, s, sTcb, _ =>
      receiveCallTakesPastPop st epId tid s sTcb = true ∧
        ∃ rt, st.getTcb? tid = some rt ∧ rt.boundNotificationCode = 0

/-- **The arm's reply leg, pop, transfer and the receive's return carry the
Call take's guard**: on the state the return leaves, the endpoint is as it was,
the queued caller `s` a thread keeping every word the take reads, its binding
and its home, the server its home, and the arm's take guard (`CallReady`)
holds, each read on the pre-state.  Per arm, the arm's own carry across the
reply leg and pop (`storeReplyRendezvous_callDonationGuard`,
`popDonationSettled_callDonationGuard`, `keepHeldPop_callTakeGuard`,
`popUnheldSettled_callDonationGuard`, `storeReplyLeg_callDonationGuard`); the
transfer and the return once (`callDonationGuard_through`,
`callTakeGuard_through`). -/
theorem ReplyRecvArm.callTakeGuard (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmits st epId tid s sTcb rid)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    {S2 : SystemState}
    (hFr : transferFrame S2 (arm.pop (arm.leg st c tid rid msg) c tid scId home))
    (hNo2 : S2.objects.noResizeDue) :
    ∃ sTcb2, (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep) ∧
      (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2) ∧
      SenderWordsKept sTcb2 sTcb ∧ sTcb2.scBindingScCode = sTcb.scBindingScCode ∧
      determineTargetCore (receiveReturnSchedContext true S2 tid) s = determineTargetCore st s ∧
      determineTargetCore (receiveReturnSchedContext true S2 tid) tid =
        determineTargetCore st tid ∧
      arm.CallReady (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid := by
  -- every lending arm, once its carry across the reply leg and pop is read
  have lend : ∀ {P : SystemState}, transferFrame S2 P →
      P.objects[epId]? = some (.endpoint ep) →
      (∃ sTcbP, P.objects[s.toObjId]? = some (.tcb sTcbP) ∧ SenderWordsKept sTcbP sTcb ∧
        sTcbP.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore P s = determineTargetCore st s ∧
        determineTargetCore P tid = determineTargetCore st tid ∧
        receiveCallTakesReplyInPlace P epId tid s sTcbP rid = true ∧
        callerContextReady P s sTcbP rid = true ∧
        ∃ rtP, P.getTcb? tid = some rtP ∧
          (rtP.scBindingScCode = 0 ∨ receiveReturnFires true P tid = true)) →
      arm.callLends = true →
      ∃ sTcb2, (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep) ∧
        (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2) ∧
        SenderWordsKept sTcb2 sTcb ∧ sTcb2.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore (receiveReturnSchedContext true S2 tid) s = determineTargetCore st s ∧
        determineTargetCore (receiveReturnSchedContext true S2 tid) tid =
          determineTargetCore st tid ∧
        arm.CallReady (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid := by
    intro P hF hEP ⟨sTcbP, hSP, hK, hB, hDs, hDt, hTk, hCx, rtP, hRt, hOr⟩ hL
    obtain ⟨sTcb2, hEQ, hSQ, hKQ, hBQ, hDsQ, hDtQ, hGQ⟩ :=
      callDonationGuard_through hF hNo2 hEP hSP hTk hCx hRt hOr
    refine ⟨sTcb2, hEQ, hSQ, hKQ.trans hK, hBQ.trans hB, hDsQ.trans hDs, hDtQ.trans hDt, ?_⟩
    unfold CallReady; rw [hL]; exact hGQ
  have ofDonates : ∀ {P : SystemState},
      (∃ sTcbP, P.objects[s.toObjId]? = some (.tcb sTcbP) ∧ SenderWordsKept sTcbP sTcb ∧
        sTcbP.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore P s = determineTargetCore st s ∧
        determineTargetCore P tid = determineTargetCore st tid ∧
        receiveCallDonatesInPlace P epId tid s sTcbP rid = true) →
      (∃ sTcbP, P.objects[s.toObjId]? = some (.tcb sTcbP) ∧ SenderWordsKept sTcbP sTcb ∧
        sTcbP.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore P s = determineTargetCore st s ∧
        determineTargetCore P tid = determineTargetCore st tid ∧
        receiveCallTakesReplyInPlace P epId tid s sTcbP rid = true ∧
        callerContextReady P s sTcbP rid = true ∧
        ∃ rtP, P.getTcb? tid = some rtP ∧
          (rtP.scBindingScCode = 0 ∨ receiveReturnFires true P tid = true)) := by
    intro P ⟨sTcbP, hSP, hK, hB, hDs, hDt, hG⟩
    obtain ⟨hTk, hCx, hR⟩ := receiveCallDonatesInPlace_pre hG
    exact ⟨sTcbP, hSP, hK, hB, hDs, hDt, hTk, hCx, hR⟩
  cases arm with
  | rendezvous =>
    obtain ⟨_, hG, hNe⟩ := hAd
    have hNo := replyWakesInPlace_noResizeDue hG
    have hG0 := hG
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG0
    obtain ⟨⟨⟨⟨⟨_, _⟩, hFC⟩, hLR⟩, hFR⟩, hRpG⟩ := hG0
    rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRp] at hRpG
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hRpG
    obtain ⟨hNx, -⟩ := hRpG
    obtain ⟨hE1, rest⟩ := storeReplyRendezvous_callDonationGuard st c tid rid msg ct rp epId ep s
      sTcb hNo hT hFC hRp hNx hLR hFR hE hS hSC hNe hCA
    exact lend hFr hE1 rest rfl
  | unlinked =>
    obtain ⟨_, hG, hNe⟩ := hAd
    have hG' := hG
    simp only [replyUnlinkedInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG'
    obtain ⟨⟨⟨⟨⟨_, _⟩, hFC⟩, hLR⟩, hFR⟩, hRpG⟩ := hG'
    rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRp] at hRpG
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hRpG
    obtain ⟨hNx, -⟩ := hRpG
    have hW : replyWakesInPlace st c ct rid = true := hG
    obtain ⟨hE1, rest⟩ := storeReplyLeg_callDonationGuard st c tid rid msg ct rp epId ep s
      sTcb (replyWakesInPlace_noResizeDue hW) hT hFC hRp hNx hLR hFR hE hS hSC hNe hCA
    exact lend hFr hE1 rest rfl
  | donated =>
    obtain ⟨_, hSRes, hG, rfl, rfl⟩ := hAd
    obtain ⟨rp', scId, sc, hRp', hN, hScO, hHead, hBelow, hCode, _, hNe, hNo, _, hFC, hLR, hFR,
      _, _⟩ := replyPopsInPlace_donation st c tid rid msg ct hT hSRes hG
    rw [hRp] at hRp'
    cases hRp'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
      rw [hCode]; rfl
    rw [hSc] at hFr
    have hCA' : receiveCallDonatesPastPop st epId tid s sTcb rid (scId.val + 1) = true := by
      have h := hCA; simp only [CallAdmits, hCode] at h; exact h
    obtain ⟨hE1, rest⟩ := popDonationSettled_callDonationGuard st c tid rid msg ct rp scId sc
      (determineTargetCore st c) epId ep s sTcb _ rfl hNo hT hFC hRp hN hScO hHead hBelow
      (fun e => hNe e.symm) hLR hFR (replyPopsInPlace_serverTcb hG) hE hS hSC hCA'
    exact lend hFr hE1 (ofDonates rest) rfl
  | unheld =>
    obtain ⟨_, hG, hNe, rfl, rfl⟩ := hAd
    obtain ⟨hCA1, rt, hRtT, hRt0⟩ := hCA
    obtain ⟨rp', scId, hRp', hN, hCode, _, hNo, _, hFC, hLR, hFR, _, -⟩ :=
      replyUnheldPopsInPlace_pop st c rid msg ct hT hG
    obtain ⟨rp'', scId', sc, hRp'', hN', hScO, hHead, hBelow⟩ := replyUnheldPopsInPlace_stack st c rid hG
    rw [hRp] at hRp' hRp''
    cases hRp'
    cases hRp''
    rw [hN] at hN'
    cases hN'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
      rw [hCode]; rfl
    rw [hSc] at hFr
    rw [hCode] at hCA1
    obtain ⟨hE1, rest⟩ := popUnheldSettled_callDonationGuard st c tid rid msg ct rp scId sc
      (determineTargetCore st c) epId ep s sTcb rt _ rfl hNo hT hFC hRp hN hScO hHead hBelow hNe
      hLR hFR hRtT hRt0 hE hS hSC hCA1
    exact lend hFr hE1 (ofDonates rest) rfl
  | held =>
    obtain ⟨_, hG, rfl⟩ := hAd
    obtain ⟨hCA1, rt, hRtT, hBN0⟩ := hCA
    obtain ⟨rp', scId, sc, _, hRp', hN, hScO, hHead, hBelow, hCode, _, _, hNe, hNo, _, _, _, hFC,
      hLR, hFR, _, _⟩ := replyHeldPopsInPlace_pop st c tid rid msg ct hT hG
    rw [hRp] at hRp'
    cases hRp'
    have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
      rw [hCode]; rfl
    rw [hSc] at hFr
    obtain ⟨hE1, sTcbP, hSP, hK, hB, hDs, hDt, hGP, rtP, hRtP, hBNP⟩ :=
      keepHeldPop_callTakeGuard st c tid rid msg ct rp scId sc epId ep s sTcb rt _ rfl hNo hT hFC
        hRp hN hScO hHead hBelow (fun e => hNe e.symm) hLR hFR hRtT hE hS hSC hCA1
    obtain ⟨sTcb2, hEQ, hSQ, hKQ, hBQ, hDsQ, hDtQ, hGQ⟩ :=
      callTakeGuard_through hFr hE1 hSP hGP hRtP (hBNP.trans hBN0)
    refine ⟨sTcb2, hEQ, hSQ, hKQ.trans hK, hBQ.trans hB, hDsQ.trans hDs, hDtQ.trans hDt, ?_⟩
    unfold CallReady; exact hGQ

/-- **The reply-receive meeting a queued caller, over every arm and answer**:
under the arm's reply-leg guard and its Call-take guard (`CallAdmits`), a caller
`s` at the head of the endpoint's send queue, blocked by a routed
capability-free call and delivering no fault (each read on the pre-state), and a
reply-leg transfer answering `(summary, S2)` within the transfer's frame, the
composite is the arm's reply leg and pop, the transfer, the server's context
return, the take, the arm's lend of the caller's context (every context, core
and word read on the pre-state) and the server's priority walk, then the
caller's answer.  The one equality every Call-take shape is joined to the
specification through: the reply leg and pop per arm (`ReplyRecvArm.legPop`),
the guard per arm (`ReplyRecvArm.callTakeGuard`), the take once
(`replyRecvAnsweringOnCore_callTake_of_pop`). -/
theorem replyRecvAnsweringOnCore_arm_callTake (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId}
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmits st epId tid s sTcb rid)
    (hSz : ¬ msg.registers.size > maxMessageRegisters)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .call capAddr mi)
    (hF : sTcb.ipcFaultSend = false)
    {summary : CapTransferSummary} {S2 : SystemState}
    (hXf : replyRecvReplyTransfer answer st tid c grant
      (arm.pop (arm.leg st c tid rid msg) c tid scId home) = .ok (summary, S2))
    (hFr : transferFrame S2 (arm.pop (arm.leg st c tid rid msg) c tid scId home))
    (hNo2 : S2.objects.noResizeDue) :
    ∃ sTcb2, (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep) ∧
      (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2) ∧
      SenderWordsKept sTcb2 sTcb ∧
      arm.CallReady (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid ∧
      endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
        .ok ({ results := #[] }, replyRecvAnswerCaller answer
          (PriorityInheritance.propagatePipChainCrossCore (arm.callLend
            (receiveCallTakeState (receiveReturnSchedContext true S2 tid) epId s sTcb2 tid rid) s
            tid ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s) (determineTargetCore st tid))
            tid core).1 c summary.capInfo) := by
  obtain ⟨hRecS, -, -, -, S1, x, hEq, hPop⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid msg core ct rp hAd hSz hT hRO hRp
  obtain ⟨sTcb2, hE2, hS2, hK, hB, hDs, hDt, hG2⟩ := arm.callTakeGuard (scId := scId)
    (home := home) st c tid rid msg ct rp epId ep s sTcb hAd hCA hT hRp hE hS hSC hFr hNo2
  have hR2 : registerRoutedSyscall
      (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb2.registerContext)
      SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 = .call capAddr mi := by
    rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  obtain ⟨hRecv, hC, hD⟩ := arm.callTake_receive _ epId ep tid rid core s sTcb2 capAddr mi hE2 hH
    hS2 hG2 hF2 hR2
  rw [hB, hDs, hDt] at hD
  exact ⟨sTcb2, hE2, hS2, hK, hG2, replyRecvAnsweringOnCore_callTake_of_pop arm answer st epId tid
    c rid msg grant core s hRecS hEq hPop hXf hRecv hC hD⟩

/-! ### The Call take's writes after the reply leg and pop, in place -/

theorem ReplyRecvArm.callLend_msg (arm : ReplyRecvArm) (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (X : SystemState) (s tid : SeLe4n.ThreadId) (scS : SeLe4n.SchedContextId)
    (dh rh : CoreId) (hNo : X.objects.noResizeDue) (hS : r ≠ s) :
    arm.callLend (X.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) s tid scS dh rh =
      (arm.callLend X s tid scS dh rh).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold ReplyRecvArm.callLend
  split
  · exact lendSchedContextInPlace_msg r ρ μ π X s tid scS dh rh hNo hS
  · rfl

theorem ReplyRecvArm.callLend_noResizeDue (arm : ReplyRecvArm) (X : SystemState)
    (s tid : SeLe4n.ThreadId) (scS : SeLe4n.SchedContextId) (dh rh : CoreId)
    (hNo : X.objects.noResizeDue) : (arm.callLend X s tid scS dh rh).objects.noResizeDue := by
  unfold ReplyRecvArm.callLend
  split
  · exact lendSchedContextInPlace_noResizeDue X s tid scS dh rh hNo
  · exact hNo

/-- **The Call take's writes before the server's own frame, over the arm**: the
caller popped, blocked on the reply and linked, the server made ready, the
arm's lend, the server's priority walk, then the answered caller's frame with
the transfer's report (read from the server's saved registers `rf`). -/
@[inline] def ReplyRecvArm.callTakeLegs (arm : ReplyRecvArm) (capInfo : Nat) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) : SystemState :=
  deliverReplyRecvCapsFrame capInfo (PriorityInheritance.propagatePipChainCrossCore
    (arm.callLend (storeReceiveCallReady Y epId s nextCode tid rid) s tid scS dh rh) tid core).1
    c layout rf len badge

/-- **The Call take's tail, over the arm, stages the caller's held reply and
the server's message as frames**, the take, the lend and the walk committed
past both writes. -/
theorem ReplyRecvArm.callTakeFrame_staged (arm : ReplyRecvArm) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (sTcb : TCB)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (capInfo : Nat) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hNo : Y.objects.noResizeDue) (hNe : tid ≠ c) (hSC : s ≠ c) (hST : s ≠ tid)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .call capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore (arm.callLend
          (receiveCallTakeState (Y.mapTcbInPlace c (holdMessage
            { registers := Architecture.regMessageBody layout rf len, badge := badge }))
            epId s sTcb tid rid) s tid scS dh rh) tid core).1 c capInfo) tid 0 =
      writeReceiverMessageFrame
        (arm.callTakeLegs capInfo Y c tid s rid epId sTcb.queueNextCode scS dh rh core layout rf
          len badge) tid sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
        sTcb.ipcBadged := by
  generalize hM : ({ registers := Architecture.regMessageBody layout rf len, badge := badge } :
    IpcMessage) = m
  unfold ReplyRecvArm.callTakeLegs writeReceiverMessageFrame
  have hcs : c ≠ s := fun e => hSC e.symm
  have hct : c ≠ tid := fun e => hNe e.symm
  have hNoC : (Y.mapTcbInPlace c (holdMessage m)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo
  rw [receiveCallTakeState_eq_hold _ _ _ _ _ _ hNoC]
  rw [(blockedSender_of_routedCall _ s sTcb capAddr mi hR hF).2]
  rw [storeReceiveCallReady_msg c id _ id _ epId s _ tid rid hNo hcs hct]
  have hNoR := storeReceiveCallReady_noResizeDue Y epId s sTcb.queueNextCode tid rid hNo
  generalize storeReceiveCallReady Y epId s sTcb.queueNextCode tid rid = R at hNoR
  generalize hMS :
    ({ registers := Architecture.regMessageBody arm64DefaultLayout sTcb.registerContext mi.length,
       badge := sTcb.ipcBadgeView } : IpcMessage) = mS
  have hNoRc : (R.mapTcbInPlace c (holdMessage m)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoR
  rw [arm.callLend_msg tid id _ id _ s tid scS dh rh hNoRc hST.symm,
    arm.callLend_msg c id _ id R s tid scS dh rh hNoR hcs]
  have hNoM := arm.callLend_noResizeDue R s tid scS dh rh hNoR
  rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ ?_,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoM]
  rotate_left
  · exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoM
  have hNoY := propagatePipChainCrossCore_noResizeDue _ tid core hNoM
  generalize (PriorityInheritance.propagatePipChainCrossCore (arm.callLend R s tid scS dh rh) tid
    core).1 = Z at hNoY ⊢
  rw [show ∀ m : IpcMessage, TCB.withMessageSlots id (fun _ => some m) id = holdMessage m from
    fun _ => rfl]
  rw [SystemState.mapTcbInPlace_swap Z _ _ (fun h => absurd h hNe)]
  have hNoZt : (Z.mapTcbInPlace tid (holdMessage mS)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoY
  rw [stageDeliveredMessage_holdMessage_caps _ c _ _ hNoZt
      (by rw [← hM, Architecture.regMessageBody_size]; exact hSz4),
    writeDeliveredFrameIfReady_mapTcbInPlace Z c tid _ _ _ hct,
    ← hM, returnFrameOfMessage_regMessageBody_capsOpt]
  rw [show writeDeliveredFrameIfReady Z c (regMessageFrameCapsOpt layout rf len badge capInfo)
      (fun _ => Z.mapTcbInPlace c (holdMessage
        { registers := Architecture.regMessageBody layout rf len, badge := badge })) =
      deliverReplyRecvCapsFrame capInfo Z c layout rf len badge from rfl]
  have hNoD := deliverReplyRecvCapsFrame_noResizeDue capInfo Z c layout rf len badge hNoY
  generalize deliverReplyRecvCapsFrame capInfo Z c layout rf len badge = D at hNoD ⊢
  have hSzS : mS.registers.size ≤ 4 := by
    rw [← hMS]
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageDeliveredMessage_holdMessage _ tid _ hNoD hSzS, ← hMS,
    Architecture.returnFrameOfMessage_regMessageBody, Architecture.regMessageFrameW_eq,
    TCB.ipcBadgeView_eq_opt]

/-- The Call take's guard on the state the receive runs on asks the take's
slots of the receive whatever the arm lends. -/
theorem ReplyRecvArm.CallReady.takesReply {arm : ReplyRecvArm} {Q : SystemState}
    {epId : SeLe4n.ObjId} {tid s : SeLe4n.ThreadId} {sTcb : TCB} {rid : SeLe4n.ReplyId}
    (h : arm.CallReady Q epId tid s sTcb rid) :
    receiveCallTakesReplyInPlace Q epId tid s sTcb rid = true := by
  unfold ReplyRecvArm.CallReady at h
  split at h
  · simp only [receiveCallDonatesInPlace, Bool.and_eq_true] at h; exact h.1
  · exact receiveCallTakesReplyInPlace_of_inPlace h

theorem ReplyRecvArm.CallReady.ne {arm : ReplyRecvArm} {Q : SystemState}
    {epId : SeLe4n.ObjId} {tid s : SeLe4n.ThreadId} {sTcb : TCB} {rid : SeLe4n.ReplyId}
    (h : arm.CallReady Q epId tid s sTcb rid) : s ≠ tid := fun e => by
  have h' := h.takesReply
  simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, bne_iff_ne, ne_eq] at h'
  exact h'.1.1.1.1.1.1.1.1.1.2 e.symm

/-- **The reply-receive taking a queued caller, over every arm, its reply
transferring nothing, delivered**: the arm's reply leg and pop, the server's
context return, the take, the arm's lend, the server's priority walk and the
caller's frame (`ReplyRecvArm.callTakeLegs`). -/
@[noinline] def performReplyRecvArmCallTakeLegs (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) : SystemState :=
  arm.callTakeLegs 0 (receiveReturnSchedContextFast true
    (arm.pop (arm.legReady st c tid rid) c tid scId home) tid.val) c tid s rid epId nextCode scS
    dh rh core layout rf len badge

/-- The inert Call take over the arm: the legs (`performReplyRecvArmCallTakeLegs`)
and then the server's frame (`writeReceiverMessageFrame`), each out of line so
the arm releases the server's register file between them. -/
@[inline] def performReplyRecvArmCallTakeDelivered (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (sRf : SeLe4n.RegisterFile) (sLen : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) : SystemState :=
  writeReceiverMessageFrame (performReplyRecvArmCallTakeLegs arm scId home st c tid rid epId s
    nextCode scS dh rh core layout rf len badge) tid sRf sLen badgeWord badged

/-- **The reply-receive taking a queued caller, its reply transferring nothing,
is the specification's, over every arm**: under the arm's reply-leg guard and
Call-take guard, a reply of at most four words transferring no capability, and
a caller `s` at the head of the send queue blocked by a routed capability-free
call, not delivering a fault (every check read on the pre-state), the checked
arm's result is `performReplyRecvArmCallTakeDelivered`, every context, core and
word it takes read on the pre-state. -/
theorem replyRecvOnCore_arm_callTakeDelivered (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmits st epId tid s sTcb rid)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hInert : replyTransferInert st tid ct grant = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .call capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmCallTakeDelivered arm scId home st c tid rid epId s
        sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
        (determineTargetCore st tid) core layout rf len badge sTcb.registerContext mi.length
        (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged) := by
  have hSz : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]; unfold maxMessageRegisters; omega
  obtain ⟨-, hNe, hNo, -, -⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge } core ct rp hAd
      hSz hT hRO hRp
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNoX := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid
    (arm.legReady_noResizeDue st c tid rid hNo)
  have hNoP : (arm.pop (arm.leg st c tid rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge }) c tid scId
      home).objects.noResizeDue := by
    rw [arm.pop_leg_hold st c tid rid _ hNo hNe]
    exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoX
  have hXf := replyRecvReplyTransfer_of_inert none st tid c grant ct hTc (fun _ => hInert)
    (arm.pop (arm.leg st c tid rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge }) c tid scId home)
  obtain ⟨sTcb2, -, -, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_callTake arm none st epId
    tid c rid _ grant core ct rp ep s sTcb capAddr mi hAd hCA hSz hT hRO hRp hE hH hS hSC hR hF
    hXf (transferFrame.refl _) hNoP
  have hR2 : registerRoutedSyscall
      (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb2.registerContext)
      SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 = .call capAddr mi := by
    rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  have hST := hG2.ne
  unfold endpointReplyRecvOnCore
  rw [hEq]
  dsimp only
  rw [CapTransferSummary.capInfo_empty, replyRecvAnswerCaller_none]
  rw [arm.pop_leg_hold st c tid rid _ hNo hNe,
    receiveReturnSchedContext_msg c id _ id true _ tid hNoX hNe.symm]
  rw [arm.callTakeFrame_staged _ c tid s rid epId sTcb2 _ _ _ core layout rf len badge 0 capAddr mi
    (receiveReturnSchedContext_noResizeDue true _ tid hNoX) hNe hSC hST hSz4 hR2 hF2,
    hK.queueNext, hK.regs, hK.badge, hK.badged]
  unfold performReplyRecvArmCallTakeDelivered performReplyRecvArmCallTakeLegs
  rw [receiveReturnSchedContextFast_eq]

/-- **The reply-receive taking a queued caller, over every arm, its reply leg
transferring, delivered**: the arm's reply leg and pop, the transfer in place
on no endpoint, the server's context return, the take, the arm's lend, the
server's priority walk, then the caller's frame with the transfer's report.
The replier and the caller enter as the words the transfer reads of them, all
read before the reply's writes. -/
@[noinline] def performReplyRecvArmCallTakeCapsLegs (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := arm.pop (arm.legReady st c tid rid) c tid scId home
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    arm.callTakeLegs (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (receiveReturnSchedContextFast true
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X) tid.val)
      c tid s rid epId nextCode scS dh rh core layout rf len badge

/-- The installing Call take over the arm, its legs
(`performReplyRecvArmCallTakeCapsLegs`) and then the server's frame
(`writeReceiverMessageFrame`). -/
@[inline] def performReplyRecvArmCallTakeCapsDelivered (arm : ReplyRecvArm)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (sRf : SeLe4n.RegisterFile) (sLen : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  writeReceiverMessageFrame (performReplyRecvArmCallTakeCapsLegs arm scId home st c tid rid epId s
    nextCode scS dh rh core layout rf len badge sv sb sroot count rv rb rroot) tid sRf sLen
    badgeWord badged

/-- **The reply-receive taking a queued caller, its reply leg transferring, is
the specification's, over every arm**: under the guard of
`replyRecvOnCore_arm_callTakeDelivered` (its inert transfer replaced by a
granting replier whose frame asks for `count` capabilities, `hReq`), the
checked arm's result is `performReplyRecvArmCallTakeCapsDelivered`. -/
theorem replyRecvOnCore_arm_callTakeCapsDelivered (arm : ReplyRecvArm)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (stcb : TCB) (count : Nat)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmits st epId tid s sTcb rid)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .call capAddr mi)
    (hF : sTcb.ipcFaultSend = false)
    (hReq : replyCapRequest st tid true = frameCapRequestOf st stcb count) :
    (match endpointReplyRecvOnCore epId tid rid c
        { registers := Architecture.regMessageBody layout rf len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmCallTakeCapsDelivered arm scId home st c tid rid epId s
        sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
        (determineTargetCore st tid) core layout rf len badge sTcb.registerContext mi.length
        (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
        stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2] ct.ipcBuffer
        ct.spaceCells[0]) := by
  have hSz : ¬ (Architecture.regMessageBody layout rf len).size > maxMessageRegisters := by
    rw [Architecture.regMessageBody_size]; unfold maxMessageRegisters; omega
  obtain ⟨-, hNe, hNo, -, -⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid
      { registers := Architecture.regMessageBody layout rf len, badge := badge } core ct rp hAd
      hSz hT hRO hRp
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hP1 := arm.pop_leg_hold (scId := scId) (home := home) st c tid rid
    { registers := Architecture.regMessageBody layout rf len, badge := badge } hNo hNe
  have hNoX := arm.legReady_noResizeDue st c tid rid hNo
  have hAP := (arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid hNoX).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid hNoX
  generalize hX : arm.pop (arm.legReady st c tid rid) c tid scId home = X at hP1 hNoP hAP
  generalize hMsg : ({ registers := Architecture.regMessageBody layout rf len, badge := badge } :
    IpcMessage) = msg at hP1
  obtain ⟨sm, Y1, hT1⟩ := receiveTransferCaps_ok (frameCapRequestOf st stcb count) none
    (capTargetOf st ct) X
  have hNoY := receiveTransferCaps_noResizeDue _ _ _ X Y1 sm hNoP hT1
  have hHT : receiveTransferCaps (frameCapRequestOf st stcb count) none (capTargetOf st ct)
      (X.mapTcbInPlace c (holdMessage msg)) = .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withMessageSlots _ _ _) c _ _ _ X hNoP, hT1]
    rfl
  have hFr := (receiveTransferCaps_reply_transferFrame (S := X.mapTcbInPlace c (holdMessage msg))
    ((ipcBufferReadsAgree_mapTcbInPlace X c (holdMessage msg) (fun _ => ⟨rfl, rfl⟩)).trans hAP)
    ((RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoP) c.toObjId stcb ct count hHT).1
  have hXf : replyRecvReplyTransfer none st tid c true
      (arm.pop (arm.leg st c tid rid msg) c tid scId home) =
      .ok (sm, Y1.mapTcbInPlace c (holdMessage msg)) := by
    show replyTransferCaps st tid c true _ = _
    unfold replyTransferCaps
    rw [hReq, hTgt, hP1, hHT]
  rw [← hP1] at hFr
  subst hMsg
  obtain ⟨sTcb2, -, -, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_callTake arm none st epId
    tid c rid _ true core ct rp ep s sTcb capAddr mi hAd hCA hSz hT hRO hRp hE hH hS hSC hR hF hXf
    hFr ((SystemState.mapTcbInPlace_noResizeDue _ _ _).mpr hNoY)
  have hR2 : registerRoutedSyscall
      (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb2.registerContext)
      SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 = .call capAddr mi := by
    rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  have hST := hG2.ne
  unfold endpointReplyRecvOnCore
  rw [hEq]
  dsimp only
  rw [CapTransferSummary.capInfo_empty, replyRecvAnswerCaller_none]
  rw [receiveReturnSchedContext_msg c id _ id true Y1 tid hNoY hNe.symm]
  rw [arm.callTakeFrame_staged _ c tid s rid epId sTcb2 _ _ _ core layout rf len badge sm.capInfo
    capAddr mi (receiveReturnSchedContext_noResizeDue true Y1 tid hNoY) hNe hSC hST hSz4 hR2 hF2,
    hK.queueNext, hK.regs, hK.badge, hK.badged, ← receiveReturnSchedContextFast_eq]
  have hKl := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => arm.callTakeLegs i (receiveReturnSchedContextFast true Y tid.val) c tid s rid epId
      sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
      (determineTargetCore st tid) core layout rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hKl
  rw [hAP.frameCapRequestOf, hAP.capTargetOf, hT1] at hKl
  unfold performReplyRecvArmCallTakeCapsDelivered performReplyRecvArmCallTakeCapsLegs
  rw [hX]
  dsimp only
  rw [hKl]

/-! ### The long message -/

/-- **The in-place donation reads no IPC buffer**: it rewrites a context, the
taken caller's reply frame and the frame below it, two threads' binding codes
and the scheduler's marks, never a VSpace root, a buffer address, a frame, a
CNode or the machine. -/
theorem ipcBufferReadsAgree_donateSchedContextInPlace (st : SystemState)
    (client server : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (donateSchedContextInPlace st client server scId) st := by
  unfold donateSchedContextInPlace
  split
  · exact .refl st
  rename_i sc _
  split
  · exact .refl st
  split
  · exact .refl st
  split
  · exact .refl st
  split
  · exact .refl st
  dsimp only
  refine (ipcBufferReadsAgree_markKeyChangeParts _ _ _ _ _).trans ?_
  refine (ipcBufferReadsAgree_markCandidacyGainFor _ _ _).trans ?_
  refine (ipcBufferReadsAgree_markKeyChangeParts _ _ _ _ _).trans ?_
  refine (ipcBufferReadsAgree_markCandidacyGainFor _ _ _).trans ?_
  have hRV : ∀ (g : Reply → Reply) (o : KernelObject),
      ipcBufferViewOf (SystemState.mapReplyObject g o) = ipcBufferViewOf o := by
    intro g o; cases o <;> rfl
  have U : ∀ (f : SchedContext → SchedContext) (k : SeLe4n.ObjId) (g : Reply → Reply),
      ((st.updateSchedContext scId f).modifyObject k (SystemState.mapReplyObject g)).objects.noResizeDue ∧
      ipcBufferReadsAgree ((st.updateSchedContext scId f).modifyObject k
        (SystemState.mapReplyObject g)) st := fun f k g =>
    ⟨modifyObject_noResizeDue _ _ _ (updateSchedContext_noResizeDue st scId f hNo),
      (ipcBufferReadsAgree_modifyObject _ _ _ (hRV g) (updateSchedContext_noResizeDue st scId f hNo)).trans
        (ipcBufferReadsAgree_updateSchedContext st scId f hNo)⟩
  split
  · refine (ipcBufferReadsAgree_updateTcb _ _ _ ?_ ?_).trans
      ((ipcBufferReadsAgree_updateTcb _ _ _ ?_ ?_).trans ?_)
    · exact fun _ => ⟨rfl, rfl⟩
    · exact updateTcb_noResizeDue _ _ _ (U _ _ _).1
    · exact fun _ => ⟨rfl, rfl⟩
    · exact (U _ _ _).1
    · exact (U _ _ _).2
  · refine (ipcBufferReadsAgree_updateTcb _ _ _ ?_ ?_).trans
      ((ipcBufferReadsAgree_updateTcb _ _ _ ?_ ?_).trans
        ((ipcBufferReadsAgree_modifyObject _ _ _ (hRV _) ?_).trans ?_))
    · exact fun _ => ⟨rfl, rfl⟩
    · exact updateTcb_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _ (U _ _ _).1)
    · exact fun _ => ⟨rfl, rfl⟩
    · exact modifyObject_noResizeDue _ _ _ (U _ _ _).1
    · exact (U _ _ _).1
    · exact (U _ _ _).2

theorem ipcBufferReadsAgree_lendSchedContextInPlace (X : SystemState)
    (donor donee : SeLe4n.ThreadId) (scS : SeLe4n.SchedContextId) (dh rh : CoreId)
    (hNo : X.objects.noResizeDue) :
    ipcBufferReadsAgree (lendSchedContextInPlace X donor donee scS dh rh) X :=
  (ipcBufferReadsAgree_of_offReleaseLinks (migrateSchedContextReplenishment_agree _ scS dh rh)
    (migrateSchedContextReplenishment_machine _ scS dh rh)).trans
    (ipcBufferReadsAgree_donateSchedContextInPlace X donor donee scS hNo)

theorem ReplyRecvArm.ipcBufferReadsAgree_callLend (arm : ReplyRecvArm) (X : SystemState)
    (s tid : SeLe4n.ThreadId) (scS : SeLe4n.SchedContextId) (dh rh : CoreId)
    (hNo : X.objects.noResizeDue) : ipcBufferReadsAgree (arm.callLend X s tid scS dh rh) X := by
  unfold ReplyRecvArm.callLend
  split
  · exact ipcBufferReadsAgree_lendSchedContextInPlace X s tid scS dh rh hNo
  · exact .refl X

/-- **The long Call take's writes before the server's own frame, over the
arm**: as `ReplyRecvArm.callTakeLegs`, the caller's long frame with the
replier's overflow words copied into its buffer (`deliverLongReplyRecvFrame`). -/
@[inline] def ReplyRecvArm.callTakeLegsLong (arm : ReplyRecvArm) (capInfo : Nat) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  deliverLongReplyRecvFrame (PriorityInheritance.propagatePipChainCrossCore
    (arm.callLend (storeReceiveCallReady Y epId s nextCode tid rid) s tid scS dh rh) tid core).1
    c rf len tid badge capInfo

/-- **The long Call take's tail, over the arm**, stages the caller's held reply
and the server's message as frames. -/
theorem ReplyRecvArm.callTakeFrame_stagedLong (arm : ReplyRecvArm) (st0 Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (sTcb : TCB)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (capInfo : Nat) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hNo : Y.objects.noResizeDue) (hAY : ipcWordReadsAgree Y st0) (hNe : tid ≠ c) (hSC : s ≠ c)
    (hST : s ≠ tid) (hLen : 4 ≤ len)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .call capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    Architecture.stageDeliveredMessage (Architecture.stageDeliveredMessage
        (PriorityInheritance.propagatePipChainCrossCore (arm.callLend
          (receiveCallTakeState (Y.mapTcbInPlace c (holdMessage
            { registers := longReplyRecvRegs rf st0 tid len, badge := badge }))
            epId s sTcb tid rid) s tid scS dh rh) tid core).1 c capInfo) tid 0 =
      writeReceiverMessageFrame
        (arm.callTakeLegsLong capInfo Y c tid s rid epId sTcb.queueNextCode scS dh rh core rf
          len badge) tid sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
        sTcb.ipcBadged := by
  unfold ReplyRecvArm.callTakeLegsLong writeReceiverMessageFrame
  generalize hM : ({ registers := longReplyRecvRegs rf st0 tid len, badge := badge } :
    IpcMessage) = m
  have hcs : c ≠ s := fun e => hSC e.symm
  have hct : c ≠ tid := fun e => hNe e.symm
  have hNoC : (Y.mapTcbInPlace c (holdMessage m)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo
  rw [receiveCallTakeState_eq_hold _ _ _ _ _ _ hNoC]
  rw [(blockedSender_of_routedCall _ s sTcb capAddr mi hR hF).2]
  rw [storeReceiveCallReady_msg c id _ id _ epId s _ tid rid hNo hcs hct]
  have hAR := ipcBufferReadsAgree_storeReceiveCallReady Y epId s sTcb.queueNextCode tid rid hNo
  have hNoR := storeReceiveCallReady_noResizeDue Y epId s sTcb.queueNextCode tid rid hNo
  generalize storeReceiveCallReady Y epId s sTcb.queueNextCode tid rid = R at hNoR hAR
  generalize hMS :
    ({ registers := Architecture.regMessageBody arm64DefaultLayout sTcb.registerContext mi.length,
       badge := sTcb.ipcBadgeView } : IpcMessage) = mS
  have hNoRc : (R.mapTcbInPlace c (holdMessage m)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoR
  rw [arm.callLend_msg tid id _ id _ s tid scS dh rh hNoRc hST.symm,
    arm.callLend_msg c id _ id R s tid scS dh rh hNoR hcs]
  have hNoM := arm.callLend_noResizeDue R s tid scS dh rh hNoR
  rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ ?_,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoM]
  rotate_left
  · exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoM
  have hNoY := propagatePipChainCrossCore_noResizeDue _ tid core hNoM
  have hAZ : ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore
      (arm.callLend R s tid scS dh rh) tid core).1 st0 :=
    ((ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core hNoM).trans
      ((arm.ipcBufferReadsAgree_callLend R s tid scS dh rh hNoR).trans hAR)).words.trans hAY
  generalize (PriorityInheritance.propagatePipChainCrossCore (arm.callLend R s tid scS dh rh) tid
    core).1 = Z at hNoY hAZ ⊢
  rw [show ∀ m : IpcMessage, TCB.withMessageSlots id (fun _ => some m) id = holdMessage m from
    fun _ => rfl]
  rw [SystemState.mapTcbInPlace_swap Z _ _ (fun h => absurd h hNe)]
  have hNoZt : (Z.mapTcbInPlace tid (holdMessage mS)).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoY
  have hAZs := (ipcBufferReadsAgree_mapTcbInPlace _ tid (holdMessage mS)
    (fun _ => ⟨rfl, rfl⟩)).words.trans hAZ
  rw [← hM, ← deliverLongReplyRecvFrame_eq _ st0 c tid rf len badge capInfo hNoZt hAZs hLen,
    deliverLongReplyRecvFrame_mapTcbInPlace _ c tid tid rf len badge capInfo (holdMessage mS)
      (fun _ => ⟨rfl, rfl⟩) hct]
  have hNoD := deliverLongReplyRecvFrame_noResizeDue Z c rf len tid badge capInfo hNoY
  generalize deliverLongReplyRecvFrame Z c rf len tid badge capInfo = D at hNoD ⊢
  have hSzS : mS.registers.size ≤ 4 := by
    rw [← hMS]
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageDeliveredMessage_holdMessage _ tid _ hNoD hSzS, ← hMS,
    Architecture.returnFrameOfMessage_regMessageBody, Architecture.regMessageFrameW_eq,
    TCB.ipcBadgeView_eq_opt]

end SeLe4n.Kernel
