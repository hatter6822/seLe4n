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

end SeLe4n.Kernel
