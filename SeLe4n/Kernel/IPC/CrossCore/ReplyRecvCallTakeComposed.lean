/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeComposed
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCallTakeFrame

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
def CallReady (lends : Bool) (Q : SystemState) (epId : SeLe4n.ObjId)
    (tid s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) : Prop :=
  if lends then receiveCallDonatesInPlace Q epId tid s sTcb rid = true
  else receiveCallTakesInPlace Q epId tid s sTcb rid = true

/-- The rendezvous donation, in place: the taken caller `s`'s context `scS`
lent to the server where the arm lends, nothing otherwise. -/
@[inline] def callLend (lends : Bool) (X : SystemState) (s tid : SeLe4n.ThreadId)
    (scS : SeLe4n.SchedContextId) (donorHome doneeHome : CoreId) : SystemState :=
  if lends then lendSchedContextInPlace X s tid scS donorHome doneeHome else X

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
theorem callTake_receive (lends : Bool) (Q : SystemState) (epId : SeLe4n.ObjId)
    (ep : Endpoint) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (core : CoreId)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : Q.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : Q.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : ReplyRecvArm.CallReady lends Q epId tid s sTcb rid) (hF : sTcb.ipcFaultSend = false)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .call capAddr mi) :
    endpointReceiveDualWithCapsOnCore epId tid (some rid) core Q =
        (receiveCallTakeState Q epId s sTcb tid rid, .ok (s, { results := #[] }, none)) ∧
      rendezvousDequeuedCall (receiveCallTakeState Q epId s sTcb tid rid) s = true ∧
      applyRendezvousCallDonation (receiveCallTakeState Q epId s sTcb tid rid) tid s =
        .ok (ReplyRecvArm.callLend lends (receiveCallTakeState Q epId s sTcb tid rid) s tid
          ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore Q s) (determineTargetCore Q tid)) := by
  unfold CallReady at hG
  unfold callLend
  cases lends
  · simp only [Bool.false_eq_true, ↓reduceIte] at hG ⊢
    obtain ⟨hRecv, -, -⟩ := receiveCallTake_delivered Q epId ep tid rid core s sTcb capAddr mi
      hE hH hT hG hF hR
    exact ⟨hRecv, receiveCallTake_lendsNothing Q epId ep tid rid core s sTcb hE hH hT hG⟩
  · simp only [↓reduceIte] at hG ⊢
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

/-- The receive's return does not fire for a server bound to no notification. -/
theorem receiveReturnFires_of_unbound {P : SystemState} {tid : SeLe4n.ThreadId} {rt : TCB}
    (hRt : P.getTcb? tid = some rt) (hBN : rt.boundNotificationCode = 0) :
    receiveReturnFires true P tid = false := by
  unfold receiveReturnFires
  simp [hRt, hBN]

/-- **A take lending nothing, through the transfer and the receive's return**:
where the return does not fire on the state the pop leaves (the held arm's
server, and a server bound to its own context, each bound to no
notification), the transfer keeps that, so the return writes nothing. -/
theorem callTakeGuard_through {P S2 : SystemState} (hFr : transferFrame S2 P)
    {epId : SeLe4n.ObjId} {ep : Endpoint} {tid s : SeLe4n.ThreadId} {sTcbP : TCB}
    {rid : SeLe4n.ReplyId}
    (hE : P.objects[epId]? = some (.endpoint ep)) (hS : P.objects[s.toObjId]? = some (.tcb sTcbP))
    (hG : receiveCallTakesInPlace P epId tid s sTcbP rid = true)
    (hNF : receiveReturnFires true P tid = false) :
    ∃ sTcb2, (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep) ∧
      (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2) ∧
      SenderWordsKept sTcb2 sTcbP ∧ sTcb2.scBindingScCode = sTcbP.scBindingScCode ∧
      determineTargetCore (receiveReturnSchedContext true S2 tid) s = determineTargetCore P s ∧
      determineTargetCore (receiveReturnSchedContext true S2 tid) tid = determineTargetCore P tid ∧
      receiveCallTakesInPlace (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid =
        true := by
  have hQ : receiveReturnSchedContext true S2 tid = S2 :=
    receiveReturnSchedContext_of_fires_false ((receiveReturnFires_of_transferFrame hFr tid).trans hNF)
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

/-- **What a take lending nothing asks of the pre-state on the arms that lend**,
for a server bound to its own scheduling context: seL4-MCS's `reply_push`
lends only to a server holding none, so the server keeps its own context and
the caller keeps its.  The take read past the reply leg and pop
(`receiveCallTakesPastPop`), the server bound to a context and to no
notification, so the receive's return takes nothing back from it.  The
rendezvous, unlinked and unheld arms only: the donated arm's pop
(`replyPopsInPlace`) needs the context the reply heads bound to the server,
so the pop unbinds it and the take lends (`donated_serverBound_head`), and the
held arm's take lends nothing already (`CallAdmits`). -/
def ReplyRecvArm.CallAdmitsOwn : ReplyRecvArm → SystemState → SeLe4n.ObjId → SeLe4n.ThreadId →
    SeLe4n.ThreadId → TCB → Prop
  | .rendezvous, st, epId, tid, s, sTcb =>
      receiveCallTakesPastPop st epId tid s sTcb = true ∧
        ∃ rt, st.getTcb? tid = some rt ∧ rt.scBindingScCode ≠ 0 ∧ rt.boundNotificationCode = 0
  | .unlinked, st, epId, tid, s, sTcb =>
      receiveCallTakesPastPop st epId tid s sTcb = true ∧
        ∃ rt, st.getTcb? tid = some rt ∧ rt.scBindingScCode ≠ 0 ∧ rt.boundNotificationCode = 0
  | .unheld, st, epId, tid, s, sTcb =>
      receiveCallTakesPastPop st epId tid s sTcb = true ∧
        ∃ rt, st.getTcb? tid = some rt ∧ rt.scBindingScCode ≠ 0 ∧ rt.boundNotificationCode = 0
  | .donated, _, _, _, _, _ => False
  | .held, _, _, _, _, _ => False

/-- **The donated arm meets no server holding its own context**: its pop's
guard (`replyPopsInPlace`) asks that the context the reply heads be bound to
the server, so the server holds the context the caller lent it, the pop
returns it, and the take lends the next caller's (`callLends`).  Hence the
own-context take (`CallAdmitsOwn`) has no donated case. -/
theorem ReplyRecvArm.donated_serverBound_head {scId : SeLe4n.SchedContextId} {home : CoreId}
    {st : SystemState} {tid c : SeLe4n.ThreadId} {rid : SeLe4n.ReplyId} {ct : TCB}
    (h : ReplyRecvArm.donated.LegAdmits scId home st tid c rid ct) :
    (∃ rp scH sc, st.getReply? rid = some rp ∧ rp.next = some (.head scH) ∧
      st.getSchedContext? scH = some sc ∧ sc.boundThreadCode = tid.val + 1) ∧
      ReplyRecvArm.donated.callLends = true := by
  obtain ⟨_, _, hG, _, _⟩ := h
  refine ⟨?_, rfl⟩
  unfold replyPopsInPlace at hG
  simp only [Bool.and_eq_true] at hG
  obtain ⟨_, hM⟩ := hG
  split at hM
  · next rp hRp =>
    split at hM
    · next scH hN =>
      simp only [Bool.and_eq_true] at hM
      obtain ⟨_, hM⟩ := hM
      split at hM
      · next sc hSc =>
        simp only [Bool.and_eq_true, beq_iff_eq] at hM
        exact ⟨rp, scH, sc, hRp, hN, hSc, hM.1.2⟩
      · cases hM
    · cases hM
  · cases hM

/-- **The Call take's guard at the lend it takes**: the arm's own guard where
the take lends as the arm does (`CallAdmits`), the own-context guard where it
does not (`CallAdmitsOwn`). -/
def ReplyRecvArm.CallAdmitsAt (arm : ReplyRecvArm) (lends : Bool) (st : SystemState)
    (epId : SeLe4n.ObjId) (tid s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) : Prop :=
  if lends = arm.callLends then arm.CallAdmits st epId tid s sTcb rid
  else arm.CallAdmitsOwn st epId tid s sTcb

/-- A take's reply-slot guard is its no-lend guard where the server is bound
to a context (`callDonatesNothing_of_bound`). -/
theorem receiveCallTakesInPlace_of_takesReply {P : SystemState} {epId : SeLe4n.ObjId}
    {tid s : SeLe4n.ThreadId} {sTcb rt : TCB} {rid : SeLe4n.ReplyId}
    (h : receiveCallTakesReplyInPlace P epId tid s sTcb rid = true)
    (hRt : P.getTcb? tid = some rt) (hB : rt.scBindingScCode ≠ 0) :
    receiveCallTakesInPlace P epId tid s sTcb rid = true := by
  unfold receiveCallTakesReplyInPlace at h
  unfold receiveCallTakesInPlace
  rw [hRt] at h ⊢
  simpa only [Option.isSome_some, Bool.and_true, callDonatesNothing_of_bound sTcb rt hB] using h

/-- **The own-context take's guard across the arm's reply leg, pop, transfer
and the receive's return**: on the rendezvous and unlinked arms the reply leg
keeps the server's binding and its return's guard
(`storeReplyRendezvous_callTakeGuard`, `storeReplyLeg_callTakeGuard`), on the
unheld arm the pop writes no server (`popUnheldSettled_callTakeGuard`); the
take lends nothing, and the server, bound to no notification, has nothing
taken back by the return (`callTakeGuard_through`). -/
theorem ReplyRecvArm.callTakeGuardOwn (arm : ReplyRecvArm) (lends : Bool)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hLx : ¬ lends = arm.callLends)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmitsOwn st epId tid s sTcb)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep))
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    {S2 : SystemState}
    (hFr : transferFrame S2 (arm.pop (arm.leg st c tid rid msg) c tid scId home)) :
    ∃ sTcb2, (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep) ∧
      (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2) ∧
      SenderWordsKept sTcb2 sTcb ∧ sTcb2.scBindingScCode = sTcb.scBindingScCode ∧
      determineTargetCore (receiveReturnSchedContext true S2 tid) s = determineTargetCore st s ∧
      determineTargetCore (receiveReturnSchedContext true S2 tid) tid =
        determineTargetCore st tid ∧
      ReplyRecvArm.CallReady lends (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid := by
  have hL : lends = false := by
    cases arm <;> cases lends <;> first | rfl | exact absurd rfl hLx | exact absurd hCA id
  subst hL
  -- the rendezvous and unlinked arms, once the reply leg's carry is read
  have leg : ∀ {P : SystemState}, transferFrame S2 P →
      P.objects[epId]? = some (.endpoint ep) →
      (∃ sTcb1, P.objects[s.toObjId]? = some (.tcb sTcb1) ∧ SenderWordsKept sTcb1 sTcb ∧
        sTcb1.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore P s = determineTargetCore st s ∧
        determineTargetCore P tid = determineTargetCore st tid ∧
        receiveCallTakesReplyInPlace P epId tid s sTcb1 rid = true ∧
        (callerContextReady st s sTcb rid = true → callerContextReady P s sTcb1 rid = true) ∧
        ∃ rt1, P.getTcb? tid = some rt1 ∧ rt1.scBindingScCode ≠ 0 ∧
          receiveReturnFires true P tid = false) →
      ∃ sTcb2, (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep) ∧
        (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2) ∧
        SenderWordsKept sTcb2 sTcb ∧ sTcb2.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore (receiveReturnSchedContext true S2 tid) s = determineTargetCore st s ∧
        determineTargetCore (receiveReturnSchedContext true S2 tid) tid =
          determineTargetCore st tid ∧
        ReplyRecvArm.CallReady false (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid := by
    intro P hF hEP ⟨sTcb1, hSP, hK, hB, hDs, hDt, hTk, _, rt1, hRt1, hB1, hNF⟩
    obtain ⟨sTcb2, hEQ, hSQ, hKQ, hBQ, hDsQ, hDtQ, hGQ⟩ := callTakeGuard_through hF hEP hSP
      (receiveCallTakesInPlace_of_takesReply hTk hRt1 hB1) hNF
    exact ⟨sTcb2, hEQ, hSQ, hKQ.trans hK, hBQ.trans hB, hDsQ.trans hDs, hDtQ.trans hDt, hGQ⟩
  cases arm with
  | rendezvous =>
    obtain ⟨hTk, rt, hRtT, hRtB, hBN0⟩ := hCA
    obtain ⟨_, hG, hNe⟩ := hAd
    have hNo := replyWakesInPlace_noResizeDue hG
    have hG0 := hG
    simp only [replyWakesInPlace, Bool.and_eq_true] at hG0
    obtain ⟨⟨⟨⟨⟨_, _⟩, hFC⟩, hLR⟩, hFR⟩, hRpG⟩ := hG0
    rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRp] at hRpG
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hRpG
    obtain ⟨hNx, -⟩ := hRpG
    obtain ⟨hE1, sTcb1, hS1, hK, hB, hDs, hDt, hTk1, hCx, rt1, hRt1, hB1, hF1⟩ :=
      storeReplyRendezvous_callTakeGuard st c tid rid msg ct rp epId ep s sTcb hNo hT hFC hRp hNx
        hLR hFR hE hS hSC hNe rt hRtT hTk
    exact leg hFr hE1 ⟨sTcb1, hS1, hK, hB, hDs, hDt, hTk1, hCx, rt1, hRt1, fun e => hRtB (hB1.symm.trans e),
      hF1.trans (receiveReturnFires_of_unbound hRtT hBN0)⟩
  | unlinked =>
    obtain ⟨hTk, rt, hRtT, hRtB, hBN0⟩ := hCA
    obtain ⟨_, hG, hNe⟩ := hAd
    have hG' := hG
    simp only [replyUnlinkedInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG'
    obtain ⟨⟨⟨⟨⟨_, _⟩, hFC⟩, hLR⟩, hFR⟩, hRpG⟩ := hG'
    rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hRp] at hRpG
    simp only [Bool.and_eq_true, Option.isNone_iff_eq_none] at hRpG
    obtain ⟨hNx, -⟩ := hRpG
    have hW : replyWakesInPlace st c ct rid = true := hG
    obtain ⟨hE1, sTcb1, hS1, hK, hB, hDs, hDt, hTk1, hCx, rt1, hRt1, hB1, hF1⟩ :=
      storeReplyLeg_callTakeGuard st c tid rid msg ct rp epId ep s sTcb
        (replyWakesInPlace_noResizeDue hW) hT hFC hRp hNx hLR hFR hE hS hSC hNe rt hRtT hTk
    exact leg hFr hE1 ⟨sTcb1, hS1, hK, hB, hDs, hDt, hTk1, hCx, rt1, hRt1, fun e => hRtB (hB1.symm.trans e),
      hF1.trans (receiveReturnFires_of_unbound hRtT hBN0)⟩
  | unheld =>
    obtain ⟨hTk, rt, hRtT, hRtB, hBN0⟩ := hCA
    obtain ⟨_, hG, hNe, rfl, rfl⟩ := hAd
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
    obtain ⟨hE1, sTcbP, hSP, hK, hB, hDs, hDt, hGP, rtP, hRtP, hBNP⟩ :=
      popUnheldSettled_callTakeGuard st c tid rid msg ct rp scId sc (determineTargetCore st c) epId
        ep s sTcb rt _ rfl hNo hT hFC hRp hN hScO hHead hBelow hNe hLR hFR hRtT hRtB hE hS hSC hTk
    obtain ⟨sTcb2, hEQ, hSQ, hKQ, hBQ, hDsQ, hDtQ, hGQ⟩ :=
      callTakeGuard_through hFr hE1 hSP hGP (receiveReturnFires_of_unbound hRtP (hBNP.trans hBN0))
    exact ⟨sTcb2, hEQ, hSQ, hKQ.trans hK, hBQ.trans hB, hDsQ.trans hDs, hDtQ.trans hDt, hGQ⟩
  | donated => exact hCA.elim
  | held => exact hCA.elim

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
theorem ReplyRecvArm.callTakeGuard (arm : ReplyRecvArm) (lends : Bool)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (ct : TCB) (rp : Reply)
    (epId : SeLe4n.ObjId) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmitsAt lends st epId tid s sTcb rid)
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
      ReplyRecvArm.CallReady lends (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid := by
  unfold CallAdmitsAt at hCA
  by_cases hLx : lends = arm.callLends
  case neg =>
    rw [if_neg hLx] at hCA
    exact arm.callTakeGuardOwn lends st c tid rid msg ct rp epId ep s sTcb hLx hAd hCA hT hRp hE hS
      hSC hFr
  rw [if_pos hLx] at hCA
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
      lends = true →
      ∃ sTcb2, (receiveReturnSchedContext true S2 tid).objects[epId]? = some (.endpoint ep) ∧
        (receiveReturnSchedContext true S2 tid).objects[s.toObjId]? = some (.tcb sTcb2) ∧
        SenderWordsKept sTcb2 sTcb ∧ sTcb2.scBindingScCode = sTcb.scBindingScCode ∧
        determineTargetCore (receiveReturnSchedContext true S2 tid) s = determineTargetCore st s ∧
        determineTargetCore (receiveReturnSchedContext true S2 tid) tid =
          determineTargetCore st tid ∧
        ReplyRecvArm.CallReady lends (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid := by
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
    exact lend hFr hE1 rest hLx
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
    exact lend hFr hE1 rest hLx
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
    exact lend hFr hE1 (ofDonates rest) hLx
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
    exact lend hFr hE1 (ofDonates rest) hLx
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
      callTakeGuard_through hFr hE1 hSP hGP (receiveReturnFires_of_unbound hRtP (hBNP.trans hBN0))
    refine ⟨sTcb2, hEQ, hSQ, hKQ.trans hK, hBQ.trans hB, hDsQ.trans hDs, hDtQ.trans hDt, ?_⟩
    unfold CallReady; rw [hLx]; exact hGQ

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
theorem replyRecvAnsweringOnCore_arm_callTake (arm : ReplyRecvArm) (lends : Bool)
    {scId : SeLe4n.SchedContextId} {home : CoreId}
    (answer : Option Architecture.FaultReplyOutcome) (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (msg : IpcMessage) (grant : Bool)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmitsAt lends st epId tid s sTcb rid)
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
      ReplyRecvArm.CallReady lends (receiveReturnSchedContext true S2 tid) epId tid s sTcb2 rid ∧
      endpointReplyRecvAnsweringOnCore answer epId tid rid c msg grant core st =
        .ok ({ results := #[] }, replyRecvAnswerCaller answer
          (PriorityInheritance.propagatePipChainCrossCore (ReplyRecvArm.callLend lends
            (receiveCallTakeState (receiveReturnSchedContext true S2 tid) epId s sTcb2 tid rid) s
            tid ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s) (determineTargetCore st tid))
            tid core).1 c summary.capInfo) := by
  obtain ⟨hRecS, -, -, -, S1, x, hEq, hPop⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid msg core ct rp hAd hSz hT hRO hRp
  obtain ⟨sTcb2, hE2, hS2, hK, hB, hDs, hDt, hG2⟩ := arm.callTakeGuard lends (scId := scId)
    (home := home) st c tid rid msg ct rp epId ep s sTcb hAd hCA hT hRp hE hS hSC hFr hNo2
  have hR2 : registerRoutedSyscall
      (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb2.registerContext)
      SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 = .call capAddr mi := by
    rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  obtain ⟨hRecv, hC, hD⟩ := ReplyRecvArm.callTake_receive lends _ epId ep tid rid core s sTcb2 capAddr mi hE2 hH
    hS2 hG2 hF2 hR2
  rw [hB, hDs, hDt] at hD
  exact ⟨sTcb2, hE2, hS2, hK, hG2, replyRecvAnsweringOnCore_callTake_of_pop arm answer st epId tid
    c rid msg grant core s hRecS hEq hPop hXf hRecv hC hD⟩

/-! ### The Call take's writes after the reply leg and pop, in place -/

theorem ReplyRecvArm.callLend_msg (lends : Bool) (r : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (π : Nat → Nat) (X : SystemState) (s tid : SeLe4n.ThreadId) (scS : SeLe4n.SchedContextId)
    (dh rh : CoreId) (hNo : X.objects.noResizeDue) (hS : r ≠ s) :
    ReplyRecvArm.callLend lends (X.mapTcbInPlace r (TCB.withMessageSlots ρ μ π)) s tid scS dh rh =
      (ReplyRecvArm.callLend lends X s tid scS dh rh).mapTcbInPlace r (TCB.withMessageSlots ρ μ π) := by
  unfold ReplyRecvArm.callLend
  split
  · exact lendSchedContextInPlace_msg r ρ μ π X s tid scS dh rh hNo hS
  · rfl

theorem ReplyRecvArm.callLend_noResizeDue (lends : Bool) (X : SystemState)
    (s tid : SeLe4n.ThreadId) (scS : SeLe4n.SchedContextId) (dh rh : CoreId)
    (hNo : X.objects.noResizeDue) : (ReplyRecvArm.callLend lends X s tid scS dh rh).objects.noResizeDue := by
  unfold ReplyRecvArm.callLend
  split
  · exact lendSchedContextInPlace_noResizeDue X s tid scS dh rh hNo
  · exact hNo

/-! ### The reply's inline words, read once on the pre-state

The Call-take answers take the four words the reply leg reads of the
replier's message registers (`Architecture.regLayoutWord`, read by the arm on
the pre-state) in place of its register file, so nothing outside the server's
TCB holds the register file when the server's frame is written. -/

/-- Word `j` of a reply's four inline words `m0`..`m3`, `0` past them. -/
@[inline] def replyInlineWord (m0 m1 m2 m3 : UInt64) : Nat → UInt64
  | 0 => m0
  | 1 => m1
  | 2 => m2
  | 3 => m3
  | _ => 0

/-- The reply's body built from its four inline words, cut to its length `n`. -/
@[inline] def replyBodyOfWords (n : Nat) (m0 m1 m2 m3 : UInt64) : Array SeLe4n.RegValue :=
  (#[⟨m0⟩, ⟨m1⟩, ⟨m2⟩, ⟨m3⟩] : Array SeLe4n.RegValue).extract 0 n

theorem replyInlineWord_regLayoutWord (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (j : Nat) (h : j < 4) :
    replyInlineWord (Architecture.regLayoutWord layout rf 0) (Architecture.regLayoutWord layout rf 1)
      (Architecture.regLayoutWord layout rf 2) (Architecture.regLayoutWord layout rf 3) j =
      Architecture.regLayoutWord layout rf j := by
  rcases j with _ | _ | _ | _ | j
  · rfl
  · rfl
  · rfl
  · rfl
  · omega

theorem regMessageBody_eq_words (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (h : Architecture.regMessageLength layout len ≤ 4) :
    Architecture.regMessageBody layout rf len =
      replyBodyOfWords (Architecture.regMessageLength layout len)
        (Architecture.regLayoutWord layout rf 0) (Architecture.regLayoutWord layout rf 1)
        (Architecture.regLayoutWord layout rf 2) (Architecture.regLayoutWord layout rf 3) := by
  apply Array.ext
  · rw [Architecture.regMessageBody_size]; simp only [replyBodyOfWords, Array.size_extract,
      List.size_toArray, List.length_cons, List.length_nil]; omega
  · intro i h1 h2
    have hL : i < Architecture.regMessageLength layout len := by
      rw [Architecture.regMessageBody_size] at h1; exact h1
    have hw := Architecture.regMessageBody_word layout rf len i
    rw [Array.getElem?_eq_getElem h1, Option.map_some, Option.getD_some,
      Architecture.regMessageWord_eq_regLayoutWord _ _ _ _ hL] at hw
    have e : ((replyBodyOfWords (Architecture.regMessageLength layout len)
        (Architecture.regLayoutWord layout rf 0) (Architecture.regLayoutWord layout rf 1)
        (Architecture.regLayoutWord layout rf 2) (Architecture.regLayoutWord layout rf 3))[i]'h2).word
        = Architecture.regLayoutWord layout rf i := by
      rw [← replyInlineWord_regLayoutWord layout rf i (by omega)]
      simp only [replyBodyOfWords, Array.getElem_extract, Nat.zero_add]
      rcases i with _ | _ | _ | _ | i <;> first | rfl | omega
    cases hA : (Architecture.regMessageBody layout rf len)[i]
    cases hB : (replyBodyOfWords (Architecture.regMessageLength layout len)
        (Architecture.regLayoutWord layout rf 0) (Architecture.regLayoutWord layout rf 1)
        (Architecture.regLayoutWord layout rf 2) (Architecture.regLayoutWord layout rf 3))[i]
    rw [hA] at hw; rw [hB] at e
    simp only [RegValue.mk.injEq]
    exact hw.trans e.symm

/-- Word `i` of a reply's frame, `0` past its length: its inline word
(`replyInlineWord`).  Out of line, so it returns a bare machine word, as
`Architecture.regMessageWord`. -/
@[noinline] def replyFrameWord (layout : SeLe4n.SyscallRegisterLayout) (len i : Nat)
    (m0 m1 m2 m3 : UInt64) : UInt64 :=
  if i < Architecture.regMessageLength layout len then replyInlineWord m0 m1 m2 m3 i else 0

theorem replyFrameWord_regLayoutWord (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len i : Nat) (hi : i < 4) :
    replyFrameWord layout len i (Architecture.regLayoutWord layout rf 0)
      (Architecture.regLayoutWord layout rf 1) (Architecture.regLayoutWord layout rf 2)
      (Architecture.regLayoutWord layout rf 3) = Architecture.regMessageWord layout rf len i := by
  unfold replyFrameWord
  split
  · next h => rw [replyInlineWord_regLayoutWord layout rf i hi,
      Architecture.regMessageWord_eq_regLayoutWord _ _ _ _ h]
  · next h => unfold Architecture.regMessageWord; rw [dif_neg h]

/-- `deliverReplyRecvCapsFrame` of the reply's four inline words, read on the
pre-state, in place of the replier's register file. -/
@[noinline] def deliverReplyRecvCapsFrameW (capInfo : Nat) (Y : SystemState)
    (c : SeLe4n.ThreadId) (layout : SeLe4n.SyscallRegisterLayout) (len : Nat)
    (badge : Option SeLe4n.Badge) (m0 m1 m2 m3 : UInt64) : SystemState :=
  writeDeliveredFrameIfReady Y c
    { x0 := Architecture.badgeWordOrZero badge
      x1 := regMessageInfoWordCaps layout len capInfo
      x2 := replyFrameWord layout len 0 m0 m1 m2 m3
      x3 := replyFrameWord layout len 1 m0 m1 m2 m3
      x4 := replyFrameWord layout len 2 m0 m1 m2 m3
      x5 := replyFrameWord layout len 3 m0 m1 m2 m3 }
    (fun _ => Y.mapTcbInPlace c (holdMessage
      { registers := replyBodyOfWords (Architecture.regMessageLength layout len) m0 m1 m2 m3,
        badge := badge }))

theorem deliverReplyRecvCapsFrameW_eq (capInfo : Nat) (Y : SystemState) (c : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (h : Architecture.regMessageLength layout len ≤ 4) :
    deliverReplyRecvCapsFrameW capInfo Y c layout len badge
      (Architecture.regLayoutWord layout rf 0) (Architecture.regLayoutWord layout rf 1)
      (Architecture.regLayoutWord layout rf 2) (Architecture.regLayoutWord layout rf 3) =
      deliverReplyRecvCapsFrame capInfo Y c layout rf len badge := by
  unfold deliverReplyRecvCapsFrameW deliverReplyRecvCapsFrame holdReplyRecvBody
    regMessageFrameCapsOpt
  simp only [replyFrameWord_regLayoutWord layout rf len _ (by decide : 0 < 4),
    replyFrameWord_regLayoutWord layout rf len _ (by decide : 1 < 4),
    replyFrameWord_regLayoutWord layout rf len _ (by decide : 2 < 4),
    replyFrameWord_regLayoutWord layout rf len _ (by decide : 3 < 4),
    ← regMessageBody_eq_words layout rf len h]

/-- Reply word `i` of a fault reply of `n` inline words, or the faulted
thread's own `fallback` past them (`faultReplyWord` at offset 0, read from the
four inline words).  Out of line, as `faultReplyWord`. -/
@[noinline] def faultReplyWordW (n i : Nat) (fallback m0 m1 m2 m3 : UInt64) : UInt64 :=
  if i < n then replyInlineWord m0 m1 m2 m3 i else fallback

theorem faultReplyWordW_eq (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (n i : Nat) (fb : UInt64) (h : n ≤ 4) :
    faultReplyWordW n i fb (Architecture.regLayoutWord layout rf 0)
      (Architecture.regLayoutWord layout rf 1) (Architecture.regLayoutWord layout rf 2)
      (Architecture.regLayoutWord layout rf 3) = faultReplyWord layout rf n 0 i fb := by
  unfold faultReplyWordW faultReplyWord
  split
  · next hi => rw [replyInlineWord_regLayoutWord layout rf i (by omega), Nat.add_zero]
  · rfl

/-- `performFaultAnswer` of a reply of `n` inline words at offset 0, each word
read from the reply's four inline words (`faultReplyWordW`) in place of the
replier's register file. -/
@[noinline] def performFaultAnswerW (X : SystemState) (c : SeLe4n.ThreadId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (n : Nat) (m0 m1 m2 m3 : UInt64) :
    SystemState :=
  if kind == 1 || kind == 2 then
    applyFaultRestart X c
      { pc := ip, sp := sp, lr := lr, x0 := x0, x1 := x1, x2 := x2, x3 := x3,
        x4 := x4, x5 := x5, x6 := x6, x7 := x7 }
  else if label != 0 then faultAbandonOnCore X c (faultAbandonCore X c)
  else if kind == 3 then
    applyFaultRestart X c
      { pc := faultReplyWordW n 8 ip m0 m1 m2 m3, sp := faultReplyWordW n 9 sp m0 m1 m2 m3,
        lr := faultReplyWordW n 10 lr m0 m1 m2 m3,
        x0 := faultReplyWordW n 0 x0 m0 m1 m2 m3, x1 := faultReplyWordW n 1 x1 m0 m1 m2 m3,
        x2 := faultReplyWordW n 2 x2 m0 m1 m2 m3, x3 := faultReplyWordW n 3 x3 m0 m1 m2 m3,
        x4 := faultReplyWordW n 4 x4 m0 m1 m2 m3, x5 := faultReplyWordW n 5 x5 m0 m1 m2 m3,
        x6 := faultReplyWordW n 6 x6 m0 m1 m2 m3, x7 := faultReplyWordW n 7 x7 m0 m1 m2 m3 }
  else
    applyFaultRestart X c
      { pc := faultReplyWordW n 0 ip m0 m1 m2 m3, sp := faultReplyWordW n 1 sp m0 m1 m2 m3,
        lr := lr, x0 := x0, x1 := x1, x2 := x2, x3 := x3,
        x4 := x4, x5 := x5, x6 := x6, x7 := x7 }

theorem performFaultAnswerW_eq (X : SystemState) (c : SeLe4n.ThreadId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (n : Nat) (h : n ≤ 4) :
    performFaultAnswerW X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 n
      (Architecture.regLayoutWord layout rf 0) (Architecture.regLayoutWord layout rf 1)
      (Architecture.regLayoutWord layout rf 2) (Architecture.regLayoutWord layout rf 3) =
      performFaultAnswer X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n 0 := by
  unfold performFaultAnswerW performFaultAnswer
  simp only [faultReplyWordW_eq layout rf n _ _ h]

/-- Reply word `i` of a long fault reply, its inline words given as the four
`m0`..`m3` (`faultReplyWordLong` with the replier's registers read once). -/
@[noinline] def faultReplyWordLongW (X : @& SystemState) (s : SeLe4n.ThreadId) (len i : Nat)
    (fallback m0 m1 m2 m3 : UInt64) : UInt64 :=
  if i < len then (if i < 4 then replyInlineWord m0 m1 m2 m3 i else overflowWordAt X s (i - 4))
  else fallback

theorem faultReplyWordLongW_eq (X : SystemState) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len i : Nat) (fb : UInt64) :
    faultReplyWordLongW X s len i fb (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) =
      faultReplyWordLong X s rf len i fb := by
  unfold faultReplyWordLongW faultReplyWordLong
  split
  · split
    · next hi => rw [replyInlineWord_regLayoutWord _ rf i hi]
    · rfl
  · rfl

/-- `performFaultAnswerLong` with each inline reply word read from the four
`m0`..`m3` (`faultReplyWordLongW`). -/
@[noinline] def performFaultAnswerLongW (X : SystemState) (c : SeLe4n.ThreadId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (s : SeLe4n.ThreadId)
    (len : Nat) (m0 m1 m2 m3 : UInt64) : SystemState :=
  if kind == 1 || kind == 2 then
    applyFaultRestart X c
      { pc := ip, sp := sp, lr := lr, x0 := x0, x1 := x1, x2 := x2, x3 := x3,
        x4 := x4, x5 := x5, x6 := x6, x7 := x7 }
  else if label != 0 then faultAbandonOnCore X c (faultAbandonCore X c)
  else if kind == 3 then
    applyFaultRestart X c
      { pc := faultReplyWordLongW X s len 8 ip m0 m1 m2 m3,
        sp := faultReplyWordLongW X s len 9 sp m0 m1 m2 m3,
        lr := faultReplyWordLongW X s len 10 lr m0 m1 m2 m3,
        x0 := faultReplyWordLongW X s len 0 x0 m0 m1 m2 m3,
        x1 := faultReplyWordLongW X s len 1 x1 m0 m1 m2 m3,
        x2 := faultReplyWordLongW X s len 2 x2 m0 m1 m2 m3,
        x3 := faultReplyWordLongW X s len 3 x3 m0 m1 m2 m3,
        x4 := faultReplyWordLongW X s len 4 x4 m0 m1 m2 m3,
        x5 := faultReplyWordLongW X s len 5 x5 m0 m1 m2 m3,
        x6 := faultReplyWordLongW X s len 6 x6 m0 m1 m2 m3,
        x7 := faultReplyWordLongW X s len 7 x7 m0 m1 m2 m3 }
  else
    applyFaultRestart X c
      { pc := faultReplyWordLongW X s len 0 ip m0 m1 m2 m3,
        sp := faultReplyWordLongW X s len 1 sp m0 m1 m2 m3,
        lr := lr, x0 := x0, x1 := x1, x2 := x2, x3 := x3,
        x4 := x4, x5 := x5, x6 := x6, x7 := x7 }

theorem performFaultAnswerLongW_eq (X : SystemState) (c : SeLe4n.ThreadId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) :
    performFaultAnswerLongW X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 s len
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) =
      performFaultAnswerLong X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 s rf len := by
  unfold performFaultAnswerLongW performFaultAnswerLong
  simp only [faultReplyWordLongW_eq X s rf len]

/-- The long reply's four inline words as the layout's message registers
(`Architecture.regMessageRegs` of the AArch64 layout). -/
theorem regMessageRegs_arm64_eq_words (rf : SeLe4n.RegisterFile) :
    Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf =
      #[⟨Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0⟩,
        ⟨Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1⟩,
        ⟨Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2⟩,
        ⟨Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3⟩] := by
  have hS : (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf).size = 4 := by
    simp only [Architecture.regMessageRegs, Array.size_map]; rfl
  apply Array.ext
  · rw [hS]; rfl
  · intro i h1 h2
    have hw := Architecture.regMessageRegs_word SeLe4n.arm64DefaultLayout rf i
    rw [Array.getElem?_eq_getElem h1, Option.map_some, Option.getD_some] at hw
    cases hA : (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf)[i]
    rw [hA] at hw
    rw [hS] at h1
    rcases i with _ | _ | _ | _ | i <;> first | simpa using hw | omega

/-- `deliverLongReplyRecvFrame` with the reply's four inline words read on the
pre-state in place of the replier's register file. -/
@[inline] def deliverLongReplyRecvFrameW (X : SystemState) (r : SeLe4n.ThreadId) (len : Nat)
    (s : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge) (capInfo : Nat)
    (m0 m1 m2 m3 : UInt64) : SystemState :=
  match X.getTcb? r with
  | some t =>
    if t.ipcState = .ready then
      let k := overflowSlotsFrom X r 0 (len - 4)
      overflowCopyStore
        (X.mapTcbInPlace r (withFrameWords
          (Architecture.badgeWordIf (badge.getD SeLe4n.Badge.zero) badge.isSome)
          (longMessageInfoWord len k capInfo)
          (replyFrameWord SeLe4n.arm64DefaultLayout len 0 m0 m1 m2 m3)
          (replyFrameWord SeLe4n.arm64DefaultLayout len 1 m0 m1 m2 m3)
          (replyFrameWord SeLe4n.arm64DefaultLayout len 2 m0 m1 m2 m3)
          (replyFrameWord SeLe4n.arm64DefaultLayout len 3 m0 m1 m2 m3)))
        r s 0 (len - 4)
    else X.mapTcbInPlace r (holdMessage
      { registers := #[⟨m0⟩, ⟨m1⟩, ⟨m2⟩, ⟨m3⟩] ++ (overflowRegsFrom X s 0 (len - 4)).toArray,
        badge := SeLe4n.Badge.opt (badge.getD SeLe4n.Badge.zero) badge.isSome })
  | none => X

theorem deliverLongReplyRecvFrameW_eq (X : SystemState) (r : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (s : SeLe4n.ThreadId) (badge : Option SeLe4n.Badge)
    (capInfo : Nat) :
    deliverLongReplyRecvFrameW X r len s badge capInfo
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) =
      deliverLongReplyRecvFrame X r rf len s badge capInfo := by
  unfold deliverLongReplyRecvFrameW deliverLongReplyRecvFrame deliverLongSendFrame
    holdLongSendMessage longSendMessage
  simp only [replyFrameWord_regLayoutWord _ rf len _ (by decide : 0 < 4),
    replyFrameWord_regLayoutWord _ rf len _ (by decide : 1 < 4),
    replyFrameWord_regLayoutWord _ rf len _ (by decide : 2 < 4),
    replyFrameWord_regLayoutWord _ rf len _ (by decide : 3 < 4),
    regMessageRegs_arm64_eq_words rf]
  rfl
/-- **The Call take's writes before the server's own frame, over the arm**: the
caller popped, blocked on the reply and linked, the server made ready, the
arm's lend, the server's priority walk, then the answered caller's frame with
the transfer's report (read from the server's saved registers `rf`). -/
@[inline] def ReplyRecvArm.callTakeLegs (arm : ReplyRecvArm) (lends : Bool) (capInfo : Nat) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) : SystemState :=
  deliverReplyRecvCapsFrame capInfo (PriorityInheritance.propagatePipChainCrossCore
    (ReplyRecvArm.callLend lends (storeReceiveCallReady Y epId s nextCode tid rid) s tid scS dh rh) tid core).1
    c layout rf len badge

/-- `ReplyRecvArm.callTakeLegs` with the reply's four inline words in place of
the replier's register file (`deliverReplyRecvCapsFrameW`). -/
@[inline] def ReplyRecvArm.callTakeLegsW (arm : ReplyRecvArm) (lends : Bool) (capInfo : Nat) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) (badge : Option SeLe4n.Badge)
    (m0 m1 m2 m3 : UInt64) : SystemState :=
  deliverReplyRecvCapsFrameW capInfo (PriorityInheritance.propagatePipChainCrossCore
    (ReplyRecvArm.callLend lends (storeReceiveCallReady Y epId s nextCode tid rid) s tid scS dh rh) tid core).1
    c layout len badge m0 m1 m2 m3

theorem ReplyRecvArm.callTakeLegsW_eq (arm : ReplyRecvArm) (lends : Bool) (capInfo : Nat) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (h : Architecture.regMessageLength layout len ≤ 4) :
    arm.callTakeLegsW lends capInfo Y c tid s rid epId nextCode scS dh rh core layout len badge
      (Architecture.regLayoutWord layout rf 0) (Architecture.regLayoutWord layout rf 1)
      (Architecture.regLayoutWord layout rf 2) (Architecture.regLayoutWord layout rf 3) =
      arm.callTakeLegs lends capInfo Y c tid s rid epId nextCode scS dh rh core layout rf len badge := by
  unfold ReplyRecvArm.callTakeLegsW ReplyRecvArm.callTakeLegs
  rw [deliverReplyRecvCapsFrameW_eq (h := h)]

/-- **The Call take's tail, over the arm, stages the caller's held reply and
the server's message as frames**, the take, the lend and the walk committed
past both writes. -/
theorem ReplyRecvArm.callTakeFrame_staged (arm : ReplyRecvArm) (lends : Bool) (Y : SystemState)
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
        (PriorityInheritance.propagatePipChainCrossCore (ReplyRecvArm.callLend lends
          (receiveCallTakeState (Y.mapTcbInPlace c (holdMessage
            { registers := Architecture.regMessageBody layout rf len, badge := badge }))
            epId s sTcb tid rid) s tid scS dh rh) tid core).1 c capInfo) tid 0 =
      writeReceiverMessageFrame
        (arm.callTakeLegs lends capInfo Y c tid s rid epId sTcb.queueNextCode scS dh rh core layout rf
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
  rw [ReplyRecvArm.callLend_msg lends tid id _ id _ s tid scS dh rh hNoRc hST.symm,
    ReplyRecvArm.callLend_msg lends c id _ id R s tid scS dh rh hNoR hcs]
  have hNoM := ReplyRecvArm.callLend_noResizeDue lends R s tid scS dh rh hNoR
  rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ ?_,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoM]
  rotate_left
  · exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoM
  have hNoY := propagatePipChainCrossCore_noResizeDue _ tid core hNoM
  generalize (PriorityInheritance.propagatePipChainCrossCore (ReplyRecvArm.callLend lends R s tid scS dh rh) tid
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
theorem ReplyRecvArm.CallReady.takesReply {lends : Bool} {Q : SystemState}
    {epId : SeLe4n.ObjId} {tid s : SeLe4n.ThreadId} {sTcb : TCB} {rid : SeLe4n.ReplyId}
    (h : ReplyRecvArm.CallReady lends Q epId tid s sTcb rid) :
    receiveCallTakesReplyInPlace Q epId tid s sTcb rid = true := by
  unfold ReplyRecvArm.CallReady at h
  split at h
  · simp only [receiveCallDonatesInPlace, Bool.and_eq_true] at h; exact h.1
  · exact receiveCallTakesReplyInPlace_of_inPlace h

theorem ReplyRecvArm.CallReady.ne {lends : Bool} {Q : SystemState}
    {epId : SeLe4n.ObjId} {tid s : SeLe4n.ThreadId} {sTcb : TCB} {rid : SeLe4n.ReplyId}
    (h : ReplyRecvArm.CallReady lends Q epId tid s sTcb rid) : s ≠ tid := fun e => by
  have h' := h.takesReply
  simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, bne_iff_ne, ne_eq] at h'
  exact h'.1.1.1.1.1.1.1.1.1.2 e.symm

/-- **The reply-receive taking a queued caller, over every arm, its reply
transferring nothing, delivered**: the arm's reply leg and pop, the server's
context return, the take, the arm's lend, the server's priority walk and the
caller's frame (`ReplyRecvArm.callTakeLegs`). -/
@[noinline] def performReplyRecvArmCallTakeLegs (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) (badge : Option SeLe4n.Badge)
    (m0 m1 m2 m3 : UInt64) : SystemState :=
  arm.callTakeLegsW lends 0 (receiveReturnSchedContextFast true
    (arm.pop (arm.legReady st c tid rid) c tid scId home) tid.val) c tid s rid epId nextCode scS
    dh rh core layout len badge m0 m1 m2 m3

/-- The inert Call take over the arm: the legs (`performReplyRecvArmCallTakeLegs`)
and then the server's frame (`writeReceiverMessageFrame`), each out of line; the
legs take the reply's four inline words, read on the pre-state, and not the
server's register file, which only the server's TCB holds when its frame is
written. -/
@[inline] def performReplyRecvArmCallTakeDelivered (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) (badge : Option SeLe4n.Badge)
    (m0 m1 m2 m3 : UInt64) (sRf : SeLe4n.RegisterFile) (sLen : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) : SystemState :=
  writeReceiverMessageFrame (performReplyRecvArmCallTakeLegs arm lends scId home st c tid rid epId s
    nextCode scS dh rh core layout len badge m0 m1 m2 m3) tid sRf sLen badgeWord badged

/-- **The reply-receive taking a queued caller, its reply transferring nothing,
is the specification's, over every arm**: under the arm's reply-leg guard and
Call-take guard, a reply of at most four words transferring no capability, and
a caller `s` at the head of the send queue blocked by a routed capability-free
call, not delivering a fault (every check read on the pre-state), the checked
arm's result is `performReplyRecvArmCallTakeDelivered`, every context, core and
word it takes read on the pre-state. -/
theorem replyRecvOnCore_arm_callTakeDelivered (arm : ReplyRecvArm) (lends : Bool)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmitsAt lends st epId tid s sTcb rid)
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
      .ok ((), performReplyRecvArmCallTakeDelivered arm lends scId home st c tid rid epId s
        sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
        (determineTargetCore st tid) core layout len badge (Architecture.regLayoutWord layout rf 0)
        (Architecture.regLayoutWord layout rf 1) (Architecture.regLayoutWord layout rf 2)
        (Architecture.regLayoutWord layout rf 3)
        sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged) := by
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
  obtain ⟨sTcb2, -, -, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_callTake arm lends none st epId
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
  rw [arm.callTakeFrame_staged lends _ c tid s rid epId sTcb2 _ _ _ core layout rf len badge 0 capAddr mi
    (receiveReturnSchedContext_noResizeDue true _ tid hNoX) hNe hSC hST hSz4 hR2 hF2,
    hK.queueNext, hK.regs, hK.badge, hK.badged]
  unfold performReplyRecvArmCallTakeDelivered performReplyRecvArmCallTakeLegs
  rw [ReplyRecvArm.callTakeLegsW_eq (h := hSz4),
    receiveReturnSchedContextFast_eq]

/-- **The reply-receive taking a queued caller, over every arm, its reply leg
transferring, delivered**: the arm's reply leg and pop, the transfer in place
on no endpoint, the server's context return, the take, the arm's lend, the
server's priority walk, then the caller's frame with the transfer's report.
The replier and the caller enter as the words the transfer reads of them, all
read before the reply's writes. -/
@[noinline] def performReplyRecvArmCallTakeCapsLegs (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) (badge : Option SeLe4n.Badge)
    (m0 m1 m2 m3 : UInt64)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := arm.pop (arm.legReady st c tid rid) c tid scId home
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    arm.callTakeLegsW lends (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (receiveReturnSchedContextFast true
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X) tid.val)
      c tid s rid epId nextCode scS dh rh core layout len badge m0 m1 m2 m3

/-- The installing Call take over the arm, its legs
(`performReplyRecvArmCallTakeCapsLegs`) and then the server's frame
(`writeReceiverMessageFrame`). -/
@[inline] def performReplyRecvArmCallTakeCapsDelivered (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) (badge : Option SeLe4n.Badge)
    (m0 m1 m2 m3 : UInt64) (sRf : SeLe4n.RegisterFile) (sLen : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  writeReceiverMessageFrame (performReplyRecvArmCallTakeCapsLegs arm lends scId home st c tid rid epId s
    nextCode scS dh rh core layout len badge m0 m1 m2 m3 sv sb sroot count rv rb rroot) tid sRf sLen
    badgeWord badged

/-- **The reply-receive taking a queued caller, its reply leg transferring, is
the specification's, over every arm**: under the guard of
`replyRecvOnCore_arm_callTakeDelivered` (its inert transfer replaced by a
granting replier whose frame asks for `count` capabilities, `hReq`), the
checked arm's result is `performReplyRecvArmCallTakeCapsDelivered`. -/
theorem replyRecvOnCore_arm_callTakeCapsDelivered (arm : ReplyRecvArm) (lends : Bool)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (stcb : TCB) (count : Nat)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmitsAt lends st epId tid s sTcb rid)
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
      .ok ((), performReplyRecvArmCallTakeCapsDelivered arm lends scId home st c tid rid epId s
        sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
        (determineTargetCore st tid) core layout len badge (Architecture.regLayoutWord layout rf 0)
        (Architecture.regLayoutWord layout rf 1) (Architecture.regLayoutWord layout rf 2)
        (Architecture.regLayoutWord layout rf 3)
        sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
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
  obtain ⟨sTcb2, -, -, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_callTake arm lends none st epId
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
  rw [arm.callTakeFrame_staged lends _ c tid s rid epId sTcb2 _ _ _ core layout rf len badge sm.capInfo
    capAddr mi (receiveReturnSchedContext_noResizeDue true Y1 tid hNoY) hNe hSC hST hSz4 hR2 hF2,
    hK.queueNext, hK.regs, hK.badge, hK.badged, ← receiveReturnSchedContextFast_eq]
  have hKl := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => arm.callTakeLegs lends i (receiveReturnSchedContextFast true Y tid.val) c tid s rid epId
      sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
      (determineTargetCore st tid) core layout rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hKl
  rw [hAP.frameCapRequestOf, hAP.capTargetOf, hT1] at hKl
  unfold performReplyRecvArmCallTakeCapsDelivered performReplyRecvArmCallTakeCapsLegs
  simp only [ReplyRecvArm.callTakeLegsW_eq (h := hSz4)]
  rw [hX, hKl]

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

theorem ReplyRecvArm.ipcBufferReadsAgree_callLend (lends : Bool) (X : SystemState)
    (s tid : SeLe4n.ThreadId) (scS : SeLe4n.SchedContextId) (dh rh : CoreId)
    (hNo : X.objects.noResizeDue) : ipcBufferReadsAgree (ReplyRecvArm.callLend lends X s tid scS dh rh) X := by
  unfold ReplyRecvArm.callLend
  split
  · exact ipcBufferReadsAgree_lendSchedContextInPlace X s tid scS dh rh hNo
  · exact .refl X

/-- **The long Call take's writes before the server's own frame, over the
arm**: as `ReplyRecvArm.callTakeLegs`, the caller's long frame with the
replier's overflow words copied into its buffer (`deliverLongReplyRecvFrame`). -/
@[inline] def ReplyRecvArm.callTakeLegsLong (arm : ReplyRecvArm) (lends : Bool) (capInfo : Nat) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) : SystemState :=
  deliverLongReplyRecvFrame (PriorityInheritance.propagatePipChainCrossCore
    (ReplyRecvArm.callLend lends (storeReceiveCallReady Y epId s nextCode tid rid) s tid scS dh rh) tid core).1
    c rf len tid badge capInfo

/-- `ReplyRecvArm.callTakeLegsLong` with the reply's four inline words in place
of the replier's register file (`deliverLongReplyRecvFrameW`). -/
@[inline] def ReplyRecvArm.callTakeLegsLongW (arm : ReplyRecvArm) (lends : Bool) (capInfo : Nat)
    (Y : SystemState) (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (len : Nat)
    (badge : Option SeLe4n.Badge) (m0 m1 m2 m3 : UInt64) : SystemState :=
  deliverLongReplyRecvFrameW (PriorityInheritance.propagatePipChainCrossCore
    (ReplyRecvArm.callLend lends (storeReceiveCallReady Y epId s nextCode tid rid) s tid scS dh rh) tid core).1
    c len tid badge capInfo m0 m1 m2 m3

theorem ReplyRecvArm.callTakeLegsLongW_eq (arm : ReplyRecvArm) (lends : Bool) (capInfo : Nat) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) :
    arm.callTakeLegsLongW lends capInfo Y c tid s rid epId nextCode scS dh rh core len badge
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) =
      arm.callTakeLegsLong lends capInfo Y c tid s rid epId nextCode scS dh rh core rf len badge := by
  unfold ReplyRecvArm.callTakeLegsLongW ReplyRecvArm.callTakeLegsLong
  rw [deliverLongReplyRecvFrameW_eq]

/-- **The long Call take's tail, over the arm**, stages the caller's held reply
and the server's message as frames. -/
theorem ReplyRecvArm.callTakeFrame_stagedLong (arm : ReplyRecvArm) (lends : Bool) (st0 Y : SystemState)
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
        (PriorityInheritance.propagatePipChainCrossCore (ReplyRecvArm.callLend lends
          (receiveCallTakeState (Y.mapTcbInPlace c (holdMessage
            { registers := longReplyRecvRegs rf st0 tid len, badge := badge }))
            epId s sTcb tid rid) s tid scS dh rh) tid core).1 c capInfo) tid 0 =
      writeReceiverMessageFrame
        (arm.callTakeLegsLong lends capInfo Y c tid s rid epId sTcb.queueNextCode scS dh rh core rf
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
  rw [ReplyRecvArm.callLend_msg lends tid id _ id _ s tid scS dh rh hNoRc hST.symm,
    ReplyRecvArm.callLend_msg lends c id _ id R s tid scS dh rh hNoR hcs]
  have hNoM := ReplyRecvArm.callLend_noResizeDue lends R s tid scS dh rh hNoR
  rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ ?_,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoM]
  rotate_left
  · exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoM
  have hNoY := propagatePipChainCrossCore_noResizeDue _ tid core hNoM
  have hAZ : ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore
      (ReplyRecvArm.callLend lends R s tid scS dh rh) tid core).1 st0 :=
    ((ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core hNoM).trans
      ((ReplyRecvArm.ipcBufferReadsAgree_callLend lends R s tid scS dh rh hNoR).trans hAR)).words.trans hAY
  generalize (PriorityInheritance.propagatePipChainCrossCore (ReplyRecvArm.callLend lends R s tid scS dh rh) tid
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


/-- **The reply-receive taking a queued caller, over every arm, its reply
transferring nothing, delivered, at more than four words**: the arm's reply leg
and pop, the server's context return, the take, the arm's lend, the server's
priority walk and the caller's long frame (`ReplyRecvArm.callTakeLegsLong`). -/
@[noinline] def performReplyRecvArmCallTakeLegsLong (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (len : Nat) (badge : Option SeLe4n.Badge) (m0 m1 m2 m3 : UInt64) : SystemState :=
  arm.callTakeLegsLongW lends 0 (receiveReturnSchedContextFast true
    (arm.pop (arm.legReady st c tid rid) c tid scId home) tid.val) c tid s rid epId nextCode scS
    dh rh core len badge m0 m1 m2 m3

/-- The inert long Call take over the arm: the legs
(`performReplyRecvArmCallTakeLegsLong`) and then the server's frame
(`writeReceiverMessageFrame`), each out of line. -/
@[inline] def performReplyRecvArmCallTakeDeliveredLong (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (len : Nat) (badge : Option SeLe4n.Badge) (m0 m1 m2 m3 : UInt64)
    (sRf : SeLe4n.RegisterFile) (sLen : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool) :
    SystemState :=
  writeReceiverMessageFrame (performReplyRecvArmCallTakeLegsLong arm lends scId home st c tid rid epId
    s nextCode scS dh rh core len badge m0 m1 m2 m3) tid sRf sLen badgeWord badged

/-- **The reply-receive taking a queued caller at more than four words, its
reply transferring nothing, is the specification's, over every arm**: as
`replyRecvOnCore_arm_callTakeDelivered`, the reply's overflow words read from
the server's buffer on the pre-state. -/
theorem replyRecvOnCore_arm_callTakeDeliveredLong (arm : ReplyRecvArm) (lends : Bool)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmitsAt lends st epId tid s sTcb rid)
    (hLen : 5 ≤ len)
    (hSzL : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
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
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmCallTakeDeliveredLong arm lends scId home st c tid rid epId s
        sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
        (determineTargetCore st tid) core len badge (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3)
        sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged) := by
  have hSz := hSzL
  obtain ⟨-, hNe, hNo, -, -⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid
      { registers := longReplyRecvRegs rf st tid len, badge := badge } core ct rp hAd
      hSz hT hRO hRp
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNoX := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid
    (arm.legReady_noResizeDue st c tid rid hNo)
  have hNoP : (arm.pop (arm.leg st c tid rid
      { registers := longReplyRecvRegs rf st tid len, badge := badge }) c tid scId
      home).objects.noResizeDue := by
    rw [arm.pop_leg_hold st c tid rid _ hNo hNe]
    exact (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoX
  have hXf := replyRecvReplyTransfer_of_inert none st tid c grant ct hTc (fun _ => hInert)
    (arm.pop (arm.leg st c tid rid
      { registers := longReplyRecvRegs rf st tid len, badge := badge }) c tid scId home)
  obtain ⟨sTcb2, -, -, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_callTake arm lends none st epId
    tid c rid { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core ct rp ep s sTcb capAddr mi hAd hCA hSz hT hRO hRp hE hH hS hSC hR hF
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
  have hAY := (ipcBufferReadsAgree_receiveReturnSchedContext true _ tid hNoX).words.trans
    ((arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid
      (arm.legReady_noResizeDue st c tid rid hNo)).trans
      (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)).words
  rw [arm.callTakeFrame_stagedLong lends st _ c tid s rid epId sTcb2 _ _ _ core rf len badge 0 capAddr mi
    (receiveReturnSchedContext_noResizeDue true _ tid hNoX) hAY hNe hSC hST (by omega) hR2 hF2,
    hK.queueNext, hK.regs, hK.badge, hK.badged]
  unfold performReplyRecvArmCallTakeDeliveredLong performReplyRecvArmCallTakeLegsLong
  rw [ReplyRecvArm.callTakeLegsLongW_eq, receiveReturnSchedContextFast_eq]

@[noinline] def performReplyRecvArmCallTakeCapsLegsLong (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (len : Nat) (badge : Option SeLe4n.Badge) (m0 m1 m2 m3 : UInt64)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  let X := arm.pop (arm.legReady st c tid rid) c tid scId home
  capTransferK X c.toObjId sv sb sroot count rv rb rroot
    fun free dcn dsl n x0 x1 x2 a0 b0 a1 b1 a2 b2 =>
    arm.callTakeLegsLongW lends (capStepsInfo c.toObjId false x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl X 0 n free 0 0)
      (receiveReturnSchedContextFast true
        (capStepsApply c.toObjId false rv rb x0 x1 x2 a0 b0 a1 b1 a2 b2 dcn dsl 0 n free X) tid.val)
      c tid s rid epId nextCode scS dh rh core len badge m0 m1 m2 m3

/-- The installing Call take over the arm, its legs
(`performReplyRecvArmCallTakeCapsLegsLong`) and then the server's frame
(`writeReceiverMessageFrame`). -/
@[inline] def performReplyRecvArmCallTakeCapsDeliveredLong (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (len : Nat) (badge : Option SeLe4n.Badge) (m0 m1 m2 m3 : UInt64)
    (sRf : SeLe4n.RegisterFile) (sLen : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool)
    (sv : Option Capability) (sb : SeLe4n.VAddr) (sroot : Option Capability) (count : Nat)
    (rv : Option Capability) (rb : SeLe4n.VAddr) (rroot : Option Capability) : SystemState :=
  writeReceiverMessageFrame (performReplyRecvArmCallTakeCapsLegsLong arm lends scId home st c tid rid epId s
    nextCode scS dh rh core len badge m0 m1 m2 m3 sv sb sroot count rv rb rroot) tid sRf sLen
    badgeWord badged

/-- **The reply-receive taking a queued caller, its reply leg transferring, is
the specification's, over every arm**: under the guard of
`replyRecvOnCore_arm_callTakeDeliveredLong` (its inert transfer replaced by a
granting replier whose frame asks for `count` capabilities, `hReq`), the
checked arm's result is `performReplyRecvArmCallTakeCapsDeliveredLong`. -/
theorem replyRecvOnCore_arm_callTakeCapsDeliveredLong (arm : ReplyRecvArm) (lends : Bool)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB)
    (capAddr : SeLe4n.CPtr) (mi : MessageInfo) (stcb : TCB) (count : Nat)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmitsAt lends st epId tid s sTcb rid)
    (hLen : 5 ≤ len)
    (hSzL : ¬ (longReplyRecvRegs rf st tid len).size > maxMessageRegisters)
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
        { registers := longReplyRecvRegs rf st tid len, badge := badge } true core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmCallTakeCapsDeliveredLong arm lends scId home st c tid rid epId s
        sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
        (determineTargetCore st tid) core len badge (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3)
        sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
        stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] count ct.spaceCells[2] ct.ipcBuffer
        ct.spaceCells[0]) := by
  have hSz := hSzL
  obtain ⟨-, hNe, hNo, -, -⟩ :=
    arm.legPop (scId := scId) (home := home) st tid c rid
      { registers := longReplyRecvRegs rf st tid len, badge := badge } core ct rp hAd
      hSz hT hRO hRp
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hTgt : receiverCapTarget? st c = capTargetOf st ct := by
    unfold receiverCapTarget? capTargetOf; rw [hTc]
  have hP1 := arm.pop_leg_hold (scId := scId) (home := home) st c tid rid
    { registers := longReplyRecvRegs rf st tid len, badge := badge } hNo hNe
  have hNoX := arm.legReady_noResizeDue st c tid rid hNo
  have hAP := (arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid hNoX).trans
    (arm.ipcBufferReadsAgree_legReady st c tid rid hNo)
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid hNoX
  generalize hX : arm.pop (arm.legReady st c tid rid) c tid scId home = X at hP1 hNoP hAP
  generalize hMsg : ({ registers := longReplyRecvRegs rf st tid len, badge := badge } :
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
  obtain ⟨sTcb2, -, -, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_callTake arm lends none st epId
    tid c rid { registers := longReplyRecvRegs rf st tid len, badge := badge } true core ct rp ep s sTcb capAddr mi hAd hCA hSz hT hRO hRp hE hH hS hSC hR hF hXf
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
  have hAY := (ipcBufferReadsAgree_receiveReturnSchedContext true Y1 tid hNoY).words.trans
    ((ipcWordReadsAgree_receiveTransferCaps _ _ _ hNoP hT1).trans hAP.words)
  rw [arm.callTakeFrame_stagedLong lends st _ c tid s rid epId sTcb2 _ _ _ core rf len badge sm.capInfo
    capAddr mi (receiveReturnSchedContext_noResizeDue true Y1 tid hNoY) hAY hNe hSC hST (by omega)
    hR2 hF2,
    hK.queueNext, hK.regs, hK.badge, hK.badged, ← receiveReturnSchedContextFast_eq]
  have hKl := capTransferK_eq_at X c.toObjId false stcb count ct
    (fun i Y => arm.callTakeLegsLong lends i (receiveReturnSchedContextFast true Y tid.val) c tid s rid epId
      sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
      (determineTargetCore st tid) core rf len badge)
  simp only [transferEndpoint?, Bool.false_eq_true, ↓reduceIte] at hKl
  rw [hAP.frameCapRequestOf, hAP.capTargetOf, hT1] at hKl
  unfold performReplyRecvArmCallTakeCapsDeliveredLong performReplyRecvArmCallTakeCapsLegsLong
  simp only [ReplyRecvArm.callTakeLegsLongW_eq]
  rw [hX, hKl]

/-! ### The fault answer -/

/-- **The Call take's tail under any caller answer, over the arm, stages the
server's message as its frame**: for an answer `A` to the caller that commutes
past a message-slot write to the server and keeps the table unresized, the
take, the lend and the walk commit past the server's write. -/
theorem ReplyRecvArm.callAnswerFrame_staged (arm : ReplyRecvArm) (lends : Bool)
    (A : SystemState → SystemState) (Y : SystemState)
    (tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (sTcb : TCB)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (capAddr : SeLe4n.CPtr)
    (mi : MessageInfo)
    (hA : ∀ (X : SystemState) (m : IpcMessage), X.objects.noResizeDue →
      A (X.mapTcbInPlace tid (holdMessage m)) = (A X).mapTcbInPlace tid (holdMessage m))
    (hAN : ∀ X : SystemState, X.objects.noResizeDue → (A X).objects.noResizeDue)
    (hNo : Y.objects.noResizeDue) (hST : s ≠ tid)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .call capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    Architecture.stageDeliveredMessage (A (PriorityInheritance.propagatePipChainCrossCore
        (ReplyRecvArm.callLend lends (receiveCallTakeState Y epId s sTcb tid rid) s tid scS dh rh) tid
        core).1) tid 0 =
      writeReceiverMessageFrame (A (PriorityInheritance.propagatePipChainCrossCore
        (ReplyRecvArm.callLend lends (storeReceiveCallReady Y epId s sTcb.queueNextCode tid rid) s tid scS dh
          rh) tid core).1) tid sTcb.registerContext mi.length
        (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged := by
  unfold writeReceiverMessageFrame
  rw [receiveCallTakeState_eq_hold _ _ _ _ _ _ hNo]
  rw [(blockedSender_of_routedCall _ s sTcb capAddr mi hR hF).2]
  have hNoR := storeReceiveCallReady_noResizeDue Y epId s sTcb.queueNextCode tid rid hNo
  generalize storeReceiveCallReady Y epId s sTcb.queueNextCode tid rid = R at hNoR ⊢
  generalize hMS :
    ({ registers := Architecture.regMessageBody arm64DefaultLayout sTcb.registerContext mi.length,
       badge := sTcb.ipcBadgeView } : IpcMessage) = mS
  rw [ReplyRecvArm.callLend_msg lends tid id _ id R s tid scS dh rh hNoR hST.symm]
  have hNoM := ReplyRecvArm.callLend_noResizeDue lends R s tid scS dh rh hNoR
  rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoM]
  have hNoY := propagatePipChainCrossCore_noResizeDue _ tid core hNoM
  generalize (PriorityInheritance.propagatePipChainCrossCore (ReplyRecvArm.callLend lends R s tid scS dh rh) tid
    core).1 = Z at hNoY ⊢
  rw [show TCB.withMessageSlots id (fun _ => some mS) id = holdMessage mS from rfl, hA Z mS hNoY]
  have hSzS : mS.registers.size ≤ 4 := by
    rw [← hMS]
    simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  rw [stageDeliveredMessage_holdMessage _ tid _ (hAN Z hNoY) hSzS, ← hMS,
    Architecture.returnFrameOfMessage_regMessageBody, Architecture.regMessageFrameW_eq,
    TCB.ipcBadgeView_eq_opt]

/-- **The fault Call take's writes before the server's own frame, over the
arm**: the caller popped, blocked on the reply and linked, the server made
ready, the arm's lend, the server's priority walk, then the fault answer to the
faulted caller (`performFaultAnswer`). -/
@[inline] def ReplyRecvArm.callFaultTakeLegs (arm : ReplyRecvArm) (lends : Bool) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (n off : Nat) :
    SystemState :=
  performFaultAnswer (PriorityInheritance.propagatePipChainCrossCore
    (ReplyRecvArm.callLend lends (storeReceiveCallReady Y epId s nextCode tid rid) s tid scS dh rh) tid core).1
    c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout rf n off

/-- `ReplyRecvArm.callFaultTakeLegs` at offset 0 with the reply's four inline
words in place of the replier's register file (`performFaultAnswerW`). -/
@[inline] def ReplyRecvArm.callFaultTakeLegsW (arm : ReplyRecvArm) (lends : Bool) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (n : Nat) (m0 m1 m2 m3 : UInt64) :
    SystemState :=
  performFaultAnswerW (PriorityInheritance.propagatePipChainCrossCore
    (ReplyRecvArm.callLend lends (storeReceiveCallReady Y epId s nextCode tid rid) s tid scS dh rh) tid core).1
    c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 n m0 m1 m2 m3

theorem ReplyRecvArm.callFaultTakeLegsW_eq (arm : ReplyRecvArm) (lends : Bool) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (n : Nat) (h : n ≤ 4) :
    arm.callFaultTakeLegsW lends Y c tid s rid epId nextCode scS dh rh core kind label ip sp lr
      x0 x1 x2 x3 x4 x5 x6 x7 n (Architecture.regLayoutWord layout rf 0) (Architecture.regLayoutWord layout rf 1)
      (Architecture.regLayoutWord layout rf 2) (Architecture.regLayoutWord layout rf 3) =
      arm.callFaultTakeLegs lends Y c tid s rid epId nextCode scS dh rh core kind label ip sp lr
        x0 x1 x2 x3 x4 x5 x6 x7 layout rf n 0 := by
  unfold ReplyRecvArm.callFaultTakeLegsW ReplyRecvArm.callFaultTakeLegs
  rw [performFaultAnswerW_eq (h := h)]

/-- **The reply-receive answering a fault and taking a queued caller, over
every arm, in place**: the arm's reply leg with no message and pop, the
server's context return, the take, the arm's lend, the server's priority walk
and the fault answer (`ReplyRecvArm.callFaultTakeLegs`). -/
@[noinline] def performReplyRecvArmCallFaultTakeLegs (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (layout : SeLe4n.SyscallRegisterLayout)
    (len : Nat) (m0 m1 m2 m3 : UInt64) : SystemState :=
  arm.callFaultTakeLegsW lends (receiveReturnSchedContextFast true
    (arm.pop (arm.faultLeg st c tid rid) c tid scId home) tid.val) c tid s rid epId nextCode scS
    dh rh core kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7
    (Architecture.regMessageLength layout len) m0 m1 m2 m3

/-- The fault Call take over the arm, its legs and then the server's frame
(`writeReceiverMessageFrame`), each out of line. -/
@[inline] def performReplyRecvArmCallFaultTakeDelivered (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (layout : SeLe4n.SyscallRegisterLayout)
    (len : Nat) (m0 m1 m2 m3 : UInt64) (sRf : SeLe4n.RegisterFile) (sLen : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) : SystemState :=
  writeReceiverMessageFrame (performReplyRecvArmCallFaultTakeLegs arm lends scId home st c tid rid epId
    s nextCode scS dh rh core kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 layout len m0 m1 m2 m3)
    tid sRf sLen badgeWord badged

/-- **The reply-receive answering a fault and taking a queued caller is the
specification's, over every arm**: under the arm's reply-leg guard and
Call-take guard, for a caller carrying fault `tf` and a caller `s` at the head
of the send queue blocked by a routed capability-free call, not delivering a
fault (every check read on the pre-state), the arm's transition, then the
server's staged message, is `performReplyRecvArmCallFaultTakeDelivered`. -/
theorem replyRecvTransferOnCore_arm_callFaultTake (arm : ReplyRecvArm) (lends : Bool)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badge : Option SeLe4n.Badge) (grant : Bool) (core : CoreId)
    (ct : TCB) (rp : Reply) (ep : Endpoint) (tf : ThreadFault)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmitsAt lends st epId tid s sTcb rid)
    (hSz4 : Architecture.regMessageLength layout len ≤ 4)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .call capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match replyRecvTransferOnCore epId tid rid c label
        { registers := Architecture.regMessageBody layout rf len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmCallFaultTakeDelivered arm lends scId home st c tid rid epId s
        sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
        (determineTargetCore st tid) core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr
        ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7
        layout len (Architecture.regLayoutWord layout rf 0)
        (Architecture.regLayoutWord layout rf 1) (Architecture.regLayoutWord layout rf 2)
        (Architecture.regLayoutWord layout rf 3) sTcb.registerContext mi.length
        (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨-, hNe, hNo, -, -⟩ := arm.legPop (scId := scId) (home := home) st tid c rid
    IpcMessage.empty core ct rp hAd (by simp [IpcMessage.empty]) hT hRO hRp
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label
    { registers := Architecture.regMessageBody layout rf len, badge := badge } hTc hPF
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid
    (arm.leg_noResizeDue st c tid rid IpcMessage.empty hNo)
  have hXf : replyRecvReplyTransfer (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regMessageBody layout rf len, badge := badge }) st tid c grant
      (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) =
      .ok ({ results := #[] }, arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) := by
    rw [hAns]; rfl
  obtain ⟨sTcb2, -, -, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_callTake arm lends _ st epId tid c
    rid IpcMessage.empty grant core ct rp ep s sTcb capAddr mi hAd hCA
    (by simp [IpcMessage.empty]) hT hRO hRp hE hH hS hSC hR hF hXf (transferFrame.refl _) hNoP
  have hR2 : registerRoutedSyscall
      (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb2.registerContext)
      SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 = .call capAddr mi := by
    rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  have hST := hG2.ne
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label
      { registers := Architecture.regMessageBody layout rf len, badge := badge })
      { registers := Architecture.regMessageBody layout rf len, badge := badge } =
      IpcMessage.empty := by rw [hAns]; rfl
  unfold replyRecvTransferOnCore
  rw [hL, hEq]
  dsimp only
  rw [CapTransferSummary.capInfo_empty, hAns]
  unfold replyRecvAnswerCaller
  dsimp only
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswer _ c ct tf hPF _ _ layout rf
    (Architecture.regMessageLength layout len) 0
    (by simp only [Architecture.regMessageBody_size, Nat.min_self])
    (fun i hi => wordAt_regMessageBody layout rf len i hi)]
  have hSt := arm.callAnswerFrame_staged lends (fun X => performFaultAnswer X c ct.faultKind label
      ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
      ct.faultX5 ct.faultX6 ct.faultX7 layout rf (Architecture.regMessageLength layout len) 0)
    _ tid s rid epId sTcb2 ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
    (determineTargetCore st tid) core capAddr mi
    (fun X m hX => performFaultAnswer_msg X c tid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ layout rf _ _
      (fun e => hNe e.symm) hX)
    (fun X hX => performFaultAnswer_noResizeDue X c _ _ _ _ _ _ _ _ _ _ _ _ _ layout rf _ _ hX)
    (receiveReturnSchedContext_noResizeDue true _ tid hNoP) hST hR2 hF2
  dsimp only at hSt
  rw [hSt, hK.queueNext, hK.regs, hK.badge, hK.badged]
  unfold performReplyRecvArmCallFaultTakeDelivered performReplyRecvArmCallFaultTakeLegs
  rw [ReplyRecvArm.callFaultTakeLegsW_eq (h := hSz4)]
  unfold ReplyRecvArm.callFaultTakeLegs
  rw [receiveReturnSchedContextFast_eq, arm.faultLeg_eq]

/-! ### The long fault answer -/

/-- **The Call take's writes keep every buffer read**: the pop, the caller's
and the server's state writes, the server's held message, the arm's lend and
the priority walk write no buffer. -/
theorem ReplyRecvArm.callTakeState_wordsAgree (lends : Bool) (Q : SystemState)
    (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (sTcb : TCB) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId)
    (hNo : Q.objects.noResizeDue) :
    ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore (ReplyRecvArm.callLend lends
      (receiveCallTakeState Q epId s sTcb tid rid) s tid scS dh rh) tid core).1 Q := by
  rw [receiveCallTakeState_eq_hold _ _ _ _ _ _ hNo]
  have hNoR := storeReceiveCallReady_noResizeDue Q epId s sTcb.queueNextCode tid rid hNo
  have hAR := ipcBufferReadsAgree_storeReceiveCallReady Q epId s sTcb.queueNextCode tid rid hNo
  generalize storeReceiveCallReady Q epId s sTcb.queueNextCode tid rid = R at hNoR hAR
  have hNoH : (R.mapTcbInPlace tid (holdMessage (blockedSenderMessage
      (storePopHead Q epId false s sTcb.queueNext) s sTcb))).objects.noResizeDue :=
    (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNoR
  have hNoM := ReplyRecvArm.callLend_noResizeDue lends _ s tid scS dh rh hNoH
  exact ((ipcBufferReadsAgree_propagatePipChainCrossCore _ tid core hNoM).trans
    ((ReplyRecvArm.ipcBufferReadsAgree_callLend lends _ s tid scS dh rh hNoH).trans
    ((ipcBufferReadsAgree_mapTcbInPlace R tid (holdMessage (blockedSenderMessage
      (storePopHead Q epId false s sTcb.queueNext) s sTcb)) (fun _ => ⟨rfl, rfl⟩)).trans
      hAR))).words

/-- **The long fault Call take's writes before the server's own frame, over
the arm**: as `ReplyRecvArm.callFaultTakeLegs`, the answer's words past MR3
read from the replier's buffer (`performFaultAnswerLong`). -/
@[inline] def ReplyRecvArm.callFaultTakeLegsLong (arm : ReplyRecvArm) (lends : Bool) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (rf : SeLe4n.RegisterFile) (len : Nat) :
    SystemState :=
  performFaultAnswerLong (PriorityInheritance.propagatePipChainCrossCore
    (ReplyRecvArm.callLend lends (storeReceiveCallReady Y epId s nextCode tid rid) s tid scS dh rh) tid core).1
    c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid rf len

/-- `ReplyRecvArm.callFaultTakeLegsLong` with the reply's four inline words in
place of the replier's register file (`performFaultAnswerLongW`). -/
@[inline] def ReplyRecvArm.callFaultTakeLegsLongW (arm : ReplyRecvArm) (lends : Bool) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (len : Nat) (m0 m1 m2 m3 : UInt64) :
    SystemState :=
  performFaultAnswerLongW (PriorityInheritance.propagatePipChainCrossCore
    (ReplyRecvArm.callLend lends (storeReceiveCallReady Y epId s nextCode tid rid) s tid scS dh rh) tid core).1
    c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid len m0 m1 m2 m3

theorem ReplyRecvArm.callFaultTakeLegsLongW_eq (arm : ReplyRecvArm) (lends : Bool) (Y : SystemState)
    (c tid s : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (nextCode : Nat)
    (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (rf : SeLe4n.RegisterFile) (len : Nat) :
    arm.callFaultTakeLegsLongW lends Y c tid s rid epId nextCode scS dh rh core kind label ip sp lr
      x0 x1 x2 x3 x4 x5 x6 x7 len (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
      (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) =
      arm.callFaultTakeLegsLong lends Y c tid s rid epId nextCode scS dh rh core kind label ip sp lr
        x0 x1 x2 x3 x4 x5 x6 x7 rf len := by
  unfold ReplyRecvArm.callFaultTakeLegsLongW ReplyRecvArm.callFaultTakeLegsLong
  rw [performFaultAnswerLongW_eq]

/-- **The long reply-receive answering a fault and taking a queued caller,
over every arm, in place**: as `performReplyRecvArmCallFaultTakeLegs`, the
answer's words past MR3 read from the replier's buffer. -/
@[noinline] def performReplyRecvArmCallFaultTakeLegsLong (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (len : Nat) (m0 m1 m2 m3 : UInt64) :
    SystemState :=
  arm.callFaultTakeLegsLongW lends (receiveReturnSchedContextFast true
    (arm.pop (arm.faultLeg st c tid rid) c tid scId home) tid.val) c tid s rid epId nextCode scS
    dh rh core kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 len m0 m1 m2 m3

/-- The long fault Call take over the arm, its legs and then the server's
frame. -/
@[inline] def performReplyRecvArmCallFaultTakeDeliveredLong (arm : ReplyRecvArm) (lends : Bool)
    (scId : SeLe4n.SchedContextId) (home : CoreId) (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (s : SeLe4n.ThreadId)
    (nextCode : Nat) (scS : SeLe4n.SchedContextId) (dh rh core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (len : Nat) (m0 m1 m2 m3 : UInt64)
    (sRf : SeLe4n.RegisterFile) (sLen : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool) :
    SystemState :=
  writeReceiverMessageFrame (performReplyRecvArmCallFaultTakeLegsLong arm lends scId home st c tid rid
    epId s nextCode scS dh rh core kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 len m0 m1 m2 m3)
    tid sRf sLen badgeWord badged

/-- **The long reply-receive answering a fault and taking a queued caller is
the specification's, over every arm**: as
`replyRecvTransferOnCore_arm_callFaultTake`, the reply of more than four
words. -/
theorem replyRecvTransferOnCore_arm_callFaultTakeLong (arm : ReplyRecvArm) (lends : Bool)
    {scId : SeLe4n.SchedContextId} {home : CoreId} (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (rp : Reply) (ep : Endpoint) (tf : ThreadFault)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hAd : arm.LegAdmits scId home st tid c rid ct)
    (hCA : arm.CallAdmitsAt lends st epId tid s sTcb rid) (hLen : 4 ≤ len)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hRO : ct.replyObject = some rid)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hE : st.objects[epId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hS : st.objects[s.toObjId]? = some (.tcb sTcb)) (hSC : s ≠ c)
    (hR : registerRoutedSyscall (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
      SeLe4n.arm64DefaultLayout sTcb.registerContext 32 = .call capAddr mi)
    (hF : sTcb.ipcFaultSend = false) :
    (match replyRecvTransferOnCore epId tid rid c label
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st with
      | .ok (summary, st') =>
          (.ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo) :
            Except KernelError (Unit × SystemState))
      | .error e => .error e) =
      .ok ((), performReplyRecvArmCallFaultTakeDeliveredLong arm lends scId home st c tid rid epId s
        sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
        (determineTargetCore st tid) core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr
        ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7
        len (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) sTcb.registerContext mi.length
        (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨-, hNe, hNo, -, -⟩ := arm.legPop (scId := scId) (home := home) st tid c rid
    IpcMessage.empty core ct rp hAd (by simp [IpcMessage.empty]) hT hRO hRp
  let msg : IpcMessage := { registers := longReplyRecvRegs rf st tid len, badge := badge }
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label msg hTc hPF
  have hNoL := arm.leg_noResizeDue st c tid rid IpcMessage.empty hNo
  have hNoP := arm.pop_noResizeDue (scId := scId) (home := home) _ c tid hNoL
  have hXf : replyRecvReplyTransfer (replyRecvCallerFaultAnswer? st c label msg) st tid c grant
      (arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) =
      .ok ({ results := #[] }, arm.pop (arm.leg st c tid rid IpcMessage.empty) c tid scId home) := by
    rw [hAns]; rfl
  obtain ⟨sTcb2, -, -, hK, hG2, hEq⟩ := replyRecvAnsweringOnCore_arm_callTake arm lends _ st epId tid c
    rid IpcMessage.empty grant core ct rp ep s sTcb capAddr mi hAd hCA
    (by simp [IpcMessage.empty]) hT hRO hRp hE hH hS hSC hR hF hXf (transferFrame.refl _) hNoP
  have hR2 : registerRoutedSyscall
      (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb2.registerContext)
      SeLe4n.arm64DefaultLayout sTcb2.registerContext 32 = .call capAddr mi := by
    rw [hK.regs]; exact hR
  have hF2 : sTcb2.ipcFaultSend = false := by rw [hK.faultSend]; exact hF
  have hST := hG2.ne
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label msg) msg =
      IpcMessage.empty := by rw [hAns]; rfl
  have hNoQ := receiveReturnSchedContext_noResizeDue true _ tid hNoP
  have hW := (ReplyRecvArm.callTakeState_wordsAgree lends _ epId s sTcb2 tid rid ⟨sTcb.scBindingScCode - 1⟩
    (determineTargetCore st s) (determineTargetCore st tid) core hNoQ).trans
    ((ipcBufferReadsAgree_receiveReturnSchedContext true _ tid hNoP).trans
      ((arm.ipcBufferReadsAgree_pop (scId := scId) (home := home) _ c tid hNoL).trans
        (arm.ipcBufferReadsAgree_leg st c tid rid IpcMessage.empty hNo))).words
  unfold replyRecvTransferOnCore
  rw [hL, hEq]
  dsimp only
  rw [CapTransferSummary.capInfo_empty]
  unfold replyRecvAnswerCaller
  rw [hAns]
  dsimp only
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ tid rf len
    (replyWordOr_longReplyRecvRegs st _ tid rf len label hLen hW)]
  have hSt := arm.callAnswerFrame_staged lends (fun X => performFaultAnswerLong X c ct.faultKind label
      ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
      ct.faultX5 ct.faultX6 ct.faultX7 tid rf len)
    _ tid s rid epId sTcb2 ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
    (determineTargetCore st tid) core capAddr mi
    (fun X m hX => performFaultAnswerLong_msg X c tid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ tid rf len
      (fun e => hNe e.symm) hX)
    (fun X hX => performFaultAnswerLong_noResizeDue X c _ _ _ _ _ _ _ _ _ _ _ _ _ tid rf len hX)
    hNoQ hST hR2 hF2
  dsimp only at hSt
  rw [hSt, hK.queueNext, hK.regs, hK.badge, hK.badged]
  unfold performReplyRecvArmCallFaultTakeDeliveredLong performReplyRecvArmCallFaultTakeLegsLong
  rw [ReplyRecvArm.callFaultTakeLegsLongW_eq]
  unfold ReplyRecvArm.callFaultTakeLegsLong
  rw [receiveReturnSchedContextFast_eq, arm.faultLeg_eq]

/-! ### The arm's Call-take guard, read on the pre-state -/

/-- Whether the server `tid` is a thread whose field `f` reads zero. -/
@[inline] def replyRecvServerReadsZero (st : SystemState) (tid : SeLe4n.ThreadId)
    (f : TCB → Nat) : Bool :=
  match st.getTcb? tid with
  | some rt => f rt == 0
  | none => false

theorem replyRecvServerReadsZero_spec {st : SystemState} {tid : SeLe4n.ThreadId}
    {f : TCB → Nat} (h : replyRecvServerReadsZero st tid f = true) :
    ∃ rt, st.getTcb? tid = some rt ∧ f rt = 0 := by
  unfold replyRecvServerReadsZero at h
  cases hT : st.getTcb? tid with
  | none => rw [hT] at h; cases h
  | some rt => rw [hT] at h; exact ⟨rt, rfl, beq_iff_eq.mp h⟩

/-- **The arm's Call-take guard as a test on the pre-state**
(`ReplyRecvArm.callGuard_spec`), for the queued caller `s`. -/
@[inline] def ReplyRecvArm.callGuard : ReplyRecvArm → SystemState → SeLe4n.ObjId →
    SeLe4n.ThreadId → SeLe4n.ThreadId → TCB → SeLe4n.ReplyId → Bool
  | .rendezvous, st, epId, tid, s, sTcb, rid => receiveCallDonatesPastReply st epId tid s sTcb rid
  | .unlinked, st, epId, tid, s, sTcb, rid => receiveCallDonatesPastReply st epId tid s sTcb rid
  | .donated, st, epId, tid, s, sTcb, rid =>
      receiveCallDonatesPastPop st epId tid s sTcb rid (replyHeadContextCode st rid)
  | .unheld, st, epId, tid, s, sTcb, rid =>
      receiveCallDonatesPastPop st epId tid s sTcb rid (replyHeadContextCode st rid) &&
        replyRecvServerReadsZero st tid TCB.scBindingScCode
  | .held, st, epId, tid, s, sTcb, _ =>
      receiveCallTakesPastPop st epId tid s sTcb &&
        replyRecvServerReadsZero st tid TCB.boundNotificationCode

theorem ReplyRecvArm.callGuard_spec {arm : ReplyRecvArm} {st : SystemState}
    {epId : SeLe4n.ObjId} {tid s : SeLe4n.ThreadId} {sTcb : TCB} {rid : SeLe4n.ReplyId}
    (h : arm.callGuard st epId tid s sTcb rid = true) :
    arm.CallAdmits st epId tid s sTcb rid := by
  cases arm <;> simp only [ReplyRecvArm.callGuard, Bool.and_eq_true] at h <;>
    simp only [ReplyRecvArm.CallAdmits]
  · exact h
  · exact h
  · exact ⟨h.1, replyRecvServerReadsZero_spec h.2⟩
  · exact ⟨h.1, replyRecvServerReadsZero_spec h.2⟩
  · exact h

/-- Whether the server `tid` is a thread bound to a scheduling context and to
no notification. -/
@[inline] def replyRecvServerOwnContext (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some rt => rt.scBindingScCode != 0 && rt.boundNotificationCode == 0
  | none => false

/-- **The own-context Call-take guard as a test on the pre-state**
(`ReplyRecvArm.callOwnGuard_spec`): the rendezvous, unlinked and unheld arms
only; the donated and held arms have none (`CallAdmitsOwn`). -/
@[inline] def ReplyRecvArm.callOwnGuard : ReplyRecvArm → SystemState → SeLe4n.ObjId →
    SeLe4n.ThreadId → SeLe4n.ThreadId → TCB → Bool
  | .rendezvous, st, epId, tid, s, sTcb =>
      receiveCallTakesPastPop st epId tid s sTcb && replyRecvServerOwnContext st tid
  | .unlinked, st, epId, tid, s, sTcb =>
      receiveCallTakesPastPop st epId tid s sTcb && replyRecvServerOwnContext st tid
  | .unheld, st, epId, tid, s, sTcb =>
      receiveCallTakesPastPop st epId tid s sTcb && replyRecvServerOwnContext st tid
  | .donated, _, _, _, _, _ => false
  | .held, _, _, _, _, _ => false

theorem ReplyRecvArm.callOwnGuard_spec {arm : ReplyRecvArm} {st : SystemState}
    {epId : SeLe4n.ObjId} {tid s : SeLe4n.ThreadId} {sTcb : TCB}
    (h : arm.callOwnGuard st epId tid s sTcb = true) :
    arm.CallAdmitsOwn st epId tid s sTcb := by
  have own : receiveCallTakesPastPop st epId tid s sTcb = true →
      replyRecvServerOwnContext st tid = true →
      receiveCallTakesPastPop st epId tid s sTcb = true ∧
        ∃ rt, st.getTcb? tid = some rt ∧ rt.scBindingScCode ≠ 0 ∧
          rt.boundNotificationCode = 0 := by
    intro h1 h2
    unfold replyRecvServerOwnContext at h2
    cases hT : st.getTcb? tid with
    | none => rw [hT] at h2; cases h2
    | some rt =>
      rw [hT] at h2
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, beq_iff_eq] at h2
      exact ⟨h1, rt, rfl, h2.1, h2.2⟩
  cases arm <;> simp only [ReplyRecvArm.callOwnGuard, Bool.and_eq_true, Bool.false_eq_true] at h
  · exact own h.1 h.2
  · exact own h.1 h.2
  · exact own h.1 h.2

/-- **Whether the endpoint's send queue offers a caller the receive leg may
take in place**: its head is not the answered caller, delivers no fault, and
its saved frame routes as a capability-free call, each read on the
pre-state. -/
@[inline] def replyRecvCallerQueued (st : SystemState) (epId : SeLe4n.ObjId)
    (c : SeLe4n.ThreadId) : Bool :=
  match st.getEndpoint? epId with
  | some ep =>
      match ep.sendQ.head with
      | some s =>
          s.val != c.val &&
          (match st.getTcb? s with
           | some sTcb =>
               !sTcb.ipcFaultSend &&
               (match registerRoutedSyscallOf
                   (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
                   SeLe4n.arm64DefaultLayout sTcb.registerContext with
                | .call _ _ => true
                | _ => false)
           | none => false)
      | none => false
  | none => false

theorem replyRecvCallerQueued_spec {st : SystemState} {epId : SeLe4n.ObjId}
    {c : SeLe4n.ThreadId} (h : replyRecvCallerQueued st epId c = true) :
    ∃ (ep : Endpoint) (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr)
      (mi : MessageInfo),
      st.getEndpoint? epId = some ep ∧ ep.sendQ.head = some s ∧ st.getTcb? s = some sTcb ∧
      s ≠ c ∧ sTcb.ipcFaultSend = false ∧
      registerRoutedSyscallOf (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
        SeLe4n.arm64DefaultLayout sTcb.registerContext = .call capAddr mi := by
  unfold replyRecvCallerQueued at h
  cases hEp : st.getEndpoint? epId with
  | none => rw [hEp] at h; cases h
  | some ep =>
  rw [hEp] at h
  dsimp only at h
  cases hH : ep.sendQ.head with
  | none => rw [hH] at h; cases h
  | some s =>
  rw [hH] at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hSC, hT⟩ := h
  have hSC' : s ≠ c := fun e => by subst e; simp at hSC
  cases hTs : st.getTcb? s with
  | none => rw [hTs] at hT; cases hT
  | some sTcb =>
  rw [hTs] at hT
  simp only [Bool.and_eq_true, Bool.not_eq_true'] at hT
  obtain ⟨hF, hR⟩ := hT
  split at hR
  · next capAddr mi hR' => exact ⟨ep, s, sTcb, capAddr, mi, rfl, hH, hTs, hSC', hF, hR'⟩
  · cases hR

end SeLe4n.Kernel
