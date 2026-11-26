/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.AnswerCommute
import SeLe4n.Kernel.IPC.CrossCore.ReceiveReturnInPlace

/-!
# The receive leg commutes with the answer to another caller

WS-SX SX31.  `AnswerCommute` and `DeliveryCommute` show the answer to a
caller `r` (one write of its answer slots, `TCB.withAnswerSlots`) commuting
with the run queue, the reply-waiter queues, the priority walk, the stores and
the queue pop.  This file carries the rest of a `.replyRecv` receive leg: the
reads it makes, which are equal through the answer when the thread they read
is not `r`; the receiver's and the sender's state and message stores; the
reply links; the wake; the queue append; the pre-receive donation's cleanup;
the context return; the post-receive donation and the priority hand-off.

The answer here keeps the stashed receive reply (`π = id`): both answers do
(the stage and the restart), and a reply's stash check reads it
(`SystemState.replyStashedAt`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

section Reads

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (κ : Nat → Nat)

/-- A read of one object that cannot see a thread's answer slots. -/
theorem objects_read_answer {α : Type} (Z : SystemState) (k : SeLe4n.ObjId)
    (f : Option KernelObject → α)
    (hf : ∀ t, f (some (.tcb (TCB.withAnswerSlots ρ μ id κ t))) = f (some (.tcb t))) :
    f ((Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).objects[k]?) = f (Z.objects[k]?) :=
  objects_read_mapTcbInPlace r Z k f hf

theorem getEndpoint?_answer (Z : SystemState) (k : SeLe4n.ObjId) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getEndpoint? k = Z.getEndpoint? k :=
  objects_read_answer r ρ μ κ Z k (fun o => match o with
    | some (.endpoint ep) => some ep | _ => none) (fun _ => rfl)

theorem getReply?_answer (Z : SystemState) (k : SeLe4n.ReplyId) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getReply? k = Z.getReply? k :=
  objects_read_answer r ρ μ κ Z k.toObjId (fun o => match o with
    | some (.reply x) => some x | _ => none) (fun _ => rfl)

theorem getNotification?_answer (Z : SystemState) (k : SeLe4n.ObjId) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getNotification? k = Z.getNotification? k :=
  objects_read_answer r ρ μ κ Z k (fun o => match o with
    | some (.notification x) => some x | _ => none) (fun _ => rfl)

theorem getSchedContext?_answer (Z : SystemState) (k : SeLe4n.SchedContextId) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getSchedContext? k = Z.getSchedContext? k :=
  objects_read_answer r ρ μ κ Z k.toObjId (fun o => match o with
    | some (.schedContext x) => some x | _ => none) (fun _ => rfl)

theorem getObject?_isSome_answer (Z : SystemState) (k : SeLe4n.ObjId) :
    ((Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getObject? k).isSome = (Z.getObject? k).isSome :=
  objects_read_answer r ρ μ κ Z k (fun o => o.isSome) (fun _ => rfl)

theorem getTcb?_answer_ne (Z : SystemState) (t : SeLe4n.ThreadId) (h : t ≠ r) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getTcb? t = Z.getTcb? t := by
  rw [SystemState.getTcb?_mapTcbInPlace, if_neg (Ne.symm h)]

/-- The stash check reads a stasher's state and stashed reply, which the
answer keeps. -/
theorem replyStashedAt_answer (Z : SystemState) (rid : SeLe4n.ReplyId) (x : Reply) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).replyStashedAt rid x = Z.replyStashedAt rid x := by
  unfold SystemState.replyStashedAt
  split
  · rfl
  · rcases getTcb?_answer_cases r ρ μ id κ Z _ with h | ⟨_, h⟩ <;> rw [h]
    cases Z.getTcb? _ <;> rfl

theorem replyStashValid_answer (Z : SystemState) (rid : Option SeLe4n.ReplyId) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).replyStashValid rid = Z.replyStashValid rid := by
  unfold SystemState.replyStashValid
  rcases rid with _ | rid
  · rfl
  · simp only [getReply?_answer, replyStashedAt_answer]

theorem rendezvousDequeuedCall_answer (Z : SystemState) (t : SeLe4n.ThreadId) :
    rendezvousDequeuedCall (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t =
      rendezvousDequeuedCall Z t := by
  unfold rendezvousDequeuedCall
  rw [lookupTcb_answer]
  by_cases h : r = t
  · rw [if_pos h]; cases lookupTcb Z t <;> rfl
  · rw [if_neg h]

theorem receiveRendezvousSender?_answer (Z : SystemState) (k : SeLe4n.ObjId) :
    receiveRendezvousSender? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) k =
      receiveRendezvousSender? Z k := by
  unfold receiveRendezvousSender?; rw [getEndpoint?_answer]

theorem placedCoreOf?_answer (Z : SystemState) (t : SeLe4n.ThreadId) :
    placedCoreOf? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t = placedCoreOf? Z t := by
  unfold placedCoreOf?
  simp only [queuedOn_answer, SystemState.mapTcbInPlace_scheduler]

theorem lookupIPCBuffer_answer (Z : SystemState) (tcb : TCB) (w : Bool) :
    Architecture.IpcBufferRead.lookupIPCBuffer w (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tcb =
      Architecture.IpcBufferRead.lookupIPCBuffer w Z tcb :=
  lookupIPCBuffer_mapTcbInPlace r Z tcb w

theorem receiverHasBuffer_answer (Z : SystemState) (tcb : TCB) :
    receiverHasBuffer (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tcb = receiverHasBuffer Z tcb := by
  unfold receiverHasBuffer; rw [lookupIPCBuffer_answer]

theorem receiverBufferWord?_answer (Z : SystemState) (tcb : TCB) (i : Nat) :
    receiverBufferWord? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tcb i = receiverBufferWord? Z tcb i := by
  unfold receiverBufferWord?; rw [lookupIPCBuffer_answer]; rfl

theorem receivePathSlot?_answer (Z : SystemState) (tcb : TCB) (c i d : UInt64) :
    receivePathSlot? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tcb c i d = receivePathSlot? Z tcb c i d := by
  have hC : ∀ k, (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getCNode? k = Z.getCNode? k :=
    getCNode?_mapTcbInPlace_blind r Z
  unfold receivePathSlot?
  simp only [lookupSlot_congr_getCNode? _ Z hC, lookupSlotCap_congr_getCNode? _ Z hC,
    lookupSlotForCNodeOp_congr_getCNode? _ Z hC]

theorem receiveSlot?_answer (Z : SystemState) (tcb : TCB) :
    receiveSlot? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tcb = receiveSlot? Z tcb := by
  unfold receiveSlot?; simp only [receiverBufferWord?_answer, receivePathSlot?_answer]

/-- The receiver's side of a transfer, read at a receiver that is not the
answered thread. -/
theorem receiverCapTarget?_answer (Z : SystemState) (t : SeLe4n.ThreadId) (h : t ≠ r) :
    receiverCapTarget? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t = receiverCapTarget? Z t := by
  unfold receiverCapTarget?
  rw [getTcb?_answer_ne r ρ μ κ Z t h]
  simp only [receiverHasBuffer_answer, receiveSlot?_answer]

theorem ipcBufferReadMr_answer (Z : SystemState) (t : SeLe4n.ThreadId) (i : Nat) (h : t ≠ r) :
    Architecture.IpcBufferRead.ipcBufferReadMr (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t i =
      Architecture.IpcBufferRead.ipcBufferReadMr Z t i := by
  unfold Architecture.IpcBufferRead.ipcBufferReadMr
  rw [getTcb?_answer_ne r ρ μ κ Z t h]
  simp only [lookupIPCBuffer_answer]; rfl

theorem readOverflowWord_answer (Z : SystemState) (t : SeLe4n.ThreadId) (h : t ≠ r) :
    Architecture.RegisterDecode.readOverflowWord (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t =
      Architecture.RegisterDecode.readOverflowWord Z t := by
  funext i
  unfold Architecture.RegisterDecode.readOverflowWord
  rw [ipcBufferReadMr_answer r ρ μ κ Z t i h]

theorem decodeSyscallArgsFromState_answer (op : Nat) (Z : SystemState) (t : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (regs : SeLe4n.RegisterFile) (n : Nat) (h : t ≠ r) :
    Architecture.RegisterDecode.decodeSyscallArgsFromState op
        (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t layout regs n =
      Architecture.RegisterDecode.decodeSyscallArgsFromState op Z t layout regs n := by
  unfold Architecture.RegisterDecode.decodeSyscallArgsFromState
  rw [readOverflowWord_answer r ρ μ κ Z t h]

theorem blockedSenderDecode_answer (Z : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB) (h : t ≠ r) :
    blockedSenderDecode (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t tcb = blockedSenderDecode Z t tcb := by
  unfold blockedSenderDecode; rw [decodeSyscallArgsFromState_answer r ρ μ κ _ _ t _ _ _ h]

theorem blockedSenderMessage_answer (Z : SystemState) (t : SeLe4n.ThreadId) (tcb : TCB) (h : t ≠ r) :
    blockedSenderMessage (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t tcb = blockedSenderMessage Z t tcb := by
  unfold blockedSenderMessage; rw [blockedSenderDecode_answer r ρ μ κ Z t tcb h]

theorem senderExtraCapAddrs_answer (Z : SystemState) (tcb : TCB) (n : Nat) :
    senderExtraCapAddrs (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tcb n = senderExtraCapAddrs Z tcb n := by
  have : senderExtraCapAddr? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tcb = senderExtraCapAddr? Z tcb := by
    funext i; unfold senderExtraCapAddr?; rw [lookupIPCBuffer_answer]; rfl
  unfold senderExtraCapAddrs; rw [this]

/-- The capability request a receive reads off its send queue's head, at a
head that is not the answered thread. -/
theorem receiveCapRequest_answer (Z : SystemState) (k : SeLe4n.ObjId)
    (h : receiveRendezvousSender? Z k ≠ some r) :
    receiveCapRequest (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) k = receiveCapRequest Z k := by
  unfold receiveCapRequest
  rw [receiveRendezvousSender?_answer]
  cases hS : receiveRendezvousSender? Z k with
  | none => rfl
  | some s =>
    have hs : s ≠ r := fun e => h (by rw [hS, e])
    dsimp only
    rw [getTcb?_answer_ne r ρ μ κ Z s hs]
    cases Z.getTcb? s with
    | none => rfl
    | some tcb =>
      dsimp only
      unfold blockedSenderCapRequest senderFrameCapRequest
      simp only [blockedSenderDecode_answer r ρ μ κ Z s tcb hs, senderExtraCapAddrs_answer]

end Reads

section Stores

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (κ : Nat → Nat)

/-- A store at a present key in the stored kind, through the answer: at
another thread, or of objects the answer leaves alone. -/
theorem storeObject_answer (Z : SystemState) (k : SeLe4n.ObjId) (o0 o : KernelObject)
    (hk : Z.objects[k]? = some o0) (hNo : Z.objects.noResizeDue)
    (hL : storeLeavesIndexAndTypes Z k o.objectType = true)
    (hw : k ≠ r.toObjId ∨ (KernelObject.mapTcb (TCB.withAnswerSlots ρ μ id κ) o = o ∧
      KernelObject.mapTcb (TCB.withAnswerSlots ρ μ id κ) o0 = o0)) :
    storeObject k o (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      mapStepState r (TCB.withAnswerSlots ρ μ id κ) (storeObject k o Z) := by
  rw [storeObject_eq_of_leaves hL]
  rcases hw with hne | ⟨h1, h2⟩
  · exact storeObject_mapTcbInPlace_ne r Z k o0 o hk hne hNo hL
  · exact storeObject_mapTcbInPlace_of_fixed r Z k o0 o hk hNo h1 h2 hL

theorem storeObject_present_noResizeDue (Z Z' : SystemState) (k : SeLe4n.ObjId) (o0 o : KernelObject)
    (hk : Z.objects[k]? = some o0) (hNo : Z.objects.noResizeDue)
    (hL : storeLeavesIndexAndTypes Z k o.objectType = true) (h : storeObject k o Z = .ok ((), Z')) :
    Z'.objects.noResizeDue := by
  rw [storeObject_eq_of_leaves hL] at h
  cases h
  exact insert_present_noResizeDue Z k o0 o hk hNo

theorem storeLeaves_reply {Z : SystemState} {rid : SeLe4n.ReplyId} {x : Reply}
    (h : Z.getReply? rid = some x) (y : Reply) :
    storeLeavesIndexAndTypes Z rid.toObjId (KernelObject.reply y).objectType = true := by
  unfold storeLeavesIndexAndTypes storeKeepsKind
  rw [(SystemState.getReply?_eq_some_iff _ _ _).mp h]; rfl

theorem storeTcbIpcStateAndMessage_answer (Z : SystemState) (t : SeLe4n.ThreadId)
    (s : ThreadIpcState) (m : Option IpcMessage) (hNo : Z.objects.noResizeDue) (h : t ≠ r) :
    storeTcbIpcStateAndMessage (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t s m =
      (storeTcbIpcStateAndMessage Z t s m).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold storeTcbIpcStateAndMessage
  exact modifyTcb_mapTcbInPlace r Z t _ hNo (fun e => absurd e h)

theorem storeTcbIpcStateAndMessage_noResizeDue (Z Z' : SystemState) (t : SeLe4n.ThreadId)
    (s : ThreadIpcState) (m : Option IpcMessage) (hNo : Z.objects.noResizeDue)
    (h : storeTcbIpcStateAndMessage Z t s m = .ok Z') : Z'.objects.noResizeDue :=
  modifyTcb_noResizeDue Z Z' t _ hNo h

theorem linkReply_answer (Z : SystemState) (rid : SeLe4n.ReplyId) (c : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) :
    SystemState.linkReply rid c (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      mapStepState r (TCB.withAnswerSlots ρ μ id κ) (SystemState.linkReply rid c Z) := by
  unfold SystemState.linkReply
  rw [getReply?_answer]
  cases hR : Z.getReply? rid with
  | none => rfl
  | some x =>
    dsimp only
    split
    · exact storeObject_answer r ρ μ κ Z _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hNo
        (storeLeaves_reply hR _) (.inr ⟨rfl, rfl⟩)
    · rfl

theorem linkReply_noResizeDue (Z Z' : SystemState) (rid : SeLe4n.ReplyId) (c : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) (h : SystemState.linkReply rid c Z = .ok ((), Z')) :
    Z'.objects.noResizeDue := by
  unfold SystemState.linkReply at h
  cases hR : Z.getReply? rid with
  | none => rw [hR] at h; cases h
  | some x =>
    rw [hR] at h
    dsimp only at h
    split at h
    · exact storeObject_present_noResizeDue Z Z' _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hR)
        hNo (storeLeaves_reply hR _) h
    · cases h

theorem linkCallerReply_answer (Z : SystemState) (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hNo : Z.objects.noResizeDue) (h : c ≠ r) :
    SystemState.linkCallerReply c rid (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      mapStepState r (TCB.withAnswerSlots ρ μ id κ) (SystemState.linkCallerReply c rid Z) := by
  unfold SystemState.linkCallerReply
  rw [linkReply_answer r ρ μ κ Z rid c hNo]
  cases hL : SystemState.linkReply rid c Z with
  | error e => rfl
  | ok p =>
    obtain ⟨⟨⟩, Za⟩ := p
    have hNo1 := linkReply_noResizeDue Z Za rid c hNo hL
    dsimp only [mapStepState]
    rw [getTcb?_answer_ne r ρ μ κ Za c h]
    cases hT : Za.getTcb? c with
    | none => rfl
    | some tcb =>
      dsimp only
      split
      · exact storeObject_answer r ρ μ κ Za _ _ _ ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT) hNo1
          (storeLeavesIndexAndTypes_tcb_of_getTcb? hT)
          (.inl (fun e => h (SeLe4n.ThreadId.toObjId_injective _ _ e)))
      · rfl

theorem linkCallerReply_noResizeDue (Z Z' : SystemState) (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hNo : Z.objects.noResizeDue) (h : SystemState.linkCallerReply c rid Z = .ok ((), Z')) :
    Z'.objects.noResizeDue := by
  unfold SystemState.linkCallerReply at h
  cases hL : SystemState.linkReply rid c Z with
  | error e => rw [hL] at h; cases h
  | ok p =>
    obtain ⟨⟨⟩, Za⟩ := p
    rw [hL] at h
    have hNo1 := linkReply_noResizeDue Z Za rid c hNo hL
    dsimp only at h
    cases hT : Za.getTcb? c with
    | none => rw [hT] at h; cases h
    | some tcb =>
      rw [hT] at h
      dsimp only at h
      split at h
      · exact storeObject_present_noResizeDue Za Z' _ _ (.tcb _) ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT)
          hNo1 (storeLeavesIndexAndTypes_tcb_of_getTcb? hT) h
      · cases h

theorem recordReplyStasher_answer (Z : SystemState) (code : Nat) (t : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).recordReplyStasher code t =
      (Z.recordReplyStasher code t).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  unfold SystemState.recordReplyStasher
  rcases code with _ | k
  · rfl
  · dsimp only
    rw [getReply?_answer]
    cases hR : Z.getReply? ⟨k⟩ with
    | none => rfl
    | some x =>
      dsimp only
      rw [storeObject_answer r ρ μ κ Z _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hNo
          (storeLeaves_reply hR _) (.inr ⟨rfl, rfl⟩), storeObject_eq_of_leaves (storeLeaves_reply hR _)]
      rfl

theorem recordReplyStasher_noResizeDue (Z : SystemState) (code : Nat) (t : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) : (Z.recordReplyStasher code t).objects.noResizeDue := by
  unfold SystemState.recordReplyStasher
  rcases code with _ | k
  · exact hNo
  · dsimp only
    cases hR : Z.getReply? ⟨k⟩ with
    | none => exact hNo
    | some x =>
      dsimp only
      rw [storeObject_eq_of_leaves (storeLeaves_reply hR _)]
      exact insert_present_noResizeDue Z _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hNo

theorem wakeThread_answer (Z : SystemState) (t : SeLe4n.ThreadId) (ec : CoreId)
    (hNo : Z.objects.noResizeDue) :
    wakeThread (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) t ec =
      ((wakeThread Z t ec).1.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ), (wakeThread Z t ec).2) := by
  unfold wakeThread
  dsimp only
  rw [determineTargetCore_answer, enqueueRunnableOnCore_answer r ρ μ id κ Z _ t hNo]
  rcases getTcb?_answer_cases r ρ μ id κ Z t with h | ⟨_, h⟩ <;> rw [h]
  cases Z.getTcb? t <;> rfl

theorem storeTcbQueueLinks_noResizeDue' (Z Z' : SystemState) (t : SeLe4n.ThreadId)
    (p : Option SeLe4n.ThreadId) (pp : Option QueuePPrev) (n : Option SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) (h : storeTcbQueueLinks Z t p pp n = .ok Z') : Z'.objects.noResizeDue :=
  modifyTcb_noResizeDue Z Z' t _ hNo h

/-- **The queue append commutes with the answer** — the answered thread may be
the queue's tail, whose successor link the append writes. -/
theorem endpointQueueEnqueue_answer (Z : SystemState) (k : SeLe4n.ObjId) (isRecv : Bool)
    (t : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) :
    endpointQueueEnqueue k isRecv t (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      (endpointQueueEnqueue k isRecv t Z).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold endpointQueueEnqueue
  cases hO : Z.getObject? k with
  | none =>
    have : (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getObject? k = none := by
      have := getObject?_isSome_answer r ρ μ κ Z k; rw [hO] at this
      exact Option.not_isSome_iff_eq_none.mp (by simpa using this)
    rw [this]; rfl
  | some o =>
    cases o with
    | endpoint ep =>
      rw [getObject?_answer_endpoint r ρ μ id κ Z k ep hO]
      have hk : Z.objects[k]? = some (.endpoint ep) := hO
      have hL : ∀ e : Endpoint, storeLeavesIndexAndTypes Z k (KernelObject.endpoint e).objectType = true :=
        fun e => by unfold storeLeavesIndexAndTypes storeKeepsKind; rw [hk]; rfl
      have hNoE : ∀ e : Endpoint,
          ({ Z with objects := Z.objects.insert k (.endpoint e) } : SystemState).objects.noResizeDue :=
        fun e => insert_present_noResizeDue Z k _ _ hk hNo
      dsimp only
      rw [lookupTcb_answer]
      have hT : ∀ (x : Option TCB), (if r = t then x.map (TCB.withAnswerSlots ρ μ id κ) else x) = none ↔ x = none := by
        intro x; split <;> cases x <;> simp
      cases hLt : lookupTcb Z t with
      | none => simp only [Option.map_none, ite_self]; rfl
      | some tcb =>
        have hEq : (if r = t then (some tcb).map (TCB.withAnswerSlots ρ μ id κ) else some tcb) =
            some (if r = t then TCB.withAnswerSlots ρ μ id κ tcb else tcb) := by split <;> rfl
        rw [hEq]
        dsimp only
        have hI : (if r = t then TCB.withAnswerSlots ρ μ id κ tcb else tcb).ipcState = tcb.ipcState := by
          split <;> rfl
        have hQ : (if r = t then TCB.withAnswerSlots ρ μ id κ tcb else tcb).queuePPrev = tcb.queuePPrev ∧
            (if r = t then TCB.withAnswerSlots ρ μ id κ tcb else tcb).queuePrev = tcb.queuePrev ∧
            (if r = t then TCB.withAnswerSlots ρ μ id κ tcb else tcb).queueNext = tcb.queueNext := by
          split <;> exact ⟨rfl, rfl, rfl⟩
        simp only [hI, hQ.1, hQ.2.1, hQ.2.2]
        split
        · rfl
        · split
          · rfl
          · split
            · rw [storeObject_mapTcbInPlace_of_fixed r Z k _ _ hk hNo rfl rfl (hL _),
                storeObject_eq_of_leaves (hL _)]
              exact storeTcbQueueLinks_answer r ρ μ id κ _ t _ _ _ (hNoE _)
            · rename_i tailTid _
              rw [lookupTcb_answer]
              cases hTl : lookupTcb Z tailTid with
              | none => simp only [Option.map_none, ite_self]; rfl
              | some tl =>
                have hEq2 : (if r = tailTid then (some tl).map (TCB.withAnswerSlots ρ μ id κ) else some tl) =
                    some (if r = tailTid then TCB.withAnswerSlots ρ μ id κ tl else tl) := by split <;> rfl
                rw [hEq2]
                dsimp only
                have hQ2 : (if r = tailTid then TCB.withAnswerSlots ρ μ id κ tl else tl).queuePPrev = tl.queuePPrev ∧
                    (if r = tailTid then TCB.withAnswerSlots ρ μ id κ tl else tl).queuePrev = tl.queuePrev := by
                  split <;> exact ⟨rfl, rfl⟩
                rw [hQ2.1, hQ2.2, storeObject_mapTcbInPlace_of_fixed r Z k _ _ hk hNo rfl rfl (hL _),
                  storeObject_eq_of_leaves (hL _)]
                dsimp only
                rw [storeTcbQueueLinks_answer r ρ μ id κ _ tailTid _ _ _ (hNoE _)]
                cases hS : storeTcbQueueLinks { Z with objects := Z.objects.insert k (.endpoint _) } tailTid
                    tl.queuePrev tl.queuePPrev (some t) with
                | error e => rfl
                | ok Zb =>
                  exact storeTcbQueueLinks_answer r ρ μ id κ Zb t _ _ _
                    (storeTcbQueueLinks_noResizeDue' _ _ _ _ _ _ (hNoE _) hS)
    | _ =>
      unfold SystemState.getObject? at hO ⊢
      rw [SystemState.objects_mapTcbInPlace, hO]
      by_cases hx : (r.toObjId == k) = true <;>
        simp only [hx, if_true, if_false, Option.map_some, Bool.false_eq_true] <;> rfl

theorem endpointQueueEnqueue_noResizeDue (Z Z' : SystemState) (k : SeLe4n.ObjId) (isRecv : Bool)
    (t : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue)
    (h : endpointQueueEnqueue k isRecv t Z = .ok Z') : Z'.objects.noResizeDue := by
  unfold endpointQueueEnqueue at h
  cases hO : Z.getObject? k with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    cases o with
    | endpoint ep =>
      have hk : Z.objects[k]? = some (.endpoint ep) := hO
      have hL : ∀ e : Endpoint, storeLeavesIndexAndTypes Z k (KernelObject.endpoint e).objectType = true :=
        fun e => by unfold storeLeavesIndexAndTypes storeKeepsKind; rw [hk]; rfl
      have hNoE : ∀ e : Endpoint,
          ({ Z with objects := Z.objects.insert k (.endpoint e) } : SystemState).objects.noResizeDue :=
        fun e => insert_present_noResizeDue Z k _ _ hk hNo
      dsimp only at h
      cases hLt : lookupTcb Z t with
      | none => rw [hLt] at h; cases h
      | some tcb =>
        rw [hLt] at h
        dsimp only at h
        split at h
        · cases h
        · split at h
          · cases h
          · split at h
            · rw [storeObject_eq_of_leaves (hL _)] at h
              exact storeTcbQueueLinks_noResizeDue' _ _ _ _ _ _ (hNoE _) h
            · split at h
              · cases h
              · rw [storeObject_eq_of_leaves (hL _)] at h
                dsimp only at h
                split at h
                · cases h
                · rename_i Zb hS
                  exact storeTcbQueueLinks_noResizeDue' _ _ _ _ _ _
                    (storeTcbQueueLinks_noResizeDue' _ _ _ _ _ _ (hNoE _) hS) h
    | _ => cases h

theorem endpointQueuePopHead_noResizeDue (Z : SystemState) (k : SeLe4n.ObjId) (isRecv : Bool)
    (t : SeLe4n.ThreadId) (tcb : TCB) (Z' : SystemState) (hNo : Z.objects.noResizeDue)
    (h : endpointQueuePopHead k isRecv Z = .ok (t, tcb, Z')) : Z'.objects.noResizeDue := by
  unfold endpointQueuePopHead at h
  cases hO : Z.getObject? k with
  | none => rw [hO] at h; cases h
  | some o =>
    rw [hO] at h
    cases o with
    | endpoint ep =>
      have hk : Z.objects[k]? = some (.endpoint ep) := hO
      have hL : ∀ e : Endpoint, storeLeavesIndexAndTypes Z k (KernelObject.endpoint e).objectType = true :=
        fun e => by unfold storeLeavesIndexAndTypes storeKeepsKind; rw [hk]; rfl
      dsimp only at h
      split at h
      · cases h
      · split at h
        · cases h
        · rw [storeObject_eq_of_leaves (hL _)] at h
          have hNo1 := fun e : Endpoint => insert_present_noResizeDue Z k _ (.endpoint e) hk hNo
          dsimp only at h
          split at h
          · cases h
          · rename_i Zb hZb
            split at h
            · cases h
            · rename_i Zc hZc
              cases h
              refine storeTcbQueueLinks_noResizeDue' _ _ _ _ _ _ ?_ hZc
              split at hZb
              · cases hZb; exact hNo1 _
              · split at hZb
                · cases hZb
                · exact storeTcbQueueLinks_noResizeDue' _ _ _ _ _ _ (hNo1 _) hZb
    | _ => cases h


/-- **A TCB store over a thread read through the answer**: the stored TCB is
the read one rewritten by `f`, so at the answered thread itself the store
commutes with the answer when `f` does. -/
theorem storeObject_tcb_answer (Z : SystemState) (x : SeLe4n.ThreadId) (t : TCB) (f : TCB → TCB)
    (hT : Z.getTcb? x = some t) (hNo : Z.objects.noResizeDue)
    (hc : x = r → ∀ y, f (TCB.withAnswerSlots ρ μ id κ y) = TCB.withAnswerSlots ρ μ id κ (f y)) :
    storeObject x.toObjId (.tcb (f (if r = x then TCB.withAnswerSlots ρ μ id κ t else t)))
        (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      mapStepState r (TCB.withAnswerSlots ρ μ id κ) (storeObject x.toObjId (.tcb (f t)) Z) := by
  have hk : Z.objects[x.toObjId]? = some (.tcb t) := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
  by_cases hx : r = x
  · subst hx
    rw [if_pos rfl, hc rfl t]
    have hT' : (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getTcb? r =
        some (TCB.withAnswerSlots ρ μ id κ t) := by
      rw [SystemState.getTcb?_mapTcbInPlace, if_pos rfl, hT]; rfl
    rw [storeObject_eq_of_leaves (storeLeavesIndexAndTypes_tcb_of_getTcb? hT'),
      storeObject_eq_of_leaves (storeLeavesIndexAndTypes_tcb_of_getTcb? hT)]
    simp only [mapStepState, Except.ok.injEq, Prod.mk.injEq, true_and]
    have hg : Z.objects.get? r.toObjId = some (.tcb t) := by
      simpa only [RHTable_getElem?_eq_get?] using hk
    have hNo' : (Z.objects.mapValueAt r.toObjId (KernelObject.mapTcb (TCB.withAnswerSlots ρ μ id κ))).noResizeDue :=
      (RHTable.noResizeDue_mapValueAt _ _ _).mpr hNo
    have hg' : (Z.objects.mapValueAt r.toObjId (KernelObject.mapTcb (TCB.withAnswerSlots ρ μ id κ))).get? r.toObjId =
        some (.tcb (TCB.withAnswerSlots ρ μ id κ t)) := by
      rw [RHTable.get?_mapValueAt, hg]; simp; rfl
    unfold SystemState.mapTcbInPlace
    dsimp only
    rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? hNo' hg'),
      RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? hNo hg),
      RHTable.mapValueAt_mapValueAt, RHTable.mapValueAt_mapValueAt]
    rfl
  · rw [if_neg hx]
    exact storeObject_answer r ρ μ κ Z _ _ _ hk hNo (storeLeavesIndexAndTypes_tcb_of_getTcb? hT)
      (.inl (fun e => hx (SeLe4n.ThreadId.toObjId_injective _ _ e).symm))

/-- The stasher record writes a Reply only: on a table with no resize due every
thread reads as it was. -/
theorem recordReplyStasher_getTcb?_of_noResizeDue (Z : SystemState) (code : Nat) (recv t : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) :
    (Z.recordReplyStasher code recv).getTcb? t = Z.getTcb? t := by
  unfold SystemState.recordReplyStasher
  rcases code with _ | k
  · rfl
  · dsimp only
    cases hR : Z.getReply? ⟨k⟩ with
    | none => rfl
    | some x =>
      dsimp only
      have hk := (SystemState.getReply?_eq_some_iff _ _ _).mp hR
      have hg : Z.objects.get? (⟨k⟩ : SeLe4n.ReplyId).toObjId = some (.reply x) := by
        simpa only [RHTable_getElem?_eq_get?] using hk
      rw [storeObject_eq_of_leaves (storeLeaves_reply hR _)]
      dsimp only
      unfold SystemState.getTcb?
      simp only [RHTable_getElem?_eq_get?]
      rw [RHTable.insert_eq_mapValueAt _ (RHTable.findsInPlace_of_get? hNo hg), RHTable.get?_mapValueAt]
      by_cases hEq : (⟨k⟩ : SeLe4n.ReplyId).toObjId = t.toObjId
      · rw [if_pos (by simp [hEq]), ← hEq, hg]; rfl
      · rw [if_neg (by simp [hEq])]

end Stores

/-! ## The scheduler marks a donation makes -/

section Marks

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (κ : Nat → Nat)

theorem hasSufficientBudget_answer (Z : SystemState) (t : TCB) (b : Prop) [Decidable b] :
    hasSufficientBudget (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ))
        (if b then TCB.withAnswerSlots ρ μ id κ t else t) = hasSufficientBudget Z t := by
  have hB : (if b then TCB.withAnswerSlots ρ μ id κ t else t).schedContextBinding = t.schedContextBinding := by
    split <;> rfl
  unfold hasSufficientBudget
  rw [hB]
  simp only [getSchedContext?_answer]

theorem markReschedulePendingWhere_answer (Z : SystemState) (p : CoreId → Bool) (cs : List CoreId) :
    markReschedulePendingWhere (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) p cs =
      (markReschedulePendingWhere Z p cs).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  induction cs generalizing Z with
  | nil => rfl
  | cons c cs ih =>
    simp only [markReschedulePendingWhere]
    split
    · exact ih (Z.markReschedulePendingOnCore c)
    · exact ih _

theorem markCandidacyGainFor_answer (Z : SystemState) (tid : SeLe4n.ThreadId) (b : Bool) :
    markCandidacyGainFor (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tid b =
      (markCandidacyGainFor Z tid b).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  unfold markCandidacyGainFor
  split
  · rfl
  · rw [SystemState.getTcb?_mapTcbInPlace]
    by_cases h : r = tid
    · rw [if_pos h]
      cases Z.getTcb? tid with
      | none => rfl
      | some t =>
        have := hasSufficientBudget_answer r ρ μ κ Z t True
        simp only [if_true] at this
        simp only [Option.map_some, this]
        split
        · exact markKeyFlagsOver_answer r ρ μ id κ Z tid _ _ _
        · rfl
    · rw [if_neg h]
      cases Z.getTcb? tid with
      | none => rfl
      | some t =>
        have := hasSufficientBudget_answer r ρ μ κ Z t False
        simp only [if_false] at this
        simp only [this]
        split
        · exact markKeyFlagsOver_answer r ρ μ id κ Z tid _ _ _
        · rfl

/-- The key hook over a pre-state and a post-state both answered. -/
theorem markKeyChangeFrom_answer (pre post : SystemState) (tid : SeLe4n.ThreadId) :
    markKeyChangeFrom (pre.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ))
        (post.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tid =
      (markKeyChangeFrom pre post tid).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  cases hT : pre.getTcb? tid with
  | none =>
    have hT' : (pre.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getTcb? tid = none := by
      rw [SystemState.getTcb?_mapTcbInPlace, hT]; split <;> rfl
    unfold markKeyChangeFrom
    rw [hT, hT']
    dsimp only
    simp only [queuedOn_answer, SystemState.mapTcbInPlace_scheduler]
    exact markReschedulePendingWhere_answer r ρ μ κ post _ _
  | some t =>
    have hT' : (pre.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getTcb? tid =
        some (if r = tid then TCB.withAnswerSlots ρ μ id κ t else t) := by
      rw [SystemState.getTcb?_mapTcbInPlace, hT]; split <;> rfl
    rw [markKeyChangeFrom_of_getTcb _ _ tid _ hT', markKeyChangeFrom_of_getTcb _ _ tid _ hT,
      hasSufficientBudget_answer, markCandidacyGainFor_answer]
    have hP : (if r = tid then TCB.withAnswerSlots ρ μ id κ t else t).boostedPriority = t.boostedPriority ∧
        (if r = tid then TCB.withAnswerSlots ρ μ id κ t else t).deadline = t.deadline ∧
        (if r = tid then TCB.withAnswerSlots ρ μ id κ t else t).domain = t.domain := by
      split <;> exact ⟨rfl, rfl, rfl⟩
    rw [hP.1, hP.2.1, hP.2.2, markKeyChangeParts_answer]

end Marks

/-! ## The donation return's reads -/

section DonationReads

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (κ : Nat → Nat)

/-- A read of one thread that cannot see its answer slots. -/
theorem getTcb?_read_answer {α : Type} (Z : SystemState) (x : SeLe4n.ThreadId) (F : Option TCB → α)
    (hF : ∀ t, F (some (TCB.withAnswerSlots ρ μ id κ t)) = F (some t)) :
    F ((Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getTcb? x) = F (Z.getTcb? x) := by
  rcases getTcb?_answer_cases r ρ μ id κ Z x with h | ⟨_, h⟩ <;> rw [h]
  cases Z.getTcb? x with
  | none => rfl
  | some t => exact hF t

theorem lookupTcb_read_answer {α : Type} (Z : SystemState) (x : SeLe4n.ThreadId) (F : Option TCB → α)
    (hF : ∀ t, F (some (TCB.withAnswerSlots ρ μ id κ t)) = F (some t)) :
    F (lookupTcb (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) x) = F (lookupTcb Z x) := by
  rw [lookupTcb_answer]
  split
  · cases lookupTcb Z x with
    | none => rfl
    | some t => exact hF t
  · rfl

theorem donationRecipientAcceptable_answer (Z : SystemState) (x : SeLe4n.ThreadId) :
    donationRecipientAcceptable (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) x =
      donationRecipientAcceptable Z x :=
  lookupTcb_read_answer r ρ μ κ Z x (fun o => match o with
    | none => true | some tcb => tcb.schedContextBinding == SchedContextBinding.unbound) (fun _ => rfl)

theorem outerCallerAcceptable_answer (Z : SystemState) (s o : SeLe4n.ThreadId)
    (n : Option SeLe4n.ThreadId) :
    outerCallerAcceptable (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) s o n =
      outerCallerAcceptable Z s o n := by
  unfold outerCallerAcceptable
  rcases n with _ | outer
  · rfl
  · dsimp only
    congr 1
    exact getTcb?_read_answer r ρ μ κ Z outer (fun x => match x with
      | none => false
      | some outerTcb => !outerTcb.schedContextBinding.isDonated &&
          match outerTcb.ipcState with
          | ThreadIpcState.blockedOnReply _ _ => true
          | _ => false) (fun _ => rfl)

theorem heldPopOuter?_answer (Z : SystemState) (h : SeLe4n.ThreadId) (n : Option SeLe4n.ThreadId) :
    heldPopOuter? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) h n = heldPopOuter? Z h n :=
  getTcb?_read_answer r ρ μ κ Z h (fun x => match x with
    | some ht => heldPopOwner? ht.schedContextBinding n | none => n) (fun _ => rfl)

theorem donationHeadOf?_answer (Z : SystemState) (scId : SeLe4n.SchedContextId) (sc : SchedContext) :
    donationHeadOf? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) scId sc = donationHeadOf? Z scId sc := by
  unfold donationHeadOf?; simp only [getReply?_answer]

theorem replyStackOuterCaller?_answer (Z : SystemState) (scId : SeLe4n.SchedContextId) :
    replyStackOuterCaller? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) scId =
      replyStackOuterCaller? Z scId := by
  unfold replyStackOuterCaller?; simp only [getSchedContext?_answer, donationHeadOf?_answer, getReply?_answer]

theorem preReceiveDonation?_answer (Z : SystemState) (x : SeLe4n.ThreadId) :
    preReceiveDonation? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) x = preReceiveDonation? Z x :=
  lookupTcb_read_answer r ρ μ κ Z x (fun o => match o with
    | some recvTcb => match recvTcb.schedContextBinding with
      | .donated scId originalOwner => some (scId, originalOwner)
      | _ => none
    | none => none) (fun _ => rfl)

theorem replenishHomeOfSchedContext_answer (Z : SystemState) (scId : SeLe4n.SchedContextId) (c : CoreId) :
    replenishHomeOfSchedContext (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) scId c =
      replenishHomeOfSchedContext Z scId c := by
  unfold replenishHomeOfSchedContext; simp only [getSchedContext?_answer, determineTargetCore_answer]

end DonationReads

/-! ## The donation return's stores -/

section DonationStores

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (κ : Nat → Nat)

theorem storeLeaves_schedContext {Z : SystemState} {k : SeLe4n.SchedContextId} {x : SchedContext}
    (h : Z.getSchedContext? k = some x) (y : SchedContext) :
    storeLeavesIndexAndTypes Z k.toObjId (KernelObject.schedContext y).objectType = true := by
  have hk : Z.objects[k.toObjId]? = some (.schedContext x) := by
    unfold SystemState.getSchedContext? at h; split at h <;> simp_all
  unfold storeLeavesIndexAndTypes storeKeepsKind
  rw [hk]; rfl

theorem objects_of_getSchedContext? {Z : SystemState} {k : SeLe4n.SchedContextId} {x : SchedContext}
    (h : Z.getSchedContext? k = some x) : Z.objects[k.toObjId]? = some (.schedContext x) := by
  unfold SystemState.getSchedContext? at h; split at h <;> simp_all

/-- A reply-record rewrite at a present Reply, through the answer. -/
theorem replyStore_answer (Z : SystemState) (rid : SeLe4n.ReplyId) (g : Reply → Reply)
    (hNo : Z.objects.noResizeDue) :
    (match (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).getReply? rid with
      | some x => match storeObject rid.toObjId (.reply (g x)) (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) with
        | Except.error e => Except.error e
        | Except.ok ((), st') => Except.ok st'
      | none => (Except.error KernelError.objectNotFound : Except KernelError SystemState)) =
    (match Z.getReply? rid with
      | some x => match storeObject rid.toObjId (.reply (g x)) Z with
        | Except.error e => Except.error e
        | Except.ok ((), st') => Except.ok st'
      | none => Except.error KernelError.objectNotFound).map
        (fun (s : SystemState) => s.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  rw [getReply?_answer]
  cases hR : Z.getReply? rid with
  | none => rfl
  | some x =>
    dsimp only
    rw [storeObject_answer r ρ μ κ Z _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hNo
        (storeLeaves_reply hR _) (.inr ⟨rfl, rfl⟩), storeObject_eq_of_leaves (storeLeaves_reply hR _)]
    rfl

theorem replyStore_noResizeDue (Z Z' : SystemState) (rid : SeLe4n.ReplyId) (g : Reply → Reply)
    (hNo : Z.objects.noResizeDue)
    (h : (match Z.getReply? rid with
      | some x => match storeObject rid.toObjId (.reply (g x)) Z with
        | Except.error e => Except.error e
        | Except.ok ((), st') => Except.ok st'
      | none => (Except.error KernelError.objectNotFound : Except KernelError SystemState)) = .ok Z') :
    Z'.objects.noResizeDue := by
  cases hR : Z.getReply? rid with
  | none => rw [hR] at h; cases h
  | some x =>
    rw [hR] at h
    dsimp only at h
    rw [storeObject_eq_of_leaves (storeLeaves_reply hR _)] at h
    cases h
    exact insert_present_noResizeDue Z _ _ _ ((SystemState.getReply?_eq_some_iff _ _ _).mp hR) hNo

theorem storeDonationHeadClear_answer (Z : SystemState) (rid? : Option SeLe4n.ReplyId)
    (hNo : Z.objects.noResizeDue) :
    storeDonationHeadClear rid? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      (storeDonationHeadClear rid? Z).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  rcases rid? with _ | rid
  · rfl
  · exact replyStore_answer r ρ μ κ Z rid _ hNo

theorem storeDonationHeadClear_noResizeDue (Z Z' : SystemState) (rid? : Option SeLe4n.ReplyId)
    (hNo : Z.objects.noResizeDue) (h : storeDonationHeadClear rid? Z = .ok Z') : Z'.objects.noResizeDue := by
  rcases rid? with _ | rid
  · cases h; exact hNo
  · exact replyStore_noResizeDue Z Z' rid _ hNo h

theorem storeReplyReHead_answer (Z : SystemState) (scId : SeLe4n.SchedContextId)
    (rid? : Option SeLe4n.ReplyId) (hNo : Z.objects.noResizeDue) :
    storeReplyReHead scId rid? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      (storeReplyReHead scId rid? Z).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  rcases rid? with _ | rid
  · rfl
  · exact replyStore_answer r ρ μ κ Z rid _ hNo

theorem storeReplyReHead_noResizeDue (Z Z' : SystemState) (scId : SeLe4n.SchedContextId)
    (rid? : Option SeLe4n.ReplyId)
    (hNo : Z.objects.noResizeDue) (h : storeReplyReHead scId rid? Z = .ok Z') : Z'.objects.noResizeDue := by
  rcases rid? with _ | rid
  · cases h; exact hNo
  · exact replyStore_noResizeDue Z Z' rid _ hNo h

theorem storeDonationHeadPop_answer (Z : SystemState) (scId : SeLe4n.SchedContextId)
    (head? : Option (SeLe4n.ReplyId × Reply)) (hNo : Z.objects.noResizeDue) :
    storeDonationHeadPop scId head? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      (storeDonationHeadPop scId head? Z).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  rcases head? with _ | ⟨rid, x⟩
  · rfl
  · simp only [storeDonationHeadPop]
    rw [storeDonationHeadClear_answer r ρ μ κ Z _ hNo]
    cases h : storeDonationHeadClear (some rid) Z with
    | error e => rfl
    | ok Za => exact storeReplyReHead_answer r ρ μ κ Za scId _ (storeDonationHeadClear_noResizeDue _ _ _ hNo h)

theorem storeDonationHeadPop_noResizeDue (Z Z' : SystemState) (scId : SeLe4n.SchedContextId)
    (head? : Option (SeLe4n.ReplyId × Reply)) (hNo : Z.objects.noResizeDue)
    (h : storeDonationHeadPop scId head? Z = .ok Z') : Z'.objects.noResizeDue := by
  rcases head? with _ | ⟨rid, x⟩
  · cases h; exact hNo
  · simp only [storeDonationHeadPop] at h
    cases h1 : storeDonationHeadClear (some rid) Z with
    | error e => rw [h1] at h; cases h
    | ok Za =>
      rw [h1] at h
      exact storeReplyReHead_noResizeDue Za Z' scId _ (storeDonationHeadClear_noResizeDue _ _ _ hNo h1) h

theorem lookupTcb_answer' (Z : SystemState) (x : SeLe4n.ThreadId) :
    lookupTcb (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) x =
      (lookupTcb Z x).map (fun t => if r = x then TCB.withAnswerSlots ρ μ id κ t else t) := by
  rw [lookupTcb_answer]
  by_cases h : r = x
  · rw [if_pos h]; cases lookupTcb Z x <;> simp [h]
  · rw [if_neg h]; cases lookupTcb Z x <;> simp [h]

theorem keepDonatedSchedContext_answer (Z : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (n : Option SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) :
    keepDonatedSchedContext (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) holder scId n =
      (keepDonatedSchedContext Z holder scId n).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold keepDonatedSchedContext
  rw [getSchedContext?_answer]
  cases hS : Z.getSchedContext? scId with
  | none => rfl
  | some sc =>
    dsimp only
    rw [outerCallerAcceptable_answer, heldPopOuter?_answer, donationHeadOf?_answer]
    split
    · rfl
    · split
      · rfl
      · cases hH : donationHeadOf? Z scId sc with
        | error e => rfl
        | ok head? =>
          dsimp only
          rw [storeObject_answer r ρ μ κ Z _ _ _ (objects_of_getSchedContext? hS) hNo
              (storeLeaves_schedContext hS _) (.inr ⟨rfl, rfl⟩), storeObject_eq_of_leaves (storeLeaves_schedContext hS _)]
          have hNo1 := insert_present_noResizeDue Z _ _
            (.schedContext (donationSeverSchedContext sc (head?.bind fun p => p.snd.prev)))
            (objects_of_getSchedContext? hS) hNo
          dsimp only [mapStepState]
          rw [storeDonationHeadPop_answer r ρ μ κ _ scId head? hNo1]
          cases hP : storeDonationHeadPop scId head? _ with
          | error e => rfl
          | ok Zb =>
            have hNo2 := storeDonationHeadPop_noResizeDue _ _ scId head? hNo1 hP
            dsimp only [Except.map]
            rw [lookupTcb_answer']
            cases hL : lookupTcb Zb holder with
            | none => rfl
            | some ht =>
              dsimp only [Option.map]
              have hB : (if r = holder then TCB.withAnswerSlots ρ μ id κ ht else ht).schedContextBinding =
                  ht.schedContextBinding := by split <;> rfl
              rw [hB]
              split
              · rfl
              · have := storeObject_tcb_answer r ρ μ κ Zb holder ht
                  (fun y => { y with
                    scBindingScCode := (donationReturnBinding scId (heldPopOwner? ht.schedContextBinding n)).scCode,
                    scBindingOwnerCode := (donationReturnBinding scId (heldPopOwner? ht.schedContextBinding n)).ownerCode })
                  (getTcb?_of_lookupTcb _ _ _ hL) hNo2 (fun _ _ => rfl)
                simp only [] at this
                rw [this]
                cases storeObject holder.toObjId _ Zb with
                | error e => rfl
                | ok p => obtain ⟨⟨⟩, Zc⟩ := p; rfl

theorem returnDonatedSchedContext_answer (Z : SystemState) (server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (n : Option SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) :
    returnDonatedSchedContext (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) server scId owner n =
      (returnDonatedSchedContext Z server scId owner n).map
        (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold returnDonatedSchedContext
  rw [getSchedContext?_answer]
  cases hS : Z.getSchedContext? scId with
  | none => rfl
  | some sc =>
    dsimp only
    rw [outerCallerAcceptable_answer, donationRecipientAcceptable_answer, donationHeadOf?_answer]
    split
    · rfl
    · split
      · rfl
      · split
        · rfl
        · cases hH : donationHeadOf? Z scId sc with
          | error e => rfl
          | ok head? =>
            dsimp only
            rw [storeObject_answer r ρ μ κ Z _ _ _ (objects_of_getSchedContext? hS) hNo
                (storeLeaves_schedContext hS _) (.inr ⟨rfl, rfl⟩),
              storeObject_eq_of_leaves (storeLeaves_schedContext hS _)]
            have hNo1 := insert_present_noResizeDue Z _ _
              (.schedContext (donationReturnSchedContext sc owner (head?.bind fun p => p.snd.prev)))
              (objects_of_getSchedContext? hS) hNo
            dsimp only [mapStepState]
            rw [storeDonationHeadPop_answer r ρ μ κ _ scId head? hNo1]
            cases hP : storeDonationHeadPop scId head? _ with
            | error e => rfl
            | ok Zb =>
              have hNo2 := storeDonationHeadPop_noResizeDue _ _ scId head? hNo1 hP
              dsimp only [Except.map]
              rw [lookupTcb_answer']
              cases hL : lookupTcb Zb owner with
              | none => rfl
              | some ct =>
                dsimp only [Option.map]
                have h1 := storeObject_tcb_answer r ρ μ κ Zb owner ct
                  (fun y => { y with
                    scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (donationReturnBinding scId n),
                    scBindingOwnerCode := SeLe4n.Kernel.SchedContextBinding.ownerCode (donationReturnBinding scId n) })
                  (getTcb?_of_lookupTcb _ _ _ hL) hNo2 (fun _ _ => rfl)
                simp only [] at h1
                rw [h1]
                cases hC : storeObject owner.toObjId _ Zb with
                | error e => rfl
                | ok p =>
                  obtain ⟨⟨⟩, Zc⟩ := p
                  have hNo3 := storeObject_present_noResizeDue Zb Zc _ _ (.tcb _)
                    ((SystemState.getTcb?_eq_some_iff _ _ _).mp (getTcb?_of_lookupTcb _ _ _ hL)) hNo2
                    (storeLeavesIndexAndTypes_tcb_of_getTcb? (getTcb?_of_lookupTcb _ _ _ hL)) hC
                  dsimp only [mapStepState]
                  rw [lookupTcb_answer']
                  cases hL3 : lookupTcb Zc server with
                  | none => rfl
                  | some st' =>
                    dsimp only [Option.map]
                    have h2 := storeObject_tcb_answer r ρ μ κ Zc server st'
                      (fun y => { y with scBindingScCode := 0, scBindingOwnerCode := 0 })
                      (getTcb?_of_lookupTcb _ _ _ hL3) hNo3 (fun _ _ => rfl)
                    simp only [] at h2
                    rw [h2]
                    cases storeObject server.toObjId _ Zc with
                    | error e => rfl
                    | ok p =>
                      obtain ⟨⟨⟩, Zd⟩ := p
                      dsimp only [mapStepState, Except.map]
                      rw [markKeyChangeFrom_answer, markKeyChangeFrom_answer]

theorem tcbStore_noResizeDue (Z Z' : SystemState) (x : SeLe4n.ThreadId) (t v : TCB)
    (hL : lookupTcb Z x = some t) (hNo : Z.objects.noResizeDue)
    (h : storeObject x.toObjId (.tcb v) Z = .ok ((), Z')) : Z'.objects.noResizeDue :=
  storeObject_present_noResizeDue Z Z' _ _ (.tcb _)
    ((SystemState.getTcb?_eq_some_iff _ _ _).mp (getTcb?_of_lookupTcb _ _ _ hL)) hNo
    (storeLeavesIndexAndTypes_tcb_of_getTcb? (getTcb?_of_lookupTcb _ _ _ hL)) h

theorem keepDonatedSchedContext_noResizeDue (Z Z' : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (n : Option SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue)
    (h : keepDonatedSchedContext Z holder scId n = .ok Z') : Z'.objects.noResizeDue := by
  unfold keepDonatedSchedContext at h
  cases hS : Z.getSchedContext? scId with
  | none => rw [hS] at h; cases h
  | some sc =>
    rw [hS] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · cases hH : donationHeadOf? Z scId sc with
        | error e => rw [hH] at h; cases h
        | ok head? =>
          rw [hH] at h
          dsimp only at h
          rw [storeObject_eq_of_leaves (storeLeaves_schedContext hS _)] at h
          have hNo1 := insert_present_noResizeDue Z _ _
            (.schedContext (donationSeverSchedContext sc (head?.bind fun p => p.snd.prev)))
            (objects_of_getSchedContext? hS) hNo
          dsimp only at h
          cases hP : storeDonationHeadPop scId head? _ with
          | error e => rw [hP] at h; cases h
          | ok Zb =>
            rw [hP] at h
            have hNo2 := storeDonationHeadPop_noResizeDue _ _ scId head? hNo1 hP
            dsimp only at h
            cases hL : lookupTcb Zb holder with
            | none => rw [hL] at h; cases h
            | some ht =>
              rw [hL] at h
              dsimp only at h
              split at h
              · cases h
              · cases hC : storeObject holder.toObjId _ Zb with
                | error e => rw [hC] at h; cases h
                | ok p =>
                  obtain ⟨⟨⟩, Zc⟩ := p
                  rw [hC] at h
                  cases h
                  exact tcbStore_noResizeDue _ _ _ _ _ hL hNo2 hC

theorem returnDonatedSchedContext_noResizeDue (Z Z' : SystemState) (server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (n : Option SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue)
    (h : returnDonatedSchedContext Z server scId owner n = .ok Z') : Z'.objects.noResizeDue := by
  unfold returnDonatedSchedContext at h
  cases hS : Z.getSchedContext? scId with
  | none => rw [hS] at h; cases h
  | some sc =>
    rw [hS] at h
    dsimp only at h
    split at h
    · cases h
    · split at h
      · cases h
      · split at h
        · cases h
        · cases hH : donationHeadOf? Z scId sc with
          | error e => rw [hH] at h; cases h
          | ok head? =>
            rw [hH] at h
            dsimp only at h
            rw [storeObject_eq_of_leaves (storeLeaves_schedContext hS _)] at h
            have hNo1 := insert_present_noResizeDue Z _ _
              (.schedContext (donationReturnSchedContext sc owner (head?.bind fun p => p.snd.prev)))
              (objects_of_getSchedContext? hS) hNo
            dsimp only at h
            cases hP : storeDonationHeadPop scId head? _ with
            | error e => rw [hP] at h; cases h
            | ok Zb =>
              rw [hP] at h
              have hNo2 := storeDonationHeadPop_noResizeDue _ _ scId head? hNo1 hP
              dsimp only at h
              cases hL : lookupTcb Zb owner with
              | none => rw [hL] at h; cases h
              | some ct =>
                rw [hL] at h
                dsimp only at h
                cases hC : storeObject owner.toObjId _ Zb with
                | error e => rw [hC] at h; cases h
                | ok p =>
                  obtain ⟨⟨⟩, Zc⟩ := p
                  rw [hC] at h
                  have hNo3 := tcbStore_noResizeDue _ _ _ _ _ hL hNo2 hC
                  dsimp only at h
                  cases hL3 : lookupTcb Zc server with
                  | none => rw [hL3] at h; cases h
                  | some st' =>
                    rw [hL3] at h
                    dsimp only at h
                    cases hC3 : storeObject server.toObjId _ Zc with
                    | error e => rw [hC3] at h; cases h
                    | ok p =>
                      obtain ⟨⟨⟩, Zd⟩ := p
                      rw [hC3] at h
                      cases h
                      show (markKeyChangeFrom _ _ _).objects.noResizeDue
                      rw [markKeyChangeFrom_objects, markKeyChangeFrom_objects]
                      exact tcbStore_noResizeDue _ _ _ _ _ hL3 hNo3 hC3

end DonationStores

/-! ## The context return and the pre-receive cleanup -/

section ReturnAndCleanup

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (κ : Nat → Nat)

theorem modifyObject_answer (Z : SystemState) (x : SeLe4n.ObjId) (F : KernelObject → KernelObject)
    (hNo : Z.objects.noResizeDue)
    (hF : ∀ o, F (KernelObject.mapTcb (TCB.withAnswerSlots ρ μ id κ) o) =
      KernelObject.mapTcb (TCB.withAnswerSlots ρ μ id κ) (F o)) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).modifyObject x F =
      (Z.modifyObject x F).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  rw [SystemState.modifyObject_eq_mapValueAt _ _ _ hNo,
    SystemState.modifyObject_eq_mapValueAt (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) _ _ hNo]
  exact SystemState.mapTcbInPlace_swap_objects Z r _ x F (fun _ => hF)

theorem updateSchedContext_answer (Z : SystemState) (scId : SeLe4n.SchedContextId)
    (f : SchedContext → SchedContext) (hNo : Z.objects.noResizeDue) :
    (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).updateSchedContext scId f =
      (Z.updateSchedContext scId f).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  rw [SystemState.updateSchedContext_eq_impl]
  unfold SystemState.updateSchedContextImpl
  rw [getSchedContext?_answer]
  split
  · exact modifyObject_answer r ρ μ κ Z _ _ hNo (fun o => by cases o <;> rfl)
  · rfl

theorem schedContextReturnLinks_answer (Z : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) (hR : r ≠ tid) :
    schedContextReturnLinks (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) vS tid =
      (schedContextReturnLinks Z vS tid).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  rw [schedContextReturnLinks_eq_impl]
  unfold schedContextReturnLinksImpl
  rw [getSchedContext?_answer, getTcb?_answer_ne r ρ μ κ Z tid (Ne.symm hR)]
  cases Z.getSchedContext? (SeLe4n.SchedContextId.ofObjId vS.val) with
  | none => rfl
  | some _ =>
    cases hT : Z.getTcb? tid with
    | none => rfl
    | some tcb =>
      dsimp only
      have hRun : runningCoreOf? (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tid =
          runningCoreOf? Z tid := rfl
      have hB := hasSufficientBudget_answer r ρ μ κ Z tcb False
      simp only [if_false] at hB
      rw [hB, hRun, updateSchedContext_answer r ρ μ κ _ _ _ hNo,
        updateTcb_answer r ρ μ id κ _ tid _ (updateSchedContext_noResizeDue _ _ _ hNo)
          (fun h => absurd h.symm hR)]
      cases runningCoreOf? Z tid with
      | none => dsimp only; rw [markCandidacyGainFor_answer, markKeyChangeParts_answer]
      | some c =>
        dsimp only
        rw [show ∀ (S : SystemState), (S.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)).markReschedulePendingOnCore c =
            (S.markReschedulePendingOnCore c).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) from fun _ => rfl,
          markCandidacyGainFor_answer, markKeyChangeParts_answer]

theorem schedContextReturnPerform_answer (Z : SystemState) (vS : SeLe4n.ValidObjId)
    (tid : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) (hR : r ≠ tid) :
    schedContextReturnPerform (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) vS tid =
      (schedContextReturnPerform Z vS tid).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  unfold schedContextReturnPerform SchedContextOps.purgeReplenishment
  rw [schedContextReturnLinks_answer r ρ μ κ Z vS tid hNo hR, releaseRemoveAnywhere_mapTcbInPlace]

theorem schedContextReturnAdmitted_answer (Z : SystemState) (vS : SeLe4n.ValidObjId)
    (vT : SeLe4n.ValidThreadId) (hR : r ≠ vT.val) :
    schedContextReturnAdmitted (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) vS vT =
      schedContextReturnAdmitted Z vS vT := by
  unfold schedContextReturnAdmitted
  rw [getSchedContext?_answer, getTcb?_answer_ne r ρ μ κ Z _ (Ne.symm hR)]

/-- **The receive's context return commutes with the answer** to another
thread. -/
theorem receiveReturnSchedContext_answer (blocks : Bool) (Z : SystemState) (tid : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) (hR : r ≠ tid) :
    receiveReturnSchedContext blocks (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tid =
      (receiveReturnSchedContext blocks Z tid).mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ) := by
  unfold receiveReturnSchedContext
  cases blocks with
  | false => rfl
  | true =>
    simp only [↓reduceIte]
    rw [getTcb?_answer_ne r ρ μ κ Z tid (Ne.symm hR)]
    cases Z.getTcb? tid with
    | none => rfl
    | some t =>
      dsimp only
      split
      · rfl
      unfold maybeReturnSchedContext
      rw [getNotification?_answer]
      cases Z.getNotification? _ with
      | none => rfl
      | some ntfn =>
        dsimp only
        cases ntfn.schedContext with
        | none => rfl
        | some s =>
          dsimp only
          split
          · rename_i vS vT _ hT
            have hV : vT.val = tid := by
              unfold SeLe4n.ThreadId.toValid? at hT
              split at hT
              · cases hT
              · cases hT; rfl
            rw [schedContextReturnAdmitted_answer r ρ μ κ Z vS vT (hV ▸ hR)]
            split
            · exact schedContextReturnPerform_answer r ρ μ κ Z vS tid hNo hR
            · rfl
          · rfl

theorem keepDonatedSchedContextResolved_answer (Z : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (hNo : Z.objects.noResizeDue) :
    keepDonatedSchedContextResolved (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) holder scId =
      (keepDonatedSchedContextResolved Z holder scId).map
        (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold keepDonatedSchedContextResolved
  rw [replyStackOuterCaller?_answer]
  cases replyStackOuterCaller? Z scId with
  | error e => rfl
  | ok n => exact keepDonatedSchedContext_answer r ρ μ κ Z holder scId n hNo

theorem returnDonatedSchedContextResolved_answer (Z : SystemState) (server : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) :
    returnDonatedSchedContextResolved (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) server scId owner =
      (returnDonatedSchedContextResolved Z server scId owner).map
        (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold returnDonatedSchedContextResolved
  rw [replyStackOuterCaller?_answer]
  cases replyStackOuterCaller? Z scId with
  | error e => rfl
  | ok n => exact returnDonatedSchedContext_answer r ρ μ κ Z server scId owner n hNo

theorem popHeldReplyHead_answer (Z : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue) :
    popHeldReplyHead (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) holder scId owner =
      (popHeldReplyHead Z holder scId owner).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold popHeldReplyHead
  rw [donationRecipientAcceptable_answer]
  split
  · exact returnDonatedSchedContextResolved_answer r ρ μ κ Z holder scId owner hNo
  · exact keepDonatedSchedContextResolved_answer r ρ μ κ Z holder scId hNo

theorem popHeldReplyHead_noResizeDue (Z Z' : SystemState) (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId) (hNo : Z.objects.noResizeDue)
    (h : popHeldReplyHead Z holder scId owner = .ok Z') : Z'.objects.noResizeDue := by
  unfold popHeldReplyHead returnDonatedSchedContextResolved keepDonatedSchedContextResolved at h
  split at h
  · cases hN : replyStackOuterCaller? Z scId with
    | error e => rw [hN] at h; cases h
    | ok n => rw [hN] at h; exact returnDonatedSchedContext_noResizeDue Z Z' holder scId owner n hNo h
  · cases hN : replyStackOuterCaller? Z scId with
    | error e => rw [hN] at h; cases h
    | ok n => rw [hN] at h; exact keepDonatedSchedContext_noResizeDue Z Z' holder scId n hNo h

theorem cleanupPreReceiveDonationChecked_answer (Z : SystemState) (x : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) :
    cleanupPreReceiveDonationChecked (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) x =
      (cleanupPreReceiveDonationChecked Z x).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold cleanupPreReceiveDonationChecked
  rw [lookupTcb_answer']
  cases lookupTcb Z x with
  | none => rfl
  | some t =>
    dsimp only [Option.map]
    have hB : (if r = x then TCB.withAnswerSlots ρ μ id κ t else t).schedContextBinding =
        t.schedContextBinding := by split <;> rfl
    rw [hB]
    cases t.schedContextBinding with
    | donated scId owner => exact popHeldReplyHead_answer r ρ μ κ Z x scId owner hNo
    | _ => rfl

theorem cleanupPreReceiveDonationChecked_noResizeDue (Z Z' : SystemState) (x : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) (h : cleanupPreReceiveDonationChecked Z x = .ok Z') :
    Z'.objects.noResizeDue := by
  unfold cleanupPreReceiveDonationChecked at h
  cases hL : lookupTcb Z x with
  | none => rw [hL] at h; cases h; exact hNo
  | some t =>
    rw [hL] at h
    dsimp only at h
    split at h
    · exact popHeldReplyHead_noResizeDue Z Z' x _ _ hNo h
    all_goals (cases h; exact hNo)

/-- **The pre-receive cleanup and the migration it owes commute with the
answer**: the answered thread may be the context's original owner or the
outer caller the return settles on, whose binding the return rewrites. -/
theorem cleanupPreReceiveDonationMigrated_answer (Z : SystemState) (x : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) :
    cleanupPreReceiveDonationMigrated (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) x =
      (cleanupPreReceiveDonationMigrated Z x).map (·.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) := by
  unfold cleanupPreReceiveDonationMigrated
  rw [cleanupPreReceiveDonationChecked_answer r ρ μ κ Z x hNo]
  cases cleanupPreReceiveDonationChecked Z x with
  | error e => rfl
  | ok Zc =>
    dsimp only [Except.map]
    unfold preReceiveReturnMigration
    rw [preReceiveDonation?_answer, determineTargetCore_answer]
    split
    · dsimp only
      rw [replenishHomeOfSchedContext_answer, migrateSchedContextReplenishment_mapTcbInPlace]
    · rfl

theorem cleanupPreReceiveDonationMigrated_noResizeDue (Z Z' : SystemState) (x : SeLe4n.ThreadId)
    (hNo : Z.objects.noResizeDue) (h : cleanupPreReceiveDonationMigrated Z x = .ok Z') :
    Z'.objects.noResizeDue := by
  obtain ⟨Zc, hC, rfl⟩ := cleanupPreReceiveDonationMigrated_ok_decompose h
  have hNoC := cleanupPreReceiveDonationChecked_noResizeDue Z Zc x hNo hC
  unfold preReceiveReturnMigration
  split
  · exact migrateSchedContextReplenishment_noResizeDue _ _ _ _ hNoC
  · exact hNoC

end ReturnAndCleanup

/-! ## The receive body, at a queued sender -/

section ReceiveRendezvous

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (κ : Nat → Nat)

/-- **A receive that takes a queued sender commutes with the answer** to a
thread that is neither the receiver nor the sender. -/
theorem endpointReceiveDualOnCore_answer_of_sender (Z : SystemState) (k : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : Option SeLe4n.ReplyId) (ec : CoreId) (ep : Endpoint)
    (s : SeLe4n.ThreadId) (hE : Z.getEndpoint? k = some ep) (hS : ep.sendQ.head = some s)
    (hs : s ≠ r) (ht : tid ≠ r) (hNo : Z.objects.noResizeDue) :
    endpointReceiveDualOnCore k tid rid ec (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      ((endpointReceiveDualOnCore k tid rid ec Z).1.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ),
        (endpointReceiveDualOnCore k tid rid ec Z).2) := by
  have hk : Z.objects[k]? = some (.endpoint ep) := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hE
  unfold endpointReceiveDualOnCore
  rw [getEndpoint?_answer, hE]
  dsimp only
  rw [hS]
  dsimp only
  rw [endpointQueuePopHead_answer r ρ μ id κ Z k false ep hk (by simp [hS, hs]) hNo]
  cases hP : endpointQueuePopHead k false Z with
  | error e => rfl
  | ok p =>
    obtain ⟨sender, stcb, Za⟩ := p
    have hsend : sender = s := endpointQueuePopHead_popped_eq_head k false Z Za ep sender s stcb hk
      (by simp [hS]) hP
    subst hsend
    have hNo1 := endpointQueuePopHead_noResizeDue Z k false sender stcb Za hNo hP
    dsimp only
    rw [blockedSenderMessage_answer r ρ μ κ Za sender stcb hs]
    split
    · simp only [↓reduceIte]
      split
      · rw [storeTcbIpcStateAndMessage_answer r ρ μ κ Za sender _ _ hNo1 hs]
        cases h2 : storeTcbIpcStateAndMessage Za sender (.blockedOnReply k (some tid)) none with
        | error e => rfl
        | ok Zb =>
          have hNo2 := storeTcbIpcStateAndMessage_noResizeDue Za Zb _ _ _ hNo1 h2
          dsimp only [Except.map]
          cases rid with
          | none => rfl
          | some rid =>
            dsimp only
            rw [linkCallerReply_answer r ρ μ κ Zb sender rid hNo2 hs]
            cases h3 : SystemState.linkCallerReply sender rid Zb with
            | error e => rfl
            | ok p3 =>
              obtain ⟨⟨⟩, Zc⟩ := p3
              have hNo3 := linkCallerReply_noResizeDue Zb Zc sender rid hNo2 h3
              dsimp only [mapStepState]
              rw [storeTcbIpcStateAndMessage_answer r ρ μ κ Zc tid _ _ hNo3 ht]
              cases h4 : storeTcbIpcStateAndMessage Zc tid .ready _ with
              | error e => rfl
              | ok Zd =>
                dsimp only [Except.map]
                rw [linkReplyWaiter_answer]
      · rw [storeTcbIpcStateAndMessage_answer r ρ μ κ Za sender _ _ hNo1 hs]
        cases h2 : storeTcbIpcStateAndMessage Za sender .ready none with
        | error e => rfl
        | ok Zb =>
          have hNo2 := storeTcbIpcStateAndMessage_noResizeDue Za Zb _ _ _ hNo1 h2
          dsimp only [Except.map]
          rw [updateTcb_answer r ρ μ id κ Zb sender _ hNo2 (fun e => absurd e hs),
            storeTcbIpcStateAndMessage_answer r ρ μ κ _ tid _ _ (updateTcb_noResizeDue _ _ _ hNo2) ht]
          cases storeTcbIpcStateAndMessage (Zb.updateTcb sender _) tid .ready _ with
          | error e => rfl
          | ok Zd => rfl
    · simp only [↓reduceIte, Bool.false_eq_true]
      rw [storeTcbIpcStateAndMessage_answer r ρ μ κ Za sender _ _ hNo1 hs]
      cases h2 : storeTcbIpcStateAndMessage Za sender .ready none with
      | error e => rfl
      | ok Zb =>
        have hNo2 := storeTcbIpcStateAndMessage_noResizeDue Za Zb _ _ _ hNo1 h2
        dsimp only [Except.map]
        rw [wakeThread_answer r ρ μ κ Zb sender ec hNo2]
        dsimp only
        rw [storeTcbIpcStateAndMessage_answer r ρ μ κ _ tid _ _ (wakeThread_noResizeDue _ _ _ hNo2) ht]
        cases storeTcbIpcStateAndMessage (wakeThread Zb sender ec).1 tid .ready _ with
        | error e => rfl
        | ok Zd => rfl

/-- **The receive body commutes with the answer** to a thread that is neither
the receiver nor its send queue's head. -/
theorem endpointReceiveDualOnCore_answer (Z : SystemState) (k : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : Option SeLe4n.ReplyId) (ec : CoreId)
    (hHead : receiveRendezvousSender? Z k ≠ some r) (ht : tid ≠ r) (hNo : Z.objects.noResizeDue) :
    endpointReceiveDualOnCore k tid rid ec (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      ((endpointReceiveDualOnCore k tid rid ec Z).1.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ),
        (endpointReceiveDualOnCore k tid rid ec Z).2) := by
  cases hE : Z.getEndpoint? k with
  | none =>
    unfold endpointReceiveDualOnCore
    rw [getEndpoint?_answer, hE]
    dsimp only
    rw [getObject?_isSome_answer]
    split <;> rfl
  | some ep =>
    cases hS : ep.sendQ.head with
    | some s =>
      have hs : s ≠ r := fun e => hHead (by unfold receiveRendezvousSender?; rw [hE]; simp [hS, e])
      exact endpointReceiveDualOnCore_answer_of_sender r ρ μ κ Z k tid rid ec ep s hE hS hs ht hNo
    | none =>
      unfold endpointReceiveDualOnCore
      rw [getEndpoint?_answer, hE]
      dsimp only
      rw [hS]
      dsimp only
      rw [cleanupPreReceiveDonationMigrated_answer r ρ μ κ Z tid hNo]
      cases hC : cleanupPreReceiveDonationMigrated Z tid with
      | error e => rfl
      | ok Zc =>
        have hNoC := cleanupPreReceiveDonationMigrated_noResizeDue Z Zc tid hNo hC
        dsimp only [Except.map]
        rw [endpointQueueEnqueue_answer r ρ μ κ Zc k true tid hNoC]
        cases hQ : endpointQueueEnqueue k true tid Zc with
        | error e => rfl
        | ok Zq =>
          have hNoQ := endpointQueueEnqueue_noResizeDue Zc Zq k true tid hNoC hQ
          dsimp only [Except.map]
          rw [storeTcbIpcStateAndMessage_answer r ρ μ κ Zq tid _ _ hNoQ ht]
          cases hB : storeTcbIpcStateAndMessage Zq tid (.blockedOnReceive k) none with
          | error e => rfl
          | ok Zb =>
            have hNoB := storeTcbIpcStateAndMessage_noResizeDue Zq Zb _ _ _ hNoQ hB
            dsimp only [Except.map]
            rw [getTcb?_answer_ne r ρ μ κ Zb tid ht]
            cases hT : Zb.getTcb? tid with
            | none =>
              dsimp only
              rw [removeRunnableOnCore_answer]
            | some rTcb =>
              dsimp only
              rw [replyStashValid_answer]
              split
              · have hNoS := recordReplyStasher_noResizeDue Zb (SeLe4n.ReplyId.optCode rid) tid hNoB
                have hT' : (Zb.recordReplyStasher (SeLe4n.ReplyId.optCode rid) tid).getTcb? tid = some rTcb := by
                  rw [recordReplyStasher_getTcb?_of_noResizeDue _ _ _ _ hNoB, hT]
                rw [recordReplyStasher_answer r ρ μ κ Zb _ tid hNoB,
                  storeObject_answer r ρ μ κ _ _ _ (.tcb { rTcb with
                      pendingReceiveReplyCode := SeLe4n.ReplyId.optCode rid })
                    ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT') hNoS
                    (storeLeavesIndexAndTypes_tcb_of_getTcb? hT')
                    (.inl (fun e => ht (SeLe4n.ThreadId.toObjId_injective _ _ e))),
                  storeObject_eq_of_leaves (obj := .tcb { rTcb with
                      pendingReceiveReplyCode := SeLe4n.ReplyId.optCode rid })
                    (storeLeavesIndexAndTypes_tcb_of_getTcb? hT')]
                dsimp only [mapStepState]
                rw [removeRunnableOnCore_answer]
              · rfl

/-- The receive body keeps the object table free of a due resize. -/
theorem endpointReceiveDualOnCore_noResizeDue (Z : SystemState) (k : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : Option SeLe4n.ReplyId) (ec : CoreId) (hNo : Z.objects.noResizeDue) :
    (endpointReceiveDualOnCore k tid rid ec Z).1.objects.noResizeDue := by
  unfold endpointReceiveDualOnCore
  cases hE : Z.getEndpoint? k with
  | none => dsimp only; split <;> exact hNo
  | some ep =>
    dsimp only
    cases hS : ep.sendQ.head with
    | some s =>
      dsimp only
      cases hP : endpointQueuePopHead k false Z with
      | error e => exact hNo
      | ok p =>
        obtain ⟨sender, stcb, Za⟩ := p
        have hNo1 := endpointQueuePopHead_noResizeDue Z k false sender stcb Za hNo hP
        dsimp only
        split
        · simp only [↓reduceIte]
          split
          · cases h2 : storeTcbIpcStateAndMessage Za sender (.blockedOnReply k (some tid)) none with
            | error e => exact hNo
            | ok Zb =>
              have hNo2 := storeTcbIpcStateAndMessage_noResizeDue Za Zb _ _ _ hNo1 h2
              dsimp only
              cases rid with
              | none => exact hNo
              | some rid =>
                dsimp only
                cases h3 : SystemState.linkCallerReply sender rid Zb with
                | error e => exact hNo
                | ok p3 =>
                  obtain ⟨⟨⟩, Zc⟩ := p3
                  have hNo3 := linkCallerReply_noResizeDue Zb Zc sender rid hNo2 h3
                  dsimp only
                  cases h4 : storeTcbIpcStateAndMessage Zc tid .ready _ with
                  | error e => exact hNo
                  | ok Zd =>
                    exact linkReplyWaiter_noResizeDue _ _ _
                      (storeTcbIpcStateAndMessage_noResizeDue Zc Zd _ _ _ hNo3 h4)
          · cases h2 : storeTcbIpcStateAndMessage Za sender .ready none with
            | error e => exact hNo
            | ok Zb =>
              have hNo2 := storeTcbIpcStateAndMessage_noResizeDue Za Zb _ _ _ hNo1 h2
              dsimp only
              cases h4 : storeTcbIpcStateAndMessage (Zb.updateTcb sender _) tid .ready _ with
              | error e => exact hNo
              | ok Zd =>
                exact storeTcbIpcStateAndMessage_noResizeDue _ Zd _ _ _ (updateTcb_noResizeDue _ _ _ hNo2) h4
        · simp only [↓reduceIte, Bool.false_eq_true]
          cases h2 : storeTcbIpcStateAndMessage Za sender .ready none with
          | error e => exact hNo
          | ok Zb =>
            have hNo2 := storeTcbIpcStateAndMessage_noResizeDue Za Zb _ _ _ hNo1 h2
            dsimp only
            cases h4 : storeTcbIpcStateAndMessage (wakeThread Zb sender ec).1 tid .ready _ with
            | error e => exact hNo
            | ok Zd =>
              exact storeTcbIpcStateAndMessage_noResizeDue _ Zd _ _ _ (wakeThread_noResizeDue _ _ _ hNo2) h4
    | none =>
      dsimp only
      cases hC : cleanupPreReceiveDonationMigrated Z tid with
      | error e => exact hNo
      | ok Zc =>
        have hNoC := cleanupPreReceiveDonationMigrated_noResizeDue Z Zc tid hNo hC
        dsimp only
        cases hQ : endpointQueueEnqueue k true tid Zc with
        | error e => exact hNo
        | ok Zq =>
          have hNoQ := endpointQueueEnqueue_noResizeDue Zc Zq k true tid hNoC hQ
          dsimp only
          cases hB : storeTcbIpcStateAndMessage Zq tid (.blockedOnReceive k) none with
          | error e => exact hNo
          | ok Zb =>
            have hNoB := storeTcbIpcStateAndMessage_noResizeDue Zq Zb _ _ _ hNoQ hB
            dsimp only
            cases hT : Zb.getTcb? tid with
            | none => exact removeRunnableOnCore_noResizeDue _ _ _ hNoB
            | some rTcb =>
              dsimp only
              split
              · have hNoS := recordReplyStasher_noResizeDue Zb (SeLe4n.ReplyId.optCode rid) tid hNoB
                have hT' : (Zb.recordReplyStasher (SeLe4n.ReplyId.optCode rid) tid).getTcb? tid = some rTcb := by
                  rw [recordReplyStasher_getTcb?_of_noResizeDue _ _ _ _ hNoB, hT]
                rw [storeObject_eq_of_leaves (obj := .tcb { rTcb with
                      pendingReceiveReplyCode := SeLe4n.ReplyId.optCode rid })
                    (storeLeavesIndexAndTypes_tcb_of_getTcb? hT')]
                exact removeRunnableOnCore_noResizeDue _ _ _
                  (insert_present_noResizeDue _ _ _ _ ((SystemState.getTcb?_eq_some_iff _ _ _).mp hT') hNoS)
              · exact hNo

/-- An answer-slot write is invisible to a capability transfer. -/
theorem LinkBlindWrite.withAnswerSlots : LinkBlindWrite (TCB.withAnswerSlots ρ μ id κ) :=
  ⟨fun _ _ _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- **The capability-carrying receive commutes with the answer** to a thread
that is neither the receiver nor its send queue's head. -/
theorem endpointReceiveDualWithCapsOnCore_answer (Z : SystemState) (k : SeLe4n.ObjId)
    (tid : SeLe4n.ThreadId) (rid : Option SeLe4n.ReplyId) (ec : CoreId)
    (hHead : receiveRendezvousSender? Z k ≠ some r) (ht : tid ≠ r) (hNo : Z.objects.noResizeDue) :
    endpointReceiveDualWithCapsOnCore k tid rid ec (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) =
      ((endpointReceiveDualWithCapsOnCore k tid rid ec Z).1.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ),
        (endpointReceiveDualWithCapsOnCore k tid rid ec Z).2) := by
  unfold endpointReceiveDualWithCapsOnCore
  dsimp only
  rw [receiveCapRequest_answer r ρ μ κ Z k hHead, receiverCapTarget?_answer r ρ μ κ Z tid ht,
    endpointReceiveDualOnCore_answer r ρ μ κ Z k tid rid ec hHead ht hNo, receiveRendezvousSender?_answer]
  have hNo1 := endpointReceiveDualOnCore_noResizeDue Z k tid rid ec hNo
  cases hR : endpointReceiveDualOnCore k tid rid ec Z with
  | mk Za res =>
    rw [hR] at hNo1
    cases res with
    | error e => rfl
    | ok p =>
      obtain ⟨sid, sgi⟩ := p
      dsimp only
      split
      · rfl
      · rw [receiveTransferCaps_mapTcbInPlace (LinkBlindWrite.withAnswerSlots ρ μ κ) r _ _ _ _ hNo1]
        cases receiveTransferCaps (receiveCapRequest Z k) (some k) (receiverCapTarget? Z tid) Za with
        | error e => rfl
        | ok q => obtain ⟨sm, Zb⟩ := q; rfl

end ReceiveRendezvous

end SeLe4n.Kernel
