-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.IPC.CrossCore.DeliveredInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInPlace

/-!
# Fault delivery, carried as words

WS-ZA ZA6.31.  seL4's `handleFault` writes the fault into the faulting TCB
(`tcbFault`, two words) and sends it to the handler in the message registers
(`sendFaultIPC`).  The specification here (`faultDeliverOnCoreChecked`) is
handed the fault and its context as records, and its handler lookup builds a
target record; this module is the same delivery handed **words**: the fault's
own words (`ThreadFaultWords`'s kind, flag, two words and lookup failure) and
its context's twelve, as scalars, with the handler resolved in continuation
form (`resolveFaultHandlerK`), so no fault, context, target or result record
is built.  Each form is proven equal to the specification it stands for
(`faultDeliverCheckedWords_eq`).
-/

namespace SeLe4n.Kernel

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency

-- ============================================================================
-- §1  The handler lookup, in continuation form
-- ============================================================================

/-- **`resolveFaultHandler` in continuation form**: the thread's configured
handler address resolved through its own CSpace (`resolveCapAddressKUnrolled`),
the refusal to `onErr`, the handler's endpoint and capability to `onOk`, so a
caller that matches the result at once builds no target and no `Except`
(`resolveFaultHandlerK_eq`).  Every gate is the specification's: a configured
handler, a CSpace root, a resolved slot holding a capability with send and a
grant right, naming an endpoint. -/
@[inline] def resolveFaultHandlerK {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (onErr : Unit → α) (onOk : SeLe4n.ObjId → Capability → α) : α :=
  match st.getTcb? tid with
  | none => onErr ()
  | some tcb =>
    if tcb.faultHandlerSet then
      match st.getCNode? tcb.cspaceRoot with
      | none => onErr ()
      | some rootCn =>
        resolveCapAddressKUnrolled tcb.cspaceRoot tcb.faultHandlerWord rootCn.depth st
          (fun _ => onErr ())
          (fun cnode slot =>
            match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
            | none => onErr ()
            | some cap =>
              if faultHandlerCapAuthorized cap then
                match cap.target with
                | .object epId =>
                  match st.getEndpoint? epId with
                  | some _ => onOk epId cap
                  | none => onErr ()
                | _ => onErr ()
              else onErr ())
    else onErr ()

theorem resolveFaultHandlerK_eq {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (onErr : Unit → α) (onOk : SeLe4n.ObjId → Capability → α) :
    resolveFaultHandlerK st tid onErr onOk =
      (match resolveFaultHandler st tid with
       | .error _ => onErr ()
       | .ok tgt => onOk tgt.endpoint tgt.cap) := by
  unfold resolveFaultHandlerK resolveFaultHandler
  cases st.getTcb? tid with
  | none => rfl
  | some tcb =>
    simp only [TCB.faultHandler]
    cases tcb.faultHandlerSet with
    | false => rfl
    | true =>
      simp only [↓reduceIte]
      unfold resolveFaultHandlerCPtr
      cases st.getCNode? tcb.cspaceRoot with
      | none => rfl
      | some rootCn =>
        simp only []
        rw [resolveCapAddressKUnrolled_eq, resolveCapAddressK_eq]
        cases resolveCapAddress tcb.cspaceRoot tcb.faultHandlerWord rootCn.depth st with
        | error e => rfl
        | ok ref =>
          obtain ⟨cnode, slot⟩ := ref
          simp only []
          cases SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
          | none => rfl
          | some cap =>
            simp only []
            cases faultHandlerCapAuthorized cap
            · rfl
            · simp only [↓reduceIte]
              cases cap.target with
              | object epId =>
                rcases hE : st.getEndpoint? epId with _ | _ <;> simp only [hE]
              | _ => rfl

-- ============================================================================
-- §2  The fault recorded and the delivery, handed words
-- ============================================================================

/-- **The fault recorded as words** (`recordPendingFault` of the record they
encode, `recordPendingFault_eq_words`): the faulting thread's fault fields
written in its own cell, and its message marked as the fault. -/
@[inline] def recordFaultWords (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : ThreadFaultWords) : SystemState :=
  st.updateTcb tid fun tcb => { tcb.withFaultWords w with ipcFaultSend := true }

theorem recordPendingFault_eq_words (st : SystemState) (tid : SeLe4n.ThreadId)
    (tf : ThreadFault) :
    recordPendingFault st tid tf =
      recordFaultWords st tid (ThreadFaultWords.ofFault tf.fault tf.context) := rfl

/-- The words a fault and its context are stored as, field by field. -/
@[inline] def faultWordsOf (k : Nat) (flag : Bool) (w0 w1 : UInt64) (lk : KernelError)
    (ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) : ThreadFaultWords :=
  { kind := k, flag := flag, word0 := w0, word1 := w1, lookup := lk, ip := ip, sp := sp,
    lr := lr, spsr := spsr, x0 := x0, x1 := x1, x2 := x2, x3 := x3, x4 := x4, x5 := x5,
    x6 := x6, x7 := x7 }

theorem faultWordsOf_fields (w : ThreadFaultWords) :
    faultWordsOf w.kind w.flag w.word0 w.word1 w.lookup w.ip w.sp w.lr w.spsr w.x0 w.x1 w.x2
      w.x3 w.x4 w.x5 w.x6 w.x7 = w := rfl

-- ============================================================================
-- §2a  The delivered fault, written into the handler's registers
-- ============================================================================

/-- **The unchecked call dispatch, in place** (`callDispatchChecked_inPlace`
without the flow gate, which the fault delivery has already passed): a call that
finds a receiver and transfers no capability commits `performCallRendezvous`'s
state with an empty transfer summary. -/
theorem callDispatch_inPlace (st : SystemState)
    (endpointId : SeLe4n.ObjId) (ep : Endpoint) (caller r : SeLe4n.ThreadId) (rt : TCB)
    (rid : SeLe4n.ReplyId) (payload : SendPayload) (msg : IpcMessage) (slot : SeLe4n.Slot)
    (core : CoreId)
    (hM : sendPayloadMessage st caller payload = msg)
    (hReq : sendCapRequest st endpointId caller payload = none)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.receiveQ.head = some r)
    (hT : st.objects[r.toObjId]? = some (.tcb rt)) (hRid : rt.pendingReceiveReply = some rid)
    (hG : callWakesInPlace st endpointId caller r rt rid = true) :
    ∃ sgi, endpointCallCrossCoreDispatch endpointId caller payload slot core st =
      (performCallRendezvous st endpointId caller r rt.queueNext rid msg core,
       .ok ({ results := #[] }, sgi)) := by
  have hG' := hG
  simp only [callWakesInPlace, sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG'
  have hCRes : caller.isReserved = false := hG'.1.1.1.1.1.1.1.1.2
  have hRRes : r.isReserved = false := hG'.1.1.1.1.1.1.1.1.1.1.1.1.1.1
  have hEp : st.getEndpoint? endpointId = some ep :=
    (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE
  obtain ⟨hEq, hDon⟩ := callRendezvous_inPlace st endpointId ep caller r rt rid payload msg core hM
    hE hH hT hRid hG
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff caller).mpr hCRes)
  obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff r).mpr hRRes)
  have hcv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv
  have hrv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hrv
  refine ⟨(wakeThread ((storePopHead st endpointId true r rt.queueNext).updateTcb r
    (callReceiverTcb msg)) r core).2, ?_⟩
  unfold endpointCallCrossCoreDispatch
  rw [endpointCallWithCapsOnCore_no_caps _ _ _ _ _ _ hReq, hEq]
  simp only [Except.map, hEp, hH, hcv, hrv]
  unfold applyCallDonationOnCore
  rw [applyCallDonation_eq_ok_self_of_no_donation _ _ _ (by rw [hcv', hrv']; exact hDon)]
  simp only [hcv', hrv', hDon]
  rfl

/-- **The call rendezvous's delivery is the held message's stage**: the
receiver woken without the message, the priority walk, then the specification's
stage of the message held in the receiver's TCB. -/
theorem stageWokenDelivery_performCallRendezvous_held (st : SystemState)
    (endpointId : SeLe4n.ObjId) (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (msg : IpcMessage) (core : CoreId)
    (hNo : st.objects.noResizeDue) (hNe : caller ≠ r) :
    Architecture.stageWokenDelivery
        (performCallRendezvous st endpointId caller r next rid msg core) (some r) 0 =
      Architecture.stageDeliveredMessage
        ((PriorityInheritance.propagatePipChainCrossCore
          (storeCallRendezvousReady st endpointId caller r (ThreadId.optCode next) rid core)
          r core).1.mapTcbInPlace r (holdMessage msg)) r 0 := by
  have hNoS := storeCallRendezvousReady_noResizeDue st endpointId caller r
    (ThreadId.optCode next) rid core hNo
  unfold performCallRendezvous
  rw [storeCallRendezvous_eq_hold _ _ _ _ _ _ _ _ hNo hNe,
    propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoS, Architecture.stageWokenDelivery_some]

/-- The message length of the fault a kind code names (`faultMessageLength`). -/
@[inline] def faultLengthOfKind : Nat → Nat
  | 1 | 2 => 4
  | 3 => 13
  | _ => 5

/-- The label of the fault a kind code names (`faultLabel`). -/
@[inline] def faultLabelOfKind : Nat → Nat
  | 1 => FaultLabel.vmFault
  | 2 => FaultLabel.capFault
  | 3 => FaultLabel.unknownSyscall
  | _ => FaultLabel.userException

/-- The message-info word a delivered fault's frame carries, `overflow` words
written past the frame.  Out of line, as `regMessageInfoWord`, so the
`MessageInfo` it encodes is never built. -/
@[noinline] def faultInfoWord (k overflow : Nat) : UInt64 :=
  (({ length := min (min (faultLengthOfKind k) (4 + overflow)) maxMessageRegisters
      extraCaps := min 0 Model.maxExtraCaps
      label := min (faultLabelOfKind k) (errorLabelBase - 1) } : MessageInfo).encode).toUInt64

/-- The frame's `MR0` for a fault of kind `k`.  Each register word is chosen
out of line, so the frame is a straight run of words and never built. -/
@[noinline] def faultFrameMR0 (k : Nat) (ip x0 : UInt64) : UInt64 :=
  if k == 3 then x0 else ip

/-- The frame's `MR1` for a fault of kind `k`. -/
@[noinline] def faultFrameMR1 (k : Nat) (w0 x1 sp : UInt64) : UInt64 :=
  if k == 1 || k == 2 then w0 else if k == 3 then x1 else sp

/-- The frame's `MR2` for a fault of kind `k`. -/
@[noinline] def faultFrameMR2 (k : Nat) (flag : Bool) (x2 spsr : UInt64) : UInt64 :=
  if k == 1 || k == 2 then encodeFlag flag else if k == 3 then x2 else spsr

/-- The frame's `MR3` for a fault of kind `k`. -/
@[noinline] def faultFrameMR3 (k : Nat) (w0 w1 : UInt64) (lk : KernelError) (x3 : UInt64) :
    UInt64 :=
  if k == 1 then w1
  else if k == 2 then Nat.toUInt64 (KernelError.toDiscriminant lk)
  else if k == 3 then x3 else w0

/-- **The frame a delivered fault writes**, word by word from the fault's words
(`encodeFault`'s layout: `MR0`-`MR3` in `x2`-`x5`), the badge in `x0`
(`faultFrameW_eq`). -/
@[inline] def faultFrameW (k : Nat) (flag : Bool) (w0 w1 : UInt64) (lk : KernelError)
    (ip sp spsr x0 x1 x2 x3 : UInt64) (overflow : Nat) (badgeWord : SeLe4n.Badge)
    (badged : Bool) : SyscallReturnFrame :=
  { x0 := badgeWordIf badgeWord badged
    x1 := faultInfoWord k overflow
    x2 := faultFrameMR0 k ip x0
    x3 := faultFrameMR1 k w0 x1 sp
    x4 := faultFrameMR2 k flag x2 spsr
    x5 := faultFrameMR3 k w0 w1 lk x3 }

/-- **The fault's frame is its message's.** -/
theorem faultFrameW_eq (f : Fault) (ctx : FaultContext) (overflow : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) :
    faultFrameW (ThreadFaultWords.ofFault f {}).kind (ThreadFaultWords.ofFault f {}).flag
        (ThreadFaultWords.ofFault f {}).word0 (ThreadFaultWords.ofFault f {}).word1
        (ThreadFaultWords.ofFault f {}).lookup ctx.faultIP ctx.sp ctx.spsr ctx.x0 ctx.x1 ctx.x2
        ctx.x3 overflow badgeWord badged =
      Architecture.returnFrameOfMessage
        (faultMessage f ctx (SeLe4n.Badge.opt badgeWord badged)) 0 overflow := by
  have hB : badgeWordIf badgeWord badged =
      ((SeLe4n.Badge.opt badgeWord badged).map SeLe4n.Badge.word).getD 0 := by
    rw [← badgeWordOrZero_opt]; rfl
  cases f <;>
    simp only [faultFrameW, faultFrameMR0, faultFrameMR1, faultFrameMR2, faultFrameMR3,
      Architecture.returnFrameOfMessage, faultMessage, encodeFault, hB,
      faultInfoWord, Architecture.returnMessageInfo, faultLengthOfKind, faultLabelOfKind,
      faultMessageLength, faultLabel, ThreadFaultWords.ofFault, Fault.kindCode, regOf,
      FaultContext.gprAt, List.size_toArray, List.length_cons, List.length_nil,
      Array.getElem?_toList, List.getElem?_toArray, List.getElem?_cons_zero,
      List.getElem?_cons_succ, Option.map_some, Option.getD_some, Nat.toUInt64_eq,
      UInt64.ofNat_toNat] <;> simp only [Nat.reduceBEq, Bool.or_false, Bool.or_true,
        Bool.false_eq_true, ↓reduceIte] <;> rfl

-- ============================================================================
-- §2b  The words past the fourth, written into the handler's IPC buffer
-- ============================================================================

theorem getVSpaceRoot?_mapTcbInPlace (X : SystemState) (r : SeLe4n.ThreadId) (g : TCB → TCB)
    (id : SeLe4n.ObjId) : (X.mapTcbInPlace r g).getVSpaceRoot? id = X.getVSpaceRoot? id := by
  unfold SystemState.getVSpaceRoot?
  rw [SystemState.objects_mapTcbInPlace]
  by_cases h : (r.toObjId == id) = true
  · rw [if_pos h]
    cases X.objects[id]? with
    | none => rfl
    | some o => cases o <;> rfl
  · rw [if_neg h]

/-- **A slot's address is the thread's space's, not its registers'**: a TCB
write that keeps the thread's VSpace root and IPC buffer resolves every slot
where it was. -/
theorem ipcBufferSlotPAddr?_mapTcbInPlace (X : SystemState) (r : SeLe4n.ThreadId)
    (g : TCB → TCB) (t t' : TCB) (idx : Nat) (needWrite : Bool)
    (hV : t'.vspaceRoot = t.vspaceRoot) (hB : t'.ipcBuffer = t.ipcBuffer) :
    Architecture.IpcBufferRead.ipcBufferSlotPAddr? (X.mapTcbInPlace r g) t' idx needWrite =
      Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t idx needWrite := by
  unfold Architecture.IpcBufferRead.ipcBufferSlotPAddr?
  rw [hV, hB, getVSpaceRoot?_mapTcbInPlace]
  rfl

/-- …so a delivery's overflow writes are where they were. -/
theorem overflowDeliveryWrites_mapTcbInPlace (X : SystemState) (r : SeLe4n.ThreadId)
    (g : TCB → TCB) (t t' : TCB) (hV : t'.vspaceRoot = t.vspaceRoot)
    (hB : t'.ipcBuffer = t.ipcBuffer) :
    ∀ (ws : List SeLe4n.RegValue) (i : Nat),
      Architecture.overflowDeliveryWrites (X.mapTcbInPlace r g) t' ws i =
        Architecture.overflowDeliveryWrites X t ws i
  | [], _ => rfl
  | w :: rest, i => by
    unfold Architecture.overflowDeliveryWrites
    rw [ipcBufferSlotPAddr?_mapTcbInPlace X r g t t' i true hV hB]
    split
    · rw [overflowDeliveryWrites_mapTcbInPlace X r g t t' hV hB rest (i + 1)]
    · rfl

theorem recordPhysicalWrites_cons (S : SystemState) (w : Architecture.PhysicalWrite)
    (ws : List Architecture.PhysicalWrite) :
    Architecture.recordPhysicalWrites S (w :: ws) =
      Architecture.recordPhysicalWrites (S.recordPhysicalWrite w) ws := by
  cases ws <;> rfl

/-- **Staging a held message is writing its frame and its words past the
fourth** (`stageDeliveredMessage_holdMessage` for a message of any length): on
a table with no resize due, a ready thread holding a message stages the frame
whose length counts the overflow words its IPC buffer takes, then those words,
resolved against the thread as it was before the message was held. -/
theorem stageDeliveredMessage_holdMessage_overflow (X : SystemState) (r : SeLe4n.ThreadId)
    (msg : IpcMessage) (ws : List SeLe4n.RegValue) (hNo : X.objects.noResizeDue)
    (hTail : msg.registers.toList.drop 4 = ws) :
    Architecture.stageDeliveredMessage (X.mapTcbInPlace r (holdMessage msg)) r 0 =
      match X.getTcb? r with
      | some t =>
        if t.ipcState = .ready then
          Architecture.recordPhysicalWrites
            (X.mapTcbInPlace r (withFrameWords
              (Architecture.returnFrameOfMessage msg 0
                (Architecture.overflowDeliveryWrites X t ws 0).length).x0
              (Architecture.returnFrameOfMessage msg 0
                (Architecture.overflowDeliveryWrites X t ws 0).length).x1
              (Architecture.returnFrameOfMessage msg 0
                (Architecture.overflowDeliveryWrites X t ws 0).length).x2
              (Architecture.returnFrameOfMessage msg 0
                (Architecture.overflowDeliveryWrites X t ws 0).length).x3
              (Architecture.returnFrameOfMessage msg 0
                (Architecture.overflowDeliveryWrites X t ws 0).length).x4
              (Architecture.returnFrameOfMessage msg 0
                (Architecture.overflowDeliveryWrites X t ws 0).length).x5))
            (Architecture.overflowDeliveryWrites X t ws 0)
        else X.mapTcbInPlace r (holdMessage msg)
      | none => X := by
  unfold Architecture.stageDeliveredMessage
  rw [SystemState.getTcb?_mapTcbInPlace, if_pos rfl]
  cases hT : X.getTcb? r with
  | none => exact mapTcbInPlace_eq_self_of_getTcb?_none X r _ hT
  | some t =>
    simp only [Option.map_some, TCB.withMessageSlots_ipcState, TCB.withMessageSlots_pendingMessage]
    split
    · have hW : Architecture.messageOverflowWrites (X.mapTcbInPlace r (holdMessage msg))
          (holdMessage msg t) msg = Architecture.overflowDeliveryWrites X t ws 0 := by
        unfold Architecture.messageOverflowWrites
        rw [hTail]
        exact overflowDeliveryWrites_mapTcbInPlace X r _ t (holdMessage msg t) rfl rfl ws 0
      rw [hW]
      unfold Architecture.writeDeliveredFrameToTcb
      rw [SystemState.updateTcb_eq_mapTcbInPlace (X.mapTcbInPlace r (holdMessage msg)) _ _ hNo,
        SystemState.mapTcbInPlace_mapTcbInPlace]
      rfl
    · rfl

/-- The address of overflow slot `i` of thread `r`'s IPC buffer, writable, read
off the thread where it stands (`ipcBufferSlotPAddr?`); `none` for a key that
holds no thread. -/
@[inline] def overflowSlotOf (S : SystemState) (r : SeLe4n.ThreadId) (i : Nat) : Option PAddr :=
  match S.getTcb? r with
  | some t => Architecture.IpcBufferRead.ipcBufferSlotPAddr? S t i true
  | none => none

/-- How many of the `n` overflow slots from `i` on resolve, up to the first
that does not: the length of the prefix a delivery writes
(`overflowDeliveryWrites`). -/
def overflowSlotsFrom (S : SystemState) (r : SeLe4n.ThreadId) : Nat → Nat → Nat
  | _, 0 => 0
  | i, n + 1 =>
    match overflowSlotOf S r i with
    | some _ => overflowSlotsFrom S r (i + 1) n + 1
    | none => 0

/-- The number of message registers past the fourth a fault of kind `k`
carries (`encodeFault`'s layout): nine for an unknown syscall, one for a user
exception, none for a VM or capability fault. -/
@[inline] def faultOverflowLength (k : Nat) : Nat :=
  if k == 1 || k == 2 then 0 else if k == 3 then 9 else 1

/-- Overflow word `i` of a fault of kind `k` (`encodeFault`'s `MR4` on): an
unknown syscall's `x4`-`x7`, restart PC, `SP`, `LR`, `SPSR` and number, a user
exception's code. -/
@[noinline] def faultOverflowWord (k i : Nat) (w0 w1 ip sp lr spsr x4 x5 x6 x7 : UInt64) :
    UInt64 :=
  if k == 3 then
    match i with
    | 0 => x4 | 1 => x5 | 2 => x6 | 3 => x7 | 4 => ip | 5 => sp | 6 => lr | 7 => spsr
    | _ => w0
  else w1

/-- The overflow registers `faultOverflowWord` names, `n` of them from `i`. -/
def faultOverflowRegs (k : Nat) (w0 w1 ip sp lr spsr x4 x5 x6 x7 : UInt64) :
    Nat → Nat → List SeLe4n.RegValue
  | _, 0 => []
  | i, n + 1 => regOf (faultOverflowWord k i w0 w1 ip sp lr spsr x4 x5 x6 x7) ::
      faultOverflowRegs k w0 w1 ip sp lr spsr x4 x5 x6 x7 (i + 1) n

theorem faultOverflowRegs_length (k : Nat) (w0 w1 ip sp lr spsr x4 x5 x6 x7 : UInt64) :
    ∀ (i n : Nat), (faultOverflowRegs k w0 w1 ip sp lr spsr x4 x5 x6 x7 i n).length = n
  | _, 0 => rfl
  | i, n + 1 => by
    simp only [faultOverflowRegs, List.length_cons,
      faultOverflowRegs_length k w0 w1 ip sp lr spsr x4 x5 x6 x7 (i + 1) n]

/-- **The fault's words past the fourth, written in place**: each recorded as a
user-word store at its slot's address, word by word, up to the first slot that
does not resolve (`faultOverflowStore_eq`). -/
def faultOverflowStore (S : SystemState) (r : SeLe4n.ThreadId) (k : Nat)
    (w0 w1 ip sp lr spsr x4 x5 x6 x7 : UInt64) : Nat → Nat → SystemState
  | _, 0 => S
  | i, n + 1 =>
    match overflowSlotOf S r i with
    | some pa => faultOverflowStore
        (S.recordPhysicalWrite (.storeUserWord pa
          (faultOverflowWord k i w0 w1 ip sp lr spsr x4 x5 x6 x7)))
        r k w0 w1 ip sp lr spsr x4 x5 x6 x7 (i + 1) n
    | none => S

theorem overflowSlotsFrom_eq (S : SystemState) (r : SeLe4n.ThreadId) (X : SystemState) (t : TCB)
    (hS : ∀ j, overflowSlotOf S r j = Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t j true)
    (ws : List SeLe4n.RegValue) (i : Nat) :
    overflowSlotsFrom S r i ws.length = (Architecture.overflowDeliveryWrites X t ws i).length := by
  induction ws generalizing i with
  | nil => rfl
  | cons w rest ih =>
    simp only [List.length_cons, overflowSlotsFrom, hS]
    unfold Architecture.overflowDeliveryWrites
    split
    · next pa hPa => rw [hPa, ih, List.length_cons]
    · next hPa => rw [hPa]; rfl

theorem faultOverflowStore_eq (r : SeLe4n.ThreadId) (X : SystemState) (t : TCB) (k : Nat)
    (w0 w1 ip sp lr spsr x4 x5 x6 x7 : UInt64) :
    ∀ (n i : Nat) (S : SystemState),
      (∀ j, overflowSlotOf S r j = Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t j true) →
      faultOverflowStore S r k w0 w1 ip sp lr spsr x4 x5 x6 x7 i n =
        Architecture.recordPhysicalWrites S (Architecture.overflowDeliveryWrites X t
          (faultOverflowRegs k w0 w1 ip sp lr spsr x4 x5 x6 x7 i n) i)
  | 0, _, S, _ => (Architecture.recordPhysicalWrites_nil S).symm
  | n + 1, i, S, hS => by
    simp only [faultOverflowStore, faultOverflowRegs, hS]
    unfold Architecture.overflowDeliveryWrites
    split
    · next pa hPa =>
      rw [hPa, recordPhysicalWrites_cons]
      have hReg : (regOf (faultOverflowWord k i w0 w1 ip sp lr spsr x4 x5 x6 x7)).val.toUInt64 =
          faultOverflowWord k i w0 w1 ip sp lr spsr x4 x5 x6 x7 := by
        simp only [regOf, Nat.toUInt64_eq, UInt64.ofNat_toNat]
      rw [hReg]
      exact faultOverflowStore_eq r X t k w0 w1 ip sp lr spsr x4 x5 x6 x7 n (i + 1) _
        (fun j => hS j)
    · next hPa => rw [hPa]; exact (Architecture.recordPhysicalWrites_nil S).symm

/-- A fault message's registers past the fourth are `faultOverflowRegs`'s. -/
theorem faultMessage_overflowRegs (f : Fault) (ctx : FaultContext) (b : Option SeLe4n.Badge) :
    (faultMessage f ctx b).registers.toList.drop 4 =
      faultOverflowRegs (ThreadFaultWords.ofFault f ctx).kind
        (ThreadFaultWords.ofFault f ctx).word0 (ThreadFaultWords.ofFault f ctx).word1
        ctx.faultIP ctx.sp ctx.lr ctx.spsr ctx.x4 ctx.x5 ctx.x6 ctx.x7 0
        (faultOverflowLength (ThreadFaultWords.ofFault f ctx).kind) := by
  cases f <;> rfl

/-- The fault message held where the woken handler is, unexpectedly, not
ready (`writeDeliveredFrameIfReady`'s `otherwise`).  Out of line, so the
message is built only on that path. -/
@[noinline] def holdFaultMessageBody (X : SystemState) (r : SeLe4n.ThreadId)
    (k : Nat) (flag : Bool) (w0 w1 : UInt64) (lk : KernelError)
    (ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (badgeWord : SeLe4n.Badge)
    (badged : Bool) : SystemState :=
  let w := faultWordsOf k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7
  match w.fault? with
  | some f =>
    X.mapTcbInPlace r (holdMessage (faultMessage f w.context (SeLe4n.Badge.opt badgeWord badged)))
  | none => X

/-- **A fault's delivery to a woken thread, in place**: the fault's frame
written into the thread's saved registers (`faultFrameW`), its length counting
the words past the fourth the thread's IPC buffer takes, and those words
recorded as user-word stores (`faultOverflowStore`).  A thread that is,
unexpectedly, not ready holds the message (`holdFaultMessageBody`).  Each step
reads the words it needs before it writes (`deliverFaultFrame_eq`). -/
@[inline] def deliverFaultFrame (X : SystemState) (r : SeLe4n.ThreadId)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (k : Nat) (flag : Bool) (w0 w1 : UInt64)
    (lk : KernelError) (ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) : SystemState :=
  match X.getTcb? r with
  | some t =>
    if t.ipcState = .ready then
      let n := overflowSlotsFrom X r 0 (faultOverflowLength k)
      faultOverflowStore
        (X.mapTcbInPlace r (withFrameWords (badgeWordIf badgeWord badged)
          (faultInfoWord k n) (faultFrameMR0 k ip x0) (faultFrameMR1 k w0 x1 sp)
          (faultFrameMR2 k flag x2 spsr) (faultFrameMR3 k w0 w1 lk x3)))
        r k w0 w1 ip sp lr spsr x4 x5 x6 x7 0 (faultOverflowLength k)
    else holdFaultMessageBody X r k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7
      badgeWord badged
  | none => X

/-- Every kind code from `4` up names a user exception's frame. -/
theorem faultFrameW_of_user (k : Nat) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3) (flag : Bool)
    (w0 w1 : UInt64) (lk : KernelError) (ip sp spsr x0 x1 x2 x3 : UInt64) (overflow : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) :
    faultFrameW k flag w0 w1 lk ip sp spsr x0 x1 x2 x3 overflow badgeWord badged =
      faultFrameW 4 flag w0 w1 lk ip sp spsr x0 x1 x2 x3 overflow badgeWord badged := by
  have e1 : (k == 1) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h1
  have e2 : (k == 2) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h2
  have e3 : (k == 3) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h3
  have hl : faultLengthOfKind k = faultLengthOfKind 4 := by
    unfold faultLengthOfKind; split <;> simp_all
  have hb : faultLabelOfKind k = faultLabelOfKind 4 := by
    unfold faultLabelOfKind; split <;> simp_all
  simp only [faultFrameW, faultFrameMR0, faultFrameMR1, faultFrameMR2, faultFrameMR3,
    faultInfoWord, hl, hb, e1, e2, e3, Nat.reduceBEq, Bool.or_false, Bool.false_eq_true,
    ↓reduceIte]

/-- And its words past the fourth. -/
theorem faultOverflowRegs_of_user (k : Nat) (h1 : k ≠ 1) (h2 : k ≠ 2) (h3 : k ≠ 3)
    (w0 w1 ip sp lr spsr x4 x5 x6 x7 : UInt64) :
    faultOverflowRegs k w0 w1 ip sp lr spsr x4 x5 x6 x7 0 (faultOverflowLength k) =
      faultOverflowRegs 4 w0 w1 ip sp lr spsr x4 x5 x6 x7 0 (faultOverflowLength 4) := by
  have e1 : (k == 1) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h1
  have e2 : (k == 2) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h2
  have e3 : (k == 3) = false := by simp only [beq_eq_false_iff_ne, ne_eq]; exact h3
  simp only [faultOverflowLength, faultOverflowRegs, faultOverflowWord, e1, e2, e3,
    Nat.reduceBEq, Bool.or_false, Bool.false_eq_true, ↓reduceIte]

/-- The frame a thread's fault words name is the message's of the fault they
decode to. -/
theorem faultFrameW_eq_words (w : ThreadFaultWords) (f : Fault) (hf : w.fault? = some f)
    (overflow : Nat) (badgeWord : SeLe4n.Badge) (badged : Bool) :
    faultFrameW w.kind w.flag w.word0 w.word1 w.lookup w.ip w.sp w.spsr w.x0 w.x1 w.x2 w.x3
        overflow badgeWord badged =
      Architecture.returnFrameOfMessage
        (faultMessage f w.context (SeLe4n.Badge.opt badgeWord badged)) 0 overflow := by
  rcases hk : w.kind with _ | _ | _ | _ | n <;>
    simp only [ThreadFaultWords.fault?, hk, reduceCtorEq, Option.some.injEq] at hf <;> subst hf
  · exact faultFrameW_eq (.vmFault _ _ _) w.context _ _ _
  · exact faultFrameW_eq (.capFault _ _ _) w.context _ _ _
  · exact faultFrameW_eq (.unknownSyscall _) w.context _ _ _
  · rw [faultFrameW_of_user _ (by omega) (by omega) (by omega)]
    exact faultFrameW_eq (.userException _ _) w.context _ _ _

/-- And its words past the fourth are the message's. -/
theorem faultMessage_overflowRegs_words (w : ThreadFaultWords) (f : Fault)
    (hf : w.fault? = some f) (b : Option SeLe4n.Badge) :
    (faultMessage f w.context b).registers.toList.drop 4 =
      faultOverflowRegs w.kind w.word0 w.word1 w.ip w.sp w.lr w.spsr w.x4 w.x5 w.x6 w.x7 0
        (faultOverflowLength w.kind) := by
  rcases hk : w.kind with _ | _ | _ | _ | n <;>
    simp only [ThreadFaultWords.fault?, hk, reduceCtorEq, Option.some.injEq] at hf <;> subst hf
  · exact faultMessage_overflowRegs (.vmFault _ _ _) w.context b
  · exact faultMessage_overflowRegs (.capFault _ _ _) w.context b
  · exact faultMessage_overflowRegs (.unknownSyscall _) w.context b
  · rw [faultOverflowRegs_of_user _ (by omega) (by omega) (by omega)]
    exact faultMessage_overflowRegs (.userException _ _) w.context b

/-- And the message `holdFaultMessageBody` holds is the fault's. -/
theorem holdFaultMessageBody_words (X : SystemState) (r : SeLe4n.ThreadId)
    (w : ThreadFaultWords) (f : Fault) (hf : w.fault? = some f) (badgeWord : SeLe4n.Badge)
    (badged : Bool) :
    holdFaultMessageBody X r w.kind w.flag w.word0 w.word1 w.lookup w.ip w.sp w.lr w.spsr w.x0
        w.x1 w.x2 w.x3 w.x4 w.x5 w.x6 w.x7 badgeWord badged =
      X.mapTcbInPlace r (holdMessage
        (faultMessage f w.context (SeLe4n.Badge.opt badgeWord badged))) := by
  unfold holdFaultMessageBody
  simp only [faultWordsOf_fields, hf]

/-- **The in-place delivery is the specification's stage** of the message the
fault the words decode to encodes. -/
theorem deliverFaultFrame_eq (X : SystemState) (r : SeLe4n.ThreadId) (w : ThreadFaultWords)
    (f : Fault) (hf : w.fault? = some f) (badgeWord : SeLe4n.Badge) (badged : Bool)
    (hNoX : X.objects.noResizeDue) :
    deliverFaultFrame X r badgeWord badged w.kind w.flag w.word0 w.word1 w.lookup w.ip w.sp
        w.lr w.spsr w.x0 w.x1 w.x2 w.x3 w.x4 w.x5 w.x6 w.x7 =
      Architecture.stageDeliveredMessage (X.mapTcbInPlace r (holdMessage
        (faultMessage f w.context (SeLe4n.Badge.opt badgeWord badged)))) r 0 := by
  rw [stageDeliveredMessage_holdMessage_overflow _ r _ _ hNoX
    (faultMessage_overflowRegs_words w f hf _)]
  unfold deliverFaultFrame
  cases hT : X.getTcb? r with
  | none => rfl
  | some t =>
    simp only []
    split
    · have hX : ∀ j, overflowSlotOf X r j =
          Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t j true := fun j => by
        simp only [overflowSlotOf, hT]
      have hS : ∀ (a b c d e g : UInt64) j,
          overflowSlotOf (X.mapTcbInPlace r (withFrameWords a b c d e g)) r j =
            Architecture.IpcBufferRead.ipcBufferSlotPAddr? X t j true := fun a b c d e g j => by
        simp only [overflowSlotOf, SystemState.getTcb?_mapTcbInPlace, hT, Option.map_some]
        exact ipcBufferSlotPAddr?_mapTcbInPlace X r _ t _ j true rfl rfl
      have hLen := faultOverflowRegs_length w.kind w.word0 w.word1 w.ip w.sp w.lr w.spsr w.x4
        w.x5 w.x6 w.x7 0 (faultOverflowLength w.kind)
      have hC := overflowSlotsFrom_eq X r X t hX (faultOverflowRegs w.kind w.word0 w.word1 w.ip
        w.sp w.lr w.spsr w.x4 w.x5 w.x6 w.x7 0 (faultOverflowLength w.kind)) 0
      rw [hLen] at hC
      rw [faultOverflowStore_eq r X t _ _ _ _ _ _ _ _ _ _ _ _ 0 _ (hS _ _ _ _ _ _), hC,
        ← faultFrameW_eq_words w f hf _ badgeWord badged]
      rfl
    · exact holdFaultMessageBody_words X r w f hf badgeWord badged

/-- **The fault's call rendezvous, delivered**: the handler woken without the
message, the priority walk, then the fault delivered in place
(`deliverFaultFrame`).  Each step reads the words it needs before it writes
(`performFaultCallDelivered_eq`). -/
@[noinline] def performFaultCallDelivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (nextCode : Nat) (rid : SeLe4n.ReplyId) (cap : Capability)
    (k : Nat) (flag : Bool) (w0 w1 : UInt64) (lk : KernelError)
    (ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (core : CoreId) : SystemState :=
  deliverFaultFrame (PriorityInheritance.propagatePipChainCrossCore
      (storeCallRendezvousReady st endpointId caller r nextCode rid core) r core).1 r
    cap.badgeWord cap.badged k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7

/-- The context words of a fault's words are its context's, whichever the fault. -/
theorem ofFault_ip (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).ip = ctx.faultIP := by cases f <;> rfl
theorem ofFault_sp (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).sp = ctx.sp := by cases f <;> rfl
theorem ofFault_lr (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).lr = ctx.lr := by cases f <;> rfl
theorem ofFault_spsr (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).spsr = ctx.spsr := by cases f <;> rfl
theorem ofFault_x0 (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).x0 = ctx.x0 := by cases f <;> rfl
theorem ofFault_x1 (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).x1 = ctx.x1 := by cases f <;> rfl
theorem ofFault_x2 (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).x2 = ctx.x2 := by cases f <;> rfl
theorem ofFault_x3 (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).x3 = ctx.x3 := by cases f <;> rfl
theorem ofFault_x4 (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).x4 = ctx.x4 := by cases f <;> rfl
theorem ofFault_x5 (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).x5 = ctx.x5 := by cases f <;> rfl
theorem ofFault_x6 (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).x6 = ctx.x6 := by cases f <;> rfl
theorem ofFault_x7 (f : Fault) (ctx : FaultContext) :
    (ThreadFaultWords.ofFault f ctx).x7 = ctx.x7 := by cases f <;> rfl

/-- **The delivered fault is the specification's delivery** of the message the
fault and its context encode. -/
theorem performFaultCallDelivered_eq (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller r : SeLe4n.ThreadId) (next : Option SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (cap : Capability) (f : Fault) (ctx : FaultContext) (core : CoreId)
    (hNo : st.objects.noResizeDue) (hNe : caller ≠ r) :
    performFaultCallDelivered st endpointId caller r (ThreadId.optCode next) rid cap
        (ThreadFaultWords.ofFault f ctx).kind (ThreadFaultWords.ofFault f ctx).flag
        (ThreadFaultWords.ofFault f ctx).word0 (ThreadFaultWords.ofFault f ctx).word1
        (ThreadFaultWords.ofFault f ctx).lookup (ThreadFaultWords.ofFault f ctx).ip
        (ThreadFaultWords.ofFault f ctx).sp (ThreadFaultWords.ofFault f ctx).lr
        (ThreadFaultWords.ofFault f ctx).spsr (ThreadFaultWords.ofFault f ctx).x0
        (ThreadFaultWords.ofFault f ctx).x1 (ThreadFaultWords.ofFault f ctx).x2
        (ThreadFaultWords.ofFault f ctx).x3 (ThreadFaultWords.ofFault f ctx).x4
        (ThreadFaultWords.ofFault f ctx).x5 (ThreadFaultWords.ofFault f ctx).x6
        (ThreadFaultWords.ofFault f ctx).x7 core =
      Architecture.stageWokenDelivery
        (performCallRendezvous st endpointId caller r next rid
          (faultMessage f ctx cap.badge) core) (some r) 0 := by
  rw [stageWokenDelivery_performCallRendezvous_held _ _ _ _ _ _ _ _ hNo hNe]
  have hNoX := propagatePipChainCrossCore_noResizeDue _ r core
    (storeCallRendezvousReady_noResizeDue st endpointId caller r (ThreadId.optCode next) rid
      core hNo)
  unfold performFaultCallDelivered
  have h := deliverFaultFrame_eq _ r (ThreadFaultWords.ofFault f ctx) f
    (ThreadFaultWords.fault?_ofFault f ctx) cap.badgeWord cap.badged hNoX
  rw [ThreadFaultWords.context_ofFault] at h
  exact h

/-- A delivery whose handler resolved and whose flow the policy admits, handed
the fault as words: the specification's delivery of the fault the words name
(`faultDeliverOnCore`).  Out of line, the fallback of `faultDeliverHandledWords`. -/
@[noinline] def faultDeliverHandledSpec (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (k : Nat) (flag : Bool) (w0 w1 : UInt64) (lk : KernelError)
    (ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) : SystemState :=
  let w := faultWordsOf k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7
  match w.fault? with
  | some f => (faultDeliverOnCore st tid f w.context c).1
  | none => st

/-- The blocking call's writes, each in its slot: the caller appended to the
send queue (`storeEndpointEnqueue`), then blocked on the call holding no
message (`storeSendBlock` for a call). -/
@[noinline] def storeCallBlock (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (tailCode : Nat) : SystemState :=
  (storeEndpointEnqueue st endpointId false caller (ThreadId.ofOptCode tailCode)).updateTcb caller
    (fun t => TCB.setIpcState { t with pendingMessage := none } (.blockedOnCall endpointId))

/-- **The guarded blocking call is the specification's block path**
(`sendBlock_inPlace_eq` for a call): with no receiver waiting, a caller that may
be enqueued and every write in its slot, the call is the in-place enqueue and
block, the caller descheduled and its capability's badge and grant bit
recorded. -/
theorem callBlock_inPlace_eq (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId)
    (payload : SendPayload) (executingCore : CoreId) (st : SystemState) (ep : Endpoint) (t : TCB)
    (hE : st.objects[endpointId]? = some (.endpoint ep))
    (hH : ep.receiveQ.head = none)
    (hR : st.objects[caller.toObjId]? = some (.tcb t))
    (hA : enqueueAdmits t = true)
    (hG : enqueuesInPlace st endpointId caller ep.sendQ.tail = true) :
    endpointCallOnCore endpointId caller payload executingCore st =
      (recordSendCap (removeRunnableOnCore (storeCallBlock st endpointId caller ep.sendTailCode)
        caller executingCore) caller payload.badge payload.grant, .ok none) := by
  obtain ⟨hEnq, hT, _, hL⟩ :=
    endpointEnqueue_inPlace_eq st endpointId ep false caller t ep.sendQ.tail hE rfl hR hA hG
  have hRes : caller.isReserved = false := by
    simp only [enqueuesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hG
    exact hG.1.1.1.1.1
  unfold endpointCallOnCore storeCallBlock
  rw [show SeLe4n.ThreadId.ofOptCode ep.sendTailCode = ep.sendQ.tail from rfl]
  simp only [(SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE, hH, hEnq]
  generalize storeEndpointEnqueue st endpointId false caller ep.sendQ.tail = S at hT hL ⊢
  have h1 : storeTcbIpcStateAndMessage S caller (.blockedOnCall endpointId) none =
      .ok (S.updateTcb caller
        (fun t => TCB.setIpcState { t with pendingMessage := none } (.blockedOnCall endpointId))) :=
    modifyTcb_eq_updateTcb _ hRes hT hL
  rw [h1]

/-- **The fault's blocking call, in place**: the faulting thread appended to the
handler endpoint's send queue and blocked on the call, descheduled, its
capability's badge recorded (`recordSendCapWords`); the fault is recorded after,
as the specification's delivery does. -/
@[noinline] def performFaultCallBlock (st : SystemState) (endpointId : SeLe4n.ObjId)
    (caller : SeLe4n.ThreadId) (tailCode : Nat) (cap : Capability) (core : CoreId) :
    SystemState :=
  recordSendCapWords (removeRunnableOnCore (storeCallBlock st endpointId caller tailCode)
    caller core) caller cap.badgeWord cap.badged false

/-- **The admitted delivery, handed words**: a fault whose handler is already
waiting with a reply object, every write of the call rendezvous staying in its
slot (`callWakesInPlace`), is delivered in place, its words past the fourth
into the handler's IPC buffer (`performFaultCallDelivered`), and recorded as
its words; a fault whose handler is not waiting, the faulting thread enqueued
and blocked in place (`performFaultCallBlock`), likewise; every other delivery
is the specification's (`faultDeliverHandledWords_eq`). -/
@[noinline] def faultDeliverHandledWords (st : SystemState) (tid : SeLe4n.ThreadId)
    (c : CoreId) (epId : SeLe4n.ObjId) (cap : Capability) (k : Nat) (flag : Bool)
    (w0 w1 : UInt64) (lk : KernelError) (ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) :
    SystemState :=
  match st.getEndpoint? epId with
  | some ep =>
    match ep.receiveQ.head with
    | some r =>
      match st.getTcb? r with
      | some rt =>
        match rt.pendingReceiveReply with
        | some rid =>
          if callWakesInPlace st epId tid r rt rid then
            recordFaultWords
              (performFaultCallDelivered st epId tid r rt.queueNextCode rid cap k flag w0 w1 lk
                ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7 c) tid
              (faultWordsOf k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7)
          else faultDeliverHandledSpec st tid c k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5
              x6 x7
        | none => faultDeliverHandledSpec st tid c k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5
              x6 x7
      | none => faultDeliverHandledSpec st tid c k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5
              x6 x7
    | none =>
      match st.getTcb? tid with
      | some t =>
        if enqueueAdmits t && enqueuesInPlaceCode st epId tid ep.sendTailCode then
          recordFaultWords (performFaultCallBlock st epId tid ep.sendTailCode cap c) tid
            (faultWordsOf k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7)
        else faultDeliverHandledSpec st tid c k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5
              x6 x7
      | none => faultDeliverHandledSpec st tid c k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5
              x6 x7
  | none => faultDeliverHandledSpec st tid c k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5
              x6 x7

/-- **The admitted delivery's words are the specification's**: for the handler
the thread's handler resolves to, `faultDeliverHandledWords` handed the words of
a fault and its context commits `faultDeliverOnCore`'s state. -/
theorem faultDeliverHandledWords_eq (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId)
    (f : Fault) (ctx : FaultContext) (tgt : FaultHandlerTarget)
    (hRes : resolveFaultHandler st tid = .ok tgt) :
    faultDeliverHandledWords st tid c tgt.endpoint tgt.cap
        (ThreadFaultWords.ofFault f ctx).kind (ThreadFaultWords.ofFault f ctx).flag
        (ThreadFaultWords.ofFault f ctx).word0 (ThreadFaultWords.ofFault f ctx).word1
        (ThreadFaultWords.ofFault f ctx).lookup (ThreadFaultWords.ofFault f ctx).ip
        (ThreadFaultWords.ofFault f ctx).sp (ThreadFaultWords.ofFault f ctx).lr
        (ThreadFaultWords.ofFault f ctx).spsr (ThreadFaultWords.ofFault f ctx).x0
        (ThreadFaultWords.ofFault f ctx).x1 (ThreadFaultWords.ofFault f ctx).x2
        (ThreadFaultWords.ofFault f ctx).x3 (ThreadFaultWords.ofFault f ctx).x4
        (ThreadFaultWords.ofFault f ctx).x5 (ThreadFaultWords.ofFault f ctx).x6
        (ThreadFaultWords.ofFault f ctx).x7 =
      (faultDeliverOnCore st tid f ctx c).1 := by
  have hSpec : faultDeliverHandledSpec st tid c
      (ThreadFaultWords.ofFault f ctx).kind (ThreadFaultWords.ofFault f ctx).flag
      (ThreadFaultWords.ofFault f ctx).word0 (ThreadFaultWords.ofFault f ctx).word1
      (ThreadFaultWords.ofFault f ctx).lookup (ThreadFaultWords.ofFault f ctx).ip
      (ThreadFaultWords.ofFault f ctx).sp (ThreadFaultWords.ofFault f ctx).lr
      (ThreadFaultWords.ofFault f ctx).spsr (ThreadFaultWords.ofFault f ctx).x0
      (ThreadFaultWords.ofFault f ctx).x1 (ThreadFaultWords.ofFault f ctx).x2
      (ThreadFaultWords.ofFault f ctx).x3 (ThreadFaultWords.ofFault f ctx).x4
      (ThreadFaultWords.ofFault f ctx).x5 (ThreadFaultWords.ofFault f ctx).x6
      (ThreadFaultWords.ofFault f ctx).x7 =
      (faultDeliverOnCore st tid f ctx c).1 := by
    simp only [faultDeliverHandledSpec, faultWordsOf_fields, ThreadFaultWords.fault?_ofFault,
      ThreadFaultWords.context_ofFault]
  generalize hw : ThreadFaultWords.ofFault f ctx = w at hSpec ⊢
  unfold faultDeliverHandledWords
  split
  · next ep hEp =>
    split
    · next r hH =>
      split
      · next rt hT =>
        split
        · next rid hRid =>
          split
          · next hIn =>
            have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
            have hT' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
            subst hw
            obtain ⟨sgi, hD⟩ := callDispatch_inPlace st tgt.endpoint ep tid r rt rid
              (.fault f ctx tgt.cap.badge) (faultMessage f ctx tgt.cap.badge)
              (SeLe4n.Slot.ofNat 0) c rfl
              (by unfold sendCapRequest; split <;> (try rfl); split <;> rfl)
              hE hH hT' hRid hIn
            unfold faultDeliverOnCore
            simp only [hRes, hEp, Option.bind_some, hH, hD]
            rw [recordPendingFault_eq_words, ← TCB.optCode_queueNext]
            have hIC : CapTransferSummary.installedCount { results := #[] } = 0 := rfl
            rw [hIC, ← performFaultCallDelivered_eq st tgt.endpoint tid r rt.queueNext rid tgt.cap
              f ctx c (callWakesInPlace_noResizeDue hIn) (callWakesInPlace_ne hIn),
              faultWordsOf_fields]
          · exact hSpec
        · exact hSpec
      · exact hSpec
    · next hH =>
      split
      · next t hT =>
        split
        · next hG =>
          simp only [Bool.and_eq_true] at hG
          obtain ⟨hA, hIn⟩ := hG
          rw [enqueuesInPlaceCode_eq] at hIn
          have hE := (SystemState.getEndpoint?_eq_some_iff _ _ _).mp hEp
          have hT' := (SystemState.getTcb?_eq_some_iff _ _ _).mp hT
          subst hw
          have hBlk := callBlock_inPlace_eq tgt.endpoint tid (.fault f ctx tgt.cap.badge) c st ep t
            hE hH hT' hA hIn
          have hNoR : (match st.getEndpoint? tgt.endpoint with
              | some ep => ep.receiveQ.head | none => none) = none := by
            simp only [hEp, hH]
          unfold faultDeliverOnCore
          simp only [hRes, hEp, Option.bind_some, hH]
          rw [endpointCallCrossCoreDispatch_no_receiver _ _ _ _ _ _ hNoR,
            endpointCallWithCapsOnCore_no_caps _ _ _ _ _ _
              (sendCapRequest_of_no_receiver _ _ _ _ (by simp only [hEp, Option.bind_some, hH])),
            hBlk]
          simp only [Except.map, Architecture.stageWokenDelivery_none]
          rw [recordPendingFault_eq_words]
          unfold performFaultCallBlock
          rw [recordSendCapWords_eq]
          rfl
        · exact hSpec
      · exact hSpec
  · exact hSpec

/-- **The flow-checked delivery, handed words** (`faultDeliverOnCoreChecked`,
`faultDeliverCheckedWords_eq`): the handler resolved in continuation form, the
flow gate, and on every refusal the suspend with the fault recorded as words. -/
@[noinline] def faultDeliverCheckedWords (lctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (k : Nat) (flag : Bool) (w0 w1 : UInt64)
    (lk : KernelError) (ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) : SystemState :=
  resolveFaultHandlerK st tid
    (fun _ => recordFaultWords (faultSuspendOnCore st tid c) tid
      (faultWordsOf k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7))
    (fun epId cap =>
      if endpointFlowGate lctx epId (lctx.threadLabelOf tid) (lctx.endpointLabelOf epId) then
        faultDeliverHandledWords st tid c epId cap k flag w0 w1 lk ip sp lr spsr
          x0 x1 x2 x3 x4 x5 x6 x7
      else recordFaultWords (faultSuspendOnCore st tid c) tid
        (faultWordsOf k flag w0 w1 lk ip sp lr spsr x0 x1 x2 x3 x4 x5 x6 x7))

/-- `faultDeliverCheckedWords` handed the words of a fault and a context. -/
@[inline] def faultDeliverCheckedOf (lctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (c : CoreId) (w : ThreadFaultWords) : SystemState :=
  faultDeliverCheckedWords lctx st tid c w.kind w.flag w.word0 w.word1 w.lookup w.ip w.sp w.lr
    w.spsr w.x0 w.x1 w.x2 w.x3 w.x4 w.x5 w.x6 w.x7

/-- **The words' delivery is the specification's** for the words a fault and its
context are stored as. -/
theorem faultDeliverCheckedWords_eq (lctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId) (f : Fault) (ctx : FaultContext) (c : CoreId) :
    faultDeliverCheckedOf lctx st tid c (ThreadFaultWords.ofFault f ctx) =
      (faultDeliverOnCoreChecked lctx st tid f ctx c).1 := by
  unfold faultDeliverCheckedOf faultDeliverCheckedWords
  rw [faultWordsOf_fields, resolveFaultHandlerK_eq]
  unfold faultDeliverOnCoreChecked
  cases hRes : resolveFaultHandler st tid with
  | error _ => rfl
  | ok tgt =>
    simp only []
    split
    · exact faultDeliverHandledWords_eq st tid c f ctx tgt hRes
    · rfl

/-- The words of a fault and a context are its own words beside the context's:
the fault's part does not depend on the context. -/
theorem ofFault_eq_words (f : Fault) (ctx : FaultContext) :
    ThreadFaultWords.ofFault f ctx =
      faultWordsOf (ThreadFaultWords.ofFault f {}).kind (ThreadFaultWords.ofFault f {}).flag
        (ThreadFaultWords.ofFault f {}).word0 (ThreadFaultWords.ofFault f {}).word1
        (ThreadFaultWords.ofFault f {}).lookup ctx.faultIP ctx.sp ctx.lr ctx.spsr
        ctx.x0 ctx.x1 ctx.x2 ctx.x3 ctx.x4 ctx.x5 ctx.x6 ctx.x7 := by
  cases f <;> rfl

-- ============================================================================
-- §3  The delivery from a trap's words
-- ============================================================================

/-- **The trap's delivery, handed words** (`faultDeliveredState_eq_words`): the
window spilled into the faulting thread, the context read off the spilled
registers as the specification's `faultContextOfThread` reads it, and the
checked delivery handed the fault's words and the context's. -/
@[inline] def faultDeliveredWords (lctx : LabelingContext) (st : SystemState) (k : Nat)
    (flag : Bool) (w0 w1 : UInt64) (lk : KernelError) (ip spsr : UInt64)
    (w : FaultRegisterWindow) (c : CoreId) (tid : SeLe4n.ThreadId) : SystemState :=
  let stRegs := writeFaultRegistersToTcb st tid w
  match stRegs.getTcb? tid with
  | some t =>
    faultDeliverCheckedWords lctx stRegs tid c k flag w0 w1 lk ip t.registerContext.sp
      t.registerContext.x30 spsr t.registerContext.x0 t.registerContext.x1
      t.registerContext.x2 t.registerContext.x3 t.registerContext.x4 t.registerContext.x5
      t.registerContext.x6 t.registerContext.x7
  | none => faultDeliverCheckedWords lctx stRegs tid c k flag w0 w1 lk ip 0 0 spsr 0 0 0 0 0 0 0 0

theorem faultDeliveredWords_eq (lctx : LabelingContext) (st : SystemState) (f : Fault)
    (ip spsr : UInt64) (w : FaultRegisterWindow) (c : CoreId) (tid : SeLe4n.ThreadId) :
    faultDeliveredWords lctx st (ThreadFaultWords.ofFault f {}).kind
        (ThreadFaultWords.ofFault f {}).flag (ThreadFaultWords.ofFault f {}).word0
        (ThreadFaultWords.ofFault f {}).word1 (ThreadFaultWords.ofFault f {}).lookup ip spsr w c
        tid =
      (faultDeliverOnCoreChecked lctx (writeFaultRegistersToTcb st tid w) tid f
        (faultContextOfThread (writeFaultRegistersToTcb st tid w) tid ip spsr) c).1 := by
  rw [← faultDeliverCheckedWords_eq]
  unfold faultDeliveredWords faultContextOfThread faultDeliverCheckedOf
  dsimp only
  cases (writeFaultRegistersToTcb st tid w).getTcb? tid <;> cases f <;> rfl

/-- The kind code of the fault a syndrome names: `1` for an abort, `4` for an
alignment fault or an unmodelled class, `0` where `faultOfExceptionContext`
names none (`faultOfExceptionContext_words`). -/
@[inline] def faultKindOfEsr (esr : UInt64) : Nat :=
  match classifySynchronousExceptionOfEsr esr with
  | .dataAbort | .instrAbort => 1
  | .pcAlignment | .spAlignment | .unknownReason => 4
  | .svc | .kernelAbort | .fpAccess => 0

/-- The first word of that fault: an abort's address, any other's class. -/
@[inline] def faultWord0OfEsr (esr far : UInt64) : UInt64 :=
  match classifySynchronousExceptionOfEsr esr with
  | .dataAbort | .instrAbort => far
  | _ => extractExceptionClass esr

/-- Its flag: set for an instruction abort. -/
@[inline] def faultFlagOfEsr (esr : UInt64) : Bool :=
  match classifySynchronousExceptionOfEsr esr with
  | .instrAbort => true
  | _ => false

theorem faultOfExceptionContext_none_iff_kind (ectx : ExceptionContext) :
    faultOfExceptionContext ectx = none ↔ faultKindOfEsr ectx.esr = 0 := by
  unfold faultOfExceptionContext faultKindOfEsr classifySynchronousException
  cases classifySynchronousExceptionOfEsr ectx.esr <;> simp

/-- **A fault the syndrome names is stored as the syndrome's words.** -/
theorem faultOfExceptionContext_words (ectx : ExceptionContext) (f : Fault)
    (h : faultOfExceptionContext ectx = some f) :
    (ThreadFaultWords.ofFault f {}).kind = faultKindOfEsr ectx.esr ∧
    (ThreadFaultWords.ofFault f {}).flag = faultFlagOfEsr ectx.esr ∧
    (ThreadFaultWords.ofFault f {}).word0 = faultWord0OfEsr ectx.esr ectx.far ∧
    (ThreadFaultWords.ofFault f {}).word1 = ectx.esr ∧
    (ThreadFaultWords.ofFault f {}).lookup = .invalidCapability := by
  unfold faultOfExceptionContext classifySynchronousException at h
  unfold faultKindOfEsr faultFlagOfEsr faultWord0OfEsr
  cases hc : classifySynchronousExceptionOfEsr ectx.esr <;> rw [hc] at h <;> cases h <;>
    exact ⟨rfl, rfl, rfl, rfl, rfl⟩

-- ============================================================================
-- §4  The fault reply, in place
-- ============================================================================

/-- The reply's writes with no message (`storeReplyRendezvous` at
`IpcMessage.empty`), written out so the empty message the woken thread holds is
the one constant cell, never a `some` built per reply
(`storeFaultReplyRendezvous_eq`). -/
@[noinline] def storeFaultReplyRendezvous (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) : SystemState :=
  let s1 := st.updateTcb c (callReceiverTcb IpcMessage.empty)
  let s2 := enqueueRunnableOnCore s1 (determineTargetCore s1 c) c
  let s3 := (s2.modifyObject rid.toObjId replyConsumedObject).updateTcb c
    (fun t => { t with replyObjectCode := 0 })
  s3.unlinkReplyWaiter c server

theorem storeFaultReplyRendezvous_eq (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    storeFaultReplyRendezvous st c server rid =
      storeReplyRendezvous st c server rid IpcMessage.empty := rfl

/-- **The fault reply's restart, in place** (`faultReplyTransferChecked_inPlace`):
the reply's writes with no message (`storeFaultReplyRendezvous`), the server's
priority walk, then the answered thread's
restart frame, its saved context's words, written over its registers and its
fault cleared (`applyFaultRestart`).  The frame's words are handed in from the
thread's fault words, so neither the fault nor its context is decoded. -/
@[noinline] def performFaultReplyRestart (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (core : CoreId) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) :
    SystemState :=
  applyFaultRestart (PriorityInheritance.propagatePipChainCrossCore
      (storeFaultReplyRendezvous st c server rid) server core).1 c
    { pc := ip, sp := sp, lr := lr, x0 := x0, x1 := x1, x2 := x2, x3 := x3,
      x4 := x4, x5 := x5, x6 := x6, x7 := x7 }

/-- **The fault reply, in place**: a reply to a thread blocked on it carrying a
VM or capability fault, every write in its slot (`replyWakesInPlace`), is
seL4's `handleFaultReply` for those two faults, the restart at the faulting
instruction with the saved registers whatever the reply says: the
specification's fault branch (`faultReplyOnCore`) commits
`performFaultReplyRestart`'s state. -/
theorem faultReplyTransferChecked_inPlace (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (msg : IpcMessage) (core : CoreId)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyWakesInPlace st c ct rid = true)
    (hK : (ct.faultKind == 1 || ct.faultKind == 2) = true) :
    replyTransferOnCoreChecked ctx replier c mi regs msg core st =
      .ok ((), performFaultReplyRestart st c server rid core ct.faultIp ct.faultSp ct.faultLr
        ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6
        ct.faultX7) := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨f, hPF, hDec⟩ : ∃ f, ct.pendingFault =
      some { fault := f, context := ct.faultWords.context } ∧
      decodeFaultReply f ct.faultWords.context mi regs =
        .restart (faultRestartFrameOfContext ct.faultWords.context) := by
    simp only [Bool.or_eq_true, beq_iff_eq] at hK
    rcases hK with hK | hK
    · exact ⟨.vmFault ct.faultWord0 ct.faultWord1 ct.faultFlag, by simp only [TCB.pendingFault,
        ThreadFaultWords.decode, ThreadFaultWords.fault?, TCB.faultWords, hK], rfl⟩
    · exact ⟨.capFault ct.faultWord0 ct.faultFlag ct.faultLookup, by simp only [TCB.pendingFault,
        ThreadFaultWords.decode, ThreadFaultWords.fault?, TCB.faultWords, hK], rfl⟩
  have hHas : threadHasPendingFault st c = true := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_some]
  obtain ⟨sgi, hD⟩ := replyDispatch_inPlace st replier c server ct ep rid IpcMessage.empty core
    (by simp [IpcMessage.empty]) hT hIpc hRO hSRes hG
  unfold replyTransferOnCoreChecked
  rw [hHas]
  simp only [↓reduceIte]
  unfold faultReplyOnCore
  rw [hTc]
  simp only [hPF, hD, hDec]
  rfl

end SeLe4n.Kernel
