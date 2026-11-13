-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.LongReceiveInPlace
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDonatingInPlace

/-!
# A receive that takes a queued caller and is donated its SchedContext, in place

seL4-MCS's `receiveIPC` taking a caller blocked on the endpoint: the caller is
popped and blocked on the reply, `reply_push` links it to the receiver's reply
object, and, when the receiver is passive (no SchedContext of its own) and the
caller runs on one, `schedContext_donate` hands the caller's context to the
receiver; the receiver's priority walk follows.  When every check of the take
and of the donation passes on the pre-state (`receiveCallDonatesInPlace`), the
take's writes are `storeReceiveCallReady`'s, the donation's each land in their
slot (`donateSchedContextInPlace`), the replenishment migrates between the
caller's and the receiver's home cores (both read off the pre-state), and a
message of at most four words is written straight into the receiver's saved
registers (`performReceiveCallDonatingDelivered`): the receive builds no
object, no message and no table (`receiveCallDonatingTake_delivered`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency
open Architecture.RegisterDecode

/-- **A receive taking a queued caller and donated its context writes only its
slots**: the take's (`receiveCallTakesReplyInPlace`) and the donation's
(`callDonationReady`, the caller the donor and the receiver the donee).  Read
off the codes, so the test builds nothing. -/
@[inline] def receiveCallDonatesInPlace (st : SystemState) (endpointId : SeLe4n.ObjId)
    (receiver s : SeLe4n.ThreadId) (sTcb : TCB) (rid : SeLe4n.ReplyId) : Bool :=
  receiveCallTakesReplyInPlace st endpointId receiver s sTcb rid &&
  (match st.getTcb? receiver with
   | some rt => callDonationReady st s receiver sTcb rt rid
   | none => false)

/-- **The receive's take of a donating caller within the inline words,
delivered**: the caller popped, blocked on the reply and linked, the receiver
made ready holding no message, the caller's context donated to the receiver,
its replenishment migrated from `donorHome` to `doneeHome`, the receiver's
priority walk, then the caller's inline words, read from its saved registers
`rf`, written into the receiver's saved registers. -/
@[noinline] def performReceiveCallDonatingDelivered (st : SystemState)
    (endpointId : SeLe4n.ObjId) (s : SeLe4n.ThreadId) (nextCode : Nat)
    (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId)
    (donorHome doneeHome : CoreId) (core : CoreId) (rf : SeLe4n.RegisterFile) (len : Nat)
    (badgeWord : SeLe4n.Badge) (badged : Bool) : SystemState :=
  let Y := (PriorityInheritance.propagatePipChainCrossCore
      (migrateSchedContextReplenishment
        (donateSchedContextInPlace (storeReceiveCallReady st endpointId s nextCode receiver rid)
          s receiver scId) scId donorHome doneeHome) receiver core).1
  writeDeliveredFrameIfReady Y receiver
    (Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout rf len badgeWord badged)
    (fun _ => Y.mapTcbInPlace receiver (holdMessage
      { registers := Architecture.regMessageBody SeLe4n.arm64DefaultLayout rf len,
        badge := SeLe4n.Badge.opt badgeWord badged }))

/-- **The receive's take of a donating caller within the inline words,
delivered, is the specification's**: under `receiveCallDonatesInPlace`, for a
caller blocked by a routed capability-free call of at most four words, the
WithCaps receive installs nothing and commits the take, the rendezvous donates
the caller's context to the receiver (`donateSchedContext`, in place) and
migrates its replenishment between the two threads' home cores, which the take
leaves where the pre-state had them, then runs the receiver's priority walk,
and staging the receiver's message writes `performReceiveCallDonatingDelivered`'s
state. -/
theorem receiveCallDonatingTake_delivered (st : SystemState) (endpointId : SeLe4n.ObjId)
    (ep : Endpoint) (receiver : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (core : CoreId)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hE : st.objects[endpointId]? = some (.endpoint ep)) (hH : ep.sendQ.head = some s)
    (hT : st.objects[s.toObjId]? = some (.tcb sTcb))
    (hG : receiveCallDonatesInPlace st endpointId receiver s sTcb rid = true)
    (hF : sTcb.ipcFaultSend = false)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout sTcb.registerContext 32 =
      .call capAddr mi) :
    endpointReceiveDualWithCapsOnCore endpointId receiver (some rid) core st =
        (receiveCallTakeState st endpointId s sTcb receiver rid,
          .ok (s, { results := #[] }, none)) ∧
      applyReceiveRendezvousHandoff (receiveCallTakeState st endpointId s sTcb receiver rid)
          receiver s core =
        .ok (applyReceiverPipHandoff (migrateSchedContextReplenishment
          (donateSchedContextInPlace (receiveCallTakeState st endpointId s sTcb receiver rid)
            s receiver ⟨sTcb.scBindingScCode - 1⟩) ⟨sTcb.scBindingScCode - 1⟩
          (determineTargetCore st s) (determineTargetCore st receiver)) receiver core) ∧
      Architecture.stageDeliveredMessage (Architecture.stageWokenSendCompletion
          (applyReceiverPipHandoff (migrateSchedContextReplenishment
            (donateSchedContextInPlace (receiveCallTakeState st endpointId s sTcb receiver rid)
              s receiver ⟨sTcb.scBindingScCode - 1⟩) ⟨sTcb.scBindingScCode - 1⟩
            (determineTargetCore st s) (determineTargetCore st receiver)) receiver core)
          (some s)) receiver 0 =
        performReceiveCallDonatingDelivered st endpointId s sTcb.queueNextCode receiver rid
          ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s) (determineTargetCore st receiver)
          core sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
          sTcb.ipcBadged ∧
      rendezvousDequeuedCall (receiveCallTakeState st endpointId s sTcb receiver rid) s = true ∧
      applyRendezvousCallDonation (receiveCallTakeState st endpointId s sTcb receiver rid)
          receiver s =
        .ok (migrateSchedContextReplenishment
          (donateSchedContextInPlace (receiveCallTakeState st endpointId s sTcb receiver rid)
            s receiver ⟨sTcb.scBindingScCode - 1⟩) ⟨sTcb.scBindingScCode - 1⟩
          (determineTargetCore st s) (determineTargetCore st receiver)) := by
  have hG' := hG
  simp only [receiveCallDonatesInPlace, Bool.and_eq_true] at hG'
  obtain ⟨hTR, hDR⟩ := hG'
  obtain ⟨hTake, hIpc, hBs, hBr, hF1, hF2, hF3, hF4, ⟨ct', hTc', hro'⟩, hDs, hDr⟩ :=
    receiveCallTake_inPlace_facts st endpointId ep receiver rid core s sTcb hE hH hT hTR
  have hTR' := hTR
  simp only [receiveCallTakesReplyInPlace, Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne,
    ne_eq] at hTR'
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hSG, hRRes⟩, hRS⟩, _⟩, hLR⟩, hFR⟩, hLQ⟩, hFQ⟩, _⟩, _⟩, hRp⟩, _⟩ := hTR'
  have hSG' := hSG
  simp only [sendWakesInPlace, Bool.and_eq_true, Bool.not_eq_true'] at hSG'
  obtain ⟨⟨⟨⟨⟨hSRes, _⟩, hFE⟩, hLH⟩, hFH⟩, _⟩ := hSG'
  have hNo : st.objects.noResizeDue := RHTable.noResizeDue_of_findsInPlace hFE
  have hTs : st.getTcb? s = some sTcb := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  split at hDR
  case h_2 => cases hDR
  rename_i rt hRTo
  split at hRp
  case h_2 => cases hRp
  rename_i rp hRp0
  have hFree := hRp
  simp only [Reply.isFree, Bool.and_eq_true, Option.isNone_iff_eq_none] at hFree
  obtain ⟨⟨-, hRpPrev⟩, hRpNext⟩ := hFree
  unfold callDonationReady at hDR
  rw [Bool.and_eq_true, beq_iff_eq] at hDR
  obtain ⟨hRB, hDR⟩ := hDR
  obtain ⟨k, hk⟩ : ∃ k, sTcb.scBindingScCode = k + 1 := by
    cases h : sTcb.scBindingScCode with
    | zero => rw [h] at hDR; cases hDR
    | succ k => exact ⟨k, rfl⟩
  rw [hk] at hDR
  simp only [Bool.and_eq_true] at hDR
  obtain ⟨⟨hLsc, hFsc⟩, hScM⟩ := hDR
  obtain ⟨sc, hSc⟩ : ∃ sc, st.getSchedContext? ⟨k⟩ = some sc := by
    cases h : st.getSchedContext? ⟨k⟩ with
    | none => rw [h] at hScM; cases hScM
    | some sc => exact ⟨sc, rfl⟩
  rw [hSc] at hScM
  simp only [Bool.and_eq_true, beq_iff_eq] at hScM
  obtain ⟨hBT, hOldM⟩ := hScM
  have hScId : (⟨sTcb.scBindingScCode - 1⟩ : SeLe4n.SchedContextId) = ⟨k⟩ := by rw [hk]; rfl
  rw [hScId]
  generalize hT' : receiveCallTakeState st endpointId s sTcb receiver rid = T at *
  have hR' := hF4 rp hRp0
  have hRpO : st.objects[rid.toObjId]? = some (.reply rp) :=
    (SystemState.getReply?_eq_some_iff _ _ _).mp hRp0
  have hScO : st.objects[(SeLe4n.SchedContextId.toObjId ⟨k⟩)]? = some (.schedContext sc) :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hScR : (SeLe4n.SchedContextId.toObjId ⟨k⟩) ≠ rid.toObjId := fun h => by
    rw [h, hRpO] at hScO; cases hScO
  have hSc' : T.getSchedContext? ⟨k⟩ = some sc :=
    (SystemState.getSchedContext?_eq_some_iff _ _ _).mpr
      (hF3 _ _ (fun _ h => by cases h) (fun _ h => by cases h) hScR hScO)
  have hB : sc.boundThread = some s := by
    show SeLe4n.ThreadId.ofOptCode sc.boundThreadCode = some s
    rw [hBT]; rfl
  have hC' : lookupTcb T s = some ct' := by
    unfold lookupTcb; simp only [hSRes, Bool.false_eq_true, ↓reduceIte, hTc']
  have hCaller : ({ rp with callerCode := SeLe4n.ThreadId.optCode (some s) } : Reply).caller
      ≠ none := by
    show SeLe4n.ThreadId.ofOptCode (SeLe4n.ThreadId.optCode (some s)) ≠ none
    rw [SeLe4n.ThreadId.ofOptCode_optCode]; exact Option.some_ne_none _
  have hNe : sc.scReply ≠ some rid := by
    revert hOldM
    cases sc.scReply with
    | none => intro _ h; cases h
    | some old =>
      simp only [Bool.and_eq_true, bne_iff_ne, ne_eq]
      intro h e; exact h.1.1.1 (Option.some.inj e)
  have hOld : ∀ old, sc.scReply = some old →
      (∃ oR, T.getReply? old = some oR) ∧
      storeLeavesIndexAndTypes T old.toObjId .reply = true ∧
      T.objects.findsInPlace old.toObjId = true := by
    intro old hso
    rw [hso] at hOldM
    simp only [Bool.and_eq_true, bne_iff_ne, ne_eq, Option.isSome_iff_exists] at hOldM
    obtain ⟨⟨⟨hOR, hOL⟩, hOF⟩, oR, hoR⟩ := hOldM
    have hON : old.toObjId ≠ rid.toObjId := fun h => hOR (SeLe4n.ReplyId.toObjId_injective _ _ h)
    exact ⟨⟨oR, (SystemState.getReply?_eq_some_iff _ _ _).mpr
        (hF3 _ _ (fun _ h => by cases h) (fun _ h => by cases h) hON
          ((SystemState.getReply?_eq_some_iff _ _ _).mp hoR))⟩,
      hF2 hOL, (hF1 _).trans hOF⟩
  obtain ⟨rt', hTr', hbr'⟩ := Option.map_eq_some_iff.mp (hBr.trans (by rw [hRTo]; rfl))
  have hDon := donateSchedContext_eq_inPlace T s receiver ⟨k⟩ sc ct' rt' rid _ hSc' hB hC' hro'
    hR' hRpPrev hRpNext hCaller hNe hOld hTr' hRRes (hF2 hLsc) ((hF1 _).trans hFsc) (hF2 hLQ)
    ((hF1 _).trans hFQ) (hF2 hLH) ((hF1 _).trans hFH) (hF2 hLR)
  have hDonId : callDonationSchedContext? T s receiver = some ⟨k⟩ := by
    rw [callDonationSchedContext?_congr (s := st) hBs hBr, callDonationSchedContext?_eq_bindings]
    simp only [lookupTcb, hRRes, hSRes, Bool.false_eq_true, ↓reduceIte, hRTo, hTs,
      Option.map_some]
    show donationOfBindings (some (SchedContextBinding.ofCodes rt.scBindingScCode
      rt.scBindingOwnerCode)) (some (SchedContextBinding.ofCodes sTcb.scBindingScCode
      sTcb.scBindingOwnerCode)) = _
    rw [hRB, hk]
    cases sTcb.scBindingOwnerCode <;> rfl
  obtain ⟨x, hx, hxI⟩ := Option.map_eq_some_iff.mp hIpc
  have hCall : rendezvousDequeuedCall T s = true := by
    unfold rendezvousDequeuedCall
    simp only [lookupTcb, hSRes, Bool.false_eq_true, ↓reduceIte, hx, hxI]
  obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff s).mpr hSRes)
  obtain ⟨rv, hrv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff receiver).mpr hRRes)
  have hsv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hsv
  have hrv' := SeLe4n.ThreadId.toValid?_some_val_eq _ _ hrv
  have hDonE : applyRendezvousCallDonation T receiver s =
      .ok (migrateSchedContextReplenishment (donateSchedContextInPlace T s receiver ⟨k⟩) ⟨k⟩
        (determineTargetCore st s) (determineTargetCore st receiver)) := by
    unfold applyRendezvousCallDonation
    simp only [hsv, hrv]
    unfold applyCallDonationOnCore
    rw [applyCallDonation_characterisation, hsv', hrv', hDonId]
    dsimp only
    rw [hDon]
    simp only [hDs, hDr]
  refine ⟨?_, ?_, ?_, hCall, hDonE⟩
  · have hSnd : receiveRendezvousSender? st endpointId = some s := by
      simp only [receiveRendezvousSender?, (SystemState.getEndpoint?_eq_some_iff _ _ _).mpr hE,
        Option.bind_some, hH]
    have hReq : receiveCapRequest st endpointId = none := by
      unfold receiveCapRequest
      rw [hSnd]
      simp only [hTs]
      exact (blockedSender_of_routedCall st s sTcb capAddr mi hR hF).1
    unfold endpointReceiveDualWithCapsOnCore
    rw [hTake]
    simp only [hSnd, hReq, Option.isNone_some, Bool.false_eq_true, ↓reduceIte]
    rfl
  · unfold applyReceiveRendezvousHandoff
    rw [applyReceiveRendezvousDonation_of_call _ _ _ hCall, hDonE]
    simp only [hCall, ↓reduceIte]
  · have hNoS := storeReceiveCallReady_noResizeDue st endpointId s sTcb.queueNextCode receiver
      rid hNo
    have hNo4 : T.objects.noResizeDue := by
      rw [← hT']
      unfold receiveCallTakeState
      exact linkReplyWaiter_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _
        (updateTcb_noResizeDue _ _ _ (modifyObject_noResizeDue _ _ _ (updateTcb_noResizeDue _ _ _
          (storePopHead_noResizeDue _ _ _ _ _ hNo)))))
    have hNoD := migrateSchedContextReplenishment_noResizeDue _ ⟨k⟩ (determineTargetCore st s)
      (determineTargetCore st receiver) (donateSchedContextInPlace_noResizeDue _ s receiver ⟨k⟩ hNo4)
    obtain ⟨x1, hx1, e1⟩ := donateSchedContextInPlace_ipcStateCarried T s receiver ⟨k⟩ hNo4 s x hx
    have hx2 : (migrateSchedContextReplenishment (donateSchedContextInPlace T s receiver ⟨k⟩) ⟨k⟩
        (determineTargetCore st s) (determineTargetCore st receiver)).getTcb? s = some x1 :=
      (migrateSchedContextReplenishment_getTcb? _ _ _ _ _).trans hx1
    obtain ⟨x', hx', hxI'⟩ := propagatePipChainCrossCore_ipcStateCarried _ receiver core hNoD s x1
      hx2
    unfold applyReceiverPipHandoff
    rw [Architecture.stageWokenSendCompletion_id_when_not_ready _ s x' hx'
      (by rw [hxI', e1, hxI]; simp)]
    rw [← hT', receiveCallTakeState_eq_hold _ _ _ _ _ _ hNo,
      donateSchedContextInPlace_msg _ _ _ _ _ _ _ _ hNoS hRS,
      migrateSchedContextReplenishment_mapTcbInPlace]
    have hNoD' := migrateSchedContextReplenishment_noResizeDue _ ⟨k⟩ (determineTargetCore st s)
      (determineTargetCore st receiver) (donateSchedContextInPlace_noResizeDue _ s receiver ⟨k⟩ hNoS)
    rw [propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoD']
    have hNoY := propagatePipChainCrossCore_noResizeDue _ receiver core hNoD'
    have hSz : (blockedSenderMessage (storePopHead st endpointId false s sTcb.queueNext) s
        sTcb).registers.size ≤ 4 := by
      rw [(blockedSender_of_routedCall _ s sTcb capAddr mi hR hF).2]
      simp only [Architecture.regMessageBody_size, Architecture.regMessageLength]
      have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
      omega
    rw [stageDeliveredMessage_holdMessage _ _ _ hNoY hSz,
      (blockedSender_of_routedCall _ s sTcb capAddr mi hR hF).2,
      Architecture.returnFrameOfMessage_regMessageBody, TCB.ipcBadgeView_eq_opt]
    unfold performReceiveCallDonatingDelivered
    rw [Architecture.regMessageFrameW_eq]
