-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.FaultAnswerInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCapsDelivered

/-!
# A fault answered in place by a long reply

A fault handler answering with more than four words (a long `Reply` or
`ReplyRecv`) supplies its restart words past the fourth from its IPC buffer, as
seL4's `copyMRsFaultReply` reads them.  The answer is `performFaultAnswer`'s
with each reply word read by `faultReplyWordLong`: word `i` of the
replier's inline registers below four, its IPC-buffer overflow slot
`i - 4` past them, read in the state the answer runs on.  Every write
before the answer keeps every buffer read (`ipcBufferReadsAgree`), so those are
the words the specification's message holds.

Each shape the short fault answer runs in place has its long form here:

* `.reply` waking its caller in its slots (`performFaultReplyAnswerLong`,
  `faultReplyTransferChecked_inPlaceLong`), on a donated reply
  (`performFaultReplyDonatedAnswerLong`,
  `faultReplyTransferChecked_donated_inPlaceLong`) and to a caller recording
  no server (`performFaultReplyUnheldAnswerLong`,
  `faultReplyTransferChecked_unheld_inPlaceLong`);
* `.replyRecv` blocking on the endpoint after any reply arm
  (`performReplyRecvArmFaultAnswerLong`, `ReplyRecvBlockComposed.lean`).

None builds the fault record, the reply's message, the outcome or a frame.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- Reply word `i` of a long fault reply, or the faulted thread's own
`fallback` past the `len` words the reply supplied: word `i` of the
replier `s`'s message, its inline register below four and its IPC-buffer
overflow slot past them, read in `X`.  Out of line, reading `X` borrowed, so it
returns a bare machine word and the state is not held across the restart. -/
@[noinline] def faultReplyWordLong (X : @& SystemState) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len i : Nat) (fallback : UInt64) : UInt64 :=
  if i < len then
    (if i < 4 then Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf i
     else overflowWordAt X s (i - 4))
  else fallback

/-- **The fault answer to a long reply** -- `performFaultAnswer` with each reply
word read by `faultReplyWordLong`. -/
@[noinline] def performFaultAnswerLong (X : SystemState) (c : SeLe4n.ThreadId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) : SystemState :=
  if kind == 1 || kind == 2 then
    applyFaultRestart X c
      { pc := ip, sp := sp, lr := lr, x0 := x0, x1 := x1, x2 := x2, x3 := x3,
        x4 := x4, x5 := x5, x6 := x6, x7 := x7 }
  else if label != 0 then faultAbandonOnCore X c (faultAbandonCore X c)
  else if kind == 3 then
    applyFaultRestart X c
      { pc := faultReplyWordLong X s rf len 8 ip,
        sp := faultReplyWordLong X s rf len 9 sp,
        lr := faultReplyWordLong X s rf len 10 lr,
        x0 := faultReplyWordLong X s rf len 0 x0, x1 := faultReplyWordLong X s rf len 1 x1,
        x2 := faultReplyWordLong X s rf len 2 x2, x3 := faultReplyWordLong X s rf len 3 x3,
        x4 := faultReplyWordLong X s rf len 4 x4, x5 := faultReplyWordLong X s rf len 5 x5,
        x6 := faultReplyWordLong X s rf len 6 x6, x7 := faultReplyWordLong X s rf len 7 x7 }
  else
    applyFaultRestart X c
      { pc := faultReplyWordLong X s rf len 0 ip, sp := faultReplyWordLong X s rf len 1 sp,
        lr := lr, x0 := x0, x1 := x1, x2 := x2, x3 := x3,
        x4 := x4, x5 := x5, x6 := x6, x7 := x7 }

/-- **The long fault answer read from words is the decoded one**: for a caller
`ct` carrying fault `tf`, and a reply whose words, past the faulted thread's
own, are `faultReplyWordLong`'s (`hR`), applying the decoded outcome is
`performFaultAnswerLong` of the caller's fault words and the reply's label. -/
theorem faultReplyApplyOnCore_decode_eq_performFaultAnswerLong (X : SystemState)
    (c : SeLe4n.ThreadId) (ct : TCB) (tf : ThreadFault) (hPF : ct.pendingFault = some tf)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat)
    (hR : ∀ i fb, Architecture.replyWordOr mi regs i fb = faultReplyWordLong X s rf len i fb) :
    faultReplyApplyOnCore X c (Architecture.decodeFaultReply tf.fault tf.context mi regs) =
      performFaultAnswerLong X c ct.faultKind mi.label ct.faultIp ct.faultSp ct.faultLr
        ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6
        ct.faultX7 s rf len := by
  obtain ⟨f, ctx⟩ := tf
  have hC : ctx = ct.faultWords.context := ThreadFaultWords.decode_context hPF
  subst hC
  simp only [TCB.pendingFault, ThreadFaultWords.decode, ThreadFaultWords.fault?] at hPF
  unfold performFaultAnswerLong
  rcases hk : ct.faultKind with _ | _ | _ | _ | k
  · simp only [TCB.faultWords, hk] at hPF; cases hPF
  · simp only [TCB.faultWords, hk] at hPF
    cases hPF
    rfl
  · simp only [TCB.faultWords, hk] at hPF
    cases hPF
    rfl
  · simp only [TCB.faultWords, hk] at hPF
    cases hPF
    by_cases hl : mi.label = 0
    · simp only [Architecture.decodeFaultReply, hl, ne_eq, not_true_eq_false, ↓reduceIte, hR,
        faultReplyApplyOnCore, Architecture.faultRestartFrameOfContext, ThreadFaultWords.context,
        FaultContext.gprAt]
      rfl
    · simp only [Architecture.decodeFaultReply, hl, ne_eq, not_false_eq_true, ↓reduceIte,
        faultReplyApplyOnCore]
      simp [hl]
  · simp only [TCB.faultWords, hk] at hPF
    cases hPF
    by_cases hl : mi.label = 0
    · simp only [Architecture.decodeFaultReply, hl, ne_eq, not_true_eq_false, ↓reduceIte, hR,
        faultReplyApplyOnCore, Architecture.faultRestartFrameOfContext, ThreadFaultWords.context,
        FaultContext.gprAt]
      simp
    · simp only [Architecture.decodeFaultReply, hl, ne_eq, not_false_eq_true, ↓reduceIte,
        faultReplyApplyOnCore]
      simp [hl]

/-! ## The long reply's words -/

theorem overflowRegsFrom_getElem? (S : SystemState) (s : SeLe4n.ThreadId) (i n j : Nat) :
    (overflowRegsFrom S s i n)[j]? =
      if j < n then some (⟨overflowWordAt S s (i + j)⟩ : SeLe4n.RegValue) else none := by
  rw [overflowRegsFrom_eq_map, List.getElem?_map]
  by_cases h : j < n
  · rw [if_pos h]
    simp [h]
  · rw [List.getElem?_eq_none (by simp only [List.length_range']; omega), if_neg h]
    rfl

/-- Word `i` of a long reply's words (`longSendMessage`'s registers) is the replier's inline
register below four and its overflow slot `i - 4` past them. -/
theorem wordAt_longSendRegs (S : SystemState) (s : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile)
    (len i : Nat) (hi : i < len) :
    Architecture.wordAt (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
      (overflowRegsFrom S s 0 (len - 4)).toArray) i =
      if i < 4 then Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf i
      else overflowWordAt S s (i - 4) := by
  have hSz : (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf).size = 4 := by
    simp only [Architecture.regMessageRegs, Array.size_map]; rfl
  split
  · next h4 =>
    rw [← wordAt_regMessageRegs SeLe4n.arm64DefaultLayout rf i]
    unfold Architecture.wordAt
    rw [Array.getElem?_append_left (by omega)]
  · next h4 =>
    unfold Architecture.wordAt
    rw [Array.getElem?_append_right (by omega), hSz, List.getElem?_toArray,
      overflowRegsFrom_getElem?, if_pos (by omega)]
    simp only [Option.map_some, Option.getD_some, Architecture.wordOf, Nat.zero_add]

/-- Within a long reply of `len` words, more than four, its reply words are
`faultReplyWordLong`'s on any state `X` reading the replier's buffer as `S`
does. -/
theorem replyWordOr_longSendRegs (S X : SystemState) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat) (hLen : 4 ≤ len)
    (hW : ipcWordReadsAgree X S) (i : Nat) (fb : UInt64) :
    Architecture.replyWordOr { length := len, extraCaps := extraCaps, label := label }
        (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
          (overflowRegsFrom S s 0 (len - 4)).toArray) i fb =
      faultReplyWordLong X s rf len i fb := by
  have hSz : (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
      (overflowRegsFrom S s 0 (len - 4)).toArray).size = len := by
    simp only [Array.size_append, Architecture.regMessageRegs, Array.size_map,
      List.size_toArray, overflowRegsFrom_length]
    have : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
    omega
  unfold Architecture.replyWordOr faultReplyWordLong
  simp only [hSz, Nat.min_self, Nat.add_zero]
  split
  · next hi => rw [wordAt_longSendRegs S s rf len i hi, hW.overflowWordAt]
  · rfl

/-- The same for a long reply-receive's words (`longReplyRecvRegs`), the
reply's length the words it holds. -/
theorem replyWordOr_longReplyRecvRegs (S X : SystemState) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (hLen : 4 ≤ len)
    (hW : ipcWordReadsAgree X S) (i : Nat) (fb : UInt64) :
    Architecture.replyWordOr
        { length := (longReplyRecvRegs rf S s len).size, extraCaps := 0, label := label }
        (longReplyRecvRegs rf S s len) i fb = faultReplyWordLong X s rf len i fb := by
  rw [longReplyRecvRegs_size rf S s len hLen]
  exact replyWordOr_longSendRegs S X s rf len 0 label hLen hW i fb

/-- The fault reply's writes keep every buffer read. -/
theorem ipcBufferReadsAgree_storeFaultReplyRendezvous (st : SystemState)
    (c server : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storeFaultReplyRendezvous st c server rid) st := by
  rw [storeFaultReplyRendezvous_eq, storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]
  exact (ipcBufferReadsAgree_mapTcbInPlace _ c (holdMessage IpcMessage.empty)
    (fun _ => ⟨rfl, rfl⟩)).trans (ipcBufferReadsAgree_storeReplyRendezvousReady st c server rid hNo)

theorem storeFaultReplyRendezvous_noResizeDue (st : SystemState)
    (c server : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    (storeFaultReplyRendezvous st c server rid).objects.noResizeDue := by
  rw [storeFaultReplyRendezvous_eq, storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    SystemState.mapTcbInPlace_noResizeDue]
  exact storeReplyRendezvousReady_noResizeDue st c server rid hNo

/-- The fault reply leg's writes, to a caller recording no server, keep every
buffer read. -/
theorem ipcBufferReadsAgree_storeFaultReplyLeg (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storeFaultReplyLeg st c rid) st := by
  rw [storeFaultReplyLeg_eq, storeReplyLeg_eq_hold _ _ _ _ hNo]
  exact (ipcBufferReadsAgree_mapTcbInPlace _ c (holdMessage IpcMessage.empty)
    (fun _ => ⟨rfl, rfl⟩)).trans (ipcBufferReadsAgree_storeReplyLegReady st c rid hNo)

theorem storeFaultReplyLeg_noResizeDue (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    (storeFaultReplyLeg st c rid).objects.noResizeDue := by
  rw [storeFaultReplyLeg_eq, storeReplyLeg_eq_hold _ _ _ _ hNo,
    SystemState.mapTcbInPlace_noResizeDue]
  exact storeReplyLegReady_noResizeDue st c rid hNo

/-! ## The long fault reply -/

/-- **The `.reply` arm's long fault answer, in place**: the reply's writes with
no message (`storeFaultReplyRendezvous`), the server's priority walk, then the
fault answer (`performFaultAnswerLong`) from the replier's registers and IPC
buffer. -/
@[noinline] def performFaultReplyAnswerLong (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (replier : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) : SystemState :=
  performFaultAnswerLong (PriorityInheritance.propagatePipChainCrossCore
      (storeFaultReplyRendezvous st c server rid) server core).1 c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 replier rf len

/-- **The long fault reply, in place**: a reply of `len` words, more than four,
to a thread blocked on it carrying a fault, every write in its slot
(`replyWakesInPlace`), is seL4's `handleFaultReply`: the specification's fault
branch commits `performFaultReplyAnswerLong`'s state, the reply's words read
from the replier's registers and IPC buffer. -/
theorem faultReplyTransferChecked_inPlaceLong (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (len extraCaps label : Nat) (rf : SeLe4n.RegisterFile)
    (msg : IpcMessage) (grant : Bool) (core : CoreId) (hLen : 4 ≤ len)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyWakesInPlace st c ct rid = true)
    (hF : ct.faultWords.isFault = true) :
    replyTransferOnCoreChecked ctx replier c
        { length := len, extraCaps := extraCaps, label := label }
        (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
          (overflowRegsFrom st replier 0 (len - 4)).toArray) msg grant core
        st =
      .ok ((), performFaultReplyAnswerLong st c server rid core ct.faultKind label ct.faultIp
        ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
        ct.faultX6 ct.faultX7 replier rf len) := by
  have hNo := replyWakesInPlace_noResizeDue hG
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨tf, hPF⟩ : ∃ tf, ct.pendingFault = some tf :=
    Option.isSome_iff_exists.mp (by rw [TCB.pendingFault_isSome]; exact hF)
  have hHas : threadHasPendingFault st c = true := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_some]
  obtain ⟨sgi, hD⟩ := replyDispatch_inPlace st replier c server ct ep rid IpcMessage.empty core
    (by simp [IpcMessage.empty]) hT hIpc hRO hSRes hG
  have hW : ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore
      (storeReplyRendezvous st c server rid IpcMessage.empty) server core).1 st :=
    ((ipcBufferReadsAgree_propagatePipChainCrossCore _ server core
      (storeFaultReplyRendezvous_noResizeDue st c server rid hNo)).trans
      (ipcBufferReadsAgree_storeFaultReplyRendezvous st c server rid hNo)).words
  unfold replyTransferOnCoreChecked
  rw [hHas]
  simp only [↓reduceIte]
  unfold faultReplyOnCore
  rw [hTc]
  simp only [hPF, hD]
  unfold performFaultReplyAnswerLong
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ replier rf len
    (replyWordOr_longSendRegs st _ replier rf len extraCaps label hLen hW)]
  rfl

/-- **The donated long reply's fault answer, in place**: the reply's writes
with no message, the loaned context handed back down the stack in place
(`replyDonationPopInPlace`), the server's priority walk, then the fault answer
(`performFaultAnswerLong`). -/
@[noinline] def performFaultReplyDonatedAnswerLong (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId) (core : CoreId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (replier : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) : SystemState :=
  performFaultAnswerLong (PriorityInheritance.propagatePipChainCrossCore
      (replyDonationPopInPlace (storeFaultReplyRendezvous st c server rid) c server scId home)
      server core).1 c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 replier rf len

/-- **The checked donated long fault reply, in place**: under
`replyPopsInPlace`, a long reply to a faulted caller blocked on it commits
`performFaultReplyDonatedAnswerLong`'s state. -/
theorem faultReplyTransferChecked_donated_inPlaceLong (ctx : LabelingContext) (st : SystemState)
    (replier c server : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (len extraCaps label : Nat) (rf : SeLe4n.RegisterFile)
    (msg : IpcMessage) (grant : Bool) (core : CoreId) (hLen : 4 ≤ len)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep (some server))
    (hRO : ct.replyObject = some rid)
    (hSRes : server.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode server rid = true)
    (hF : ct.faultWords.isFault = true) :
    replyTransferOnCoreChecked ctx replier c
        { length := len, extraCaps := extraCaps, label := label }
        (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
          (overflowRegsFrom st replier 0 (len - 4)).toArray) msg grant core
        st =
      .ok ((), performFaultReplyDonatedAnswerLong st c server rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) core ct.faultKind label
        ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
        ct.faultX5 ct.faultX6 ct.faultX7 replier rf len) := by
  obtain ⟨rp, scId, _, hRp, hN, _, _, _, hCode, hCRes, hNe, hNo, hLC, hFC, hLR, hFR, hDon, _⟩ :=
    replyPopsInPlace_donation st c server rid IpcMessage.empty ct hT hSRes hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hEq, _⟩ := replyOnCore_eq_store st replier c server ct ep rid rp IpcMessage.empty core
    (by simp [IpcMessage.empty]) hT hIpc hRO hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨tf, hPF⟩ : ∃ tf, ct.pendingFault = some tf :=
    Option.isSome_iff_exists.mp (by rw [TCB.pendingFault_isSome]; exact hF)
  have hHas : threadHasPendingFault st c = true := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_some]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  obtain ⟨sv, hsv⟩ := Option.isSome_iff_exists.mp
    ((SeLe4n.ThreadId.toValid?_isSome_iff server).mpr hSRes)
  have hRec : recordedReplyServer? st c = some server := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  have hNoS := storeFaultReplyRendezvous_noResizeDue st c server rid hNo
  have hW0 : ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore
      (replyDonationPopInPlace (storeFaultReplyRendezvous st c server rid) c server scId
        (determineTargetCore st c)) server core).1 st :=
    ((ipcBufferReadsAgree_propagatePipChainCrossCore _ server core
      (replyDonationPopInPlace_noResizeDue _ c server scId _ hNoS)).trans
      ((ipcBufferReadsAgree_replyDonationPopInPlace _ c server scId _ hNoS).trans
        (ipcBufferReadsAgree_storeFaultReplyRendezvous st c server rid hNo))).words
  have hW := hW0
  rw [storeFaultReplyRendezvous_eq, storeReplyRendezvous_eq_hold _ _ _ _ _ hNo] at hW
  unfold replyTransferOnCoreChecked
  rw [hHas]
  simp only [↓reduceIte]
  unfold faultReplyOnCore
  rw [hTc]
  simp only [hPF]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hsv, hAns, hcv]
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo,
    hDon cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  unfold performFaultReplyDonatedAnswerLong
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ replier rf len
    (replyWordOr_longSendRegs st _ replier rf len extraCaps label hLen hW),
    storeFaultReplyRendezvous_eq, storeReplyRendezvous_eq_hold _ _ _ _ _ hNo]

/-- **The long fault answer to a caller recording no server, in place**: the
reply leg's writes with no message, the context its reply object heads handed to
it in place, then the fault answer (`performFaultAnswerLong`). -/
@[noinline] def performFaultReplyUnheldAnswerLong (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId) (home : CoreId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (replier : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len : Nat) : SystemState :=
  performFaultAnswerLong (SchedContextOps.settleReturnedContext
      (returnUnheldSchedContextInPlace (storeFaultReplyLeg st c rid) c scId) home scId) c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 replier rf len

/-- **The checked long fault reply to a caller recording no server, in place**:
under `replyUnheldPopsInPlace`, a long reply to a faulted caller blocked on it
with no server recorded commits `performFaultReplyUnheldAnswerLong`'s state. -/
theorem faultReplyTransferChecked_unheld_inPlaceLong (ctx : LabelingContext) (st : SystemState)
    (replier c : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (len extraCaps label : Nat) (rf : SeLe4n.RegisterFile)
    (msg : IpcMessage) (grant : Bool) (core : CoreId) (hLen : 4 ≤ len)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hF : ct.faultWords.isFault = true) :
    replyTransferOnCoreChecked ctx replier c
        { length := len, extraCaps := extraCaps, label := label }
        (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
          (overflowRegsFrom st replier 0 (len - 4)).toArray) msg grant core
        st =
      .ok ((), performFaultReplyUnheldAnswerLong st c rid ⟨replyHeadContextCode st rid - 1⟩
        (determineTargetCore st c) ct.faultKind label ct.faultIp ct.faultSp ct.faultLr
        ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7
        replier rf len) := by
  obtain ⟨rp, scId, hRp, hN, hCode, hCRes, hNo, hLC, hFC, hLR, hFR, -, hPop⟩ :=
    replyUnheldPopsInPlace_pop st c rid IpcMessage.empty ct hT hG
  have hSc : (⟨replyHeadContextCode st rid - 1⟩ : SeLe4n.SchedContextId) = scId := by
    rw [hCode]; rfl
  rw [hSc]
  obtain ⟨hEq, _⟩ := replyOnCore_eq_storeLeg st replier c none ct ep rid rp IpcMessage.empty core
    (by simp [IpcMessage.empty]) hT hIpc hRO hCRes hLC hFC hLR hFR hRp (Or.inr ⟨scId, hN⟩)
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨tf, hPF⟩ : ∃ tf, ct.pendingFault = some tf :=
    Option.isSome_iff_exists.mp (by rw [TCB.pendingFault_isSome]; exact hF)
  have hHas : threadHasPendingFault st c = true := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_some]
  obtain ⟨cv, hcv⟩ := Option.isSome_iff_exists.mp ((SeLe4n.ThreadId.toValid?_isSome_iff c).mpr hCRes)
  have hRec : recordedReplyServer? st c = none := by
    simp only [recordedReplyServer?, hTc, hIpc]
  have hAns : answeredReplyObject? st c = some rid := by
    simp only [answeredReplyObject?, hTc, Option.bind_some, hRO]
  have hNoL := storeFaultReplyLeg_noResizeDue st c rid hNo
  have hW0 : ipcWordReadsAgree (SchedContextOps.settleReturnedContext
      (returnUnheldSchedContextInPlace (storeFaultReplyLeg st c rid) c scId)
      (determineTargetCore st c) scId) st :=
    ((ipcBufferReadsAgree_settleReturnedContext _ _ scId).trans
      ((ipcBufferReadsAgree_returnUnheldSchedContextInPlace _ c scId hNoL).trans
        (ipcBufferReadsAgree_storeFaultReplyLeg st c rid hNo))).words
  have hW := hW0
  rw [storeFaultReplyLeg_eq, storeReplyLeg_eq_hold _ _ _ _ hNo] at hW
  unfold replyTransferOnCoreChecked
  rw [hHas]
  simp only [↓reduceIte]
  unfold faultReplyOnCore
  rw [hTc]
  simp only [hPF]
  unfold endpointReplyCrossCoreDispatch
  rw [hEq]
  simp only [hRec, hAns, hcv, SystemState.unlinkReplyWaiterOpt]
  rw [storeReplyLeg_eq_hold _ _ _ _ hNo, hPop cv (SeLe4n.ThreadId.toValid?_some_val_eq _ _ hcv)]
  simp only []
  unfold performFaultReplyUnheldAnswerLong
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ replier rf len
    (replyWordOr_longSendRegs st _ replier rf len extraCaps label hLen hW),
    storeFaultReplyLeg_eq, storeReplyLeg_eq_hold _ _ _ _ hNo]

/-- **The long fault answer to a caller recording no server, its reply object
linked to nothing, in place** (WS-SX SX8.3): the reply leg's writes with no
message, then the fault answer (`performFaultAnswerLong`).  No context to hand
back. -/
@[noinline] def performFaultReplyUnlinkedAnswerLong (st : SystemState) (c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (replier : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (len : Nat) : SystemState :=
  performFaultAnswerLong (storeFaultReplyLeg st c rid) c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 replier rf len

/-- **The checked long fault reply to a caller recording no server, its reply
object linked to nothing, in place**: under `replyUnlinkedInPlace`, a long reply
to a faulted caller blocked on it with no server recorded commits
`performFaultReplyUnlinkedAnswerLong`'s state. -/
theorem faultReplyTransferChecked_unlinked_inPlaceLong (ctx : LabelingContext) (st : SystemState)
    (replier c : SeLe4n.ThreadId) (ct : TCB) (ep : SeLe4n.ObjId) (rid : SeLe4n.ReplyId)
    (len extraCaps label : Nat) (rf : SeLe4n.RegisterFile)
    (msg : IpcMessage) (grant : Bool) (core : CoreId) (hLen : 4 ≤ len)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnlinkedInPlace st c rid = true)
    (hF : ct.faultWords.isFault = true) :
    replyTransferOnCoreChecked ctx replier c
        { length := len, extraCaps := extraCaps, label := label }
        (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
          (overflowRegsFrom st replier 0 (len - 4)).toArray) msg grant core
        st =
      .ok ((), performFaultReplyUnlinkedAnswerLong st c rid ct.faultKind label ct.faultIp
        ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
        ct.faultX6 ct.faultX7 replier rf len) := by
  have hNo := replyWakesInPlace_noResizeDue ((replyUnlinkedInPlace_eq_wakes st c ct rid) ▸ hG)
  obtain ⟨sgi, hD⟩ := replyDispatch_unlinked_inPlace st replier c ct ep rid IpcMessage.empty core
    (by simp [IpcMessage.empty]) hT hIpc hRO hG
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨tf, hPF⟩ : ∃ tf, ct.pendingFault = some tf :=
    Option.isSome_iff_exists.mp (by rw [TCB.pendingFault_isSome]; exact hF)
  have hHas : threadHasPendingFault st c = true := by
    simp only [threadHasPendingFault, hTc, Option.bind_some, hPF, Option.isSome_some]
  have hW : ipcWordReadsAgree (storeReplyLeg st c rid IpcMessage.empty) st := by
    rw [← storeFaultReplyLeg_eq]
    exact (ipcBufferReadsAgree_storeFaultReplyLeg st c rid hNo).words
  unfold replyTransferOnCoreChecked
  rw [hHas]
  simp only [↓reduceIte]
  unfold faultReplyOnCore
  rw [hTc]
  simp only [hPF]
  rw [hD]
  simp only []
  unfold performFaultReplyUnlinkedAnswerLong
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ replier rf len
    (replyWordOr_longSendRegs st _ replier rf len extraCaps label hLen hW),
    storeFaultReplyLeg_eq]

/-! ## The long fault reply-receive -/

end SeLe4n.Kernel
