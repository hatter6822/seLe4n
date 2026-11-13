-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.FaultAnswerInPlace
import SeLe4n.Kernel.IPC.CrossCore.LongReplyRecvPopInPlace

/-!
# A fault answered in place by a long reply

A fault handler answering with more than four words (a long `Reply` or
`ReplyRecv`) supplies its restart words past the fourth from its IPC buffer, as
seL4's `copyMRsFaultReply` reads them.  The answer is `performFaultAnswer`'s
with each reply word read by `faultReplyWordLong`: word `i + off` of the
replier's inline registers below four, its IPC-buffer overflow slot
`i + off - 4` past them, read in the state the answer runs on.  Every write
before the answer keeps every buffer read (`ipcBufferReadsAgree`), so those are
the words the specification's message holds.

Each shape the short fault answer runs in place has its long form here:

* `.reply` waking its caller in its slots (`performFaultReplyAnswerLong`,
  `faultReplyTransferChecked_inPlaceLong`), on a donated reply
  (`performFaultReplyDonatedAnswerLong`,
  `faultReplyTransferChecked_donated_inPlaceLong`) and to a caller recording
  no server (`performFaultReplyUnheldAnswerLong`,
  `faultReplyTransferChecked_unheld_inPlaceLong`);
* `.replyRecv` blocking on the endpoint after each of the same three replies
  (`performReplyRecvFaultAnswerLong`, `performReplyRecvDonatedFaultAnswerLong`,
  `performReplyRecvUnheldFaultAnswerLong`, and their
  `replyRecvTransferOnCore_fault_*_inPlaceLong` theorems).

None builds the fault record, the reply's message, the outcome or a frame.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

/-- Reply word `i` of a long fault reply, or the faulted thread's own
`fallback` past the `len - off` words the reply supplied: word `i + off` of the
replier `s`'s message, its inline register below four and its IPC-buffer
overflow slot past them, read in `X`.  Out of line, reading `X` borrowed, so it
returns a bare machine word and the state is not held across the restart. -/
@[noinline] def faultReplyWordLong (X : @& SystemState) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len off i : Nat) (fallback : UInt64) : UInt64 :=
  if i + off < len then
    (if i + off < 4 then Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf (i + off)
     else overflowWordAt X s (i + off - 4))
  else fallback

/-- **The fault answer to a long reply** -- `performFaultAnswer` with each reply
word read by `faultReplyWordLong`. -/
@[noinline] def performFaultAnswerLong (X : SystemState) (c : SeLe4n.ThreadId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len off : Nat) : SystemState :=
  if kind == 1 || kind == 2 then
    applyFaultRestart X c
      { pc := ip, sp := sp, lr := lr, x0 := x0, x1 := x1, x2 := x2, x3 := x3,
        x4 := x4, x5 := x5, x6 := x6, x7 := x7 }
  else if label != 0 then faultAbandonOnCore X c (faultAbandonCore X c)
  else if kind == 3 then
    applyFaultRestart X c
      { pc := faultReplyWordLong X s rf len off 8 ip,
        sp := faultReplyWordLong X s rf len off 9 sp,
        lr := faultReplyWordLong X s rf len off 10 lr,
        x0 := faultReplyWordLong X s rf len off 0 x0, x1 := faultReplyWordLong X s rf len off 1 x1,
        x2 := faultReplyWordLong X s rf len off 2 x2, x3 := faultReplyWordLong X s rf len off 3 x3,
        x4 := faultReplyWordLong X s rf len off 4 x4, x5 := faultReplyWordLong X s rf len off 5 x5,
        x6 := faultReplyWordLong X s rf len off 6 x6, x7 := faultReplyWordLong X s rf len off 7 x7 }
  else
    applyFaultRestart X c
      { pc := faultReplyWordLong X s rf len off 0 ip, sp := faultReplyWordLong X s rf len off 1 sp,
        lr := lr, x0 := x0, x1 := x1, x2 := x2, x3 := x3,
        x4 := x4, x5 := x5, x6 := x6, x7 := x7 }

/-- **The long fault answer read from words is the decoded one**: for a caller
`ct` carrying fault `tf`, and a reply whose words, past the faulted thread's
own, are `faultReplyWordLong`'s (`hR`), applying the decoded outcome is
`performFaultAnswerLong` of the caller's fault words and the reply's label. -/
theorem faultReplyApplyOnCore_decode_eq_performFaultAnswerLong (X : SystemState)
    (c : SeLe4n.ThreadId) (ct : TCB) (tf : ThreadFault) (hPF : ct.pendingFault = some tf)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len off : Nat)
    (hR : ∀ i fb, Architecture.replyWordOr mi regs i fb = faultReplyWordLong X s rf len off i fb) :
    faultReplyApplyOnCore X c (Architecture.decodeFaultReply tf.fault tf.context mi regs) =
      performFaultAnswerLong X c ct.faultKind mi.label ct.faultIp ct.faultSp ct.faultLr
        ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6
        ct.faultX7 s rf len off := by
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

/-- Word `i` of a long reply-receive's words (`longReplyRecvRegs`) is word
`i + 1` of the long reply's. -/
theorem wordAt_longReplyRecvRegs (S : SystemState) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len i : Nat) :
    Architecture.wordAt (longReplyRecvRegs rf S s len) i =
      Architecture.wordAt (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
        (overflowRegsFrom S s 0 (len - 4)).toArray) (i + 1) := by
  unfold longReplyRecvRegs Architecture.wordAt
  simp only [longSendMessage]
  rw [Array.getElem?_extract]
  split
  · next h => rw [Nat.add_comm]
  · next h =>
    rw [Array.getElem?_eq_none (by omega)]

/-- Within a long reply of `len` words, more than four, its reply words are
`faultReplyWordLong`'s on any state `X` reading the replier's buffer as `S`
does. -/
theorem replyWordOr_longSendRegs (S X : SystemState) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat) (hLen : 4 ≤ len)
    (hW : ipcWordReadsAgree X S) (i : Nat) (fb : UInt64) :
    Architecture.replyWordOr { length := len, extraCaps := extraCaps, label := label }
        (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
          (overflowRegsFrom S s 0 (len - 4)).toArray) i fb =
      faultReplyWordLong X s rf len 0 i fb := by
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

/-- The same for a long reply-receive's words past MR0 (`longReplyRecvRegs`),
the reply's length the words it holds. -/
theorem replyWordOr_longReplyRecvRegs (S X : SystemState) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (hLen : 4 ≤ len)
    (hW : ipcWordReadsAgree X S) (i : Nat) (fb : UInt64) :
    Architecture.replyWordOr
        { length := (longReplyRecvRegs rf S s len).size, extraCaps := 0, label := label }
        (longReplyRecvRegs rf S s len) i fb = faultReplyWordLong X s rf len 1 i fb := by
  unfold Architecture.replyWordOr faultReplyWordLong
  simp only [Nat.min_self, longReplyRecvRegs_size rf S s len hLen]
  split
  · next hi =>
    rw [if_pos (by omega), wordAt_longReplyRecvRegs, wordAt_longSendRegs S s rf len (i + 1)
      (by omega), hW.overflowWordAt]
  · next hi => rw [if_neg (by omega)]

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
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 replier rf len 0

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
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ replier rf len 0
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
      server core).1 c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 replier rf len 0

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
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ replier rf len 0
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
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 replier rf len 0

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
  rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ replier rf len 0
    (replyWordOr_longSendRegs st _ replier rf len extraCaps label hLen hW),
    storeFaultReplyLeg_eq, storeReplyLeg_eq_hold _ _ _ _ hNo]

/-! ## The long fault reply-receive -/

/-- The long fault answer leaves every other thread in the IPC state it was in. -/
theorem performFaultAnswerLong_ipcStateAt (X : SystemState) (c t : SeLe4n.ThreadId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (s : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (len off : Nat)
    (hNe : c.toObjId ≠ t.toObjId) (hNo : X.objects.noResizeDue) (x : TCB)
    (hX : X.getTcb? t = some x) :
    ∃ x', (performFaultAnswerLong X c kind label ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 s rf len
      off).getTcb? t = some x' ∧ x'.ipcState = x.ipcState := by
  have hUp : ∀ (Y : SystemState) (f : TCB → TCB), Y.objects.noResizeDue →
      (Y.updateTcb c f).getTcb? t = Y.getTcb? t := fun Y f hY => by
    rw [SystemState.updateTcb_eq_mapTcbInPlace _ _ _ hY,
      SystemState.mapTcbInPlace_getTcb?_ne _ _ _ _ hNe]
  unfold performFaultAnswerLong applyFaultRestart faultAbandonOnCore
  split
  · exact ⟨x, by rw [hUp _ _ hNo]; exact hX, rfl⟩
  · split
    · obtain ⟨x1, h1, e1⟩ := ipcStateCarried_of_agree
        (removeRunnableOnCore_objectsAgreeOffRunLinks X c (faultAbandonCore X c)) t x hX
      exact ⟨x1, by rw [hUp _ _ (removeRunnableOnCore_noResizeDue _ _ _ hNo)]; exact h1, e1⟩
    · split
      · exact ⟨x, by rw [hUp _ _ hNo]; exact hX, rfl⟩
      · exact ⟨x, by rw [hUp _ _ hNo]; exact hX, rfl⟩

/-- **The blocking long reply-receive answering a fault, in place**: the
reply's writes with no message, the server's block on the endpoint and its
priority walk, then the fault answer (`performFaultAnswerLong`) from the
replier's words past MR0, in its registers and IPC buffer. -/
@[noinline] def performReplyRecvFaultAnswerLong (st : SystemState) (c tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId)
    (kind label : Nat) (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64)
    (rf : SeLe4n.RegisterFile) (len : Nat) : SystemState :=
  performFaultAnswerLong (PriorityInheritance.propagatePipChainCrossCore
      (removeRunnableOnCore (storeReceiveBlock (storeFaultReplyRendezvous st c tid rid) epId tid
        tailCode (rid.val + 1)) tid core) tid core).1 c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid rf len 1

/-- **The blocking long reply-receive answering a fault is the
specification's**, and it stages nothing for the server, which the receive
leaves blocked: under the guard of `replyRecvOnCore_blocks_inPlace`, for a
caller carrying a fault, the arm's transition is
`performReplyRecvFaultAnswerLong`. -/
theorem replyRecvTransferOnCore_fault_blocks_inPlaceLong (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (tf : ThreadFault) (hLen : 4 ≤ len)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hG : replyWakesInPlace st c ct rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hFree : rp.consumed.isFree = true) (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    replyRecvTransferOnCore epId tid rid c label
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st =
      .ok ({ results := #[] }, performReplyRecvFaultAnswerLong st c tid rid epId ep.recvTailCode
        core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1
        ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len) ∧
    Architecture.stageDeliveredMessage (performReplyRecvFaultAnswerLong st c tid rid epId
        ep.recvTailCode core ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0
        ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len) tid 0 =
      performReplyRecvFaultAnswerLong st c tid rid epId ep.recvTailCode core ct.faultKind label
        ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
        ct.faultX5 ct.faultX6 ct.faultX7 rf len := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  have hNo := replyWakesInPlace_noResizeDue hG
  have hNoS := storeFaultReplyRendezvous_noResizeDue st c tid rid hNo
  have hW : ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore
      (removeRunnableOnCore (storeReceiveBlock (storeReplyRendezvous st c tid rid IpcMessage.empty)
        epId tid ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 st :=
    ((ipcBufferReadsAgree_storeReplyRecvBlockTail _ tid rid epId ep.recvTailCode core hNoS).trans
      (ipcBufferReadsAgree_storeFaultReplyRendezvous st c tid rid hNo)).words
  refine ⟨?_, ?_⟩
  · unfold replyRecvTransferOnCore
    rw [replyRecvCallerFaultAnswer?_of_fault st c ct tf label _ hTc hPF]
    simp only [replyRecvLegMessage]
    rw [replyRecvAnsweringOnCore_blocks_inPlace _ st epId tid c rid IpcMessage.empty grant core
      ct ep0 rt ep rp (by simp [IpcMessage.empty]) hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hFree
      hStash hRec (fun h => by cases h)]
    unfold performReplyRecvFaultAnswerLong replyRecvAnswerCaller
    dsimp only
    rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ tid rf len 1
      (replyWordOr_longReplyRecvRegs st _ tid rf len label hLen hW)]
    rfl
  · have hFC : st.objects.findsInPlace c.toObjId = true := by
      simp only [replyWakesInPlace, Bool.and_eq_true] at hG
      exact hG.1.1.1.2
    have hCT : c.toObjId ≠ tid.toObjId :=
      fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
    obtain ⟨hE1, ⟨rt1, hR1, hA1⟩, hG1⟩ := storeReplyRendezvous_receiveGuard st c tid rid
      IpcMessage.empty ct rp epId ep rt hNo hT hFC hRp hNe hE hR hA hEnq hFree hStash hRec
    obtain ⟨t, hT1, hB⟩ := receiveBlock_receiver_blocked _ epId ep tid rt1 (some rid) core hE1 hR1
      hA1 hG1
    have h0 : (storeReplyRendezvous st c tid rid IpcMessage.empty).objects.noResizeDue := by
      rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, SystemState.mapTcbInPlace_noResizeDue]
      exact storeReplyRendezvousReady_noResizeDue st c tid rid hNo
    have h3 := removeRunnableOnCore_noResizeDue _ tid core (storeReceiveBlock_noResizeDue _ epId
      tid ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid)) h0)
    obtain ⟨x, hX, hEq⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h3 tid t hT1
    obtain ⟨x', hX', hEq'⟩ := performFaultAnswerLong_ipcStateAt _ c tid ct.faultKind label
      ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
      ct.faultX5 ct.faultX6 ct.faultX7 tid rf len 1 hCT
      (propagatePipChainCrossCore_noResizeDue _ _ _ h3) x hX
    unfold performReplyRecvFaultAnswerLong
    exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x' hX'
      (by rw [hEq', hEq, hB]; exact fun h => by cases h)

/-- **The donated long reply-receive answering a fault, in place**: the reply's
writes with no message, the pop and its settle, the server's block on the
endpoint, the server taken off its core and its priority walk, then the fault
answer (`performFaultAnswerLong`). -/
@[noinline] def performReplyRecvDonatedFaultAnswerLong (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId)
    (home : CoreId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (rf : SeLe4n.RegisterFile) (len : Nat) :
    SystemState :=
  performFaultAnswerLong (PriorityInheritance.propagatePipChainCrossCore
      (descheduleAtPlacement (removeRunnableOnCore (storeReceiveBlock
        (popDonationSettledInPlace (storeFaultReplyRendezvous st c tid rid) c tid scId home) epId tid
        tailCode (rid.val + 1)) tid core) tid) tid core).1 c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid rf len 1

/-- **The donated long reply-receive answering a fault is the
specification's**, and it stages nothing for the server, which the receive
leaves blocked. -/
theorem replyRecvTransferOnCore_fault_donated_inPlaceLong (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (tf : ThreadFault) (hLen : 4 ≤ len)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 (some tid))
    (hRO : ct.replyObject = some rid)
    (hSRes : tid.isReserved = false)
    (hG : replyPopsInPlace st c ct.scBindingScCode tid rid = true)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : enqueueAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    replyRecvTransferOnCore epId tid rid c label
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st =
      .ok ({ results := #[] }, performReplyRecvDonatedFaultAnswerLong st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len) ∧
    Architecture.stageDeliveredMessage (performReplyRecvDonatedFaultAnswerLong st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len) tid 0 =
      performReplyRecvDonatedFaultAnswerLong st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨_, _, _, _, _, _, _, _, _, _, hNe', hNo, _⟩ :=
    replyPopsInPlace_donation st c tid rid IpcMessage.empty ct hT hSRes hG
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe' (SeLe4n.ThreadId.toObjId_injective _ _ e)
  let msg : IpcMessage := { registers := longReplyRecvRegs rf st tid len, badge := badge }
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_donated_inPlace
    (replyRecvCallerFaultAnswer? st c label msg)
    st epId tid c rid IpcMessage.empty grant core ct ep0 rt ep rp (by simp [IpcMessage.empty])
    hT hIpc hRO hSRes hG hE hS hR hA hEnq hRp hStash hRec
    (fun h => by rw [replyRecvCallerFaultAnswer?_of_fault st c ct tf label _ hTc hPF] at h; cases h)
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label msg hTc hPF
  have hNoS := storeFaultReplyRendezvous_noResizeDue st c tid rid hNo
  have hNoP := popDonationSettledInPlace_noResizeDue _ c tid ⟨replyHeadContextCode st rid - 1⟩
    (determineTargetCore st c) hNoS
  have hW : ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore
      (descheduleAtPlacement (removeRunnableOnCore (storeReceiveBlock
        (popDonationSettledInPlace (storeReplyRendezvous st c tid rid IpcMessage.empty) c tid
          ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c)) epId tid
        ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid) tid core).1 st :=
    ((ipcBufferReadsAgree_storeReplyRecvDonatedTail _ tid rid epId ep.recvTailCode core hNoP).trans
      (((ipcBufferReadsAgree_settleReturnedContext _ (determineTargetCore st c) _).trans
        (ipcBufferReadsAgree_returnDonatedSchedContextInPlace _ tid c _ hNoS)).trans
        (ipcBufferReadsAgree_storeFaultReplyRendezvous st c tid rid hNo))).words
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label msg) msg =
      IpcMessage.empty := by rw [hAns]; rfl
  refine ⟨?_, ?_⟩
  · unfold replyRecvTransferOnCore
    rw [hL, hEq]
    unfold performReplyRecvDonatedFaultAnswerLong replyRecvAnswerCaller
    rw [hAns]
    dsimp only
    rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ tid rf len 1
      (replyWordOr_longReplyRecvRegs st _ tid rf len label hLen hW)]
    rfl
  · have h0 : (storeReplyRendezvous st c tid rid IpcMessage.empty).objects.noResizeDue := by
      rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, SystemState.mapTcbInPlace_noResizeDue]
      exact storeReplyRendezvousReady_noResizeDue st c tid rid hNo
    have h2 := popDonationSettledInPlace_noResizeDue _ c tid ⟨replyHeadContextCode st rid - 1⟩
      (determineTargetCore st c) h0
    have h3 := storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode
      (SeLe4n.ReplyId.optCode (some rid)) h2
    have h4 := removeRunnableOnCore_noResizeDue _ tid core h3
    have h5 := descheduleAtPlacement_noResizeDue _ tid h4
    obtain ⟨x1, hX1, e1⟩ := descheduleAtPlacement_ipcStateCarried _ tid tid x hX
    obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h5 tid x1 hX1
    obtain ⟨x3, hX3, e3⟩ := performFaultAnswerLong_ipcStateAt _ c tid ct.faultKind label
      ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
      ct.faultX5 ct.faultX6 ct.faultX7 tid rf len 1 hCT
      (propagatePipChainCrossCore_noResizeDue _ _ _ h5) x2 hX2
    unfold performReplyRecvDonatedFaultAnswerLong
    exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x3 hX3
      (by rw [e3, e2, e1, hB]; exact fun h => by cases h)

/-- **The long reply-receive answering a fault for a caller recording no
server, in place**: the reply leg's writes with no message, the unheld pop and
its settle, the replier's block on the endpoint and its priority walk, then the
fault answer (`performFaultAnswerLong`). -/
@[noinline] def performReplyRecvUnheldFaultAnswerLong (st : SystemState)
    (c tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (scId : SeLe4n.SchedContextId)
    (home : CoreId) (epId : SeLe4n.ObjId) (tailCode : Nat) (core : CoreId) (kind label : Nat)
    (ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 : UInt64) (rf : SeLe4n.RegisterFile) (len : Nat) :
    SystemState :=
  performFaultAnswerLong (PriorityInheritance.propagatePipChainCrossCore
      (removeRunnableOnCore (storeReceiveBlock
        (SchedContextOps.settleReturnedContext
          (returnUnheldSchedContextInPlace (storeFaultReplyLeg st c rid) c scId) home scId) epId tid
        tailCode (rid.val + 1)) tid core) tid core).1 c kind label
    ip sp lr x0 x1 x2 x3 x4 x5 x6 x7 tid rf len 1

/-- **The long reply-receive answering a fault for a caller recording no
server is the specification's**, and it stages nothing for the replier, which
the receive leaves blocked. -/
theorem replyRecvTransferOnCore_fault_unheld_inPlaceLong (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (label : Nat)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (grant : Bool)
    (core : CoreId) (ct : TCB) (ep0 : SeLe4n.ObjId) (rt : TCB) (ep : Endpoint) (rp : Reply)
    (tf : ThreadFault) (hLen : 4 ≤ len)
    (hPF : ct.pendingFault = some tf)
    (hT : st.objects[c.toObjId]? = some (.tcb ct))
    (hIpc : ct.ipcState = .blockedOnReply ep0 none)
    (hRO : ct.replyObject = some rid)
    (hG : replyUnheldPopsInPlace st c rid = true)
    (hNe : tid ≠ c)
    (hE : st.objects[epId]? = some (.endpoint ep)) (hS : ep.sendQ.head = none)
    (hR : st.objects[tid.toObjId]? = some (.tcb rt)) (hA : receiveBlockAdmits rt = true)
    (hEnq : enqueuesInPlace st epId tid ep.receiveQ.tail = true)
    (hRp : st.objects[rid.toObjId]? = some (.reply rp))
    (hStash : st.replyStashedAt rid rp = false)
    (hRec : replyRecordsInPlace st (rid.val + 1) = true) :
    replyRecvTransferOnCore epId tid rid c label
        { registers := longReplyRecvRegs rf st tid len, badge := badge } grant core st =
      .ok ({ results := #[] }, performReplyRecvUnheldFaultAnswerLong st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len) ∧
    Architecture.stageDeliveredMessage (performReplyRecvUnheldFaultAnswerLong st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len) tid 0 =
      performReplyRecvUnheldFaultAnswerLong st c tid rid
        ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) epId ep.recvTailCode core
        ct.faultKind label ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2
        ct.faultX3 ct.faultX4 ct.faultX5 ct.faultX6 ct.faultX7 rf len := by
  have hTc : st.getTcb? c = some ct := (SystemState.getTcb?_eq_some_iff _ _ _).mpr hT
  obtain ⟨_, _, _, _, _, _, hNo, _⟩ := replyUnheldPopsInPlace_pop st c rid IpcMessage.empty ct hT hG
  have hCT : c.toObjId ≠ tid.toObjId := fun e => hNe (SeLe4n.ThreadId.toObjId_injective _ _ e).symm
  let msg : IpcMessage := { registers := longReplyRecvRegs rf st tid len, badge := badge }
  obtain ⟨hEq, x, hX, hB⟩ := replyRecvAnsweringOnCore_unheld_inPlace
    (replyRecvCallerFaultAnswer? st c label msg)
    st epId tid c rid IpcMessage.empty grant core ct ep0 rt ep rp (by simp [IpcMessage.empty])
    hT hIpc hRO hG hNe hE hS hR hA hEnq hRp hStash hRec
    (fun h => by rw [replyRecvCallerFaultAnswer?_of_fault st c ct tf label _ hTc hPF] at h; cases h)
  have hAns := replyRecvCallerFaultAnswer?_of_fault st c ct tf label msg hTc hPF
  have hNoL := storeFaultReplyLeg_noResizeDue st c rid hNo
  have hNoR := returnUnheldSchedContextInPlace_noResizeDue _ c ⟨replyHeadContextCode st rid - 1⟩ hNoL
  have hNoT := settleReturnedContext_noResizeDue _ (determineTargetCore st c)
    ⟨replyHeadContextCode st rid - 1⟩ hNoR
  have hW : ipcWordReadsAgree (PriorityInheritance.propagatePipChainCrossCore
      (removeRunnableOnCore (storeReceiveBlock
        (SchedContextOps.settleReturnedContext (returnUnheldSchedContextInPlace
          (storeReplyLeg st c rid IpcMessage.empty) c ⟨replyHeadContextCode st rid - 1⟩)
          (determineTargetCore st c) ⟨replyHeadContextCode st rid - 1⟩) epId tid
        ep.recvTailCode (SeLe4n.ReplyId.optCode (some rid))) tid core) tid core).1 st :=
    ((ipcBufferReadsAgree_storeReplyRecvBlockTail _ tid rid epId ep.recvTailCode core hNoT).trans
      ((ipcBufferReadsAgree_settleReturnedContext _ (determineTargetCore st c) _).trans
        ((ipcBufferReadsAgree_returnUnheldSchedContextInPlace _ c _ hNoL).trans
          (ipcBufferReadsAgree_storeFaultReplyLeg st c rid hNo)))).words
  have hL : replyRecvLegMessage (replyRecvCallerFaultAnswer? st c label msg) msg =
      IpcMessage.empty := by rw [hAns]; rfl
  refine ⟨?_, ?_⟩
  · unfold replyRecvTransferOnCore
    rw [hL, hEq]
    unfold performReplyRecvUnheldFaultAnswerLong replyRecvAnswerCaller
    rw [hAns]
    dsimp only
    rw [faultReplyApplyOnCore_decode_eq_performFaultAnswerLong _ c ct tf hPF _ _ tid rf len 1
      (replyWordOr_longReplyRecvRegs st _ tid rf len label hLen hW)]
    rfl
  · have h0 : (storeReplyLeg st c rid IpcMessage.empty).objects.noResizeDue := by
      rw [storeReplyLeg_eq_hold _ _ _ _ hNo, SystemState.mapTcbInPlace_noResizeDue]
      exact storeReplyLegReady_noResizeDue st c rid hNo
    have h1 := returnUnheldSchedContextInPlace_noResizeDue _ c ⟨replyHeadContextCode st rid - 1⟩ h0
    have h2 := settleReturnedContext_noResizeDue _ (determineTargetCore st c)
      ⟨replyHeadContextCode st rid - 1⟩ h1
    have h3 := storeReceiveBlock_noResizeDue _ epId tid ep.recvTailCode
      (SeLe4n.ReplyId.optCode (some rid)) h2
    have h4 := removeRunnableOnCore_noResizeDue _ tid core h3
    obtain ⟨x2, hX2, e2⟩ := propagatePipChainCrossCore_ipcStateCarried _ tid core h4 tid x hX
    obtain ⟨x3, hX3, e3⟩ := performFaultAnswerLong_ipcStateAt _ c tid ct.faultKind label
      ct.faultIp ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
      ct.faultX5 ct.faultX6 ct.faultX7 tid rf len 1 hCT
      (propagatePipChainCrossCore_noResizeDue _ _ _ h4) x2 hX2
    unfold performReplyRecvUnheldFaultAnswerLong
    exact Architecture.stageDeliveredMessage_id_when_blocked _ tid 0 x3 hX3
      (by rw [e3, e2, hB]; exact fun h => by cases h)

end SeLe4n.Kernel
