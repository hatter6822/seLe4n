-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.LongReceiveInPlace

/-!
# A reply of more than four words, written in place

A reply whose message runs past the inline words is decoded as the entry
decodes it (`longMessageDecode`): the inline words in the replier's saved
registers, the rest in its IPC buffer.  When every write of the reply stays in
its slot (`replyWakesInPlace`), the reply here wakes the caller holding no
message, runs the server's priority walk, then writes the inline words into
the caller's saved registers and copies the overflow words from the replier's
IPC buffer into the caller's, word by word (`deliverLongSendFrame`), as seL4's
`doReplyTransfer` copies them (`copyMRs`).  No message is built
(`performReplyRendezvous_eq_deliveredLong`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- The decode a long message's frame reads to: the inline words and then its
overflow slots' words, as `sid` (a reply, a reply-receive, or a send or a call
transferring capabilities). -/
def longMessageDecode (sid : SyscallId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) : SyscallDecodeResult :=
  { capAddr, msgInfo := mi, syscallId := sid,
    msgRegs := Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
      (overflowRegsFrom st tid 0 (mi.length - 4)).toArray,
    inlineCount := 4, overflowCount := mi.length - 4 }

@[simp] theorem longMessageDecode_overflowCount (sid : SyscallId) (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr)
    (mi : MessageInfo) : (longMessageDecode sid st tid rf capAddr mi).overflowCount = mi.length - 4 :=
  rfl

/-- What a long reply, reply-receive or capability-carrying send or call pins
about the decode, any of the routes. -/
theorem decodeSyscallArgsFromState_of_routedReplyLongAny (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (sid : SyscallId)
    (hR : (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr mi ∧
        sid = .reply) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyRecvLong capAddr mi ∧
        sid = .replyRecv) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi ∧
        4 < mi.length)) :
    SeLe4n.arm64DefaultLayout.msgRegs.size < mi.length ∧ mi.length ≤ maxMessageRegisters ∧
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      mergeOverflowWords st tid
        { capAddr, msgInfo := mi, syscallId := sid,
          msgRegs := SeLe4n.arm64DefaultLayout.msgRegs.map (readReg rf),
          inlineCount := SeLe4n.arm64DefaultLayout.msgRegs.size, overflowCount := 0 } := by
  rcases hR with ⟨hR, rfl⟩ | ⟨hR, rfl⟩ | ⟨hR, hGt⟩
  · exact decodeSyscallArgsFromState_of_routedReplyLong st tid _ rf 32 capAddr mi hR
  · exact decodeSyscallArgsFromState_of_routedReplyRecvLong st tid _ rf 32 capAddr mi hR
  · obtain ⟨-, -, hMax, -, hLong⟩ :=
      decodeSyscallArgsFromState_of_routedTransferring st tid _ rf 32 sid capAddr mi hR
    exact ⟨hGt, hMax, hLong hGt⟩

/-- **A routed long reply whose overflow slots all read decodes** to the
inline words and then those slots' words (`longMessageDecode`). -/
theorem decodeSyscallArgsFromState_of_routedReplyLong_ok (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (sid : SyscallId)
    (hR : (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr mi ∧
        sid = .reply) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyRecvLong capAddr mi ∧
        sid = .replyRecv) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi ∧
        4 < mi.length))
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (longMessageDecode sid st tid rf capAddr mi) := by
  obtain ⟨_, _, hDec⟩ := decodeSyscallArgsFromState_of_routedReplyLongAny st tid rf capAddr mi sid hR
  have hRd : syscallReadsOverflow sid = true := by
    rcases hR with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨hR, -⟩
    · rfl
    · rfl
    · rcases (decodeSyscallArgsFromState_of_routedTransferring st tid _ rf 32 sid capAddr mi
        hR).1 with rfl | rfl <;> rfl
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  have hM := mapM_readOverflowWord st tid (mi.length - 4) 0
    (fun j _ h2 => hRead j (by omega))
  rw [hDec]
  unfold mergeOverflowWords
  simp only [hRd, ↓reduceIte,
    Array.size_map, hSz, List.range_eq_range', hM, overflowRegsFrom_eq_map, List.map_map,
    bind, Except.bind, pure, Except.pure, longMessageDecode]
  rfl

/-- …and one with an overflow slot that does not read is clamped to its inline
words (`clampedFrameDecode`), as seL4 clamps a message with no IPC buffer. -/
theorem decodeSyscallArgsFromState_of_routedReplyLong_clamped (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (sid : SyscallId)
    (hR : (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyLong capAddr mi ∧
        sid = .reply) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .replyRecvLong capAddr mi ∧
        sid = .replyRecv) ∨
      (registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .transferring sid capAddr mi ∧
        4 < mi.length))
    (j : Nat) (hj : j < mi.length - 4) (e : Architecture.IpcBufferRead.IpcBufferReadError)
    (h0 : Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .error e) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (clampedFrameDecode sid rf capAddr mi) := by
  obtain ⟨hGt, _, hDec⟩ := decodeSyscallArgsFromState_of_routedReplyLongAny st tid rf capAddr mi sid hR
  have hRd : syscallReadsOverflow sid = true := by
    rcases hR with ⟨-, rfl⟩ | ⟨-, rfl⟩ | ⟨hR, -⟩
    · rfl
    · rfl
    · rcases (decodeSyscallArgsFromState_of_routedTransferring st tid _ rf 32 sid capAddr mi
        hR).1 with rfl | rfl <;> rfl
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  rw [hDec]
  rw [mergeOverflowWords_clamped st tid rf _ capAddr mi hRd
    ⟨_, by rw [List.range_eq_range']
           exact mapM_readOverflowWord_error st tid (mi.length - 4) 0
             ⟨j, e, Nat.zero_le _, by omega, h0⟩⟩]

/-- A long reply's message, read as the decode reads it, is its inline words
and then the words its IPC buffer holds (`longSendMessage`). -/
theorem longMessageDecode_message (sid : SyscallId) (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (badge : Option SeLe4n.Badge) (hGt : 4 ≤ mi.length) (hLen : mi.length ≤ maxMessageRegisters) :
    ({ registers := extractMessageRegisters (longMessageDecode sid st tid rf capAddr mi).msgRegs mi,
       badge := badge } : IpcMessage) =
      longSendMessage SeLe4n.arm64DefaultLayout rf st tid mi.length badge := by
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  simp only [extractMessageRegisters, longSendMessage, longMessageDecode]
  congr 1
  apply Array.extract_eq_self_of_le
  simp only [Array.size_append, Architecture.regMessageRegs, Array.size_map, hSz,
    List.size_toArray, overflowRegsFrom_length]
  omega

/-! ## The reply, delivered -/

theorem ipcBufferReadsAgree_unlinkReplyWaiter (st : SystemState) (w s : SeLe4n.ThreadId) :
    ipcBufferReadsAgree (st.unlinkReplyWaiter w s) st := by
  unfold SystemState.unlinkReplyWaiter
  dsimp only
  generalize st.replyPrevCode w = pv
  generalize st.replyNextCode w = nx
  have a1 := ipcBufferReadsAgree_updateTcbAtCode st pv
    (fun x => { x with replyWaiterNextCode := nx }) (fun _ => ⟨rfl, rfl⟩)
  generalize st.updateTcbAtCode pv (fun x => { x with replyWaiterNextCode := nx }) = s1 at a1
  have a2 := ipcBufferReadsAgree_updateTcbAtCode s1 nx
    (fun x => { x with replyWaiterPrevCode := pv }) (fun _ => ⟨rfl, rfl⟩)
  generalize s1.updateTcbAtCode nx (fun x => { x with replyWaiterPrevCode := pv }) = s2 at a2
  have a3 := ipcBufferReadsAgree_mapTcbInPlace s2 s (fun x => { x with
    replyWaitersHeadCode := if pv = 0 then nx else x.replyWaitersHeadCode,
    replyWaitersCount := x.replyWaitersCount - 1 }) (fun _ => ⟨rfl, rfl⟩)
  generalize s2.mapTcbInPlace s (fun x => { x with
    replyWaitersHeadCode := if pv = 0 then nx else x.replyWaitersHeadCode,
    replyWaitersCount := x.replyWaitersCount - 1 }) = s3 at a3
  exact (ipcBufferReadsAgree_mapTcbInPlace s3 w
    (fun x => { x with replyWaiterPrevCode := 0, replyWaiterNextCode := 0 })
    (fun _ => ⟨rfl, rfl⟩)).trans (a3.trans (a2.trans a1))

theorem ipcBufferReadsAgree_storeReplyRendezvousReady (st : SystemState)
    (c server : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (hNo : st.objects.noResizeDue) :
    ipcBufferReadsAgree (storeReplyRendezvousReady st c server rid) st := by
  unfold storeReplyRendezvousReady storeReplyLegReady
  dsimp only
  generalize hS1 : st.updateTcb c receiverReady = S1
  have a1 : ipcBufferReadsAgree S1 st :=
    hS1 ▸ ipcBufferReadsAgree_updateTcb st c receiverReady (fun _ => ⟨rfl, rfl⟩) hNo
  have hNo1 : S1.objects.noResizeDue := hS1 ▸ updateTcb_noResizeDue _ _ _ hNo
  generalize hS2 : enqueueRunnableOnCore S1 (determineTargetCore S1 c) c = S2
  have a2 : ipcBufferReadsAgree S2 S1 :=
    hS2 ▸ ipcBufferReadsAgree_enqueueRunnableOnCore S1 _ c hNo1
  have hNo2 : S2.objects.noResizeDue := hS2 ▸ enqueueRunnableOnCore_noResizeDue _ _ _ hNo1
  generalize hS3 : S2.modifyObject rid.toObjId replyConsumedObject = S3
  have a3 : ipcBufferReadsAgree S3 S2 :=
    hS3 ▸ ipcBufferReadsAgree_modifyObject S2 rid.toObjId replyConsumedObject
      (fun o => by cases o <;> rfl) hNo2
  have hNo3 : S3.objects.noResizeDue := hS3 ▸ modifyObject_noResizeDue _ _ _ hNo2
  have a4 := ipcBufferReadsAgree_updateTcb S3 c (fun t => { t with replyObjectCode := 0 })
    (fun _ => ⟨rfl, rfl⟩) hNo3
  exact (ipcBufferReadsAgree_unlinkReplyWaiter _ c server).trans
    (a4.trans (a3.trans (a2.trans a1)))

/-- **The long reply, delivered**: the caller woken without the message, the
server's priority walk, then the replier's inline words (read from its saved
registers `rf`) written into the caller's saved registers and its overflow
words copied from its IPC buffer into the caller's (`deliverLongSendFrame`). -/
@[noinline] def performReplyDeliveredLong (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (rf : SeLe4n.RegisterFile) (len : Nat) (replier : SeLe4n.ThreadId)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : CoreId) : SystemState :=
  deliverLongSendFrame (PriorityInheritance.propagatePipChainCrossCore
      (storeReplyRendezvousReady st c server rid) server core).1 c
    SeLe4n.arm64DefaultLayout rf len replier badgeWord badged 0

/-- **The reply rendezvous is the delivered one** for a message of more than
four words, its inline words read in the replier's registers and the rest in
its IPC buffer. -/
theorem performReplyRendezvous_eq_deliveredLong (st : SystemState) (c server : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (rf : SeLe4n.RegisterFile) (len : Nat) (replier : SeLe4n.ThreadId)
    (badgeWord : SeLe4n.Badge) (badged : Bool) (core : CoreId)
    (hNo : st.objects.noResizeDue) (hLen : 4 ≤ len) :
    performReplyRendezvous st c server rid
        (longSendMessage SeLe4n.arm64DefaultLayout rf st replier len
          (SeLe4n.Badge.opt badgeWord badged)) core =
      performReplyDeliveredLong st c server rid rf len replier badgeWord badged core := by
  have hNoS := storeReplyRendezvousReady_noResizeDue st c server rid hNo
  unfold performReplyRendezvous performReplyDeliveredLong
  rw [storeReplyRendezvous_eq_hold _ _ _ _ _ hNo, propagatePipChainCrossCore_msg _ _ _ _ _ _ _ hNoS]
  exact (deliverLongSendFrame_eq _ st c replier SeLe4n.arm64DefaultLayout rf len badgeWord badged 0
    (propagatePipChainCrossCore_noResizeDue _ server core hNoS)
    ((ipcBufferReadsAgree_propagatePipChainCrossCore _ server core hNoS).trans
      (ipcBufferReadsAgree_storeReplyRendezvousReady st c server rid hNo)).words rfl hLen).symm

end SeLe4n.Kernel
