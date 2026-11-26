/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.ReceiveLedgerCommute
import SeLe4n.Kernel.IPC.CrossCore.LongSendInPlace

/-!
# The `.replyRecv` caller answered in the reply step

WS-SX SX31.  seL4's `doReplyTransfer` writes the replied-to caller's frame (or
runs `handleFaultReply`) before `handleRecv` runs the receive.  The composite
`endpointReplyRecvAnsweringOnCore` answers the caller last, on the tail's
result.  The equality here says the two orders give the same result, for every
answer kind, so the definition can be switched to seL4's order with every
consumer's theorem carried across it.

The tail (the context return, the receive leg, the post-receive donation and
the priority hand-off) commutes with the answer's slot write
(`ReceiveAnswerCommute`, `ReceiveAnswerFrame`), and it leaves what the stage
reads off the caller as it was (`answerReadsKept`), so the stage computed on the
receive's entry state is the stage computed on the tail's result.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency

theorem applyReceiveLegPipHandoff_noResizeDue (Z : SystemState)
    (receiver dequeued walked : SeLe4n.ThreadId) (ec : CoreId) (hNo : Z.objects.noResizeDue) :
    (applyReceiveLegPipHandoff Z receiver dequeued walked ec).objects.noResizeDue := by
  unfold applyReceiveLegPipHandoff applyReceiverPipHandoff
  split
  · exact hNo
  · split
    · exact propagatePipChainCrossCore_noResizeDue _ _ _ hNo
    · exact hNo

section Tail

variable (r : SeLe4n.ThreadId) (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile)
  (μ : Option IpcMessage → Option IpcMessage) (κ : Nat → Nat)

/-- **The tail commutes with the answer's slot write.**  The tail is the
composite's after the reply step: the context return, the receive leg, the
post-receive donation and the priority hand-off. -/
theorem replyRecvReceiveTail_answer (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (rs : SeLe4n.ThreadId) (ec : CoreId)
    (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) (hR : r ≠ tid)
    (hHead : receiveRendezvousSender? (receiveReturnSchedContext true Z tid) epId ≠ some r) :
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true (Z.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ)) tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread rs ec)) =
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true Z tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread rs ec)).map
      (fun p : CapTransferSummary × SystemState =>
        (p.1, p.2.mapTcbInPlace r (TCB.withAnswerSlots ρ μ id κ))) := by
  have hNo1 := receiveReturnSchedContext_noResizeDue true Z tid hNo
  rw [receiveReturnSchedContext_answer r ρ μ κ true Z tid hNo hR,
    endpointReceiveDualWithCapsOnCore_answer r ρ μ κ _ epId tid (some rid) ec hHead (Ne.symm hR) hNo1]
  have hNo2 := endpointReceiveDualWithCapsOnCore_noResizeDue _ epId tid (some rid) ec hNo1
  generalize endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
    (receiveReturnSchedContext true Z tid) = p at hNo2 ⊢
  obtain ⟨st2, res⟩ := p
  cases res with
  | error e => rfl
  | ok v =>
    obtain ⟨nt, summary, x⟩ := v
    dsimp only at hNo2 ⊢
    rw [replyRecvPostReceiveDonation_answer r ρ μ κ tid rs nt ec ret? st2 hNo2]
    cases hP : replyRecvPostReceiveDonation tid rs nt ec ret? st2 with
    | error e => rfl
    | ok w =>
      obtain ⟨⟨⟩, st3⟩ := w
      have hNo3 := (replyRecvPostReceiveDonation_noResizeDue_answerReadsKept tid tid rs nt ec
        ret? st2 st3 hNo2 hP).1
      dsimp only [Except.map]
      rw [applyReceiveLegPipHandoff_answer r ρ μ κ st3 tid nt rs ec hNo3]


/-- **The tail's result**: it keeps no resize due and what the stage reads off
the caller `c`, which is neither the receiver nor the send queue's head. -/
theorem replyRecvReceiveTail_noResizeDue_answerReadsKept (c : SeLe4n.ThreadId)
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rs : SeLe4n.ThreadId)
    (ec : CoreId) (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) (hc : c ≠ tid)
    (hHead : receiveRendezvousSender? (receiveReturnSchedContext true Z tid) epId ≠ some c)
    (st2 : SystemState) (nt : SeLe4n.ThreadId) (summary : CapTransferSummary)
    (x : Option (CoreId × SgiKind))
    (hRx : endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
      (receiveReturnSchedContext true Z tid) = (st2, .ok (nt, summary, x)))
    (st3 : SystemState) (hP : replyRecvPostReceiveDonation tid rs nt ec ret? st2 = .ok ((), st3)) :
    (applyReceiveLegPipHandoff st3 tid nt rs ec).objects.noResizeDue ∧
      answerReadsKept c Z (applyReceiveLegPipHandoff st3 tid nt rs ec) := by
  have hNo1 := receiveReturnSchedContext_noResizeDue true Z tid hNo
  have hK1 := receiveReturnSchedContext_answerReadsKept c true Z tid hNo
  have hNo2 := endpointReceiveDualWithCapsOnCore_noResizeDue _ epId tid (some rid) ec hNo1
  have hK2 := endpointReceiveDualWithCapsOnCore_answerReadsKept c _ epId tid (some rid) ec
    hHead (Ne.symm hc) hNo1
  rw [hRx] at hNo2 hK2
  obtain ⟨hNo3, hK3⟩ :=
    replyRecvPostReceiveDonation_noResizeDue_answerReadsKept c tid rs nt ec ret? st2 st3 hNo2 hP
  exact ⟨applyReceiveLegPipHandoff_noResizeDue st3 tid nt rs ec hNo3,
    (hK1.trans hK2).trans (hK3.trans (applyReceiveLegPipHandoff_answerReadsKept c st3 tid nt rs ec hNo3))⟩


/-- **The answer moves ahead of the tail.**  An answer that is the caller's
slot write on the tail's entry state and on every state the tail can reach
(one with no resize due and the caller's reads kept) can be written before the
tail instead of after it. -/
theorem replyRecvReceiveTail_answerFirst (c : SeLe4n.ThreadId)
    (F : SystemState → SystemState)
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rs : SeLe4n.ThreadId)
    (ec : CoreId) (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) (hc : c ≠ tid)
    (hHead : receiveRendezvousSender? (receiveReturnSchedContext true Z tid) epId ≠ some c)
    (hFZ : F Z = Z.mapTcbInPlace c (TCB.withAnswerSlots ρ μ id κ))
    (hFX : ∀ X : SystemState, X.objects.noResizeDue → answerReadsKept c Z X →
      F X = X.mapTcbInPlace c (TCB.withAnswerSlots ρ μ id κ)) :
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true (F Z) tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread rs ec)) =
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true Z tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, F (applyReceiveLegPipHandoff st3 tid nextThread rs ec))) := by
  rw [hFZ, replyRecvReceiveTail_answer c ρ μ κ epId tid rid rs ec ret? Z hNo hc hHead]
  cases hRx : endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
      (receiveReturnSchedContext true Z tid) with
  | mk st2 res =>
    cases res with
    | error e => rfl
    | ok v =>
      obtain ⟨nt, summary, x⟩ := v
      dsimp only
      cases hP : replyRecvPostReceiveDonation tid rs nt ec ret? st2 with
      | error e => rfl
      | ok w =>
        obtain ⟨⟨⟩, st3⟩ := w
        obtain ⟨hNoF, hKF⟩ := replyRecvReceiveTail_noResizeDue_answerReadsKept c epId tid rid rs ec
          ret? Z hNo hc hHead st2 nt summary x hRx st3 hP
        dsimp only [Except.map]
        rw [hFX _ hNoF hKF]

/-- **An answer that writes nothing** moves ahead of the tail too. -/
theorem replyRecvReceiveTail_inertFirst (c : SeLe4n.ThreadId)
    (F : SystemState → SystemState)
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rs : SeLe4n.ThreadId)
    (ec : CoreId) (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) (hc : c ≠ tid)
    (hHead : receiveRendezvousSender? (receiveReturnSchedContext true Z tid) epId ≠ some c)
    (hFZ : F Z = Z)
    (hFX : ∀ X : SystemState, X.objects.noResizeDue → answerReadsKept c Z X → F X = X) :
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true (F Z) tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread rs ec)) =
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true Z tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, F (applyReceiveLegPipHandoff st3 tid nextThread rs ec))) := by
  rw [hFZ]
  cases hRx : endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
      (receiveReturnSchedContext true Z tid) with
  | mk st2 res =>
    cases res with
    | error e => rfl
    | ok v =>
      obtain ⟨nt, summary, x⟩ := v
      dsimp only
      cases hP : replyRecvPostReceiveDonation tid rs nt ec ret? st2 with
      | error e => rfl
      | ok w =>
        obtain ⟨⟨⟩, st3⟩ := w
        obtain ⟨hNoF, hKF⟩ := replyRecvReceiveTail_noResizeDue_answerReadsKept c epId tid rid rs ec
          ret? Z hNo hc hHead st2 nt summary x hRx st3 hP
        dsimp only
        rw [hFX _ hNoF hKF]


end Tail

/-! ## The ordinary answer and the restart are slot writes on every reachable state -/

section Stage

open Architecture

/-- The slot write staging a message of at most four words: its return frame,
reporting `n`, with no overflow word. -/
noncomputable abbrev deliveredAnswerSlots (m : IpcMessage) (n : Nat) : TCB → TCB :=
  TCB.withAnswerSlots
    (fun rf => rf.stageDeliveredWords (returnFrameOfMessage m n 0).x0
      (returnFrameOfMessage m n 0).x1 (returnFrameOfMessage m n 0).x2
      (returnFrameOfMessage m n 0).x3 (returnFrameOfMessage m n 0).x4
      (returnFrameOfMessage m n 0).x5)
    (fun _ => none) id id

/-- **Staging a short message is its slot write**, read off what the stage reads
alone: a ready thread holding a message of at most four words. -/
theorem stageDeliveredMessage_of_answerReads (X : SystemState) (c : SeLe4n.ThreadId) (n : Nat)
    (m : IpcMessage) (hNo : X.objects.noResizeDue)
    (hR : (X.getTcb? c).map tcbAnswerReads = some (.ready, some m))
    (hS : m.registers.size ≤ 4) :
    stageDeliveredMessage X c n = X.mapTcbInPlace c (deliveredAnswerSlots m n) := by
  rw [stageDeliveredMessage_eq_answerSlots X c n hNo]
  cases hT : X.getTcb? c with
  | none => rw [hT] at hR; cases hR
  | some t =>
    rw [hT] at hR
    simp only [Option.map_some, tcbAnswerReads, Option.some.injEq, Prod.mk.injEq] at hR
    obtain ⟨h1, h2⟩ := hR
    have hW : messageOverflowWrites X t m = [] := by
      rw [messageOverflowWrites_eq_impl]
      simp only [messageOverflowWritesImpl, hS, ↓reduceIte]
    simp only [h1, h2, ↓reduceIte, hW, recordPhysicalWrites_nil, List.length_nil]

/-- **Staging writes nothing** on a thread that is not a ready one holding a
message. -/
theorem stageDeliveredMessage_of_answerReads_inert (X : SystemState) (c : SeLe4n.ThreadId)
    (n : Nat) (hNo : X.objects.noResizeDue)
    (hR : ∀ m, (X.getTcb? c).map tcbAnswerReads ≠ some (.ready, some m)) :
    stageDeliveredMessage X c n = X := by
  rw [stageDeliveredMessage_eq_answerSlots X c n hNo]
  cases hT : X.getTcb? c with
  | none => rfl
  | some t =>
    dsimp only
    by_cases h1 : t.ipcState = .ready
    · cases h2 : t.pendingMessage with
      | none => simp only [h1, ↓reduceIte]
      | some m =>
        exact absurd (by rw [hT]; simp only [Option.map_some, tcbAnswerReads, h1, h2]) (hR m)
    · simp only [h1, ↓reduceIte]

end Stage

/-! ## Each answer kind moves ahead of the tail -/

section Kinds

open Architecture

/-- **The ordinary answer moves ahead of the tail**, given that a message the
caller holds fits in its registers (no overflow word: what the stage records in
the physical-write log is then empty on every state). -/
theorem replyRecvReceiveTail_stageFirst (c : SeLe4n.ThreadId) (n : Nat)
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rs : SeLe4n.ThreadId)
    (ec : CoreId) (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) (hc : c ≠ tid)
    (hHead : receiveRendezvousSender? (receiveReturnSchedContext true Z tid) epId ≠ some c)
    (hLog : ∀ t m, Z.getTcb? c = some t → t.pendingMessage = some m → m.registers.size ≤ 4) :
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true (stageDeliveredMessage Z c n) tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread rs ec)) =
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true Z tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, stageDeliveredMessage
              (applyReceiveLegPipHandoff st3 tid nextThread rs ec) c n)) := by
  by_cases hM : ∃ m, (Z.getTcb? c).map tcbAnswerReads = some (.ready, some m)
  · obtain ⟨m, hm⟩ := hM
    have hS : m.registers.size ≤ 4 := by
      cases hT : Z.getTcb? c with
      | none => rw [hT] at hm; cases hm
      | some t =>
        rw [hT] at hm
        simp only [Option.map_some, tcbAnswerReads, Option.some.injEq, Prod.mk.injEq] at hm
        exact hLog t m hT hm.2
    exact replyRecvReceiveTail_answerFirst _ _ _ c (fun X => stageDeliveredMessage X c n)
      epId tid rid rs ec ret? Z hNo hc hHead
      (stageDeliveredMessage_of_answerReads Z c n m hNo hm hS)
      (fun X hNoX hK => stageDeliveredMessage_of_answerReads X c n m hNoX
        (by unfold answerReadsKept at hK; rw [hK]; exact hm) hS)
  · have hM' : ∀ m, (Z.getTcb? c).map tcbAnswerReads ≠ some (.ready, some m) :=
      fun m h => hM ⟨m, h⟩
    exact replyRecvReceiveTail_inertFirst c (fun X => stageDeliveredMessage X c n)
      epId tid rid rs ec ret? Z hNo hc hHead
      (stageDeliveredMessage_of_answerReads_inert Z c n hNo hM')
      (fun X hNoX hK => stageDeliveredMessage_of_answerReads_inert X c n hNoX
        (fun m h => hM' m (by unfold answerReadsKept at hK; rw [← hK]; exact h)))

/-- **The restart moves ahead of the tail**: it is the caller's slot write on
every state with no resize due. -/
theorem replyRecvReceiveTail_restartFirst (c : SeLe4n.ThreadId) (f : FaultRestartFrame)
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rs : SeLe4n.ThreadId)
    (ec : CoreId) (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) (hc : c ≠ tid)
    (hHead : receiveRendezvousSender? (receiveReturnSchedContext true Z tid) epId ≠ some c) :
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true (applyFaultRestart Z c f) tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread rs ec)) =
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true Z tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, applyFaultRestart
              (applyReceiveLegPipHandoff st3 tid nextThread rs ec) c f)) :=
  replyRecvReceiveTail_answerFirst _ _ _ c (fun X => applyFaultRestart X c f)
    epId tid rid rs ec ret? Z hNo hc hHead (applyFaultRestart_eq_answerSlots Z c f hNo)
    (fun X hNoX _ => applyFaultRestart_eq_answerSlots X c f hNoX)

/-- The overflow words a delivery writes, on two states that read every IPC
buffer's words alike, to a thread they read alike. -/
theorem overflowDeliveryWrites_of_wordReadsAgree {X Z : SystemState} (h : ipcWordReadsAgree X Z)
    (t t' : TCB) (hv : t'.spaceCells[2] = t.spaceCells[2]) (hb : t'.ipcBuffer = t.ipcBuffer) :
    ∀ (ws : List SeLe4n.RegValue) (idx : Nat),
      overflowDeliveryWrites X t' ws idx = overflowDeliveryWrites Z t ws idx
  | [], _ => rfl
  | w :: rest, idx => by
      unfold overflowDeliveryWrites
      have hP : IpcBufferRead.ipcBufferSlotPAddr? X t' idx true =
          IpcBufferRead.ipcBufferSlotPAddr? Z t idx true := by
        unfold IpcBufferRead.ipcBufferSlotPAddr? IpcBufferRead.lookupIPCBuffer
        rw [hv, hb, IpcBufferRead.bufferFrameBase?_congr h.getFrame?]
      rw [hP, overflowDeliveryWrites_of_wordReadsAgree h t t' hv hb rest (idx + 1)]

/-- **The caller's overflow words are the same** on two states that read every
IPC buffer's words alike. -/
theorem messageOverflowWrites_of_wordReadsAgree {X Z : SystemState} (h : ipcWordReadsAgree X Z)
    (c : SeLe4n.ThreadId) (t t' : TCB) (hZ : Z.getTcb? c = some t) (hX : X.getTcb? c = some t')
    (m : IpcMessage) : messageOverflowWrites X t' m = messageOverflowWrites Z t m := by
  have hT := h.getTcb?_buffer c
  rw [hX, hZ] at hT
  simp only [Option.map_some, Option.some.injEq, Prod.mk.injEq] at hT
  exact overflowDeliveryWrites_of_wordReadsAgree h t t' hT.1 hT.2 _ 0

/-- **An answer that is a slot write and a recording moves ahead of the tail**
where the dequeued sender asks to transfer nothing: the recording commutes with
the tail (`replyRecvReceiveTail_ledger`, D58) and the slot write with it
(`replyRecvReceiveTail_answer`). -/
theorem replyRecvReceiveTail_recordFirst (c : SeLe4n.ThreadId)
    (ρ : SeLe4n.RegisterFile → SeLe4n.RegisterFile) (μ : Option IpcMessage → Option IpcMessage)
    (κ : Nat → Nat) (W : List PhysicalWrite) (F : SystemState → SystemState)
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rs : SeLe4n.ThreadId)
    (ec : CoreId) (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) (hc : c ≠ tid)
    (hHead : receiveRendezvousSender? (receiveReturnSchedContext true Z tid) epId ≠ some c)
    (hNoCaps : receiveCapRequest (receiveReturnSchedContext true Z tid) epId = none)
    (hFZ : F Z = recordPhysicalWrites (Z.mapTcbInPlace c (TCB.withAnswerSlots ρ μ id κ)) W)
    (hFX : ∀ st2 nt summary x st3,
      endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true Z tid) = (st2, .ok (nt, summary, x)) →
      replyRecvPostReceiveDonation tid rs nt ec ret? st2 = .ok ((), st3) →
      F (applyReceiveLegPipHandoff st3 tid nt rs ec) =
        recordPhysicalWrites ((applyReceiveLegPipHandoff st3 tid nt rs ec).mapTcbInPlace c
          (TCB.withAnswerSlots ρ μ id κ)) W) :
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true (F Z) tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread rs ec)) =
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true Z tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, F (applyReceiveLegPipHandoff st3 tid nextThread rs ec))) := by
  have hNoCapsM : receiveCapRequest (receiveReturnSchedContext true
      (Z.mapTcbInPlace c (TCB.withAnswerSlots ρ μ id κ)) tid) epId = none := by
    rw [receiveReturnSchedContext_answer c ρ μ κ true Z tid hNo hc,
      receiveCapRequest_answer c ρ μ κ _ epId hHead, hNoCaps]
  rw [hFZ]
  refine Eq.trans (replyRecvReceiveTail_ledger W epId tid rid rs ec ret? _ hNoCapsM) ?_
  refine (congrArg (Except.map _)
    (replyRecvReceiveTail_answer c ρ μ κ epId tid rid rs ec ret? Z hNo hc hHead)).trans ?_
  cases hRx : endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
      (receiveReturnSchedContext true Z tid) with
  | mk st2 res =>
    cases res with
    | error e => rfl
    | ok v =>
      obtain ⟨nt, summary, x⟩ := v
      dsimp only
      cases hP : replyRecvPostReceiveDonation tid rs nt ec ret? st2 with
      | error e => rfl
      | ok w =>
        obtain ⟨⟨⟩, st3⟩ := w
        dsimp only [Except.map]
        rw [hFX st2 nt summary x st3 hRx hP]
/-- The register writes of a stage reporting `n` with `k` overflow words. -/
noncomputable abbrev stagedAnswerRegs (m : IpcMessage) (n k : Nat) :
    SeLe4n.RegisterFile → SeLe4n.RegisterFile :=
  fun rf => rf.stageDeliveredWords (returnFrameOfMessage m n k).x0
    (returnFrameOfMessage m n k).x1 (returnFrameOfMessage m n k).x2
    (returnFrameOfMessage m n k).x3 (returnFrameOfMessage m n k).x4
    (returnFrameOfMessage m n k).x5

/-- **Staging a message is its slot write and the recording of its overflow
words**, on a ready thread holding it. -/
theorem stageDeliveredMessage_of_ready (X : SystemState) (c : SeLe4n.ThreadId) (n : Nat)
    (t : TCB) (m : IpcMessage) (hNo : X.objects.noResizeDue) (hT : X.getTcb? c = some t)
    (h1 : t.ipcState = .ready) (h2 : t.pendingMessage = some m) :
    stageDeliveredMessage X c n =
      recordPhysicalWrites (X.mapTcbInPlace c (TCB.withAnswerSlots
        (stagedAnswerRegs m n (messageOverflowWrites X t m).length) (fun _ => none) id id))
        (messageOverflowWrites X t m) := by
  rw [stageDeliveredMessage_eq_answerSlots X c n hNo, hT]
  simp only [h1, h2, ↓reduceIte]

/-- **The ordinary answer moves ahead of the tail where the tail records
nothing** (D55's second premise, WS-SX D58): the dequeued sender asks to
transfer nothing, and every state the tail can reach reads the caller's IPC
buffer as its entry state does, so the stage records the same overflow words
before the tail and after it. -/
theorem replyRecvReceiveTail_stageFirst_quiet (c : SeLe4n.ThreadId) (n : Nat)
    (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (rs : SeLe4n.ThreadId)
    (ec : CoreId) (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z : SystemState)
    (hNo : Z.objects.noResizeDue) (hc : c ≠ tid)
    (hHead : receiveRendezvousSender? (receiveReturnSchedContext true Z tid) epId ≠ some c)
    (hNoCaps : receiveCapRequest (receiveReturnSchedContext true Z tid) epId = none)
    (hBuf : ∀ st2 nt summary x st3,
      endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true Z tid) = (st2, .ok (nt, summary, x)) →
      replyRecvPostReceiveDonation tid rs nt ec ret? st2 = .ok ((), st3) →
      ipcWordReadsAgree (applyReceiveLegPipHandoff st3 tid nt rs ec) Z) :
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true (stageDeliveredMessage Z c n) tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread rs ec)) =
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true Z tid) with
      | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
      | (st2, .ok (nextThread, summary, _)) =>
          match replyRecvPostReceiveDonation tid rs nextThread ec ret? st2 with
          | .error e => .error e
          | .ok ((), st3) => .ok (summary, stageDeliveredMessage
              (applyReceiveLegPipHandoff st3 tid nextThread rs ec) c n)) := by
  by_cases hM : ∃ m, (Z.getTcb? c).map tcbAnswerReads = some (.ready, some m)
  · obtain ⟨m, hm⟩ := hM
    cases hT : Z.getTcb? c with
    | none => rw [hT] at hm; cases hm
    | some t =>
      rw [hT] at hm
      simp only [Option.map_some, tcbAnswerReads, Option.some.injEq, Prod.mk.injEq] at hm
      exact replyRecvReceiveTail_recordFirst c _ _ _ (messageOverflowWrites Z t m)
        (fun X => stageDeliveredMessage X c n) epId tid rid rs ec ret? Z hNo hc hHead hNoCaps
        (stageDeliveredMessage_of_ready Z c n t m hNo hT hm.1 hm.2)
        (fun st2 nt summary x st3 hRx hP => by
          obtain ⟨hNoF, hKF⟩ := replyRecvReceiveTail_noResizeDue_answerReadsKept c epId tid rid rs
            ec ret? Z hNo hc hHead st2 nt summary x hRx st3 hP
          have hK := hKF
          unfold answerReadsKept at hK
          rw [hT] at hK
          cases hX : (applyReceiveLegPipHandoff st3 tid nt rs ec).getTcb? c with
          | none => rw [hX] at hK; cases hK
          | some t' =>
            rw [hX] at hK
            simp only [Option.map_some, tcbAnswerReads, Option.some.injEq, Prod.mk.injEq] at hK
            have hW := messageOverflowWrites_of_wordReadsAgree (hBuf st2 nt summary x st3 hRx hP)
              c t t' hT hX m
            dsimp only
            rw [stageDeliveredMessage_of_ready _ c n t' m hNoF hX (hK.1.trans hm.1)
              (hK.2.trans hm.2), hW])
  · have hM' : ∀ m, (Z.getTcb? c).map tcbAnswerReads ≠ some (.ready, some m) :=
      fun m h => hM ⟨m, h⟩
    exact replyRecvReceiveTail_inertFirst c (fun X => stageDeliveredMessage X c n)
      epId tid rid rs ec ret? Z hNo hc hHead
      (stageDeliveredMessage_of_answerReads_inert Z c n hNo hM')
      (fun X hNoX hK => stageDeliveredMessage_of_answerReads_inert X c n hNoX
        (fun m h => hM' m (by unfold answerReadsKept at hK; rw [← hK]; exact h)))

end Kinds

/-! ## The composite, answer first -/

/-- **The reply step's prefix carries the tail's reordering**: the composite
written with the answer in the reply step, before the receive leg (seL4's
`doReplyTransfer` before `handleRecv`), is `endpointReplyRecvAnsweringOnCore`
whenever, on every state the reply step can leave, the answer moves ahead of
the tail. -/
theorem endpointReplyRecvAnsweringOnCore_answerFirst_of_tail
    (answer : Option Architecture.FaultReplyOutcome) (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (ec : CoreId) (st : SystemState)
    (hTail : ∀ st1 sgi returnedSc? st1q replySummary st1p,
      endpointReplyOnCore tid prevCaller msg ec st = (st1, .ok sgi) →
      replyRecvPopDonation rid prevCaller st1 = .ok (returnedSc?, st1q) →
      replyRecvReplyTransfer answer st tid prevCaller grant st1q = .ok (replySummary, st1p) →
      (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
          (receiveReturnSchedContext true
            (replyRecvAnswerCaller answer st1p prevCaller replySummary.capInfo) tid) with
        | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
        | (st2, .ok (nextThread, summary, _)) =>
            match replyRecvPostReceiveDonation tid ((recordedReplyServer? st prevCaller).getD tid)
                nextThread ec returnedSc? st2 with
            | .error e => .error e
            | .ok ((), st3) => .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread
                ((recordedReplyServer? st prevCaller).getD tid) ec)) =
      (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
          (receiveReturnSchedContext true st1p tid) with
        | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
        | (st2, .ok (nextThread, summary, _)) =>
            match replyRecvPostReceiveDonation tid ((recordedReplyServer? st prevCaller).getD tid)
                nextThread ec returnedSc? st2 with
            | .error e => .error e
            | .ok ((), st3) => .ok (summary, replyRecvAnswerCaller answer
                (applyReceiveLegPipHandoff st3 tid nextThread
                  ((recordedReplyServer? st prevCaller).getD tid) ec) prevCaller replySummary.capInfo))) :
    (let recordedServer := (recordedReplyServer? st prevCaller).getD tid
     match endpointReplyOnCore tid prevCaller msg ec st with
     | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
     | (st1, .ok _) =>
         match replyRecvPopDonation rid prevCaller st1 with
         | .error e => .error e
         | .ok (returnedSc?, st1q) =>
         match replyRecvReplyTransfer answer st tid prevCaller grant st1q with
         | .error e => .error e
         | .ok (replySummary, st1p) =>
         match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
             (receiveReturnSchedContext true
               (replyRecvAnswerCaller answer st1p prevCaller replySummary.capInfo) tid) with
         | (_, .error e) => .error e
         | (st2, .ok (nextThread, summary, _)) =>
             match replyRecvPostReceiveDonation tid recordedServer nextThread ec returnedSc? st2 with
             | .error e => .error e
             | .ok ((), st3) =>
                 .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread recordedServer ec)) =
      endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg grant ec st := by
  unfold endpointReplyRecvAnsweringOnCore
  cases h1 : endpointReplyOnCore tid prevCaller msg ec st with
  | mk st1 r1 =>
    cases r1 with
    | error e => rfl
    | ok sgi =>
      dsimp only
      cases h2 : replyRecvPopDonation rid prevCaller st1 with
      | error e => rfl
      | ok v =>
        obtain ⟨returnedSc?, st1q⟩ := v
        dsimp only
        cases h3 : replyRecvReplyTransfer answer st tid prevCaller grant st1q with
        | error e => rfl
        | ok w =>
          obtain ⟨replySummary, st1p⟩ := w
          exact hTail st1 sgi returnedSc? st1q replySummary st1p h1 h2 h3


/-- **The caller answered in the reply step** (seL4's `doReplyTransfer` before
`handleRecv`): for an ordinary answer and a fault restart, the composite written
with the answer before the receive leg is `endpointReplyRecvAnsweringOnCore`.
On every state the reply step can leave, the caller is not the receiver and not
the send queue's head at the receive's entry, no resize of the object table is
due, and, on an ordinary answer, either a message the caller holds fits in its
registers (no overflow word, so the physical-write log is untouched) or the
tail records nothing and reads the caller's IPC buffer as the reply step left
it (WS-SX D55's two premises; the second is D58's).  A
declined fault reply (`abandon`) is not covered: its downstream proofs are
restated with the definition switch (WS-SX D57). -/
theorem endpointReplyRecvAnsweringOnCore_answerFirst
    (answer : Option Architecture.FaultReplyOutcome) (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (prevCaller : SeLe4n.ThreadId) (msg : IpcMessage) (grant : Bool)
    (ec : CoreId) (st : SystemState)
    (hAns : answer ≠ some .abandon) (hc : prevCaller ≠ tid)
    (hStep : ∀ st1 sgi returnedSc? st1q replySummary st1p,
      endpointReplyOnCore tid prevCaller msg ec st = (st1, .ok sgi) →
      replyRecvPopDonation rid prevCaller st1 = .ok (returnedSc?, st1q) →
      replyRecvReplyTransfer answer st tid prevCaller grant st1q = .ok (replySummary, st1p) →
      st1p.objects.noResizeDue ∧
      receiveRendezvousSender? (receiveReturnSchedContext true st1p tid) epId ≠ some prevCaller ∧
      (answer = none →
        (∀ t m, st1p.getTcb? prevCaller = some t → t.pendingMessage = some m →
          m.registers.size ≤ 4) ∨
        (receiveCapRequest (receiveReturnSchedContext true st1p tid) epId = none ∧
          ∀ st2 nt summary x st3,
            endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
              (receiveReturnSchedContext true st1p tid) = (st2, .ok (nt, summary, x)) →
            replyRecvPostReceiveDonation tid ((recordedReplyServer? st prevCaller).getD tid) nt ec
              returnedSc? st2 = .ok ((), st3) →
            ipcWordReadsAgree (applyReceiveLegPipHandoff st3 tid nt
              ((recordedReplyServer? st prevCaller).getD tid) ec) st1p))) :
    (let recordedServer := (recordedReplyServer? st prevCaller).getD tid
     match endpointReplyOnCore tid prevCaller msg ec st with
     | (_, .error e) => (Except.error e : Except KernelError (CapTransferSummary × SystemState))
     | (st1, .ok _) =>
         match replyRecvPopDonation rid prevCaller st1 with
         | .error e => .error e
         | .ok (returnedSc?, st1q) =>
         match replyRecvReplyTransfer answer st tid prevCaller grant st1q with
         | .error e => .error e
         | .ok (replySummary, st1p) =>
         match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
             (receiveReturnSchedContext true
               (replyRecvAnswerCaller answer st1p prevCaller replySummary.capInfo) tid) with
         | (_, .error e) => .error e
         | (st2, .ok (nextThread, summary, _)) =>
             match replyRecvPostReceiveDonation tid recordedServer nextThread ec returnedSc? st2 with
             | .error e => .error e
             | .ok ((), st3) =>
                 .ok (summary, applyReceiveLegPipHandoff st3 tid nextThread recordedServer ec)) =
      endpointReplyRecvAnsweringOnCore answer epId tid rid prevCaller msg grant ec st := by
  apply endpointReplyRecvAnsweringOnCore_answerFirst_of_tail
  intro st1 sgi returnedSc? st1q replySummary st1p h1 h2 h3
  obtain ⟨hNo, hHead, hLog⟩ := hStep st1 sgi returnedSc? st1q replySummary st1p h1 h2 h3
  cases answer with
  | none =>
    rcases hLog rfl with hShort | ⟨hNoCaps, hBuf⟩
    · exact replyRecvReceiveTail_stageFirst prevCaller replySummary.capInfo epId tid rid _ ec
        returnedSc? st1p hNo hc hHead hShort
    · exact replyRecvReceiveTail_stageFirst_quiet prevCaller replySummary.capInfo epId tid rid _ ec
        returnedSc? st1p hNo hc hHead hNoCaps hBuf
  | some o =>
    cases o with
    | restart f =>
      exact replyRecvReceiveTail_restartFirst prevCaller f epId tid rid _ ec returnedSc? st1p
        hNo hc hHead
    | abandon => exact absurd rfl hAns
