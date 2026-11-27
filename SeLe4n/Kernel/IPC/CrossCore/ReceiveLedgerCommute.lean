/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.CrossCore.ReceiveAnswerFrame

/-!
# The receive tail commutes with the physical-write log

WS-SX SX32 (D58).  The ordinary answer stages a message of more than four
words by recording its overflow words in the physical-write log
(`stageDeliveredMessage`).  Moving that answer ahead of the `.replyRecv`
receive tail needs the tail to commute with a recording.  Recording touches the
log alone, and no step of the tail reads it; the receive transfer is the one
step that records, and it records nothing where the dequeued sender asks to
transfer nothing.  So each step is shown to commute with a recording
(`F (recordPhysicalWrites Z ws) = recordPhysicalWrites (F Z) ws`, or its
`Except` form), and the tail with them (`replyRecvReceiveTail_ledger`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model SeLe4n.Kernel.RobinHood SeLe4n.Kernel.Concurrency
open Architecture (recordPhysicalWrites PhysicalWrite)

section Ledger

variable (ws : List PhysicalWrite)

/-- The object reads see through a recording. -/
theorem getObject?_ledger (st : SystemState) (k) : (recordPhysicalWrites st ws).getObject? k = st.getObject? k := rfl
theorem getTcb?_ledger (st : SystemState) (k) : (recordPhysicalWrites st ws).getTcb? k = st.getTcb? k := rfl
theorem lookupTcb_ledger (st : SystemState) (k) : lookupTcb (recordPhysicalWrites st ws) k = lookupTcb st k := rfl
theorem getEndpoint?_ledger (st : SystemState) (k) : (recordPhysicalWrites st ws).getEndpoint? k = st.getEndpoint? k := rfl
theorem getReply?_ledger (st : SystemState) (k) : (recordPhysicalWrites st ws).getReply? k = st.getReply? k := rfl
/-- A store commutes with a recording. -/
theorem storeObject_ledger (st : SystemState) (k : SeLe4n.ObjId) (o : KernelObject) :
    storeObject k o (recordPhysicalWrites st ws) =
      (storeObject k o st).map (fun p => (p.1, recordPhysicalWrites p.2 ws)) := rfl
theorem modifyTcb_ledger (st : SystemState) (t : SeLe4n.ThreadId) (f : TCB → TCB) :
    modifyTcb (recordPhysicalWrites st ws) t f = (modifyTcb st t f).map (recordPhysicalWrites · ws) := by
  unfold modifyTcb; rw [lookupTcb_ledger]; cases lookupTcb st t <;> rfl
theorem storeTcbIpcStateAndMessage_ledger (st : SystemState) (t) (s) (m) :
    storeTcbIpcStateAndMessage (recordPhysicalWrites st ws) t s m =
      (storeTcbIpcStateAndMessage st t s m).map (recordPhysicalWrites · ws) :=
  modifyTcb_ledger ws st t _
theorem storeTcbQueueLinks_ledger (st : SystemState) (t) (p pp n) :
    storeTcbQueueLinks (recordPhysicalWrites st ws) t p pp n =
      (storeTcbQueueLinks st t p pp n).map (recordPhysicalWrites · ws) :=
  modifyTcb_ledger ws st t _
/-- The send queue's pop commutes with a recording. -/
theorem endpointQueuePopHead_ledger (st : SystemState) (k : SeLe4n.ObjId) (b : Bool) :
    endpointQueuePopHead k b (recordPhysicalWrites st ws) =
      (endpointQueuePopHead k b st).map (fun p => (p.1, p.2.1, recordPhysicalWrites p.2.2 ws)) := by
  unfold endpointQueuePopHead
  rw [getObject?_ledger]
  cases st.getObject? k with
  | none => rfl
  | some o =>
    cases o with
    | endpoint ep =>
      dsimp only
      split
      · rfl
      · rw [lookupTcb_ledger]
        cases lookupTcb st _ with
        | none => rfl
        | some h =>
          dsimp only
          rw [storeObject_ledger]
          cases storeObject k _ st with
          | error e => rfl
          | ok p =>
            obtain ⟨⟨⟩, S1⟩ := p
            dsimp only [Except.map]
            cases h.queueNext with
            | none =>
              dsimp only
              rw [storeTcbQueueLinks_ledger]
              cases storeTcbQueueLinks S1 _ none none none <;> rfl
            | some nx =>
              dsimp only
              rw [lookupTcb_ledger]
              cases lookupTcb S1 nx with
              | none => rfl
              | some nt =>
                dsimp only
                rw [storeTcbQueueLinks_ledger]
                cases storeTcbQueueLinks S1 nx none (some .endpointHead) nt.queueNext with
                | error e => rfl
                | ok S2 =>
                  dsimp only [Except.map]
                  rw [storeTcbQueueLinks_ledger]
                  cases storeTcbQueueLinks S2 _ none none none <;> rfl
    | _ => rfl
/-- The receive queue's enqueue commutes with a recording. -/
theorem endpointQueueEnqueue_ledger (st : SystemState) (k : SeLe4n.ObjId) (b : Bool) (t : SeLe4n.ThreadId) :
    endpointQueueEnqueue k b t (recordPhysicalWrites st ws) =
      (endpointQueueEnqueue k b t st).map (recordPhysicalWrites · ws) := by
  unfold endpointQueueEnqueue
  rw [getObject?_ledger]
  cases st.getObject? k with
  | none => rfl
  | some o =>
    cases o with
    | endpoint ep =>
      dsimp only
      rw [lookupTcb_ledger]
      cases lookupTcb st t with
      | none => rfl
      | some tcb =>
        dsimp only
        split
        · rfl
        split
        · rfl
        split
        · rw [storeObject_ledger]
          cases storeObject k _ st with
          | error e => rfl
          | ok p => obtain ⟨⟨⟩, S1⟩ := p; exact storeTcbQueueLinks_ledger ws S1 t _ _ _
        · rw [lookupTcb_ledger]
          cases lookupTcb st _ with
          | none => rfl
          | some tl =>
            dsimp only
            rw [storeObject_ledger]
            cases storeObject k _ st with
            | error e => rfl
            | ok p =>
              obtain ⟨⟨⟩, S1⟩ := p
              dsimp only [Except.map]
              rw [storeTcbQueueLinks_ledger]
              cases storeTcbQueueLinks S1 _ _ _ _ with
              | error e => rfl
              | ok S2 => exact storeTcbQueueLinks_ledger ws S2 t _ _ _
    | _ => rfl
theorem linkReply_ledger (st : SystemState) (rid : SeLe4n.ReplyId) (c : SeLe4n.ThreadId) :
    SystemState.linkReply rid c (recordPhysicalWrites st ws) =
      (SystemState.linkReply rid c st).map (fun p => (p.1, recordPhysicalWrites p.2 ws)) := by
  unfold SystemState.linkReply; rw [getReply?_ledger]
  cases st.getReply? rid with
  | none => rfl
  | some r => dsimp only; split <;> rfl
theorem linkCallerReply_ledger (st : SystemState) (c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) :
    SystemState.linkCallerReply c rid (recordPhysicalWrites st ws) =
      (SystemState.linkCallerReply c rid st).map (fun p => (p.1, recordPhysicalWrites p.2 ws)) := by
  unfold SystemState.linkCallerReply
  rw [linkReply_ledger]
  cases SystemState.linkReply rid c st with
  | error e => rfl
  | ok p =>
    obtain ⟨⟨⟩, S1⟩ := p
    dsimp only [Except.map]
    rw [getTcb?_ledger]
    cases S1.getTcb? c with
    | none => rfl
    | some t => dsimp only; split <;> rfl
theorem recordReplyStasher_ledger (st : SystemState) (code : Nat) (t : SeLe4n.ThreadId) :
    (recordPhysicalWrites st ws).recordReplyStasher code t =
      recordPhysicalWrites (st.recordReplyStasher code t) ws := by
  unfold SystemState.recordReplyStasher
  cases code with
  | zero => rfl
  | succ k =>
    dsimp only; rw [getReply?_ledger]
    cases st.getReply? _ with
    | none => rfl
    | some r => rfl
theorem wakeThread_ledger (st : SystemState) (t : SeLe4n.ThreadId) (ec : CoreId) :
    wakeThread (recordPhysicalWrites st ws) t ec =
      (recordPhysicalWrites (wakeThread st t ec).1 ws, (wakeThread st t ec).2) := by
  unfold wakeThread
  dsimp only
  rw [enqueueRunnableOnCore_ledger]
  rfl
theorem blockedSenderMessage_ledger (st : SystemState) (s : SeLe4n.ThreadId) (t : TCB) :
    blockedSenderMessage (recordPhysicalWrites st ws) s t = blockedSenderMessage st s t := rfl
theorem replyStashValid_ledger (st : SystemState) (r) :
    (recordPhysicalWrites st ws).replyStashValid r = st.replyStashValid r := rfl
theorem receiveRendezvousSender?_ledger (st : SystemState) (k) :
    receiveRendezvousSender? (recordPhysicalWrites st ws) k = receiveRendezvousSender? st k := rfl
theorem receiveCapRequest_ledger (st : SystemState) (k) :
    receiveCapRequest (recordPhysicalWrites st ws) k = receiveCapRequest st k := rfl
theorem getSchedContext?_ledger (st : SystemState) (k) : (recordPhysicalWrites st ws).getSchedContext? k = st.getSchedContext? k := rfl
theorem outerCallerAcceptable_ledger (st : SystemState) (a b o) : outerCallerAcceptable (recordPhysicalWrites st ws) a b o = outerCallerAcceptable st a b o := rfl
theorem heldPopOuter?_ledger (st : SystemState) (a o) : heldPopOuter? (recordPhysicalWrites st ws) a o = heldPopOuter? st a o := rfl
theorem donationHeadOf?_ledger (st : SystemState) (k sc) : donationHeadOf? (recordPhysicalWrites st ws) k sc = donationHeadOf? st k sc := rfl
theorem replyStackOuterCaller?_ledger (st : SystemState) (k) : replyStackOuterCaller? (recordPhysicalWrites st ws) k = replyStackOuterCaller? st k := rfl
theorem donationRecipientAcceptable_ledger (st : SystemState) (k) : donationRecipientAcceptable (recordPhysicalWrites st ws) k = donationRecipientAcceptable st k := rfl
theorem storeDonationHeadClear_ledger (st : SystemState) (o) :
    storeDonationHeadClear o (recordPhysicalWrites st ws) = (storeDonationHeadClear o st).map (recordPhysicalWrites · ws) := by
  cases o with
  | none => rfl
  | some rid => simp only [storeDonationHeadClear, getReply?_ledger]; cases st.getReply? rid with
    | none => rfl
    | some r => dsimp only; rw [storeObject_ledger]; cases storeObject _ _ st with
      | error e => rfl
      | ok p => rfl
theorem storeReplyReHead_ledger (st : SystemState) (k o) :
    storeReplyReHead k o (recordPhysicalWrites st ws) = (storeReplyReHead k o st).map (recordPhysicalWrites · ws) := by
  cases o with
  | none => rfl
  | some rid => simp only [storeReplyReHead, getReply?_ledger]; cases st.getReply? rid with
    | none => rfl
    | some r => dsimp only; rw [storeObject_ledger]; cases storeObject _ _ st with
      | error e => rfl
      | ok p => rfl
theorem storeDonationHeadPop_ledger (st : SystemState) (k o) :
    storeDonationHeadPop k o (recordPhysicalWrites st ws) = (storeDonationHeadPop k o st).map (recordPhysicalWrites · ws) := by
  rcases o with _ | ⟨rid, r⟩
  · rfl
  · simp only [storeDonationHeadPop, storeDonationHeadClear_ledger]
    cases storeDonationHeadClear (some rid) st with
    | error e => rfl
    | ok s1 => exact storeReplyReHead_ledger ws s1 k _
/-- The held pop commutes with a recording. -/
theorem keepDonatedSchedContext_ledger (st : SystemState) (h k o) :
    keepDonatedSchedContext (recordPhysicalWrites st ws) h k o = (keepDonatedSchedContext st h k o).map (recordPhysicalWrites · ws) := by
  unfold keepDonatedSchedContext
  simp only [getSchedContext?_ledger, heldPopOuter?_ledger, outerCallerAcceptable_ledger, donationHeadOf?_ledger]
  split
  · split
    · rfl
    split
    · rfl
    split
    · rfl
    rw [storeObject_ledger]
    cases storeObject _ _ st with
    | error e => rfl
    | ok p =>
      obtain ⟨⟨⟩, s1⟩ := p
      dsimp only [Except.map]
      rw [storeDonationHeadPop_ledger]
      cases storeDonationHeadPop _ _ s1 with
      | error e => rfl
      | ok s2 =>
        dsimp only [Except.map]; rw [lookupTcb_ledger]
        cases lookupTcb s2 h with
        | none => rfl
        | some ht => dsimp only; split; · rfl
                     rw [storeObject_ledger]; cases storeObject _ _ s2 with
                     | error e => rfl
                     | ok p => rfl
  · rfl
theorem markReschedulePendingWhere_ledger (st : SystemState) (p : CoreId → Bool) (cs : List CoreId) :
    markReschedulePendingWhere (recordPhysicalWrites st ws) p cs =
      recordPhysicalWrites (markReschedulePendingWhere st p cs) ws := by
  induction cs generalizing st with
  | nil => rfl
  | cons c cs ih =>
    unfold markReschedulePendingWhere
    split
    · exact ih (st.markReschedulePendingOnCore c)
    · exact ih st
theorem markKeyChangeFor_ledger (st : SystemState) (t) (k) :
    markKeyChangeFor (recordPhysicalWrites st ws) t k = recordPhysicalWrites (markKeyChangeFor st t k) ws := by
  unfold markKeyChangeFor; exact markReschedulePendingWhere_ledger ws st _ _
theorem markCandidacyGainFor_ledger (st : SystemState) (t) (e : Bool) :
    markCandidacyGainFor (recordPhysicalWrites st ws) t e = recordPhysicalWrites (markCandidacyGainFor st t e) ws := by
  unfold markCandidacyGainFor
  cases e with
  | true => rfl
  | false =>
    rw [if_neg (by decide), if_neg (by decide)]
    show (match st.getTcb? t with | some x => _ | none => _) = _
    cases st.getTcb? t with
    | none => rfl
    | some x =>
      show (if hasSufficientBudget st x then _ else _) = _
      dsimp only
      split
      · exact markKeyFlagsOver_ledger ws st _ _ _ _
      · rfl
/-- The reschedule-flag hook commutes with a recording of both states it reads. -/
theorem markKeyChangeFrom_ledger (pre post : SystemState) (t) :
    markKeyChangeFrom (recordPhysicalWrites pre ws) (recordPhysicalWrites post ws) t =
      recordPhysicalWrites (markKeyChangeFrom pre post t) ws := by
  unfold markKeyChangeFrom
  show (match pre.getTcb? t with | some tcb => _ | none => _) = _
  cases pre.getTcb? t with
  | none => exact markReschedulePendingWhere_ledger ws post _ _
  | some tcb =>
    dsimp only
    rw [markCandidacyGainFor_ledger, markKeyChangeFor_ledger]; rfl
theorem releaseUnlinkOn_ledger (st : SystemState) (c k) :
    (recordPhysicalWrites st ws).releaseUnlinkOn c k = recordPhysicalWrites (st.releaseUnlinkOn c k) ws := by
  rw [SystemState.releaseUnlinkOn_eq_impl]
  unfold SystemState.releaseUnlinkOnImpl
  simp only [SystemState.releasePredOf_eq]
  show (if st.releaseQueuedOn c k then _ else _) = _
  split <;> rfl
theorem releaseLinkIn_ledger (st : SystemState) (c k t) :
    (recordPhysicalWrites st ws).releaseLinkIn c k t = recordPhysicalWrites (st.releaseLinkIn c k t) ws := by
  rw [SystemState.releaseLinkIn_eq_impl]
  unfold SystemState.releaseLinkInImpl
  simp only [SystemState.releasePredBefore_eq]
  rfl
theorem releaseRemoveOn_ledger (st : SystemState) (c k) :
    (recordPhysicalWrites st ws).releaseRemoveOn c k = recordPhysicalWrites (st.releaseRemoveOn c k) ws := by
  unfold SystemState.releaseRemoveOn; rw [releaseUnlinkOn_ledger]; rfl
theorem releaseInsertOn_ledger (st : SystemState) (c k t) :
    (recordPhysicalWrites st ws).releaseInsertOn c k t = recordPhysicalWrites (st.releaseInsertOn c k t) ws := by
  unfold SystemState.releaseInsertOn
  show (if st.releaseQueuedAnywhere k || (st.getSchedContext? k).isNone then _ else _) = _
  split
  · rfl
  · unfold SystemState.releaseInsertFresh; rw [releaseLinkIn_ledger]; rfl
theorem migrateReplenishmentWrite_ledger (st : SystemState) (k a b) (q : Bool) (t : Nat) :
    migrateReplenishmentWrite (recordPhysicalWrites st ws) k a b q t =
      recordPhysicalWrites (migrateReplenishmentWrite st k a b q t) ws := by
  unfold migrateReplenishmentWrite
  cases q
  · rfl
  · dsimp only; rw [if_pos rfl, if_pos rfl, releaseRemoveOn_ledger, releaseInsertOn_ledger]; rfl
/-- The replenishment migration commutes with a recording. -/
theorem migrateSchedContextReplenishment_ledger (st : SystemState) (k a b) :
    migrateSchedContextReplenishment (recordPhysicalWrites st ws) k a b =
      recordPhysicalWrites (migrateSchedContextReplenishment st k a b) ws := by
  rw [migrateSchedContextReplenishment_eq_impl]
  unfold migrateSchedContextReplenishmentImpl
  split
  · rfl
  · exact migrateReplenishmentWrite_ledger ws st k a b _ _
/-- The donation return commutes with a recording. -/
theorem returnDonatedSchedContext_ledger (st : SystemState) (sv k o n) :
    returnDonatedSchedContext (recordPhysicalWrites st ws) sv k o n =
      (returnDonatedSchedContext st sv k o n).map (recordPhysicalWrites · ws) := by
  unfold returnDonatedSchedContext
  simp only [getSchedContext?_ledger, outerCallerAcceptable_ledger, donationRecipientAcceptable_ledger,
    donationHeadOf?_ledger]
  split
  · split
    · rfl
    split
    · rfl
    split
    · rfl
    split
    · rfl
    rw [storeObject_ledger]
    cases storeObject _ _ st with
    | error e => rfl
    | ok p =>
      obtain ⟨⟨⟩, s1⟩ := p
      dsimp only [Except.map]
      rw [storeDonationHeadPop_ledger]
      cases storeDonationHeadPop _ _ s1 with
      | error e => rfl
      | ok s2 =>
        dsimp only [Except.map]; rw [lookupTcb_ledger]
        cases lookupTcb s2 o with
        | none => rfl
        | some ct =>
          dsimp only; rw [storeObject_ledger]
          cases storeObject _ _ s2 with
          | error e => rfl
          | ok p =>
            obtain ⟨⟨⟩, s3⟩ := p
            dsimp only [Except.map]; rw [lookupTcb_ledger]
            cases lookupTcb s3 sv with
            | none => rfl
            | some stb =>
              dsimp only; rw [storeObject_ledger]
              cases storeObject _ _ s3 with
              | error e => rfl
              | ok p =>
                obtain ⟨⟨⟩, s4⟩ := p
                dsimp only [Except.map]
                rw [markKeyChangeFrom_ledger, markKeyChangeFrom_ledger]
  · rfl
theorem returnDonatedSchedContextResolved_ledger (st : SystemState) (sv k o) :
    returnDonatedSchedContextResolved (recordPhysicalWrites st ws) sv k o =
      (returnDonatedSchedContextResolved st sv k o).map (recordPhysicalWrites · ws) := by
  unfold returnDonatedSchedContextResolved; rw [replyStackOuterCaller?_ledger]
  cases replyStackOuterCaller? st k with
  | error e => rfl
  | ok n => exact returnDonatedSchedContext_ledger ws st sv k o n
theorem keepDonatedSchedContextResolved_ledger (st : SystemState) (h k) :
    keepDonatedSchedContextResolved (recordPhysicalWrites st ws) h k =
      (keepDonatedSchedContextResolved st h k).map (recordPhysicalWrites · ws) := by
  unfold keepDonatedSchedContextResolved; rw [replyStackOuterCaller?_ledger]
  cases replyStackOuterCaller? st k with
  | error e => rfl
  | ok n => exact keepDonatedSchedContext_ledger ws st h k n
theorem popHeldReplyHead_ledger (st : SystemState) (h k r) :
    popHeldReplyHead (recordPhysicalWrites st ws) h k r =
      (popHeldReplyHead st h k r).map (recordPhysicalWrites · ws) := by
  unfold popHeldReplyHead; rw [donationRecipientAcceptable_ledger]
  split
  · exact returnDonatedSchedContextResolved_ledger ws st h k r
  · exact keepDonatedSchedContextResolved_ledger ws st h k
theorem cleanupPreReceiveDonationChecked_ledger (st : SystemState) (r) :
    cleanupPreReceiveDonationChecked (recordPhysicalWrites st ws) r =
      (cleanupPreReceiveDonationChecked st r).map (recordPhysicalWrites · ws) := by
  unfold cleanupPreReceiveDonationChecked; rw [lookupTcb_ledger]
  cases lookupTcb st r with
  | none => rfl
  | some t =>
    dsimp only
    split
    · exact popHeldReplyHead_ledger ws st _ _ _
    · rfl
/-- The pre-receive cleanup commutes with a recording. -/
theorem cleanupPreReceiveDonationMigrated_ledger (st : SystemState) (r) :
    cleanupPreReceiveDonationMigrated (recordPhysicalWrites st ws) r =
      (cleanupPreReceiveDonationMigrated st r).map (recordPhysicalWrites · ws) := by
  unfold cleanupPreReceiveDonationMigrated; rw [cleanupPreReceiveDonationChecked_ledger]
  cases cleanupPreReceiveDonationChecked st r with
  | error e => rfl
  | ok s1 =>
    dsimp only [Except.map]
    unfold preReceiveReturnMigration
    rw [show preReceiveDonation? (recordPhysicalWrites st ws) r = preReceiveDonation? st r from rfl]
    cases preReceiveDonation? st r with
    | none => rfl
    | some p =>
      obtain ⟨k, _⟩ := p
      dsimp only
      rw [show replenishHomeOfSchedContext (recordPhysicalWrites s1 ws) =
        replenishHomeOfSchedContext s1 from rfl, migrateSchedContextReplenishment_ledger]; rfl
/-- **The receive body commutes with a recording**: it records nothing itself. -/
theorem endpointReceiveDualOnCore_ledger (e : SeLe4n.ObjId) (r : SeLe4n.ThreadId) (rid : Option SeLe4n.ReplyId)
    (ec : CoreId) (st : SystemState) :
    endpointReceiveDualOnCore e r rid ec (recordPhysicalWrites st ws) =
      (recordPhysicalWrites (endpointReceiveDualOnCore e r rid ec st).1 ws,
        (endpointReceiveDualOnCore e r rid ec st).2) := by
  unfold endpointReceiveDualOnCore
  rw [getEndpoint?_ledger]
  cases st.getEndpoint? e with
  | none => dsimp only; rw [getObject?_ledger]; split <;> rfl
  | some ep =>
    dsimp only
    cases ep.sendQ.head with
    | some _ =>
      dsimp only
      rw [endpointQueuePopHead_ledger]
      cases endpointQueuePopHead e false st with
      | error x => rfl
      | ok p =>
        obtain ⟨sender, sTcb, s1⟩ := p
        dsimp only [Except.map]
        rw [blockedSenderMessage_ledger]
        generalize blockedSenderMessage s1 sender sTcb = msg
        split
        · rw [if_pos rfl, if_pos rfl]
          split
          · rw [storeTcbIpcStateAndMessage_ledger]
            cases storeTcbIpcStateAndMessage s1 sender _ none with
            | error x => rfl
            | ok s2 =>
              dsimp only [Except.map]
              cases rid with
              | none => rfl
              | some rid =>
                dsimp only; rw [linkCallerReply_ledger]
                cases SystemState.linkCallerReply sender rid s2 with
                | error x => rfl
                | ok q =>
                  obtain ⟨⟨⟩, s3⟩ := q
                  dsimp only [Except.map]; rw [storeTcbIpcStateAndMessage_ledger]
                  cases storeTcbIpcStateAndMessage s3 r .ready _ with
                  | error x => rfl
                  | ok s4 => dsimp only [Except.map]; rw [linkReplyWaiter_ledger]
          · rw [storeTcbIpcStateAndMessage_ledger]
            cases storeTcbIpcStateAndMessage s1 sender .ready none with
            | error x => rfl
            | ok s2 =>
              dsimp only [Except.map]; rw [updateTcb_ledger, storeTcbIpcStateAndMessage_ledger]
              cases storeTcbIpcStateAndMessage (s2.updateTcb sender _) r .ready _ with
              | error x => rfl
              | ok s4 => rfl
        · rw [if_neg Bool.false_ne_true, if_neg Bool.false_ne_true, storeTcbIpcStateAndMessage_ledger]
          cases storeTcbIpcStateAndMessage s1 sender .ready none with
          | error x => rfl
          | ok s2 =>
            dsimp only [Except.map]; rw [wakeThread_ledger]; dsimp only
            rw [storeTcbIpcStateAndMessage_ledger]
            cases storeTcbIpcStateAndMessage (wakeThread s2 sender ec).1 r .ready _ with
            | error x => rfl
            | ok s4 => rfl
    | none =>
      dsimp only
      rw [cleanupPreReceiveDonationMigrated_ledger]
      cases cleanupPreReceiveDonationMigrated st r with
      | error x => rfl
      | ok s1 =>
        dsimp only [Except.map]; rw [endpointQueueEnqueue_ledger]
        cases endpointQueueEnqueue e true r s1 with
        | error x => rfl
        | ok s2 =>
          dsimp only [Except.map]; rw [storeTcbIpcStateAndMessage_ledger]
          cases storeTcbIpcStateAndMessage s2 r _ none with
          | error x => rfl
          | ok s3 =>
            dsimp only [Except.map]; rw [getTcb?_ledger]
            cases s3.getTcb? r with
            | none => dsimp only; rw [removeRunnableOnCore_ledger]
            | some rt =>
              dsimp only; rw [replyStashValid_ledger]
              split
              · rw [recordReplyStasher_ledger, storeObject_ledger]
                cases storeObject _ _ (s3.recordReplyStasher _ r) with
                | error x => rfl
                | ok q => obtain ⟨⟨⟩, s4⟩ := q; dsimp only [Except.map]; rw [removeRunnableOnCore_ledger]
              · rfl
theorem storeDonationFramePush_ledger (k pr r o) (st : SystemState) :
    storeDonationFramePush k pr r o (recordPhysicalWrites st ws) =
      (storeDonationFramePush k pr r o st).map (recordPhysicalWrites · ws) := by
  unfold storeDonationFramePush
  split
  · rfl
  rw [storeObject_ledger]
  cases storeObject _ _ st with
  | error e => rfl
  | ok p =>
    obtain ⟨⟨⟩, s1⟩ := p
    dsimp only [Except.map]
    cases o with
    | none => rfl
    | some old =>
      dsimp only; rw [getReply?_ledger]
      cases s1.getReply? old with
      | none => rfl
      | some oR => dsimp only; rw [storeObject_ledger]; cases storeObject _ _ s1 <;> rfl
/-- The donation push commutes with a recording. -/
theorem donateSchedContext_ledger (st : SystemState) (c sv k) :
    donateSchedContext (recordPhysicalWrites st ws) c sv k =
      (donateSchedContext st c sv k).map (recordPhysicalWrites · ws) := by
  unfold donateSchedContext
  rw [getSchedContext?_ledger]
  cases st.getSchedContext? k with
  | none => rfl
  | some sc =>
    dsimp only
    split
    · rfl
    rw [lookupTcb_ledger]
    cases lookupTcb st c with
    | none => rfl
    | some dt =>
      dsimp only
      rw [show donationPushFrame? (recordPhysicalWrites st ws) dt = donationPushFrame? st dt from rfl]
      cases donationPushFrame? st dt with
      | error e => rfl
      | ok q =>
        obtain ⟨pr, prp⟩ := q
        dsimp only
        rw [show donationPushRefusal? (recordPhysicalWrites st ws) sv sc.scReply pr =
          donationPushRefusal? st sv sc.scReply pr from rfl]
        cases donationPushRefusal? st sv sc.scReply pr
        case some => rfl
        dsimp only; rw [storeObject_ledger]
        cases storeObject _ _ st with
        | error e => rfl
        | ok p =>
          obtain ⟨⟨⟩, s1⟩ := p
          dsimp only [Except.map]; rw [storeDonationFramePush_ledger]
          cases storeDonationFramePush _ _ _ _ s1 with
          | error e => rfl
          | ok s2 =>
            dsimp only [Except.map]; rw [lookupTcb_ledger]
            cases lookupTcb s2 c with
            | none => rfl
            | some ct =>
              dsimp only; rw [storeObject_ledger]
              cases storeObject _ _ s2 with
              | error e => rfl
              | ok p =>
                obtain ⟨⟨⟩, s3⟩ := p
                dsimp only [Except.map]; rw [lookupTcb_ledger]
                cases lookupTcb s3 sv with
                | none => rfl
                | some stb =>
                  dsimp only; rw [storeObject_ledger]
                  cases storeObject _ _ s3 with
                  | error e => rfl
                  | ok p =>
                    obtain ⟨⟨⟩, s4⟩ := p
                    dsimp only [Except.map]
                    rw [markKeyChangeFrom_ledger, markKeyChangeFrom_ledger]
theorem applyCallDonation_ledger (st : SystemState) (c r) :
    applyCallDonation (recordPhysicalWrites st ws) c r = (applyCallDonation st c r).map (recordPhysicalWrites · ws) := by
  unfold applyCallDonation
  dsimp only
  rw [lookupTcb_ledger]
  cases lookupTcb st r.val with
  | none => rfl
  | some rt =>
    dsimp only
    split
    · rw [lookupTcb_ledger]
      cases lookupTcb st c.val with
      | none => rfl
      | some ct =>
        dsimp only
        split
        · rw [donateSchedContextValid_eq, donateSchedContextValid_eq, donateSchedContext_ledger]
          cases donateSchedContext st _ _ _ <;> rfl
        · rfl
    · rfl
theorem applyRendezvousCallDonation_ledger (st : SystemState) (r d) :
    applyRendezvousCallDonation (recordPhysicalWrites st ws) r d =
      (applyRendezvousCallDonation st r d).map (recordPhysicalWrites · ws) := by
  unfold applyRendezvousCallDonation
  split
  · unfold applyCallDonationOnCore
    rw [applyCallDonation_ledger]
    cases applyCallDonation st _ _ with
    | error e => rfl
    | ok s1 =>
      dsimp only [Except.map]
      rw [show callDonationSchedContext? (recordPhysicalWrites st ws) = callDonationSchedContext? st from rfl]
      cases callDonationSchedContext? st _ _ with
      | none => rfl
      | some k =>
        dsimp only
        rw [show determineTargetCore (recordPhysicalWrites st ws) = determineTargetCore st from rfl,
          migrateSchedContextReplenishment_ledger]
  · rfl
theorem schedContextReturnLinks_ledger (st : SystemState) (v t) :
    schedContextReturnLinks (recordPhysicalWrites st ws) v t = recordPhysicalWrites (schedContextReturnLinks st v t) ws := by
  unfold schedContextReturnLinks
  rcases Option.eq_none_or_eq_some (st.getSchedContext? (SeLe4n.SchedContextId.ofObjId v.val)) with h | ⟨sc, h⟩
  · rw [SystemState.getSchedContextWitnessed?_eq_none h,
      SystemState.getSchedContextWitnessed?_eq_none (st := recordPhysicalWrites st ws) h]
  · rw [SystemState.getSchedContextWitnessed?_eq_some h,
      SystemState.getSchedContextWitnessed?_eq_some (st := recordPhysicalWrites st ws) h]
    dsimp only
    rw [getTcb?_ledger]
    cases st.getTcb? t with
    | none => rfl
    | some tcb =>
      dsimp only
      rw [show SystemState.rewriteObject (recordPhysicalWrites st ws) v.val _ _ =
        recordPhysicalWrites (SystemState.rewriteObject st v.val (.schedContext { sc with boundThreadCode := 0 })
          (SystemState.rewriteAdmissible_schedContext h _)) ws from rfl, updateTcb_ledger]
      rw [show runningCoreOf? (recordPhysicalWrites st ws) t = runningCoreOf? st t from rfl]
      cases runningCoreOf? st t with
      | none => dsimp only; rw [markCandidacyGainFor_ledger, markKeyChangeFor_ledger]; rfl
      | some c =>
        dsimp only
        rw [show SystemState.markReschedulePendingOnCore (recordPhysicalWrites _ ws) c =
          recordPhysicalWrites (SystemState.markReschedulePendingOnCore _ c) ws from rfl,
          markCandidacyGainFor_ledger, markKeyChangeFor_ledger]; rfl
theorem releaseRemoveAnywhere_ledger (st : SystemState) (k) :
    (recordPhysicalWrites st ws).releaseRemoveAnywhere k = recordPhysicalWrites (st.releaseRemoveAnywhere k) ws := by
  unfold SystemState.releaseRemoveAnywhere
  rw [show (recordPhysicalWrites st ws).releaseCoreOf k = st.releaseCoreOf k from rfl]
  cases st.releaseCoreOf k with
  | none => rfl
  | some d => exact releaseRemoveOn_ledger ws st d k
theorem schedContextReturnPerform_ledger (st : SystemState) (v t) :
    schedContextReturnPerform (recordPhysicalWrites st ws) v t = recordPhysicalWrites (schedContextReturnPerform st v t) ws := by
  unfold schedContextReturnPerform SchedContextOps.purgeReplenishment
  rw [schedContextReturnLinks_ledger, releaseRemoveAnywhere_ledger]
theorem maybeReturnSchedContext_ledger (st : SystemState) (n t) :
    maybeReturnSchedContext (recordPhysicalWrites st ws) n t = recordPhysicalWrites (maybeReturnSchedContext st n t) ws := by
  unfold maybeReturnSchedContext
  rw [show (recordPhysicalWrites st ws).getNotification? n = st.getNotification? n from rfl]
  cases st.getNotification? n with
  | none => rfl
  | some nt =>
    dsimp only
    cases nt.schedContext with
    | none => rfl
    | some sc =>
      dsimp only
      split
      · rw [show schedContextReturnAdmitted (recordPhysicalWrites st ws) = schedContextReturnAdmitted st from rfl]
        split
        · exact schedContextReturnPerform_ledger ws st _ t
        · rfl
      · rfl
/-- The receive's context return commutes with a recording. -/
theorem receiveReturnSchedContext_ledger (b : Bool) (st : SystemState) (t) :
    receiveReturnSchedContext b (recordPhysicalWrites st ws) t = recordPhysicalWrites (receiveReturnSchedContext b st t) ws := by
  unfold receiveReturnSchedContext
  cases b with
  | false => rfl
  | true =>
    rw [if_pos rfl, if_pos rfl, getTcb?_ledger]
    cases st.getTcb? t with
    | none => rfl
    | some x =>
      dsimp only
      split
      · rfl
      · exact maybeReturnSchedContext_ledger ws st _ t
theorem descheduleAtPlacement_ledger (st : SystemState) (t) :
    descheduleAtPlacement (recordPhysicalWrites st ws) t = recordPhysicalWrites (descheduleAtPlacement st t) ws := by
  unfold descheduleAtPlacement descheduleAt
  rw [show placedCoreOf? (recordPhysicalWrites st ws) t = placedCoreOf? st t from rfl]
  cases placedCoreOf? st t with
  | none => rfl
  | some c => exact removeRunnableOnCore_ledger ws st t c
/-- The post-receive donation commutes with a recording. -/
theorem replyRecvPostReceiveDonation_ledger (tid rs nt : SeLe4n.ThreadId) (sc : CoreId) (ret) (st : SystemState) :
    replyRecvPostReceiveDonation tid rs nt sc ret (recordPhysicalWrites st ws) =
      (replyRecvPostReceiveDonation tid rs nt sc ret st).map (fun p => (p.1, recordPhysicalWrites p.2 ws)) := by
  unfold replyRecvPostReceiveDonation
  rw [show rendezvousDequeuedCall (recordPhysicalWrites st ws) nt = rendezvousDequeuedCall st nt from rfl]
  cases ret with
  | none =>
    dsimp only
    split
    · rw [applyRendezvousCallDonation_ledger]
      cases applyRendezvousCallDonation st tid nt with
      | error e => rfl
      | ok s2 => dsimp only [Except.map]; rw [propagatePipChainCrossCore_ledger]
    · rw [propagatePipChainCrossCore_ledger]; rfl
  | some p =>
    obtain ⟨_, holder⟩ := p
    dsimp only
    have hD : replyRecvHolderDeschedule tid holder (recordPhysicalWrites st ws) =
        recordPhysicalWrites (replyRecvHolderDeschedule tid holder st) ws := by
      unfold replyRecvHolderDeschedule; split
      · rfl
      · exact descheduleAtPlacement_ledger ws st holder
    split
    · rw [hD, applyRendezvousCallDonation_ledger]
      cases applyRendezvousCallDonation _ tid nt with
      | error e => rfl
      | ok s2 => dsimp only [Except.map]; rw [propagatePipChainCrossCore_ledger]
    · rw [descheduleAtPlacement_ledger, propagatePipChainCrossCore_ledger]; rfl
/-- The priority hand-off commutes with a recording. -/
theorem applyReceiveLegPipHandoff_ledger (st : SystemState) (r d a ec) :
    applyReceiveLegPipHandoff (recordPhysicalWrites st ws) r d a ec =
      recordPhysicalWrites (applyReceiveLegPipHandoff st r d a ec) ws := by
  unfold applyReceiveLegPipHandoff
  rw [show rendezvousDequeuedCall (recordPhysicalWrites st ws) d = rendezvousDequeuedCall st d from rfl]
  split
  · rfl
  · split
    · exact propagatePipChainCrossCore_ledger ws st r ec
    · rfl
/-- **The receive commutes with a recording** where the dequeued sender asks to transfer nothing (`receiveCapRequest`), so the transfer records nothing. -/
theorem endpointReceiveDualWithCapsOnCore_ledger_of_noCaps (e : SeLe4n.ObjId) (r : SeLe4n.ThreadId)
    (rid : Option SeLe4n.ReplyId) (ec : CoreId) (st : SystemState)
    (hNoCaps : receiveCapRequest st e = none) :
    endpointReceiveDualWithCapsOnCore e r rid ec (recordPhysicalWrites st ws) =
      (recordPhysicalWrites (endpointReceiveDualWithCapsOnCore e r rid ec st).1 ws,
        (endpointReceiveDualWithCapsOnCore e r rid ec st).2) := by
  unfold endpointReceiveDualWithCapsOnCore
  rw [endpointReceiveDualOnCore_ledger, receiveCapRequest_ledger, receiveRendezvousSender?_ledger, hNoCaps]
  rcases endpointReceiveDualOnCore e r rid ec st with ⟨s1, _ | ⟨sender, sgi⟩⟩
  · rfl
  · dsimp only
    split
    · rfl
    · simp only [receiveTransferCaps]
/-- **The receive tail commutes with a recording** where the dequeued sender
asks to transfer nothing: the context return, the receive leg, the post-receive
donation and the priority hand-off record nothing of their own, so a recording
made before the tail is the recording made after it (WS-SX D58). -/
theorem replyRecvReceiveTail_ledger (epId : SeLe4n.ObjId) (tid : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (rs : SeLe4n.ThreadId) (ec : CoreId)
    (ret? : Option (SeLe4n.SchedContextId × SeLe4n.ThreadId)) (Z : SystemState)
    (hNoCaps : receiveCapRequest (receiveReturnSchedContext true Z tid) epId = none) :
    (match endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
        (receiveReturnSchedContext true (recordPhysicalWrites Z ws) tid) with
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
      (fun p : CapTransferSummary × SystemState => (p.1, recordPhysicalWrites p.2 ws)) := by
  rw [receiveReturnSchedContext_ledger,
    endpointReceiveDualWithCapsOnCore_ledger_of_noCaps ws _ _ _ _ _ hNoCaps]
  rcases endpointReceiveDualWithCapsOnCore epId tid (some rid) ec
      (receiveReturnSchedContext true Z tid) with ⟨st2, _ | ⟨nt, summary, x⟩⟩
  · rfl
  · dsimp only
    rw [replyRecvPostReceiveDonation_ledger]
    cases replyRecvPostReceiveDonation tid rs nt ec ret? st2 with
    | error e => rfl
    | ok w =>
      obtain ⟨⟨⟩, st3⟩ := w
      dsimp only [Except.map]
      rw [applyReceiveLegPipHandoff_ledger]
end Ledger

end SeLe4n.Kernel
