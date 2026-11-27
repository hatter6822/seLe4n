/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.IPC.Operations.Donation
import SeLe4n.Kernel.IPC.Operations.HeldContextPopInPlace
import SeLe4n.Kernel.IPC.Operations.UnheldContextPopInPlace

/-!
# The reply-receive's pop and post-receive donation, each refusal carrying its state

The reply-receive's donation pop (seL4-MCS's `reply_pop`) and its post-receive
donation (`receiveIPC` → `reply_push`, `schedContext_donate`) are kernel
computations whose refusals carry no state.  A refusal-carrying caller that
reports the state such a computation stopped in would have to keep the state
it handed over alive across it, and the computation's first store would then
copy the object table on every call that writes.

The forms here are those computations with each refusal carrying the state at
the point it refuses: the state handed in where the refusal precedes the first
write, so nothing is held, and the state the stores reached where it follows
one.  Every store is the store's own state (`SystemState.withObjectStored`,
which never refuses), and every read of the state handed in is taken before
the first write.  Each is its specification with the refusal's state forgotten,
with no assumption (`*_eq`).  They serve the reply-receive path only; the
other callers of the shared donation operations keep them as they are (WS-CK
CK2 owns those).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- A state step whose refusal carries the state it stopped in. -/
abbrev RefusalCarryingStep := SystemState → Except (KernelError × SystemState) SystemState

theorem refusalCarrying_mapError_error {ε ε' α : Type} (f : ε → ε') (e : ε) :
    (Except.error e : Except ε α).mapError f = .error (f e) := rfl

theorem refusalCarrying_mapError_ok {ε ε' α : Type} (f : ε → ε') (a : α) :
    (Except.ok a : Except ε α).mapError f = .ok a := rfl

section KeyReads

/-- Whether the thread read off the state handed in had budget there: the
reschedule hook's candidacy reading, taken before the writes. -/
@[inline] def keyChangeBudget (pre : SystemState) (t? : Option TCB) : Bool :=
  match t? with
  | some t => hasSufficientBudget pre t
  | none => false

/-- `markKeyChangeFrom` with its reads of the state handed in already taken: the
thread as it was there, and whether it had budget (`markKeyChangeFrom_eq_of`).
A writer that hands in its keys rather than its pre-state keeps no pre-state
alive across its stores. -/
def markKeyChangeOf (t? : Option TCB) (budget : Bool) (post : SystemState)
    (tid : SeLe4n.ThreadId) : SystemState :=
  match t? with
  | some tcb => markKeyChangeFor (markCandidacyGainFor post tid budget) tid
      (effectiveSchedParams post tcb)
  | none => markReschedulePendingWhere post
      (fun c => post.queuedOn c tid || post.scheduler.currentOnCore c == some tid)
      Concurrency.allCores

theorem markKeyChangeFrom_eq_of (pre post : SystemState) (tid : SeLe4n.ThreadId) :
    markKeyChangeFrom pre post tid =
      markKeyChangeOf (pre.getTcb? tid) (keyChangeBudget pre (pre.getTcb? tid)) post tid := by
  unfold markKeyChangeFrom markKeyChangeOf keyChangeBudget
  cases pre.getTcb? tid <;> rfl

end KeyReads

section ReplyStackStores

/-- `storeDonationHeadClear`, its refusal (the head is no reply) carrying the
state handed in: it precedes the store. -/
def storeDonationHeadClearR : Option SeLe4n.ReplyId → RefusalCarryingStep
  | none, st => .ok st
  | some rid, st =>
    match st.getReply? rid with
    | some r => .ok (st.withObjectStored rid.toObjId (.reply { r with prev := none, next := none }))
    | none => .error (.objectNotFound, st)

theorem storeDonationHeadClearR_eq (h? : Option SeLe4n.ReplyId) (st : SystemState) :
    (storeDonationHeadClearR h? st).mapError Prod.fst = storeDonationHeadClear h? st := by
  cases h? with
  | none => rfl
  | some rid =>
    simp only [storeDonationHeadClearR, storeDonationHeadClear,
      SystemState.storeObject_eq_withObjectStored]
    repeat' (first | rfl | (split <;> (try (rename_i h; simp only [h, refusalCarrying_mapError_error,
      refusalCarrying_mapError_ok]))))

/-- `storeReplyReHead`, its refusal (the frame below is no reply) carrying the
state handed in: it precedes the store. -/
def storeReplyReHeadR (scId : SeLe4n.SchedContextId) : Option SeLe4n.ReplyId → RefusalCarryingStep
  | none, st => .ok st
  | some rid, st =>
    match st.getReply? rid with
    | some r => .ok (st.withObjectStored rid.toObjId (.reply { r with next := some (.head scId) }))
    | none => .error (.objectNotFound, st)

theorem storeReplyReHeadR_eq (scId : SeLe4n.SchedContextId) (b? : Option SeLe4n.ReplyId)
    (st : SystemState) :
    (storeReplyReHeadR scId b? st).mapError Prod.fst = storeReplyReHead scId b? st := by
  cases b? with
  | none => rfl
  | some rid =>
    simp only [storeReplyReHeadR, storeReplyReHead, SystemState.storeObject_eq_withObjectStored]
    repeat' (first | rfl | (split <;> (try (rename_i h; simp only [h, refusalCarrying_mapError_error,
      refusalCarrying_mapError_ok]))))

/-- `storeDonationHeadPop`: the head cleared, then the frame below re-headed;
the re-head's refusal carries the cleared state. -/
def storeDonationHeadPopR (scId : SeLe4n.SchedContextId) :
    Option (SeLe4n.ReplyId × Reply) → RefusalCarryingStep
  | none, st => .ok st
  | some (rid, r), st =>
    match storeDonationHeadClearR (some rid) st with
    | .error es => .error es
    | .ok st1 => storeReplyReHeadR scId r.prev st1

theorem storeDonationHeadPopR_eq (scId : SeLe4n.SchedContextId)
    (head? : Option (SeLe4n.ReplyId × Reply)) (st : SystemState) :
    (storeDonationHeadPopR scId head? st).mapError Prod.fst = storeDonationHeadPop scId head? st := by
  cases head? with
  | none => rfl
  | some p =>
    obtain ⟨rid, r⟩ := p
    rw [storeDonationHeadPop_some, ← storeDonationHeadClearR_eq]
    simp only [storeDonationHeadPopR]
    cases storeDonationHeadClearR (some rid) st with
    | error es => rfl
    | ok st1 => exact storeReplyReHeadR_eq scId r.prev st1

end ReplyStackStores

section ContextPops

/-- `returnDonatedSchedContext` (seL4-MCS's `reply_pop`, the context handed back
to `originalOwner`): its checks refuse on the state handed in; the thread
lookups after the stores refuse on the state the stores reached. -/
def returnDonatedSchedContextR (serverTid : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (originalOwner : SeLe4n.ThreadId) (newOwner? : Option SeLe4n.ThreadId) :
    RefusalCarryingStep := fun st =>
  match st.getSchedContext? scId with
  | some sc =>
    if sc.boundThread != some serverTid then .error (.invalidArgument 0, st)
    else
    if !outerCallerAcceptable st serverTid originalOwner newOwner? then
      .error (.invalidArgument 0, st)
    else
    if !donationRecipientAcceptable st originalOwner then
      .error (.invalidArgument 0, st)
    else
    match donationHeadOf? st scId sc with
    | .error e => .error (e, st)
    | .ok head? =>
      let ownerKey := st.getTcb? originalOwner
      let ownerBudget := keyChangeBudget st ownerKey
      let serverKey := st.getTcb? serverTid
      let serverBudget := keyChangeBudget st serverKey
      let sc' := donationReturnSchedContext sc originalOwner (head?.bind (fun p => p.2.prev))
      match storeDonationHeadPopR scId head? (st.withObjectStored scId.toObjId (.schedContext sc')) with
      | .error es => .error es
      | .ok st2 =>
        match lookupTcb st2 originalOwner with
        | none => .error (.objectNotFound, st2)
        | some clientTcb =>
          let clientTcb' := { clientTcb with
            scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
            scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) }
          let st3 := st2.withObjectStored originalOwner.toObjId (.tcb clientTcb')
          match lookupTcb st3 serverTid with
          | none => .error (.objectNotFound, st3)
          | some serverTcb =>
            let serverTcb' := { serverTcb with scBindingScCode := 0, scBindingOwnerCode := 0 }
            .ok (markKeyChangeOf serverKey serverBudget (markKeyChangeOf ownerKey ownerBudget
              (st3.withObjectStored serverTid.toObjId (.tcb serverTcb')) originalOwner) serverTid)
  | none => .error (.objectNotFound, st)

theorem returnDonatedSchedContextR_eq (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId) (st : SystemState) :
    (returnDonatedSchedContextR serverTid scId originalOwner newOwner? st).mapError Prod.fst =
      returnDonatedSchedContext st serverTid scId originalOwner newOwner? := by
  unfold returnDonatedSchedContextR returnDonatedSchedContext
  simp only [SystemState.storeObject_eq_withObjectStored, ← storeDonationHeadPopR_eq,
    markKeyChangeFrom_eq_of]
  repeat' (first | rfl | (split <;> (try (rename_i h; simp only [h, refusalCarrying_mapError_error,
      refusalCarrying_mapError_ok]))))

/-- `returnDonatedSchedContextResolved`: the resolver's refusal precedes every
write. -/
def returnDonatedSchedContextResolvedR (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId) : RefusalCarryingStep :=
  fun st =>
    match replyStackOuterCaller? st scId with
    | .error e => .error (e, st)
    | .ok newOwner? => returnDonatedSchedContextR serverTid scId originalOwner newOwner? st

theorem returnDonatedSchedContextResolvedR_eq (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId) (st : SystemState) :
    (returnDonatedSchedContextResolvedR serverTid scId originalOwner st).mapError Prod.fst =
      returnDonatedSchedContextResolved st serverTid scId originalOwner := by
  unfold returnDonatedSchedContextResolvedR returnDonatedSchedContextResolved
  cases replyStackOuterCaller? st scId with
  | error e => rfl
  | ok n => exact returnDonatedSchedContextR_eq serverTid scId originalOwner n st

/-- `keepDonatedSchedContext` (seL4-MCS's `reply_pop` where the recipient holds
a context: the head popped off the holder): its checks refuse on the state
handed in; the holder's lookup and binding guard after the stores refuse on the
state the stores reached. -/
def keepDonatedSchedContextR (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (newOwner? : Option SeLe4n.ThreadId) : RefusalCarryingStep := fun st =>
  match st.getSchedContext? scId with
  | some sc =>
    if sc.boundThread != some holder then .error (.invalidArgument 0, st)
    else
    if !outerCallerAcceptable st holder holder (heldPopOuter? st holder newOwner?) then
      .error (.invalidArgument 0, st)
    else
    match donationHeadOf? st scId sc with
    | .error e => .error (e, st)
    | .ok head? =>
      match storeDonationHeadPopR scId head? (st.withObjectStored scId.toObjId
          (.schedContext (donationSeverSchedContext sc (head?.bind (fun p => p.2.prev))))) with
      | .error es => .error es
      | .ok st2 =>
        match lookupTcb st2 holder with
        | none => .error (.objectNotFound, st2)
        | some ht =>
          if ht.schedContextBinding.scId? != some scId then .error (.invalidArgument 0, st2)
          else
          let ht' := { ht with
            scBindingScCode := SchedContextBinding.scCode
              (donationReturnBinding scId (heldPopOwner? ht.schedContextBinding newOwner?)),
            scBindingOwnerCode := SchedContextBinding.ownerCode
              (donationReturnBinding scId (heldPopOwner? ht.schedContextBinding newOwner?)) }
          .ok (st2.withObjectStored holder.toObjId (.tcb ht'))
  | none => .error (.objectNotFound, st)

theorem keepDonatedSchedContextR_eq (holder : SeLe4n.ThreadId) (scId : SeLe4n.SchedContextId)
    (newOwner? : Option SeLe4n.ThreadId) (st : SystemState) :
    (keepDonatedSchedContextR holder scId newOwner? st).mapError Prod.fst =
      keepDonatedSchedContext st holder scId newOwner? := by
  unfold keepDonatedSchedContextR keepDonatedSchedContext
  simp only [SystemState.storeObject_eq_withObjectStored, ← storeDonationHeadPopR_eq]
  repeat' (first | rfl | (split <;> (try (rename_i h; simp only [h, refusalCarrying_mapError_error,
      refusalCarrying_mapError_ok]))))

/-- `keepDonatedSchedContextResolved` as compiled
(`keepDonatedSchedContextResolvedImpl`): in place where `keptPopsInPlace`
admits it, which never refuses; the resolver, whose refusal precedes every
write, then the held pop otherwise. -/
def keepDonatedSchedContextResolvedR (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) : RefusalCarryingStep := fun st =>
  if keptPopsInPlace st holder scId then .ok (keepDonatedSchedContextInPlace st holder scId)
  else
    match replyStackOuterCaller? st scId with
    | .error e => .error (e, st)
    | .ok newOwner? => keepDonatedSchedContextR holder scId newOwner? st

theorem keepDonatedSchedContextResolvedR_eq (holder : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (st : SystemState) :
    (keepDonatedSchedContextResolvedR holder scId st).mapError Prod.fst =
      keepDonatedSchedContextResolved st holder scId := by
  rw [keepDonatedSchedContextResolved_eq_impl]
  unfold keepDonatedSchedContextResolvedR keepDonatedSchedContextResolvedImpl
  split
  · rfl
  · unfold keepDonatedSchedContextResolved
    cases replyStackOuterCaller? st scId with
    | error e => rfl
    | ok n => exact keepDonatedSchedContextR_eq holder scId n st

/-- `returnUnheldSchedContext` (seL4-MCS's `reply_pop` at a head no thread
holds, the context handed to `owner`): its checks refuse on the state handed
in; the owner's lookup after the stores refuses on the state they reached. -/
def returnUnheldSchedContextR (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId) : RefusalCarryingStep := fun st =>
  match st.getSchedContext? scId with
  | some sc =>
    if sc.boundThreadCode != 0 then .error (.illegalState, st)
    else
    if !outerCallerAcceptable st owner owner newOwner? then .error (.invalidArgument 0, st)
    else
    if !donationRecipientAcceptable st owner then .error (.invalidArgument 0, st)
    else
    match donationHeadOf? st scId sc with
    | .error e => .error (e, st)
    | .ok head? =>
      let ownerKey := st.getTcb? owner
      let ownerBudget := keyChangeBudget st ownerKey
      let sc' := donationReturnSchedContext sc owner (head?.bind (fun p => p.2.prev))
      match storeDonationHeadPopR scId head? (st.withObjectStored scId.toObjId (.schedContext sc')) with
      | .error es => .error es
      | .ok st2 =>
        match lookupTcb st2 owner with
        | none => .error (.objectNotFound, st2)
        | some ot =>
          let ot' := { ot with
            scBindingScCode := SchedContextBinding.scCode (donationReturnBinding scId newOwner?),
            scBindingOwnerCode := SchedContextBinding.ownerCode (donationReturnBinding scId newOwner?) }
          .ok (markKeyChangeOf ownerKey ownerBudget (st2.withObjectStored owner.toObjId (.tcb ot'))
            owner)
  | none => .error (.objectNotFound, st)

theorem returnUnheldSchedContextR_eq (scId : SeLe4n.SchedContextId) (owner : SeLe4n.ThreadId)
    (newOwner? : Option SeLe4n.ThreadId) (st : SystemState) :
    (returnUnheldSchedContextR scId owner newOwner? st).mapError Prod.fst =
      returnUnheldSchedContext st scId owner newOwner? := by
  unfold returnUnheldSchedContextR returnUnheldSchedContext
  simp only [SystemState.storeObject_eq_withObjectStored, ← storeDonationHeadPopR_eq,
    markKeyChangeFrom_eq_of]
  repeat' (first | rfl | (split <;> (try (rename_i h; simp only [h, refusalCarrying_mapError_error,
      refusalCarrying_mapError_ok]))))

/-- `severUnheldSchedContext` (the head popped off a context no thread holds,
the caller holding a context of its own): its checks refuse on the state
handed in; the pop's re-head refuses on the state the stores reached. -/
def severUnheldSchedContextR (scId : SeLe4n.SchedContextId) : RefusalCarryingStep := fun st =>
  match st.getSchedContext? scId with
  | some sc =>
    if sc.boundThreadCode != 0 then .error (.illegalState, st)
    else
    match donationHeadOf? st scId sc with
    | .error e => .error (e, st)
    | .ok head? =>
      storeDonationHeadPopR scId head? (st.withObjectStored scId.toObjId
        (.schedContext (donationSeverSchedContext sc (head?.bind (fun p => p.2.prev)))))
  | none => .error (.objectNotFound, st)

theorem severUnheldSchedContextR_eq (scId : SeLe4n.SchedContextId)
    (newOwner? : Option SeLe4n.ThreadId) (st : SystemState) :
    (severUnheldSchedContextR scId st).mapError Prod.fst =
      severUnheldSchedContext st scId newOwner? := by
  unfold severUnheldSchedContextR severUnheldSchedContext
  simp only [SystemState.storeObject_eq_withObjectStored, ← storeDonationHeadPopR_eq]
  repeat' (first | rfl | (split <;> (try (rename_i h; simp only [h, refusalCarrying_mapError_error,
      refusalCarrying_mapError_ok]))))

/-- `popUnheldReplyHead` as compiled (`popUnheldReplyHeadImpl`): nothing where
the reply heads no context; in place where `unheldPopsInPlace` admits it, which
never refuses; otherwise the resolver, whose refusal precedes every write, then
the unheld pop settled on `home` where `target` holds no context and the sever
where it holds one. -/
def popUnheldReplyHeadR (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (home : Concurrency.CoreId) : RefusalCarryingStep := fun st =>
  match replyFrameHeadContext? st rid with
  | none => .ok st
  | some scId =>
    if unheldPopsInPlace st scId target then
      .ok (SchedContextOps.settleReturnedContext
        (returnUnheldSchedContextInPlace st target scId) home scId)
    else
    match replyStackOuterCaller? st scId with
    | .error e => .error (e, st)
    | .ok newOwner? =>
      if donationRecipientAcceptable st target then
        match returnUnheldSchedContextR scId target newOwner? st with
        | .error es => .error es
        | .ok st' => .ok (SchedContextOps.settleReturnedContext st' home scId)
      else severUnheldSchedContextR scId st

theorem popUnheldReplyHeadR_eq (rid : SeLe4n.ReplyId) (target : SeLe4n.ThreadId)
    (home : Concurrency.CoreId) (st : SystemState) :
    (popUnheldReplyHeadR rid target home st).mapError Prod.fst =
      popUnheldReplyHead st rid target home := by
  rw [popUnheldReplyHead_eq_impl]
  unfold popUnheldReplyHeadR popUnheldReplyHeadImpl
  cases replyFrameHeadContext? st rid with
  | none => rfl
  | some scId =>
    simp only []
    cases unheldPopsInPlace st scId target with
    | true => rfl
    | false =>
      simp only [Bool.false_eq_true, ↓reduceIte, returnUnheldSchedContextResolved,
        severUnheldSchedContextResolved]
      cases replyStackOuterCaller? st scId with
      | error e => cases donationRecipientAcceptable st target <;> rfl
      | ok n =>
        cases donationRecipientAcceptable st target
        · exact severUnheldSchedContextR_eq scId n st
        · simp only [↓reduceIte, ← returnUnheldSchedContextR_eq scId target n st]
          cases returnUnheldSchedContextR scId target n st <;> rfl

end ContextPops

section CallDonation

/-- `storeDonationFramePush`: the frame pushed, then the old head linked up to
it; the self-push check refuses on the state handed in, and the old head's
lookup on the state after the frame's store. -/
def storeDonationFramePushR (scId : SeLe4n.SchedContextId) (pushRid : SeLe4n.ReplyId)
    (pushReply : Reply) (oldHead? : Option SeLe4n.ReplyId) : RefusalCarryingStep := fun st =>
  if oldHead? == some pushRid then .error (.invalidArgument 0, st) else
  let st1 := st.withObjectStored pushRid.toObjId
    (.reply { pushReply with prev := oldHead?, next := some (.head scId) })
  match oldHead? with
  | none => .ok st1
  | some old =>
    match st1.getReply? old with
    | none => .error (.objectNotFound, st1)
    | some oldR => .ok (st1.withObjectStored old.toObjId (.reply { oldR with next := some (.frame pushRid) }))

theorem storeDonationFramePushR_eq (scId : SeLe4n.SchedContextId) (pushRid : SeLe4n.ReplyId)
    (pushReply : Reply) (oldHead? : Option SeLe4n.ReplyId) (st : SystemState) :
    (storeDonationFramePushR scId pushRid pushReply oldHead? st).mapError Prod.fst =
      storeDonationFramePush scId pushRid pushReply oldHead? st := by
  unfold storeDonationFramePushR storeDonationFramePush
  simp only [SystemState.storeObject_eq_withObjectStored]
  repeat' (first | rfl | (split <;> (try (rename_i h; simp only [h, refusalCarrying_mapError_error,
      refusalCarrying_mapError_ok]))))

/-- `donateSchedContext` (seL4-MCS's `schedContext_donate` with the reply
frame's push): its checks, the admission (`donationPushRefusal?`) among them,
refuse on the state handed in; the frame push's and the two thread lookups'
defensive checks after the stores carry the state the stores reached, and on a
well-formed object table they never refuse (`donateSchedContextR_stops_at_entry`). -/
def donateSchedContextR (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId) : RefusalCarryingStep := fun st =>
  match st.getSchedContext? clientScId with
  | some sc =>
    if sc.boundThread != some clientTid then .error (.invalidArgument 0, st)
    else
    match lookupTcb st clientTid with
    | none => .error (.objectNotFound, st)
    | some donorTcb =>
      match donationPushFrame? st donorTcb with
      | .error e => .error (e, st)
      | .ok (pushRid, pushReply) =>
        match donationPushRefusal? st serverTid sc.scReply pushRid with
        | some e => .error (e, st)
        | none =>
        let clientKey := st.getTcb? clientTid
        let clientBudget := keyChangeBudget st clientKey
        let serverKey := st.getTcb? serverTid
        let serverBudget := keyChangeBudget st serverKey
        let sc' := { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some serverTid),
                             scReply := some pushRid }
        match storeDonationFramePushR clientScId pushRid pushReply sc.scReply
            (st.withObjectStored clientScId.toObjId (.schedContext sc')) with
        | .error es => .error es
        | .ok st2 =>
          match lookupTcb st2 clientTid with
          | none => .error (.objectNotFound, st2)
          | some clientTcb =>
            let clientTcb' := { clientTcb with scBindingScCode := 0, scBindingOwnerCode := 0 }
            let st3 := st2.withObjectStored clientTid.toObjId (.tcb clientTcb')
            match lookupTcb st3 serverTid with
            | none => .error (.objectNotFound, st3)
            | some serverTcb =>
              let serverTcb' := { serverTcb with
                scBindingScCode := SchedContextBinding.scCode (.donated clientScId clientTid),
                scBindingOwnerCode := SchedContextBinding.ownerCode (.donated clientScId clientTid) }
              .ok (markKeyChangeOf serverKey serverBudget (markKeyChangeOf clientKey clientBudget
                (st3.withObjectStored serverTid.toObjId (.tcb serverTcb')) clientTid) serverTid)
  | none => .error (.objectNotFound, st)

theorem donateSchedContextR_eq (clientTid serverTid : SeLe4n.ThreadId)
    (clientScId : SeLe4n.SchedContextId) (st : SystemState) :
    (donateSchedContextR clientTid serverTid clientScId st).mapError Prod.fst =
      donateSchedContext st clientTid serverTid clientScId := by
  unfold donateSchedContextR donateSchedContext
  simp only [SystemState.storeObject_eq_withObjectStored, ← storeDonationFramePushR_eq,
    markKeyChangeFrom_eq_of]
  repeat' (first | rfl | (split <;> (try (rename_i h; simp only [h, refusalCarrying_mapError_error,
      refusalCarrying_mapError_ok]))))

section DonationAdmissionExact

/-- The admission's three answers, read back. -/
theorem donationPushRefusal?_none_facts {st : SystemState} {serverTid : SeLe4n.ThreadId}
    {oldHead? : Option SeLe4n.ReplyId} {pushRid : SeLe4n.ReplyId}
    (h : donationPushRefusal? st serverTid oldHead? pushRid = none) :
    oldHead? ≠ some pushRid ∧
      (∀ old, oldHead? = some old → (st.getReply? old).isSome = true) ∧
      (lookupTcb st serverTid).isSome = true := by
  cases oldHead? with
  | none =>
    cases hT : lookupTcb st serverTid
    · simp [donationPushRefusal?, hT] at h
    · exact ⟨by simp, by simp, rfl⟩
  | some old =>
    by_cases hE : old = pushRid
    · subst hE; simp [donationPushRefusal?] at h
    cases hR : st.getReply? old
    · simp [donationPushRefusal?, hE, hR] at h
    cases hT : lookupTcb st serverTid
    · simp [donationPushRefusal?, hE, hR, hT] at h
    exact ⟨by simpa using hE, fun o hO => by cases hO; rw [hR]; rfl, rfl⟩

/-- A store's state reads back: the stored object at its own key, the state
handed in at every other key. -/
theorem withObjectStored_get_eq {st : SystemState} (hInv : st.objects.invExt) (id k : SeLe4n.ObjId)
    (obj : KernelObject) :
    (st.withObjectStored id obj).objects[k]? = if k = id then some obj else st.objects[k]? := by
  split
  · next hk => subst hk; exact SystemState.withObjectStored_objects_self st k obj hInv
  · next hk =>
    have hS := SystemState.storeObject_eq_withObjectStored st id obj
    exact storeObject_objects_ne st _ id k obj hk hInv hS

/-- A key holding an object of one kind is not a key holding another. -/
theorem objKey_ne_of_kinds {st : SystemState} {a b : SeLe4n.ObjId} {oa ob : KernelObject}
    (hA : st.objects[a]? = some oa) (hB : st.objects[b]? = some ob)
    (hK : oa.objectType ≠ ob.objectType) : a ≠ b := by
  intro hE; subst hE; rw [hA] at hB; cases hB; exact hK rfl

/-- **The frame push, admitted, writes Replies only**: on a well-formed table
whose pushed frame is a Reply, the frame is not its own predecessor and the
frame below resolves, the push succeeds, keeps the table well formed and leaves
every key that held no Reply as it was. -/
theorem storeDonationFramePushR_admitted {S : SystemState} {scId : SeLe4n.SchedContextId}
    {pushRid : SeLe4n.ReplyId} {pushReply pr : Reply} {oldHead? : Option SeLe4n.ReplyId}
    (hInv : S.objects.invExt) (hPR : S.objects[pushRid.toObjId]? = some (.reply pr))
    (hNe : oldHead? ≠ some pushRid)
    (hOld : ∀ old, oldHead? = some old → (S.getReply? old).isSome = true) :
    ∃ S2, storeDonationFramePushR scId pushRid pushReply oldHead? S = .ok S2 ∧
      S2.objects.invExt ∧
      ∀ k : SeLe4n.ObjId, (∀ r, S.objects[k]? ≠ some (KernelObject.reply r)) →
        S2.objects[k]? = S.objects[k]? := by
  have hKeepA : ∀ (obj : KernelObject) (k : SeLe4n.ObjId), (∀ r, S.objects[k]? ≠ some (KernelObject.reply r)) →
      (S.withObjectStored pushRid.toObjId obj).objects[k]? = S.objects[k]? := fun obj k hk => by
    rw [withObjectStored_get_eq hInv]
    split
    · next hE => subst hE; exact absurd hPR (hk pr)
    · rfl
  have hB : (oldHead? == some pushRid) = false := by
    cases h : (oldHead? == some pushRid)
    · rfl
    · exact absurd (eq_of_beq h) hNe
  unfold storeDonationFramePushR
  rw [hB]
  simp only [Bool.false_eq_true, ↓reduceIte]
  cases oldHead? with
  | none =>
    exact ⟨_, rfl, SystemState.withObjectStored_preserves_objects_invExt _ _ _ hInv, hKeepA _⟩
  | some old =>
    dsimp only
    generalize hA : S.withObjectStored pushRid.toObjId
      (.reply { pushReply with prev := some old, next := some (.head scId) }) = A
    have hInvA : A.objects.invExt := hA ▸ SystemState.withObjectStored_preserves_objects_invExt _ _ _ hInv
    have hKA : ∀ k : SeLe4n.ObjId, (∀ r, S.objects[k]? ≠ some (KernelObject.reply r)) → A.objects[k]? = S.objects[k]? :=
      fun k hk => hA ▸ hKeepA _ k hk
    obtain ⟨oR, hOR⟩ : ∃ oR, A.getReply? old = some oR := by
      have hI := hOld old rfl
      unfold SystemState.getReply? at hI ⊢
      rw [← hA, withObjectStored_get_eq hInv]
      by_cases hE : old.toObjId = pushRid.toObjId
      · rw [if_pos hE]; exact ⟨_, rfl⟩
      · rw [if_neg hE]
        revert hI
        cases S.objects[old.toObjId]? with
        | none => intro hI; cases hI
        | some o => cases o <;> first | exact fun _ => ⟨_, rfl⟩ | (intro hI; cases hI; done)
    rw [hOR]
    refine ⟨_, rfl, SystemState.withObjectStored_preserves_objects_invExt _ _ _ hInvA, ?_⟩
    intro k hk
    have hOk : old.toObjId ≠ k := by
      intro hE; subst hE
      have := (SystemState.getReply?_eq_some_iff _ _ _).mp hOR
      rw [hKA _ hk] at this
      exact hk _ this
    rw [withObjectStored_get_eq hInvA, if_neg (Ne.symm hOk), hKA k hk]

/-- **The donation, admitted, refuses only on the state handed in** (WS-SX
SX34): on a well-formed object table, every refusal of `donateSchedContextR` is
one of its checks before the first store -- the admission
(`donationPushRefusal?`) among them -- so a refused donation reports the state
it was handed and writes nothing.  The lookups after the stores are defensive
checks that cannot refuse here: the stores write a context, Replies and the
donor's TCB, at keys holding no thread but the donor's. -/
theorem donateSchedContextR_stops_at_entry {clientTid serverTid : SeLe4n.ThreadId}
    {clientScId : SeLe4n.SchedContextId} {st st' : SystemState} {e : KernelError}
    (hInv : st.objects.invExt)
    (h : donateSchedContextR clientTid serverTid clientScId st = .error (e, st')) : st' = st := by
  unfold donateSchedContextR at h
  split at h
  case h_2 => cases h; rfl
  rename_i sc hSc
  split at h
  · cases h; rfl
  split at h
  · cases h; rfl
  rename_i donor hD
  split at h
  · cases h; rfl
  rename_i pushRid pr hPF
  split at h
  · cases h; rfl
  rename_i hAd
  exfalso
  obtain ⟨hNe, hOld, hS⟩ := donationPushRefusal?_none_facts hAd
  obtain ⟨-, hPR, -⟩ := donationPushFrame?_ok st donor pushRid pr hPF
  have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hPRO := (SystemState.getReply?_eq_some_iff _ _ _).mp hPR
  have hDO := lookupTcb_some_objects st clientTid donor hD
  have hDNR := lookupTcb_some_not_reserved st clientTid donor hD
  obtain ⟨srv, hSL⟩ := Option.isSome_iff_exists.mp hS
  have hSO := lookupTcb_some_objects st serverTid srv hSL
  have hSNR := lookupTcb_some_not_reserved st serverTid srv hSL
  dsimp only at h
  generalize hS1 : st.withObjectStored clientScId.toObjId (.schedContext
    { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some serverTid),
              scReply := some pushRid }) = S1 at h
  have hInv1 : S1.objects.invExt := hS1 ▸ SystemState.withObjectStored_preserves_objects_invExt _ _ _ hInv
  have hK1 : ∀ k, k ≠ clientScId.toObjId → S1.objects[k]? = st.objects[k]? := fun k hk => by
    rw [← hS1, withObjectStored_get_eq hInv, if_neg hk]
  have hPR1 : S1.objects[pushRid.toObjId]? = some (.reply pr) :=
    (hK1 _ (objKey_ne_of_kinds hPRO hScO (by simp [KernelObject.objectType]))).trans hPRO
  have hOld1 : ∀ old, sc.scReply = some old → (S1.getReply? old).isSome = true := by
    intro old hO
    obtain ⟨oR, hOR⟩ := Option.isSome_iff_exists.mp (hOld old hO)
    have hOO := (SystemState.getReply?_eq_some_iff _ _ _).mp hOR
    have hOO1 := (hK1 _ (objKey_ne_of_kinds hOO hScO (by simp [KernelObject.objectType]))).trans hOO
    rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hOO1]; rfl
  obtain ⟨S2, hP, hInv2, hK2⟩ := storeDonationFramePushR_admitted (scId := clientScId)
    (pushReply := pr) hInv1 hPR1 hNe hOld1
  rw [hP] at h
  dsimp only at h
  have hNotReply : ∀ {k t}, st.objects[k]? = some (KernelObject.tcb t) →
      k ≠ clientScId.toObjId ∧ ∀ r, S1.objects[k]? ≠ some (KernelObject.reply r) := by
    intro k t hk
    have hne := objKey_ne_of_kinds hk hScO (by simp [KernelObject.objectType])
    refine ⟨hne, fun r hr => ?_⟩
    rw [hK1 _ hne, hk] at hr; cases hr
  have hD2 : S2.objects[clientTid.toObjId]? = some (.tcb donor) := by
    obtain ⟨hne, hnr⟩ := hNotReply hDO
    rw [hK2 _ hnr, hK1 _ hne, hDO]
  rw [lookupTcb_of_objects_of_not_reserved S2 clientTid donor hD2 hDNR] at h
  dsimp only at h
  generalize hS3 : S2.withObjectStored clientTid.toObjId (.tcb
    { donor with scBindingScCode := 0, scBindingOwnerCode := 0 }) = S3 at h
  obtain ⟨x, hX⟩ : ∃ x, S3.objects[serverTid.toObjId]? = some (.tcb x) := by
    rw [← hS3, withObjectStored_get_eq hInv2]
    by_cases hE : serverTid.toObjId = clientTid.toObjId
    · rw [if_pos hE]; exact ⟨_, rfl⟩
    · rw [if_neg hE]
      obtain ⟨hne, hnr⟩ := hNotReply hSO
      rw [hK2 _ hnr, hK1 _ hne, hSO]; exact ⟨_, rfl⟩
  rw [lookupTcb_of_objects_of_not_reserved S3 serverTid x hX hSNR] at h
  cases h


/-- A key that holds no thread holds none after a store of anything but a thread. -/
theorem withObjectStored_noTcb {S : SystemState} (hInv : S.objects.invExt) {id k : SeLe4n.ObjId}
    {obj : KernelObject} (hObj : ∀ t, obj ≠ .tcb t)
    (h : ∀ t, S.objects[k]? ≠ some (KernelObject.tcb t)) :
    ∀ t, (S.withObjectStored id obj).objects[k]? ≠ some (KernelObject.tcb t) := by
  intro t
  rw [withObjectStored_get_eq hInv]
  split
  · intro h'; cases h'; exact hObj t rfl
  · exact h t

/-- The frame push writes Replies only, so a key holding no thread holds none after it. -/
theorem storeDonationFramePushR_noTcb {S S2 : SystemState} {scId : SeLe4n.SchedContextId}
    {pushRid : SeLe4n.ReplyId} {pushReply : Reply} {oldHead? : Option SeLe4n.ReplyId}
    (hInv : S.objects.invExt) (hP : storeDonationFramePushR scId pushRid pushReply oldHead? S = .ok S2)
    {k : SeLe4n.ObjId} (h : ∀ t, S.objects[k]? ≠ some (KernelObject.tcb t)) :
    ∀ t, S2.objects[k]? ≠ some (KernelObject.tcb t) := by
  unfold storeDonationFramePushR at hP
  split at hP
  · cases hP
  have hA := withObjectStored_noTcb (id := pushRid.toObjId)
    (obj := .reply { pushReply with prev := oldHead?, next := some (.head scId) }) hInv
    (fun _ h' => by cases h') h
  cases oldHead? with
  | none => cases hP; exact hA
  | some old =>
    dsimp only at hP
    split at hP
    · cases hP
    · cases hP
      exact withObjectStored_noTcb (SystemState.withObjectStored_preserves_objects_invExt _ _ _ hInv)
        (fun _ h' => by cases h') hA

/-- A key holding no thread looks no thread up. -/
theorem lookupTcb_none_of_noTcb {S : SystemState} {tid : SeLe4n.ThreadId}
    (h : ∀ t, S.objects[tid.toObjId]? ≠ some (KernelObject.tcb t)) : lookupTcb S tid = none := by
  cases hL : lookupTcb S tid with
  | none => rfl
  | some t => exact absurd (lookupTcb_some_objects S tid t hL) (h t)

/-- **The admission refuses exactly where the checks after the stores would**
(WS-SX SX34, D62's converse): on a well-formed object table, where the donation's
checks before the admission pass and the admission refuses, the donation as it was
before the admission -- the context's store, the frame push, the donor's lookup and
store, the server's lookup, then anything at all -- refuses with the same error.
So the admission changes no answer of `donateSchedContext` on such a state: the
`.call` and `.receive` donations it is shared with refuse as they did. -/
theorem donationPushRefusal?_some_exact {clientTid serverTid : SeLe4n.ThreadId}
    {clientScId : SeLe4n.SchedContextId} {st : SystemState} {sc : SchedContext} {donor : TCB}
    {pushRid : SeLe4n.ReplyId} {pr : Reply} {e : KernelError}
    (hInv : st.objects.invExt) (hSc : st.getSchedContext? clientScId = some sc)
    (hD : lookupTcb st clientTid = some donor)
    (hPF : donationPushFrame? st donor = .ok (pushRid, pr))
    (hAd : donationPushRefusal? st serverTid sc.scReply pushRid = some e)
    (k : TCB → SystemState → Except KernelError SystemState) :
    (match storeObject clientScId.toObjId (.schedContext
        { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some serverTid),
                  scReply := some pushRid }) st with
     | .error e => .error e
     | .ok ((), st1) =>
       match storeDonationFramePush clientScId pushRid pr sc.scReply st1 with
       | .error e => .error e
       | .ok st2 =>
         match lookupTcb st2 clientTid with
         | none => .error .objectNotFound
         | some clientTcb =>
           match storeObject clientTid.toObjId
               (.tcb { clientTcb with scBindingScCode := 0, scBindingOwnerCode := 0 }) st2 with
           | .error e => .error e
           | .ok ((), st3) =>
             match lookupTcb st3 serverTid with
             | none => .error .objectNotFound
             | some serverTcb => k serverTcb st3 : Except KernelError SystemState) = .error e := by
  simp only [SystemState.storeObject_eq_withObjectStored, ← storeDonationFramePushR_eq]
  obtain ⟨-, hPR, -⟩ := donationPushFrame?_ok st donor pushRid pr hPF
  have hScO := (SystemState.getSchedContext?_eq_some_iff _ _ _).mp hSc
  have hPRO := (SystemState.getReply?_eq_some_iff _ _ _).mp hPR
  have hDO := lookupTcb_some_objects st clientTid donor hD
  have hDNR := lookupTcb_some_not_reserved st clientTid donor hD
  generalize hS1 : st.withObjectStored clientScId.toObjId (.schedContext
    { sc with boundThreadCode := SeLe4n.ThreadId.optCode (some serverTid),
              scReply := some pushRid }) = S1
  have hInv1 : S1.objects.invExt := hS1 ▸ SystemState.withObjectStored_preserves_objects_invExt _ _ _ hInv
  have hK1 : ∀ k, k ≠ clientScId.toObjId → S1.objects[k]? = st.objects[k]? := fun k hk => by
    rw [← hS1, withObjectStored_get_eq hInv, if_neg hk]
  have hPR1 : S1.objects[pushRid.toObjId]? = some (.reply pr) :=
    (hK1 _ (objKey_ne_of_kinds hPRO hScO (by simp [KernelObject.objectType]))).trans hPRO
  -- The server refusal, the admission's last, met after the donor's store.
  have hServer : sc.scReply ≠ some pushRid →
      (∀ old, sc.scReply = some old → (st.getReply? old).isSome = true) →
      lookupTcb st serverTid = none →
      (match (storeDonationFramePushR clientScId pushRid pr sc.scReply S1).mapError Prod.fst with
       | .error e => .error e
       | .ok st2 =>
         match lookupTcb st2 clientTid with
         | none => .error .objectNotFound
         | some clientTcb =>
           match (Except.ok ((), st2.withObjectStored clientTid.toObjId
               (.tcb { clientTcb with scBindingScCode := 0, scBindingOwnerCode := 0 })) :
               Except KernelError (Unit × SystemState)) with
           | .error e => .error e
           | .ok ((), st3) =>
             match lookupTcb st3 serverTid with
             | none => .error .objectNotFound
             | some serverTcb => k serverTcb st3 : Except KernelError SystemState) =
        .error .objectNotFound := by
    intro hNe hOld hTn
    have hOld1 : ∀ old, sc.scReply = some old → (S1.getReply? old).isSome = true := by
      intro old hO
      obtain ⟨oR, hOR⟩ := Option.isSome_iff_exists.mp (hOld old hO)
      have hOO := (SystemState.getReply?_eq_some_iff _ _ _).mp hOR
      have hOO1 := (hK1 _ (objKey_ne_of_kinds hOO hScO (by simp [KernelObject.objectType]))).trans hOO
      rw [(SystemState.getReply?_eq_some_iff _ _ _).mpr hOO1]; rfl
    obtain ⟨S2, hP, hInv2, hK2⟩ := storeDonationFramePushR_admitted (scId := clientScId)
      (pushReply := pr) hInv1 hPR1 hNe hOld1
    rw [hP]
    dsimp only [refusalCarrying_mapError_ok]
    have hD1 : ∀ r, S1.objects[clientTid.toObjId]? ≠ some (KernelObject.reply r) := by
      intro r hr
      rw [hK1 _ (objKey_ne_of_kinds hDO hScO (by simp [KernelObject.objectType])), hDO] at hr
      cases hr
    have hD2 : S2.objects[clientTid.toObjId]? = some (.tcb donor) := by
      rw [hK2 _ hD1, hK1 _ (objKey_ne_of_kinds hDO hScO (by simp [KernelObject.objectType])), hDO]
    rw [lookupTcb_of_objects_of_not_reserved S2 clientTid donor hD2 hDNR]
    dsimp only
    have hL : lookupTcb (S2.withObjectStored clientTid.toObjId
        (.tcb { donor with scBindingScCode := 0, scBindingOwnerCode := 0 })) serverTid = none := by
      by_cases hRes : serverTid.isReserved
      · unfold lookupTcb; rw [if_pos hRes]
      have h0 : ∀ t, st.objects[serverTid.toObjId]? ≠ some (KernelObject.tcb t) := fun t ht => by
        rw [lookupTcb_of_objects_of_not_reserved st serverTid t ht hRes] at hTn; cases hTn
      have hne : serverTid.toObjId ≠ clientTid.toObjId := fun hE => by
        rw [SeLe4n.ThreadId.toObjId_injective _ _ hE, hD] at hTn; cases hTn
      have h1 : ∀ t, S1.objects[serverTid.toObjId]? ≠ some (KernelObject.tcb t) := by
        rw [← hS1]; exact withObjectStored_noTcb hInv (fun _ h' => by cases h') h0
      have h2 := storeDonationFramePushR_noTcb hInv1 hP h1
      apply lookupTcb_none_of_noTcb
      intro t
      rw [withObjectStored_get_eq hInv2, if_neg hne]
      exact h2 t
    rw [hL]
  -- The admission's three refusals, in its order.
  unfold donationPushRefusal? at hAd
  cases hOH : sc.scReply with
  | none =>
    rw [hOH] at hAd hServer
    cases hT : lookupTcb st serverTid with
    | some _ => simp [hT] at hAd
    | none =>
      simp [hT] at hAd
      subst hAd
      exact hServer (by simp) (by simp) hT
  | some old =>
    rw [hOH] at hAd hServer
    by_cases hE : old = pushRid
    · subst hE
      simp only [beq_self_eq_true, ↓reduceIte, Option.some.injEq] at hAd
      subst hAd
      rw [show storeDonationFramePushR clientScId old pr (some old) S1 =
        .error (.invalidArgument 0, S1) by simp [storeDonationFramePushR]]
      rfl
    have hB : (old == pushRid) = false := by simpa using hE
    simp only [hB, Bool.false_eq_true, ↓reduceIte] at hAd
    cases hR : st.getReply? old with
    | none =>
      simp only [hR, Option.isNone_none, ↓reduceIte, Option.some.injEq] at hAd
      subst hAd
      have hne : old.toObjId ≠ pushRid.toObjId := fun h' => hE (SeLe4n.ReplyId.toObjId_injective _ _ h')
      have hR1 : S1.getReply? old = none := by
        unfold SystemState.getReply? at hR ⊢
        by_cases hk : old.toObjId = clientScId.toObjId
        · rw [← hS1, withObjectStored_get_eq hInv, if_pos hk]
        · rw [hK1 _ hk]; exact hR
      have hRA : (S1.withObjectStored pushRid.toObjId
          (.reply { pr with prev := some old, next := some (.head clientScId) })).getReply? old = none := by
        unfold SystemState.getReply? at hR1 ⊢
        rw [withObjectStored_get_eq hInv1, if_neg hne]; exact hR1
      have hB' : (some old == some pushRid) = false := by simpa using hE
      rw [show storeDonationFramePushR clientScId pushRid pr (some old) S1 =
        .error (.objectNotFound, _) by
          unfold storeDonationFramePushR
          rw [hB']
          simp only [Bool.false_eq_true, ↓reduceIte]
          rw [hRA]]
      rfl
    | some oR =>
      simp only [hR, Option.isNone_some, Bool.false_eq_true, ↓reduceIte] at hAd
      cases hT : lookupTcb st serverTid with
      | some _ => simp [hT] at hAd
      | none =>
        simp [hT] at hAd
        subst hAd
        exact hServer (by simpa using hE) (fun o hO => by cases hO; rw [hR]; rfl) hT

end DonationAdmissionExact

/-- `applyCallDonationOnCore` (the receiver handed the caller's context where it
holds none and the caller holds one, the replenishments migrated between their
homes): the context it donates is the one its own guard matched, read before
the donation writes, so the state handed in is not read after it.  Its only
refusals are the donation's. -/
def applyCallDonationOnCoreR (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : Concurrency.CoreId) : RefusalCarryingStep := fun st =>
  match lookupTcb st receiverVtid.val with
  | none => .ok st
  | some receiverTcb =>
    match receiverTcb.schedContextBinding with
    | .unbound =>
      match lookupTcb st callerVtid.val with
      | none => .ok st
      | some callerTcb =>
        match callerTcb.schedContextBinding.scId? with
        | some clientScId =>
          match donateSchedContextR callerVtid.val receiverVtid.val clientScId st with
          | .error es => .error es
          | .ok st' => .ok (migrateSchedContextReplenishment st' clientScId donorHome doneeHome)
        | none => .ok st
    | _ => .ok st

theorem applyCallDonationOnCoreR_eq (callerVtid receiverVtid : SeLe4n.ValidThreadId)
    (donorHome doneeHome : Concurrency.CoreId) (st : SystemState) :
    (applyCallDonationOnCoreR callerVtid receiverVtid donorHome doneeHome st).mapError Prod.fst =
      applyCallDonationOnCore st callerVtid receiverVtid donorHome doneeHome := by
  unfold applyCallDonationOnCoreR applyCallDonationOnCore applyCallDonation
    callDonationSchedContext? donateSchedContextValid
  simp only [← donateSchedContextR_eq]
  repeat' (first | rfl | (split <;> (try (rename_i h; simp only [h, refusalCarrying_mapError_error,
      refusalCarrying_mapError_ok]))))

/-- `applyRendezvousCallDonation` (the dequeued caller's context handed to the
receiver, each thread's home core read on the state handed in): the sentinel
refuses on the state handed in. -/
def applyRendezvousCallDonationR (receiver donor : SeLe4n.ThreadId) : RefusalCarryingStep :=
  fun st =>
    match donor.toValid?, receiver.toValid? with
    | some donorV, some receiverV =>
        applyCallDonationOnCoreR donorV receiverV
          (determineTargetCore st donor) (determineTargetCore st receiver) st
    | _, _ => .error (.invalidArgument 0, st)

theorem applyRendezvousCallDonationR_eq (receiver donor : SeLe4n.ThreadId) (st : SystemState) :
    (applyRendezvousCallDonationR receiver donor st).mapError Prod.fst =
      applyRendezvousCallDonation st receiver donor := by
  unfold applyRendezvousCallDonationR applyRendezvousCallDonation
  cases donor.toValid? <;> cases receiver.toValid? <;>
    first | rfl | exact applyCallDonationOnCoreR_eq _ _ _ _ st

/-- **The other half of the pair**: a donation that succeeds was admitted, its
admission read on the state it was handed. -/
theorem donationPushRefusal?_eq_none_of_ok {clientTid serverTid : SeLe4n.ThreadId}
    {clientScId : SeLe4n.SchedContextId} {st st' : SystemState}
    (h : donateSchedContext st clientTid serverTid clientScId = .ok st') :
    ∃ sc donor pushRid pr, st.getSchedContext? clientScId = some sc ∧
      lookupTcb st clientTid = some donor ∧ donationPushFrame? st donor = .ok (pushRid, pr) ∧
      donationPushRefusal? st serverTid sc.scReply pushRid = none := by
  unfold donateSchedContext at h
  split at h
  · rename_i sc hSc
    split at h
    · cases h
    split at h
    · cases h
    rename_i donor hD
    split at h
    · cases h
    rename_i pushRid pr hPF
    split at h
    · cases h
    rename_i hAd
    exact ⟨sc, donor, pushRid, pr, hSc, hD, hPF, hAd⟩
  · cases h

/-- The rendezvous donation, refusal-carrying, refuses only on the state handed
in where the object table is well formed (`donateSchedContextR_stops_at_entry`):
the sentinel refusal and every check of the donation precede its first store. -/
theorem applyRendezvousCallDonationR_stops_at_entry {receiver donor : SeLe4n.ThreadId}
    {st st' : SystemState} {e : KernelError} (hInv : st.objects.invExt)
    (h : applyRendezvousCallDonationR receiver donor st = .error (e, st')) : st' = st := by
  unfold applyRendezvousCallDonationR at h
  split at h
  · unfold applyCallDonationOnCoreR at h
    repeat' (first | (cases h; done) | split at h)
    all_goals first
      | (cases h; rfl)
      | (rename_i hD; cases h; exact donateSchedContextR_stops_at_entry hInv hD)
  · cases h; rfl

end CallDonation

end SeLe4n.Kernel
