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
frame's push): its checks refuse on the state handed in; the frame push and the
two thread lookups after the stores refuse on the state the stores reached. -/
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

end CallDonation

end SeLe4n.Kernel
