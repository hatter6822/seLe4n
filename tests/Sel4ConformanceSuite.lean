-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Testing.Sel4ConformanceTable
import SeLe4n.Testing.Helpers
import SeLe4n.Testing.StateBuilder

/-!
# The seL4 conformance suite

Runs every row of `SeLe4n.Testing.Sel4Conformance`'s table against the kernel:
each label row against the label round trip, the selection, the decode's word
count and the return shape (`labelRowAgrees`); each syscall row against the
`Syscall` predicates and against the register reads of `decodeSyscallArgs`
over a frame whose registers all differ; each seL4 error against the error
frame seLe4n writes for it; and seL4's `messageInfoFromWord` clamp and the two
word-first decodes (the reply-capability mint's slots, the service register's
interface id) at a word `≥ 2 ^ 63`.
-/

namespace SeLe4n.Testing.Sel4ConformanceSuite

open SeLe4n
open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Architecture.RegisterDecode
open SeLe4n.Kernel.Architecture.SyscallArgDecode
open SeLe4n.Testing.Sel4Conformance

private def tag : String := "sel4-conformance"

private def expect (label : String) (cond : Bool) : IO Unit :=
  expectCond tag label cond

/-- Every label row agrees with the kernel. -/
def runLabelRows : IO Unit := do
  for r in sel4LabelRows do
    expect s!"label {r.label} {r.name}" (labelRowAgrees r)
  let absent := sel4LabelRows.filter (fun r => r.status.op?.isNone)
  IO.println s!"{tag}: {sel4LabelRows.length} label rows, {absent.length} with no seLe4n operation"
  for r in absent do
    match r.status with
    | .absent owner => IO.println s!"{tag}:   absent label {r.label} {r.name} (owner {owner})"
    | _ => pure ()

/-- A frame whose registers x0–x8 hold distinct words, x7 the syscall's. -/
def frameFor (sys : Syscall) : RegisterFile :=
  (List.range 9).foldl (fun rf i =>
      writeReg rf ⟨i⟩ (if i == 7 then sys.word else i.toUInt64 + ((5 : UInt64) <<< 12)))
    (default : RegisterFile)

/-- Every syscall row agrees with the `Syscall` predicates, and the register
decode reads the registers the row names from where seL4 reads them. -/
def runSyscallRows : IO Unit := do
  for r in sel4SyscallRows do
    expect s!"syscall {r.name} predicates" (syscallRowAgrees r)
    let rf := frameFor r.sys
    match decodeSyscallArgs SyscallId.send.toNat arm64DefaultLayout rf with
    | .error _ => expect s!"syscall {r.name} decodes" false
    | .ok (d : SyscallDecodeResult) =>
      expect s!"syscall {r.name} x0 is the capability" (d.capAddr == CPtr.ofWord (readRegWord rf ⟨0⟩))
      expect s!"syscall {r.name} x1 is the message info"
        (d.msgInfo.label == 5 && d.msgInfo.length == 1)
      expect s!"syscall {r.name} x2-x5 are the message registers"
        (d.msgRegs.map (·.word) == #[readRegWord rf ⟨2⟩, readRegWord rf ⟨3⟩, readRegWord rf ⟨4⟩,
          readRegWord rf ⟨5⟩])
      expect s!"syscall {r.name} x6 is the reply register"
        (d.replyCPtr == CPtr.ofWord (readRegWord rf ⟨6⟩) && (r.regsRead.contains 6 || !r.canReply))
      expect s!"syscall {r.name} canReply from x7" (d.canReply == r.canReply)

/-- Each seL4 error has a seLe4n error whose payload is seL4's, and the error
frame carries it: `x0 = 0`, the code in `x1`'s label, the payload in x2–x5. -/
def runErrors : IO Unit := do
  let all : List Sel4Error := [.invalidArgument, .invalidCapability, .illegalOperation,
    .rangeError, .alignmentError, .failedLookup, .truncatedMessage, .deleteFirst,
    .revokeFirst, .notEnoughMemory]
  expect "seL4 codes 1-10" (all.map (·.code) == (List.range 10).map (· + 1))
  for e in all do
    let k := e.kernelError
    expect s!"error {e.code} payload words" (k.payloadLength == e.payloadWords)
    expect s!"error {e.code} label round trip" (ofErrorLabel? (errorLabel k) == some k.erasePayload)
    let f := errorFrame k false
    expect s!"error {e.code} frame" (f.x0 == 0 && f.x2 == k.payloadWord 0 && f.x3 == k.payloadWord 1)

/-- A decoded message of the given words. -/
private def decodedOf (regs : Array RegValue) : SyscallDecodeResult :=
  { capAddr := CPtr.ofNat 0, msgInfo := { length := regs.size, extraCaps := 0, label := 0 },
    syscallId := .send, msgRegs := regs }

/-- The full-width word the word-first decodes are tested at. -/
private def wideWord : UInt64 := ((1 : UInt64) <<< 63) + 5

/-- seL4's `messageInfoFromWord` (`include/api/types.h:83`) clamps a length
past 120 to 120 and refuses nothing; the word decode is the same. -/
def runMessageInfo : IO Unit := do
  for len in ([0, 1, 4, 5, 119, 120, 121, 127] : List Nat) do
    let w : UInt64 := ((7 : UInt64) <<< 12) ||| ((2 : UInt64) <<< 7) ||| len.toUInt64
    let ok : Bool := match decodeMsgInfoWord w with
      | .ok mi => mi.length == min len 120 && mi.label == 7 && mi.extraCaps == 2
      | .error _ => false
    expect s!"messageInfoFromWord length {len}" ok
  let allOnes : Bool := match decodeMsgInfoWord (0xFFFFFFFFFFFFFFFF : UInt64) with
    | .ok mi => mi.length == 120 && mi.extraCaps == 3 && mi.label == MessageInfo.maxLabel
    | .error _ => false
  expect "messageInfoFromWord all ones" allOnes

/-- The two word-first decodes at a word `≥ 2 ^ 63`: the reply-capability
mint's slots read as `windowWordBound`, a slot no CNode addresses, and the
service register's interface id is refused `invalidArgument 0`. -/
def runWordFirst : IO Unit := do
  expect "mintReplyCap wide source slot"
    (match decodeMintReplyCapArgs (decodedOf #[⟨wideWord⟩, ⟨3⟩]) with
      | .ok a => a.srcSlot.toNat == windowWordBound && a.dstSlot.toNat == 3
      | .error _ => false)
  expect "mintReplyCap wide destination slot"
    (match decodeMintReplyCapArgs (decodedOf #[⟨2⟩, ⟨wideWord⟩]) with
      | .ok a => a.srcSlot.toNat == 2 && a.dstSlot.toNat == windowWordBound
      | .error _ => false)
  expect "serviceRegister wide interface id"
    (match decodeServiceRegisterArgs (decodedOf #[⟨wideWord⟩, ⟨1⟩, ⟨8⟩, ⟨8⟩, ⟨0⟩]) with
      | .error (.invalidArgument 0) => true
      | _ => false)
  expect "serviceRegister interface id below the bound"
    (match decodeServiceRegisterArgs (decodedOf #[⟨9⟩, ⟨1⟩, ⟨8⟩, ⟨8⟩, ⟨0⟩]) with
      | .ok a => a.interfaceId.toNat == 9
      | _ => false)

/-! ### The behaviour rows

One scenario per `sel4BehaviourRows` row, each run against the kernel.  A
hardening row's scenario runs both halves: seL4's behaviour where the gate
admits it, and the refusal where it does not. -/

section Behaviour
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency

private def bTcb (tid : Nat) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨10⟩, domain := ⟨0⟩,
    spaceCells := SeLe4n.Model.TCB.spaceCellsOf ⟨0⟩ ⟨0⟩, ipcBuffer := (SeLe4n.VAddr.ofNat 0),
    threadState := .Ready }

private def bState (objs : List (ObjId × KernelObject)) : SystemState :=
  ({ objects := objs, current := none } : SeLe4n.Testing.BootstrapBuilder).buildChecked

private def bWaiter : SeLe4n.ThreadId := ⟨2⟩
private def bScObj : SeLe4n.ObjId := ⟨60⟩
private def bScId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofObjId bScObj
private def bNtfn : SeLe4n.ObjId := ⟨80⟩

private def bNtfnObject : Bool → Notification
  | true =>
    { state := .active, hasPendingBadge := true, pendingWord := SeLe4n.Badge.ofNatMasked 7,
      schedContextCode := bScId.val + 1 }
  | false =>
    { state := .idle, hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero,
      schedContextCode := bScId.val + 1 }

/-- A notification lending context 60, with or without a pending badge, and
waiter 2 holding no context. -/
private def bNtfnState (pending : Bool) : SystemState :=
  bState [
    (bWaiter.toObjId, .tcb (bTcb 2)),
    (bScObj, .schedContext { SeLe4n.Kernel.SchedContext.empty bScId with
      notificationCode := bNtfn.val + 1 }),
    (bNtfn, .notification (bNtfnObject pending))]

private def bHolds (st : SystemState) : Bool :=
  (st.getTcb? bWaiter).any (fun t => decide (t.schedContextBinding = .bound bScId)) &&
    (st.getSchedContext? bScId).any (fun sc => decide (sc.boundThread = some bWaiter))

private def bHoldsNothing (st : SystemState) : Bool :=
  (st.getTcb? bWaiter).any (fun t => t.scBindingScCode == 0) &&
    (st.getSchedContext? bScId).any (fun sc => decide (sc.boundThread = none))

/-- The context labelled above every thread. -/
private def bContextAbove : LabelingContext :=
  { defaultLabelingContext with
    objectLabelOf := fun o =>
      if o = bScObj then SecurityLabel.kernelTrusted else SecurityLabel.publicLabel }

/-- The waiter labelled above the context: the context's label flows to it,
but not back.  The notification carries the waiter's label, since a waiter
joins a notification only at its own label (the two-way label gate). -/
private def bWaiterAbove : LabelingContext :=
  { defaultLabelingContext with
    objectLabelOf := fun o =>
      if o = bNtfn then SecurityLabel.kernelTrusted else SecurityLabel.publicLabel
    threadLabelOf := fun t =>
      if t = bWaiter then SecurityLabel.kernelTrusted else SecurityLabel.publicLabel }

/-- Waiter 2 blocks on the notification, then a signal wakes it. -/
private def bSignalled (ctx : LabelingContext) : Option SystemState :=
  match SeLe4n.Kernel.notificationWaitCrossCoreDispatchChecked ctx bNtfn bWaiter
      bootCoreId (bNtfnState false) with
  | (st1, .ok none) =>
    match SeLe4n.Kernel.sendSignalOnCoreFlowing ctx bNtfn (SeLe4n.Badge.ofNatMasked 5)
        bootCoreId st1 with
    | (st2, .ok _) => some st2
    | _ => none
  | _ => none

private def bWoken (st : SystemState) : Bool :=
  (st.getTcb? bWaiter).any (fun t => decide (t.ipcState = .ready))

private def bCheckSignal : Bool :=
  (bSignalled defaultLabelingContext).any (fun st => bWoken st && bHolds st) &&
    (bSignalled bContextAbove).any (fun st => bWoken st && bHoldsNothing st) &&
    (bSignalled bWaiterAbove).any (fun st => bWoken st && bHoldsNothing st)

private def bConsumed (ctx : LabelingContext) : Option SystemState :=
  match SeLe4n.Kernel.completeSignalArm ctx bWaiter bNtfn bootCoreId (bNtfnState true) with
  | .ok ((), st) => some st
  | .error _ => none

private def bCheckWaitConsume : Bool :=
  (bConsumed defaultLabelingContext).any bHolds &&
    (bConsumed bContextAbove).any bHoldsNothing &&
    (bConsumed bWaiterAbove).any bHoldsNothing

/-- The waiter, lent the context by a signal, waits again and blocks: the
context goes back to the notification. -/
private def bCheckWaitReturn : Bool :=
  match bSignalled defaultLabelingContext with
  | some st =>
    match SeLe4n.Kernel.completeSignalArm defaultLabelingContext bWaiter bNtfn bootCoreId st with
    | .ok ((), st') => bHolds st && bHoldsNothing st' &&
        (st'.getTcb? bWaiter).any (fun t => decide (t.ipcState = .blockedOnNotification bNtfn))
    | .error _ => false
  | none => false

/-- Caller 3 holds context 61 and has called through reply 63; server 4 holds none.  The call
lends the context, as seL4-MCS's `reply_push` does: no label check refuses it. -/
private def bCheckCallLend : Bool :=
  let caller : SeLe4n.ThreadId := ⟨3⟩
  let server : SeLe4n.ThreadId := ⟨4⟩
  let scObj : SeLe4n.ObjId := ⟨61⟩
  let scId := SeLe4n.SchedContextId.ofObjId scObj
  let st := bState [
    (caller.toObjId, .tcb { bTcb 3 with
      scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound scId),
      replyObjectCode := SeLe4n.ReplyId.optCode (some ⟨63⟩) }),
    (⟨63⟩, .reply { replyId := ⟨63⟩, callerCode := SeLe4n.ThreadId.optCode (some caller) }),
    (server.toObjId, .tcb (bTcb 4)),
    (scObj, .schedContext { SeLe4n.Kernel.SchedContext.empty scId with
      boundThreadCode := caller.val + 1, isActive := true })]
  match caller.toValid?, server.toValid? with
  | some cV, some sV =>
    match SeLe4n.Kernel.applyCallDonationOnCore st cV sV bootCoreId bootCoreId with
    | .ok st' =>
      (st'.getTcb? server).any (fun t => decide (t.schedContextBinding = .donated scId caller))
    | .error _ => false
  | _, _ => false

/-- Thread 5 holds context 62 on loan from thread 6.  Its destruction unbinds
the context, which stays unheld; the lender is not handed it back. -/
private def bCheckDestroyUnbinds : Bool :=
  let holder : SeLe4n.ThreadId := ⟨5⟩
  let lender : SeLe4n.ThreadId := ⟨6⟩
  let scObj : SeLe4n.ObjId := ⟨62⟩
  let scId := SeLe4n.SchedContextId.ofObjId scObj
  let binding : SeLe4n.Kernel.SchedContextBinding := .donated scId lender
  let tcb : TCB :=
    { bTcb 5 with
      scBindingScCode := binding.scCode
      scBindingOwnerCode := binding.ownerCode }
  let st := bState [
    (holder.toObjId, .tcb tcb), (lender.toObjId, .tcb (bTcb 6)),
    (scObj, .schedContext { SeLe4n.Kernel.SchedContext.empty scId with
      boundThreadCode := holder.val + 1, isActive := true })]
  match SeLe4n.Kernel.cancelDonationArmOnCore st holder tcb with
  | .ok st' =>
    (st'.getSchedContext? scId).any (fun sc => sc.boundThread.isNone) &&
      (st'.getTcb? holder).any (fun t => decide (t.schedContextBinding = .unbound)) &&
      (st'.getTcb? lender).any (fun t => decide (t.schedContextBinding = .unbound))
  | .error _ => false

/-- The endpoint every reply-stack scenario names. -/
private def bEp : SeLe4n.ObjId := ⟨90⟩

private def bScAt (obj : Nat) (bound : Option SeLe4n.ThreadId) (head : Option SeLe4n.ReplyId) :
    SeLe4n.ObjId × KernelObject :=
  let scId := SeLe4n.SchedContextId.ofObjId ⟨obj⟩
  (⟨obj⟩, .schedContext { SeLe4n.Kernel.SchedContext.empty scId with
    boundThreadCode := SeLe4n.ThreadId.optCode bound, scReply := head, isActive := true })

private def bBinding (st : SystemState) (t : SeLe4n.ThreadId) : Option SeLe4n.SchedContextId :=
  (st.getTcb? t).bind (fun x => x.schedContextBinding.scId?)

private def bBoundTo (st : SystemState) (obj : Nat) : Option SeLe4n.ThreadId :=
  (st.getSchedContext? (SeLe4n.SchedContextId.ofObjId ⟨obj⟩)).bind (·.boundThread)

private def bHeadOf (st : SystemState) (obj : Nat) : Option SeLe4n.ReplyId :=
  (st.getSchedContext? (SeLe4n.SchedContextId.ofObjId ⟨obj⟩)).bind (·.scReply)

/-- Caller 7, holding context 65 of its own, called server 8 and lent it
context 64 through reply 93.  The reply pops the head; seL4's `reply_pop`
donates back only to a caller holding no context, so the server keeps 64 and
the caller wakes holding 65. -/
private def bCheckReplyPopHeld : Bool :=
  let caller : SeLe4n.ThreadId := ⟨7⟩
  let server : SeLe4n.ThreadId := ⟨8⟩
  let rid : SeLe4n.ReplyId := ⟨93⟩
  let lent := SeLe4n.SchedContextId.ofObjId ⟨64⟩
  let own := SeLe4n.SchedContextId.ofObjId ⟨65⟩
  let lentBinding : SeLe4n.Kernel.SchedContextBinding := .donated lent caller
  let st := bState [
    (bEp, .endpoint {}),
    (caller.toObjId, .tcb (TCB.setIpcState { bTcb 7 with
      scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound own),
      replyObjectCode := SeLe4n.ReplyId.optCode (some rid) } (.blockedOnReply bEp (some server)))),
    (server.toObjId, .tcb { bTcb 8 with
      scBindingScCode := lentBinding.scCode, scBindingOwnerCode := lentBinding.ownerCode }),
    (rid.toObjId, .reply { replyId := rid, next := some (.head lent),
                           callerCode := SeLe4n.ThreadId.optCode (some caller) }),
    bScAt 64 (some server) (some rid), bScAt 65 (some caller) none]
  let msg : IpcMessage := { registers := #[SeLe4n.RegValue.ofNat 7], badge := none }
  match SeLe4n.Kernel.endpointReplyCrossCoreDispatch server caller msg bootCoreId st with
  | (st', .ok _) =>
    bBinding st' caller == some own && bBoundTo st' 64 == some server &&
      bBinding st' server == some lent && bHeadOf st' 64 == none &&
      (st'.getTcb? caller).any (fun t => decide (t.ipcState = .ready))
  | (_, .error _) => false

/-- Thread 5 holds context 62 on loan from thread 6, whose Call heads the
context's stack through reply 95.  SchedContext_Unbind succeeds: the holder is
unbound and the context leaves the stack (`schedContext_unbindReply`, D22). -/
private def bCheckUnbindDonated : Bool :=
  let holder : SeLe4n.ThreadId := ⟨5⟩
  let lender : SeLe4n.ThreadId := ⟨6⟩
  let rid : SeLe4n.ReplyId := ⟨95⟩
  let scId := SeLe4n.SchedContextId.ofObjId ⟨62⟩
  let binding : SeLe4n.Kernel.SchedContextBinding := .donated scId lender
  let st := bState [
    (bEp, .endpoint {}),
    (holder.toObjId, .tcb { bTcb 5 with
      scBindingScCode := binding.scCode, scBindingOwnerCode := binding.ownerCode }),
    (lender.toObjId, .tcb (TCB.setIpcState { bTcb 6 with
      replyObjectCode := SeLe4n.ReplyId.optCode (some rid) } (.blockedOnReply bEp (some holder)))),
    (rid.toObjId, .reply { replyId := rid, next := some (.head scId),
                           callerCode := SeLe4n.ThreadId.optCode (some lender) }),
    bScAt 62 (some holder) (some rid)]
  match scId.toObjId.toValid? with
  | some vS =>
    match SeLe4n.Kernel.SchedContextOps.schedContextUnbindAllOnCore vS bootCoreId st with
    | .ok (st', _) =>
      bBoundTo st' 62 == none && bHeadOf st' 62 == none && bBinding st' holder == none &&
        (st'.getReply? rid).any (fun r => decide (r.next = none))
    | .error _ => false
  | none => false

/-- Thread 9, bound to context 66, is suspended: seL4's `suspend` leaves the
binding alone (`schedContext_unbindTCB` runs only on destroy), so the thread and
the context still name each other. -/
private def bCheckSuspendKeeps : Bool :=
  let victim : SeLe4n.ThreadId := ⟨9⟩
  let scId := SeLe4n.SchedContextId.ofObjId ⟨66⟩
  let st := bState [
    (victim.toObjId, .tcb { bTcb 9 with
      scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound scId) }),
    bScAt 66 (some victim) none]
  match victim.toValid? with
  | some vV =>
    match SeLe4n.Kernel.Lifecycle.Suspend.suspendThreadOnCore st vV bootCoreId with
    | .ok (st', _) =>
      bBinding st' victim == some scId && bBoundTo st' 66 == some victim &&
        (st'.getTcb? victim).any (fun t => decide (t.threadState = .Inactive))
    | .error _ => false
  | none => false

/-- Waiter 2 holds context 60, lent by its bound notification 80, and receives
on an empty endpoint: the receive blocks, so seL4's `receiveIPC` returns the
context first (`maybeReturnSchedContext`); both links are cleared and the
notification keeps its own. -/
private def bCheckReceiveReturns : Bool :=
  let st := bState [
    (bEp, .endpoint {}),
    (bWaiter.toObjId, .tcb { bTcb 2 with
      boundNotificationCode := bNtfn.val + 1,
      scBindingScCode := SeLe4n.Kernel.SchedContextBinding.scCode (.bound bScId) }),
    (bScObj, .schedContext { SeLe4n.Kernel.SchedContext.empty bScId with
      notificationCode := bNtfn.val + 1, boundThreadCode := bWaiter.val + 1 }),
    (bNtfn, .notification { bNtfnObject false with boundTCBCode := bWaiter.val + 1 })]
  let returned := SeLe4n.Kernel.receiveReturnSchedContext true st bWaiter
  match SeLe4n.Kernel.endpointReceiveDualOnCore bEp bWaiter none bootCoreId returned with
  | (st', .ok _) =>
    bHolds st && bHoldsNothing st' &&
      (st'.getTcb? bWaiter).any (fun t => decide (t.ipcState = .blockedOnReceive bEp)) &&
      (st'.getNotification? bNtfn).any (fun n => n.schedContextCode == bScId.val + 1)
  | (_, .error _) => false

/-- Lender 3 called server 4 and lent it context 61 through reply 63, so its
frame is on a live stack.  SchedContext_Bind binds context 67 to it, as seL4's
`decodeSchedContext_Bind` does: the lender binds, and the loan stays with the
server. -/
private def bCheckBindLender : Bool :=
  let lender : SeLe4n.ThreadId := ⟨3⟩
  let server : SeLe4n.ThreadId := ⟨4⟩
  let rid : SeLe4n.ReplyId := ⟨63⟩
  let lent := SeLe4n.SchedContextId.ofObjId ⟨61⟩
  let fresh := SeLe4n.SchedContextId.ofObjId ⟨67⟩
  let binding : SeLe4n.Kernel.SchedContextBinding := .donated lent lender
  let st := bState [
    (bEp, .endpoint {}),
    (lender.toObjId, .tcb (TCB.setIpcState { bTcb 3 with
      replyObjectCode := SeLe4n.ReplyId.optCode (some rid) } (.blockedOnReply bEp (some server)))),
    (server.toObjId, .tcb { bTcb 4 with
      scBindingScCode := binding.scCode, scBindingOwnerCode := binding.ownerCode }),
    (rid.toObjId, .reply { replyId := rid, next := some (.head lent),
                           callerCode := SeLe4n.ThreadId.optCode (some lender) }),
    bScAt 61 (some server) (some rid),
    (⟨67⟩, .schedContext { SeLe4n.Kernel.SchedContext.empty fresh with
      budgetRemaining := ⟨5⟩, isActive := true })]
  match fresh.toObjId.toValid?, lender.toValid? with
  | some vS, some vT =>
    match SeLe4n.Kernel.SchedContextOps.schedContextBind vS vT st with
    | .ok ((), st') =>
      bBinding st' lender == some fresh && bBoundTo st' 67 == some lender &&
        bBinding st' server == some lent && bHeadOf st' 61 == some rid
    | .error _ => false
  | _, _ => false

/-- Object 90 public, every thread and every other object secret: the
cross-label fixture for the label-gate rows. -/
private def bLabelObj : SeLe4n.ObjId := ⟨90⟩
private def bCrossCtx : LabelingContext :=
  { objectLabelOf := fun o => if o = bLabelObj then SecurityLabel.publicLabel else SecurityLabel.kernelTrusted
    threadLabelOf := fun _ => SecurityLabel.kernelTrusted
    endpointLabelOf := fun o => if o = bLabelObj then SecurityLabel.publicLabel else SecurityLabel.kernelTrusted }
/-- Every thread public, every object secret: a lower sender on a higher
endpoint, which the lattice alone permits. -/
private def bUpCtx : LabelingContext :=
  { objectLabelOf := fun _ => SecurityLabel.kernelTrusted, threadLabelOf := fun _ => SecurityLabel.publicLabel
    endpointLabelOf := fun _ => SecurityLabel.kernelTrusted }
/-- Every label equal: the admitted half. -/
private def bSameCtx : LabelingContext :=
  { objectLabelOf := fun _ => SecurityLabel.kernelTrusted, threadLabelOf := fun _ => SecurityLabel.kernelTrusted
    endpointLabelOf := fun _ => SecurityLabel.kernelTrusted }
private def bEpState : SystemState := bState [(bLabelObj, .endpoint {}), (bWaiter.toObjId, .tcb (bTcb 2))]
private def bIdleNtfn : Notification :=
  { state := .idle, hasPendingBadge := false, pendingWord := SeLe4n.Badge.zero }
private def bNtfnLabelState : SystemState :=
  bState [(bLabelObj, .notification bIdleNtfn), (bWaiter.toObjId, .tcb (bTcb 2))]
private def bRefused {α} : Except KernelError α → Bool
  | .error .flowDenied => true
  | _ => false
private def bCheckCrossSend : Bool :=
  bRefused (endpointSendDualChecked bUpCtx bLabelObj bWaiter (.frame SeLe4n.Badge.zero false true) bEpState) &&
  !bRefused (endpointSendDualChecked bSameCtx bLabelObj bWaiter (.frame SeLe4n.Badge.zero false true) bEpState)
private def bCheckCrossReceive : Bool :=
  bRefused (endpointReceiveDualChecked bCrossCtx bLabelObj bWaiter none bEpState) &&
  !bRefused (endpointReceiveDualChecked bSameCtx bLabelObj bWaiter none bEpState)
private def bCheckCrossWait : Bool :=
  bRefused (notificationWaitChecked bCrossCtx bLabelObj bWaiter bNtfnLabelState) &&
  !bRefused (notificationWaitChecked bSameCtx bLabelObj bWaiter bNtfnLabelState)
private def bCheckCrossNotificationBind : Bool :=
  bRefused (bindNotificationChecked bCrossCtx bLabelObj bWaiter bNtfnLabelState) &&
  !bRefused (bindNotificationChecked bSameCtx bLabelObj bWaiter bNtfnLabelState)
private def bCheckCrossContextBind : Bool :=
  !schedContextBindLabelAdmits bCrossCtx bLabelObj bWaiter &&
  schedContextBindLabelAdmits bSameCtx bLabelObj bWaiter &&
  !schedContextBindNotificationLabelAdmits bCrossCtx bLabelObj bNtfn &&
  schedContextBindNotificationLabelAdmits bSameCtx bLabelObj bNtfn

/-- Each behaviour row's scenario, by the row's name. -/
private def behaviourChecks : List (String × Bool) := [
  ("signal-lends-context", bCheckSignal),
  ("wait-consume-lends-context", bCheckWaitConsume),
  ("wait-block-returns-context", bCheckWaitReturn),
  ("call-lends-context", bCheckCallLend),
  ("destroy-unbinds-context", bCheckDestroyUnbinds),
  ("reply-pop-held-keeps-context", bCheckReplyPopHeld),
  ("unbind-donated-holder", bCheckUnbindDonated),
  ("suspend-keeps-binding", bCheckSuspendKeeps),
  ("receive-block-returns-context", bCheckReceiveReturns),
  ("bind-lender", bCheckBindLender),
  ("cross-label-send-refused", bCheckCrossSend),
  ("cross-label-receive-refused", bCheckCrossReceive),
  ("cross-label-wait-refused", bCheckCrossWait),
  ("cross-label-notification-bind-refused", bCheckCrossNotificationBind),
  ("cross-label-context-bind-refused", bCheckCrossContextBind) ]

/-- Every behaviour row has its scenario and every scenario its row, and each
scenario passes. -/
def runBehaviourRows : IO Unit := do
  expect "behaviour rows and scenarios name the same behaviours"
    (sel4BehaviourRows.map (·.name) == behaviourChecks.map (·.1))
  for (name, ok) in behaviourChecks do
    expect s!"behaviour {name}" ok

end Behaviour

end SeLe4n.Testing.Sel4ConformanceSuite

def main : IO Unit := do
  IO.println "=== Sel4ConformanceSuite (WS-SX SX8.1) ==="
  SeLe4n.Testing.Sel4ConformanceSuite.runLabelRows
  SeLe4n.Testing.Sel4ConformanceSuite.runSyscallRows
  SeLe4n.Testing.Sel4ConformanceSuite.runErrors
  SeLe4n.Testing.Sel4ConformanceSuite.runMessageInfo
  SeLe4n.Testing.Sel4ConformanceSuite.runWordFirst
  SeLe4n.Testing.Sel4ConformanceSuite.runBehaviourRows
  IO.println "=== Sel4ConformanceSuite PASSED ==="
