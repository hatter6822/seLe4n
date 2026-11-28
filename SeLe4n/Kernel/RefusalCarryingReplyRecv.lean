-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingEndpoint
import SeLe4n.Kernel.RefusalCarryingReplyRecvTransfer
import SeLe4n.Kernel.IPC.CrossCore.ReplyLegFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyPopFrame
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyHeldInPlace
import SeLe4n.Kernel.IPC.CrossCore.ReplyUnheldPopFrame
import SeLe4n.Kernel.IPC.CrossCore.FaultAnswerInPlace
import SeLe4n.Kernel.IPC.CrossCore.LongReplyRecvFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCapsDelivered
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeFrame
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvLegGuards
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvBlockComposed
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvTakeComposed
import SeLe4n.Kernel.IPC.CrossCore.ReplyRecvCallTakeComposed

/-!
# Reply-receive, refusing in the state it was refused in

WS-ZA ZA4.7.  The checked reply-receive arm on a message read in registers,
proven equal to `RefusalCarrying.ofKernel` of the specification's dispatch
(`dispatchReplyRecvCheckedR_eq`).  The reply capability at the reply register
(x6, WS-SX SX7.3) is resolved in continuation form, so no gate, slot reference or result cell is built for it;
a reply-receive whose receive then blocks on an endpoint no sender waits on
writes in place on every reply arm (`replyRecvBlockArmCode`,
`replyRecvOnCore_arm_deliveredRegs`); any other takes the specification's
path.  A receive leg refused after the reply was answered reports the state
the refusing step stopped in, the completed reply kept
(`replyRecvAnsweringReport`), as seL4's `SysReplyRecv` keeps it when
`handleRecv` refuses.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- `resolveReplyRecvReply` on the reply register's address alone, with the
gate the caller's own CSpace gives (`resolveReplyRecvReplyR_eq`). -/
def resolveReplyRecvReplyR (st : SystemState) (tid : SeLe4n.ThreadId) (replyAddr : SeLe4n.CPtr) :
    Except KernelError (Option (SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge × Bool)) :=
  let gate : SyscallGate :=
    { callerId := tid
      cspaceRootCap := callerCspaceRoot st tid
      capAddr := replyAddr
      requiredRight := .write }
  match lookupReplyCap gate st with
  | .error lf => .error (.failedLookup false lf)
  | .ok (rcap, rid) =>
      match replyAnsweredCaller? st rid with
      | some prevCaller => .ok (some (rid, prevCaller, rcap.badge, rcap.rights.mem .grant))
      | none => .ok none

/-- **Whether a reply-receive's reply half replies to no one** (WS-SX SX7.2):
its reply capability resolves (`resolveReplyRecvReplyR`) to a reply object
with no caller blocked on it, so seL4-MCS's `doReplyTransfer` returns and the
receive half runs alone. -/
def replyRecvRepliesToNoOne (st : SystemState) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr) : Bool :=
  match resolveReplyRecvReplyR st tid replyAddr with
  | .ok none => true
  | _ => false

/-- **Whether a reply-receive's reply is refused** (WS-SX SX33): its reply
capability resolves to a caller the reply does not answer
(`replyRecvReplyAnswers`: the flow denied, or the caller not waiting for the
reply), so the receive half runs alone. -/
def replyRecvReplyRefused (ctx : LabelingContext) (st : SystemState) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr) : Bool :=
  match resolveReplyRecvReplyR st tid replyAddr with
  | .ok (some (_, prevCaller, _, _)) => !replyRecvReplyAnswers ctx st tid prevCaller
  | _ => false

/-- **The reply a reply-receive answers** (WS-SX SX33): the resolved reply, where
its caller is one the reply answers (`replyRecvReplyAnswers`), and nothing where
the reply is refused or has no caller, so a refused reply takes the receive half
the arms already run for a reply with no caller.  It hands back the resolution
itself, never a rebuilt one. -/
@[inline] def replyRecvAnsweredReply? (ctx : LabelingContext) (st : SystemState)
    (tid : SeLe4n.ThreadId)
    (r : Option (SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge × Bool)) :
    Option (SeLe4n.ReplyId × SeLe4n.ThreadId × Option SeLe4n.Badge × Bool) :=
  match r with
  | some (_, c, _, _) => if replyRecvReplyAnswers ctx st tid c then r else none
  | none => none

/-- The caller a reply object's reply answers: its recorded caller, where `answers`
admits it, and nothing otherwise.  It hands back the recorded caller itself. -/
@[inline] def replyRecvAnsweredCaller? (st : SystemState) (rid : SeLe4n.ReplyId)
    (answers : SeLe4n.ThreadId → Bool) : Option SeLe4n.ThreadId :=
  let c? := replyAnsweredCaller? st rid
  match c? with
  | some c => if answers c then c? else none
  | none => none

/-- **The state an answering reply-receive's refusal reports** (WS-SX SX34,
D60 option (b)): where the receive leg's flow gate passes and the reply answers
a caller on a receive that completes no bound notification, the state the
transition's refusing step stopped in (`replyRecvTransferStoppedState`): the
completed reply is kept, as seL4's `SysReplyRecv` keeps it when `handleRecv`
refuses.  The state it was handed otherwise, since those refusals precede the
first write. -/
def replyRecvAnsweringReport (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (replyAddr : SeLe4n.CPtr)
    (executingCore : Concurrency.CoreId) (cap : Capability) (st : SystemState) : SystemState :=
  match cap.target with
  | .object epId =>
    if endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
      match resolveReplyRecvReplyR st tid replyAddr with
      | .ok (some (rid, prevCaller, replyBadge, replyGrant)) =>
        if receiveCompletesSignal ctx st tid then st
        else
          replyRecvTransferStoppedState epId tid rid prevCaller mi.label
            { registers := extractMessageRegisters regs mi, badge := replyBadge } replyGrant
            executingCore st
      | _ => st
    else st
  | _ => st

/-- **The state a reply-receive arm's refusal reports**: the receive arm's
(`receiveArmReport`) when the reply half is skipped, by an extra capability
that does not look up (WS-SX SX6.1), a reply with no caller to answer (WS-SX
SX7.2) or a refused reply (WS-SX SX33), since the receive half then runs
alone; the answering report (`replyRecvAnsweringReport`) otherwise. -/
def replyRecvArmReport (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (replyAddr : SeLe4n.CPtr)
    (executingCore : Concurrency.CoreId) (cap : Capability) (st : SystemState) : SystemState :=
  match callerExtraCapsFault? st tid mi.extraCaps with
  | some _ => receiveArmReport ctx tid true replyAddr executingCore cap st
  | none =>
    if replyRecvRepliesToNoOne st tid replyAddr || replyRecvReplyRefused ctx st tid replyAddr then
      receiveArmReport ctx tid true replyAddr executingCore cap st
    else replyRecvAnsweringReport ctx tid mi regs replyAddr executingCore cap st

/-- **The flow a refused answering reply-receive carries, its receive
capability resolved on entry** (WS-SX SX36): where no extra capability fails
and the reply answers its caller `c` on the entry state, the reply leg's edge
where the reply was delivered (`replyRecvRefusalTaint`) and the receive leg's
where the receive copied a sender's message (`replyRecvReceiveLegRefusalTaint`,
on the endpoint the capability names, read on the entry state as the commit's
plan reads it); the state as it is otherwise, since a refusal that skips the
reply delivered nothing to a caller.  The rule the after-reply route's refusal
follows (`replyRecvAfterReplyRefusalTaint`), on the entry state. -/
def replyRecvEntryRefusalTaint (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (extraCaps : Nat) (replyAddr : SeLe4n.CPtr) (cap : Capability) (st s : SystemState) :
    SystemState :=
  match callerExtraCapsFault? st tid extraCaps with
  | some _ => s
  | none =>
    match resolveReplyRecvReplyR st tid replyAddr with
    | .ok (some (_, c, _, _)) =>
      if replyRecvReplyAnswers ctx st tid c then
        replyRecvRefusalTaint st tid c
          (match cap.target with
            | .object epId => replyRecvReceiveLegRefusalTaint st tid epId s
            | _ => s)
      else s
    | _ => s

/-- The checked reply-receive arm (`dispatchWithCapChecked`'s `.replyRecv`
case) through the specification's path
(`endpointReplyRecvCheckedArmGeneralR_eq`): a refusal before the reply is
answered reports the state it was handed, and a refusal of the receive leg
after it reports the state the refusing step stopped in
(`replyRecvTransferOnCoreR`, `replyRecvAnsweringReport`). -/
def endpointReplyRecvCheckedArmGeneralR (ctx : LabelingContext) (mi : MessageInfo)
    (regs : Array SeLe4n.RegValue) (replyAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
        callerExtraCapsFailK st tid mi.extraCaps
          (fun _ => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st)
          (fun _ =>
        match resolveReplyRecvReplyR st tid replyAddr with
        | .error e => .error (e, st)
        | .ok r =>
          match replyRecvAnsweredReply? ctx st tid r with
          | none => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st
          | some (rid, prevCaller, replyBadge, replyGrant) =>
            let msg : IpcMessage :=
              { registers := extractMessageRegisters regs mi, badge := replyBadge }
              if receiveCompletesSignal ctx st tid then
                match replyRecvCompletesSignalArm ctx tid prevCaller mi.label msg replyGrant
                    executingCore st with
                | .ok r => .ok r
                | .error e => .error (e, st)
              else
              match replyRecvTransferOnCoreR epId tid rid prevCaller mi.label msg
                  replyGrant executingCore st with
              | .ok (summary, st') =>
                  .ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo)
              | .error es => .error es)
    | _ => .error (.invalidCapability 0, st)

/-- The reply capability a reply-receive names, checked as
`resolveReplyRecvReplyR` checks it once its slot is found: present, not the idle
thread's, carrying the write right, naming a reply object.  A reply object with
an outstanding caller goes to `onOk` with the caller and the capability's
badge, one with none to `onNone` (WS-SX SX7.2), a refusal to `onErr`, so no
`Except`, `Option` or tuple cell is built.  `onOk` is also handed the capability
itself, as the slot holds it, so an arm that answers the caller through the
`.reply` arm's in-place forms runs them on it. -/
@[inline] def replyRecvCapK {α : Type} (st : SystemState) (cap? : Option Capability)
    (answers : SeLe4n.ThreadId → Bool) (onErr : KernelError → α) (onNone : Unit → α)
    (onOk : Capability → SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α) :
    α :=
  match cap? with
  | none => onErr (.failedLookup false (.missingCapability 0))
  | some cap =>
      if SeLe4n.Kernel.capTargetsReservedKernelObject cap then
        onErr (.failedLookup false (.missingCapability 0))
      else if !cap.hasRight .write then onErr (.failedLookup false (.missingCapability 0))
      else
        match cap.target with
        | .replyCap rid =>
            match replyRecvAnsweredCaller? st rid answers with
            | some c => onOk cap rid c cap.badge (cap.rights.mem .grant)
            | none => onNone ()
        | _ => onErr (.failedLookup false (.missingCapability 0))

/-- `resolveReplyRecvReplyR` in continuation form (`resolveReplyRecvK_eq_of`), on
the reply register's address: the slot is resolved through `lookupSlotFromK`,
as the operand is.  WS-ZA ZA4.7. -/
@[inline] def resolveReplyRecvK {α : Type} (st : SystemState) (tid : SeLe4n.ThreadId)
    (replyAddr : SeLe4n.CPtr) (answers : SeLe4n.ThreadId → Bool) (onErr : KernelError → α)
    (onNone : Unit → α)
    (onOk : Capability → SeLe4n.ReplyId → SeLe4n.ThreadId → Option SeLe4n.Badge → Bool → α) :
    α :=
  match callerCspaceRoot st tid with
  | none => onErr (.failedLookup false .invalidRoot)
  | some root =>
    lookupSlotFromK root replyAddr st
      (fun t a b c => onErr (.failedLookup false (LookupFault.ofWords t a b c)))
      (fun cnode slot =>
        replyRecvCapK st (SystemState.lookupSlotCap st { cnode := cnode, slot := slot })
          answers onErr onNone onOk)

/-- **The caller a reply-receive's reply answers, as its code**
(`SeLe4n.ThreadId.optCode`), on the state it is handed, in continuation form:
the caller the reply capability at `replyWord` names, where no extra
capability of the reply fails and the reply answers it
(`replyRecvReplyAnswers`), and `0` otherwise.  Out of line, with the state
borrowed, so nothing is built and the state is not held. -/
@[noinline] def replyRecvAnsweringCallerCode (ctx : @& LabelingContext) (tid : SeLe4n.ThreadId)
    (replyWord : UInt64) (extraCaps : Nat) (st : @& SystemState) : Nat :=
  callerExtraCapsFailK st tid extraCaps (fun _ => 0) fun _ =>
    resolveReplyRecvK st tid (SeLe4n.CPtr.ofWord replyWord)
      (fun c => replyRecvReplyAnswers ctx st tid c) (fun _ => 0) (fun _ => 0)
      (fun _ _ c _ _ => c.val + 1)

/-- WS-ZA ZA4.7: a reply-receive answers a caller blocked on this server and
then blocks, every write in its slot: the caller's reply leg may write in place
(`replyWakesInPlace`), no sender waits on the endpoint, the server may block
there in place and its reply object, consumed by the reply leg, is free, not
stashed and in its slot for the stasher record (`replyRecordsInPlace`).  Each
check reads the pre-state; `replyRecvBlocksFast_spec` carries
them to the rendezvous arm's guard (`replyRecvBlockArmCode_spec`). -/
@[inline] def replyRecvBlocksFast (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  tid.val != c.val &&
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ (some server) => server.val == tid.val
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1 &&
       replyWakesInPlace st c ct rid
   | none => false) &&
  (match st.getEndpoint? epId with
   | some ep =>
       ep.sendQ.head.isNone &&
       (match st.getTcb? tid with
        | some rt => receiveBlockAdmits rt && enqueuesInPlaceCode st epId tid ep.recvTailCode
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some rp => rp.consumedIsFree && !st.replyStashedAt rid rp &&
       replyRecordsInPlace st (rid.val + 1)
   | none => false)

/-- **The reply-receive's reply leg transfers no capability, decided in place**:
the reply capability lacks the grant right, or the replier `tid`'s frame names
no extra capability, or the answered caller `c` has no IPC buffer the kernel may
write or names no receive slot there (`replyTransferInertW`); a caller with no
TCB takes none.  Every in-place form of the arm answering an unfaulted caller is
taken only then, because none of them runs seL4's `doReplyTransfer` capability
transfer (`replyRecvReplyInertW_spec`, then `replyRecvReplyTransfer_of_inert`).
A word-only reply (no extra capability) passes on the count alone, whatever
receive path the caller configured. -/
@[inline] def replyRecvReplyInertW (st : SystemState) (tid c : SeLe4n.ThreadId) (grant : Bool) :
    Bool :=
  match st.getTcb? c with
  | some ct => replyTransferInertW st tid ct grant
  | none => true

/-- The checked reply-receive once its reply capability is resolved, through the
specification's path (`replyRecvTransferOnCore`, which answers a faulted caller
with its fault reply), a refusal reporting the state the refusing step stopped
in (`replyRecvTransferOnCoreR`).  Out of line, so the reply's message record is
built only here. -/
@[noinline] def replyRecvRendezvousR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match replyRecvTransferOnCoreR epId tid rid c label
        { registers := Architecture.regMessageBody layout rf len, badge := badge }
        grant executingCore st with
    | .ok (summary, st') =>
        .ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo)
    | .error es => .error es

/-- WS-ZA ZA6.34: **a reply-receive answering a caller recording no server that
may block in place**, read on the pre-state: the caller `c` blocked on reply
object `rid` with no server recorded (its server finalised, seL4-MCS's
`finaliseCap`), the unheld pop's checks (`replyUnheldPopsInPlace`), no sender
waiting on the endpoint, the replier a thread that may block there in place and
the reply object not stashed and in its slot for the stasher record.  Every
read is a code. -/
@[inline] def replyRecvUnheldBlocks (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  tid.val != c.val &&
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ none => true
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1
   | none => false) &&
  replyUnheldPopsInPlace st c rid &&
  (match st.getEndpoint? epId with
   | some ep =>
       ep.sendQ.head.isNone &&
       (match st.getTcb? tid with
        | some rt => receiveBlockAdmits rt && enqueuesInPlaceCode st epId tid ep.recvTailCode
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some rp => !st.replyStashedAt rid rp && replyRecordsInPlace st (rid.val + 1)
   | none => false)

/-- WS-SX SX8.3: **a reply-receive answering a caller recording no server whose
reply object is linked to nothing, that may block in place**, read on the
pre-state: the caller `c` blocked on reply object `rid` with no server recorded,
the reply object neither heading a stack nor on one (`replyUnlinkedInPlace`: the
state SchedContext_Unbind of a lent context leaves once the server is
finalised), no sender waiting on the endpoint, the replier a thread that may
block there in place and the reply object not stashed and in its slot for the
stasher record.  Every read is a code. -/
@[inline] def replyRecvUnlinkedBlocks (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  tid.val != c.val &&
  (match st.getTcb? c with
   | some ct =>
       (match ct.ipcState with
        | .blockedOnReply _ none => true
        | _ => false) &&
       ct.replyObjectCode == rid.val + 1
   | none => false) &&
  replyUnlinkedInPlace st c rid &&
  (match st.getEndpoint? epId with
   | some ep =>
       ep.sendQ.head.isNone &&
       (match st.getTcb? tid with
        | some rt => receiveBlockAdmits rt && enqueuesInPlaceCode st epId tid ep.recvTailCode
        | none => false)
   | none => false) &&
  (match st.getReply? rid with
   | some rp => !st.replyStashedAt rid rp && replyRecordsInPlace st (rid.val + 1)
   | none => false)

/-- **The reply arm whose blocking reply-receive writes in place**, as a code
read on the pre-state: 1 to 5 for the arm whose checks pass first (the
rendezvous, `replyRecvBlocksFast`; the donated, `replyRecvDonatedBlocks`; the
held, `replyRecvHeldBlocks`; the unheld, `replyRecvUnheldBlocks`; the unlinked,
`replyRecvUnlinkedBlocks`), 0 when none does.  A code, so choosing the arm
allocates nothing (`ReplyRecvArm.ofCode`, `replyRecvBlockArmCode_spec`); out of
line, so the five guards are compiled once for every answer that reads them. -/
@[noinline] def replyRecvBlockArmCode (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Nat :=
  if replyRecvBlocksFast st epId tid c rid then 1
  else if replyRecvDonatedBlocks st epId tid c rid then 2
  else if replyRecvHeldBlocks st epId tid c rid then 3
  else if replyRecvUnheldBlocks st epId tid c rid then 4
  else if replyRecvUnlinkedBlocks st epId tid c rid then 5
  else 0

/-- The arm a nonzero `replyRecvBlockArmCode` names. -/
@[inline] def ReplyRecvArm.ofCode : Nat → ReplyRecvArm
  | 1 => .rendezvous
  | 2 => .donated
  | 3 => .held
  | 4 => .unheld
  | 6 => .rendezvous
  | 7 => .unheld
  | _ => .unlinked

/-- Whether the Call take a nonzero `replyRecvCallTakeArmCode` names lends the
taken caller's context: as its arm does (`ReplyRecvArm.callLends`) on codes 1
to 5, not on the own-context codes 6 to 8, whose server keeps its own. -/
@[inline] def replyRecvCallLendsOfCode : Nat → Bool
  | 3 => false
  | 6 => false
  | 7 => false
  | 8 => false
  | _ => true

/-- **The checked reply-receive whose reply leg transfers capabilities**, its
caller unfaulted: from a replier whose frame routes as a reply-receive, under
the grant right, a reply of at most four words, on every reply arm whose
receive blocks in place (`replyRecvBlockArmCode`): the arm's reply leg and pop,
the transfer in place (seL4's `doReplyTransfer`; every CNode it writes keeps
its kind), then the receive leg (seL4's `receiveIPC`) and the caller's frame
(`performReplyRecvArmCapsDelivered`).  The replier and the caller enter as the
words the transfer reads of them, read before any write.  Any other takes the
specification's path (`replyRecvCapsArmR_eq`). -/
@[inline] def replyRecvCapsArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match st.getTcb? tid with
    | some stcb =>
        match Architecture.RegisterDecode.registerRoutedSyscallOf SyscallId.replyRecv.toNat
            SeLe4n.arm64DefaultLayout stcb.registerContext with
        | .replyRecv _ _ =>
            match st.getTcb? c with
            | some ct =>
                if grant && decide (Architecture.regMessageLength layout len ≤ 4) &&
                    replyRecvBlockArmCode st epId tid c rid != 0 then
                  .ok ((), performReplyRecvArmCapsDelivered
                    (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
                    ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
                    (receiveQueueTailCode st epId) layout rf len badge executingCore
                    stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0]
                    (routedExtraCaps stcb.registerContext) ct.spaceCells[2] ct.ipcBuffer
                    ct.spaceCells[0])
                else replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                  executingCore st
            | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                executingCore st
        | _ => replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st
    | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st

/-- **The reply arm whose reply-receive takes a waiting sender in place**, as a
code read on the pre-state: 1 to 5 for the arm whose reply-leg guard passes
first (`ReplyRecvArm.legGuard`: the rendezvous, the donated, the held, the
unheld, the unlinked), the caller's reply object the one named and present and
the endpoint's send queue offering a sender the take writes in place
(`replyRecvSenderTakes`); 0 otherwise.  A code, so choosing the arm allocates
nothing (`ReplyRecvArm.ofCode`, `replyRecvTakeArmCode_spec`); out of line, so the
guards are compiled once for every answer that reads them. -/
@[noinline] def replyRecvTakeArmCode (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Nat :=
  match st.getTcb? c with
  | some ct =>
      if ct.replyObjectCode == rid.val + 1 && (st.getReply? rid).isSome &&
          replyRecvSenderTakes st epId tid c then
        if ReplyRecvArm.rendezvous.legGuard st tid c rid ct then 1
        else if ReplyRecvArm.donated.legGuard st tid c rid ct then 2
        else if ReplyRecvArm.held.legGuard st tid c rid ct then 3
        else if ReplyRecvArm.unheld.legGuard st tid c rid ct then 4
        else if ReplyRecvArm.unlinked.legGuard st tid c rid ct then 5
        else 0
      else 0
  | none => 0

/-- **The checked reply-receive whose receive leg takes a waiting sender, over
every reply arm** (seL4-MCS's `handleReplyRecv`: `doReplyTransfer`, the
reply arm's `reply_pop`, then `receiveIPC` meeting a sender already queued --
the ordinary server loop under load): when a reply of at most four words takes
the sender in place on some reply arm (`replyRecvTakeArmCode`) and the sender's
saved frame routes as a capability-free send, the arm's reply leg and pop, the
reply leg's transfer, the take, the arm's deschedule and the frames, the
sender's six words read from its saved registers before any write.  A reply
leg transferring no capability (`replyRecvReplyInertW`) runs
`performReplyRecvArmTakeDelivered`; a granting one whose frame routes as a
reply-receive, its transfer's stores in place, runs
`performReplyRecvArmTakeCapsDelivered`.  A caller queued by a `Call` is taken
ahead of this arm (`replyRecvArmCallTakeR`); otherwise the capability arm
(`replyRecvCapsArmR`).  Any other takes the specification's path
(`replyRecvArmTakeR_eq`). -/
@[inline] def replyRecvArmTakeR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if decide (Architecture.regMessageLength layout len ≤ 4) &&
        replyRecvTakeArmCode st epId tid c rid != 0 then
      match st.getEndpoint? epId with
      | some ep =>
        match ep.sendQ.head with
        | some s =>
          match st.getTcb? s with
          | some sTcb =>
            match Architecture.RegisterDecode.registerRoutedSyscallOf
                (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
                SeLe4n.arm64DefaultLayout sTcb.registerContext with
            | .send _ mi =>
              if replyRecvReplyInertW st tid c grant then
                let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                  sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
                .ok ((), performReplyRecvArmTakeDelivered
                  (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                  ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
                  sTcb.queueNextCode executingCore layout rf len badge f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
              else
                match st.getTcb? tid with
                | some stcb =>
                  match Architecture.RegisterDecode.registerRoutedSyscallOf SyscallId.replyRecv.toNat
                      SeLe4n.arm64DefaultLayout stcb.registerContext with
                  | .replyRecv _ _ =>
                    match st.getTcb? c with
                    | some ct =>
                      if grant then
                        let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                          sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
                          sTcb.ipcBadged
                        .ok ((), performReplyRecvArmTakeCapsDelivered
                          (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                          ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid
                          epId s sTcb.queueNextCode executingCore layout rf len badge
                          f.x0 f.x1 f.x2 f.x3 f.x4 f.x5 stcb.spaceCells[2] stcb.ipcBuffer
                          stcb.spaceCells[0] (routedExtraCaps stcb.registerContext) ct.spaceCells[2]
                          ct.ipcBuffer ct.spaceCells[0])
                      else replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                        executingCore st
                    | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                        executingCore st
                  | _ => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                      executingCore st
                | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                    executingCore st
            | _ => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                executingCore st
          | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
              executingCore st
        | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
            executingCore st
      | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
          executingCore st
    else replyRecvCapsArmR epId tid c rid badge grant layout rf len label executingCore st

/-- **One arm's Call-take code**: `k` where the arm's reply-leg guard
(`ReplyRecvArm.legGuard`) and lending Call-take guard (`ReplyRecvArm.callGuard`)
pass, `kOwn` where its reply-leg guard and own-context guard
(`ReplyRecvArm.callOwnGuard`, a server bound to its own context taking the
Call lending nothing) pass, 0 otherwise.  Out of line and over the arm, so each
arm's guards are compiled once (`replyRecvArmCallCode_spec`). -/
@[noinline] def replyRecvArmCallCode (arm : ReplyRecvArm) (st : SystemState)
    (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (ct : TCB)
    (s : SeLe4n.ThreadId) (sTcb : TCB) (k kOwn : Nat) : Nat :=
  if arm.legGuard st tid c rid ct then
    if arm.callGuard st epId tid s sTcb rid then k
    else if arm.callOwnGuard st epId tid s sTcb then kOwn
    else 0
  else 0

/-- **The reply arm whose reply-receive takes a queued caller in place**, as a
code read on the pre-state: 1 to 5 for the first arm (the rendezvous, the
donated, the held, the unheld, the unlinked) whose reply-leg guard
(`ReplyRecvArm.legGuard`) and Call-take guard (`ReplyRecvArm.callGuard`) pass,
the caller's reply object the one named and present and the head of the
endpoint's send queue a caller blocked by a routed capability-free call
(`replyRecvCallerQueued`); 0 otherwise.  A code, so choosing the arm allocates
nothing (`replyRecvCallTakeArmCode_spec`); out of line, so the guards are
compiled once for every answer and length that reads them. -/
@[noinline] def replyRecvCallTakeArmCode (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Nat :=
  match st.getTcb? c with
  | some ct =>
      if ct.replyObjectCode == rid.val + 1 && (st.getReply? rid).isSome &&
          replyRecvCallerQueued st epId c then
        match st.getEndpoint? epId with
        | some ep =>
          match ep.sendQ.head with
          | some s =>
            match st.getTcb? s with
            | some sTcb =>
              if replyRecvArmCallCode .rendezvous st epId tid c rid ct s sTcb 1 6 != 0 then
                replyRecvArmCallCode .rendezvous st epId tid c rid ct s sTcb 1 6
              else if replyRecvArmCallCode .donated st epId tid c rid ct s sTcb 2 0 != 0 then
                replyRecvArmCallCode .donated st epId tid c rid ct s sTcb 2 0
              else if replyRecvArmCallCode .held st epId tid c rid ct s sTcb 3 0 != 0 then
                replyRecvArmCallCode .held st epId tid c rid ct s sTcb 3 0
              else if replyRecvArmCallCode .unheld st epId tid c rid ct s sTcb 4 7 != 0 then
                replyRecvArmCallCode .unheld st epId tid c rid ct s sTcb 4 7
              else if replyRecvArmCallCode .unlinked st epId tid c rid ct s sTcb 5 8 != 0 then
                replyRecvArmCallCode .unlinked st epId tid c rid ct s sTcb 5 8
              else 0
            | none => 0
          | none => 0
        | none => 0
      else 0
  | none => 0

/-- Whether the replier's saved frame routes as a reply-receive, the frame a
granting reply leg reads its capabilities from. -/
@[inline] def replyRecvFrameRoutesReplyRecv (st : SystemState) (tid : SeLe4n.ThreadId) : Bool :=
  match st.getTcb? tid with
  | some stcb =>
    match Architecture.RegisterDecode.registerRoutedSyscallOf SyscallId.replyRecv.toNat
        SeLe4n.arm64DefaultLayout stcb.registerContext with
    | .replyRecv _ _ => true
    | _ => false
  | none => false

/-- Whether the reply leg of a Call take transfers no capability
(`replyRecvReplyInertW`), out of line, so the admission tests and the answers
that read it share one copy. -/
@[noinline] def replyRecvCallTakeReplyInert (st : SystemState) (tid c : SeLe4n.ThreadId)
    (grant : Bool) : Bool :=
  replyRecvReplyInertW st tid c grant

/-- Whether a reply-receive with a reply of at most four words takes the queued
caller in place on some reply arm (`replyRecvCallTakeArmCode`): its reply leg
transferring no capability (`replyRecvReplyInertW`), or granting with the
replier's frame routing as a reply-receive.  Out of line and a `Bool`, so the
checks are one call and allocate nothing. -/
@[noinline] def replyRecvShortCallTakeAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) : Bool :=
  decide (Architecture.regMessageLength layout len ≤ 4) &&
    replyRecvCallTakeArmCode st epId tid c rid != 0 &&
    (replyRecvCallTakeReplyInert st tid c grant || grant && replyRecvFrameRoutesReplyRecv st tid)

/-- **The reply-receive taking a queued caller, its reply of at most four
words**: the arm's reply leg and pop, the reply leg's transfer, the take, the
arm's lend and the frames, every context, core and word it takes read on the
pre-state.  A reply leg transferring no capability runs
`performReplyRecvArmCallTakeDelivered`; a granting one
`performReplyRecvArmCallTakeCapsDelivered`.  Out of line, it returns the state,
so nothing is built around it; read only where `replyRecvShortCallTakeAdmits`
passes, and the state unchanged on a shape it does not admit. The reply enters as the four inline words the arm reads of the replier's
message registers on the pre-state (`Architecture.regLayoutWord`), not as its
register file, so nothing outside the server's TCB holds the register file
when the server's frame is written. -/
@[noinline] def replyRecvCallTakeAnswer (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (m0 m1 m2 m3 : UInt64) (len : Nat)
    (executingCore : Concurrency.CoreId) (st : SystemState) : SystemState :=
  match st.getEndpoint? epId with
  | some ep =>
    match ep.sendQ.head with
    | some s =>
      match st.getTcb? s with
      | some sTcb =>
        match Architecture.RegisterDecode.registerRoutedSyscallOf
            (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
            SeLe4n.arm64DefaultLayout sTcb.registerContext with
        | .call _ mi =>
          if replyRecvCallTakeReplyInert st tid c grant then
            performReplyRecvArmCallTakeDelivered
              (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
              (replyRecvCallLendsOfCode (replyRecvCallTakeArmCode st epId tid c rid))
              ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
              sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
              (determineTargetCore st tid) executingCore layout len badge m0 m1 m2 m3
              sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
              sTcb.ipcBadged
          else
            match st.getTcb? tid with
            | some stcb =>
              match st.getTcb? c with
              | some ct =>
                performReplyRecvArmCallTakeCapsDelivered
                  (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
                  (replyRecvCallLendsOfCode (replyRecvCallTakeArmCode st epId tid c rid))
                  ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid
                  epId s sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩
                  (determineTargetCore st s) (determineTargetCore st tid) executingCore
                  layout len badge m0 m1 m2 m3 sTcb.registerContext mi.length
                  (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
                  stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0]
                  (routedExtraCaps stcb.registerContext) ct.spaceCells[2] ct.ipcBuffer
                  ct.spaceCells[0]
              | none => st
            | none => st
        | _ => st
      | none => st
    | none => st
  | none => st

/-- **The checked reply-receive whose receive leg takes a queued caller, over
every reply arm** (seL4-MCS's `handleReplyRecv`: `doReplyTransfer`, the reply
arm's `reply_pop`, then `receiveIPC` taking a caller queued by a `Call`, and
`reply_push (canDonate)` lending that caller's context to a server holding
none): when a reply of at most four words takes the caller in place on some
reply arm (`replyRecvShortCallTakeAdmits`), the take out of line
(`replyRecvCallTakeAnswer`).  Otherwise the take arm (`replyRecvArmTakeR`); the
specification's path (`replyRecvArmCallTakeR_eq`). -/
@[inline] def replyRecvArmCallTakeR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvShortCallTakeAdmits st epId tid c rid grant layout len then
      .ok ((), replyRecvCallTakeAnswer epId tid c rid badge grant layout
        (Architecture.regLayoutWord layout rf 0)
        (Architecture.regLayoutWord layout rf 1) (Architecture.regLayoutWord layout rf 2)
        (Architecture.regLayoutWord layout rf 3) len executingCore st)
    else replyRecvArmTakeR epId tid c rid badge grant layout rf len label executingCore st

/-- **The checked reply-receive answering a faulted caller**: in place on every
shape whose writes stay in their slots, the caller's fault words read off the
pre-state and the fault answered from them and the reply's registers past MR0,
the answer the `.reply` arm applies (`performFaultAnswer`): on every reply arm
whose receive blocks in place (`replyRecvBlockArmCode`,
`performReplyRecvArmFaultAnswer`), and on every reply arm whose receive takes a
waiting sender (`replyRecvTakeArmCode`, `performReplyRecvArmFaultTakeDelivered`); the specification's otherwise
(`replyRecvFaultArmR_eq`).  The caller's words are read before the writes and
its TCB is not held across them. -/
@[inline] def replyRecvFaultArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match st.getTcb? c with
    | some ct =>
        if replyRecvBlockArmCode st epId tid c rid != 0 then
          .ok ((), performReplyRecvArmFaultAnswer
            (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
            ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
            (receiveQueueTailCode st epId) executingCore ct.faultKind label ct.faultIp ct.faultSp
            ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
            ct.faultX6 ct.faultX7 layout rf len)
        else if replyRecvTakeArmCode st epId tid c rid != 0 then
          match st.getEndpoint? epId with
          | some ep =>
            match ep.sendQ.head with
            | some s =>
              match st.getTcb? s with
              | some sTcb =>
                match Architecture.RegisterDecode.registerRoutedSyscallOf
                    (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
                    SeLe4n.arm64DefaultLayout sTcb.registerContext with
                | .send _ mi =>
                  let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                    sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
                    sTcb.ipcBadged
                  .ok ((), performReplyRecvArmFaultTakeDelivered
                    (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                    ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
                    sTcb.queueNextCode executingCore ct.faultKind label ct.faultIp ct.faultSp
                    ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
                    ct.faultX6 ct.faultX7 layout rf len f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
                | _ => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                    executingCore st
              | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                  executingCore st
            | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
                executingCore st
          | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label
              executingCore st
        else replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st
    | none => replyRecvRendezvousR epId tid c rid badge grant layout rf len label executingCore st

/-- **The fault answered and a queued caller taken, its reply of at most four
words**: the arm's reply leg with no message and pop, the take, the arm's lend,
the fault answered from the caller's words and the reply's registers past MR0
(`performReplyRecvArmCallFaultTakeDelivered`), every word read on the
pre-state.  Out of line, it returns the state, so nothing is built around it;
read only where `replyRecvCallTakeArmCode` admits and the reply is at most four
words, and the state unchanged on a shape it does not. The reply enters as the four inline words the arm reads of the replier's
message registers on the pre-state (`Architecture.regLayoutWord`), not as its
register file, so nothing outside the server's TCB holds the register file
when the server's frame is written. -/
@[noinline] def replyRecvCallFaultTakeAnswer (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (layout : SeLe4n.SyscallRegisterLayout) (m0 m1 m2 m3 : UInt64)
    (len label : Nat) (executingCore : Concurrency.CoreId) (st : SystemState) : SystemState :=
  match st.getTcb? c with
  | some ct =>
    match st.getEndpoint? epId with
    | some ep =>
      match ep.sendQ.head with
      | some s =>
        match st.getTcb? s with
        | some sTcb =>
          match Architecture.RegisterDecode.registerRoutedSyscallOf
              (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
              SeLe4n.arm64DefaultLayout sTcb.registerContext with
          | .call _ mi =>
            performReplyRecvArmCallFaultTakeDelivered
              (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
              (replyRecvCallLendsOfCode (replyRecvCallTakeArmCode st epId tid c rid))
              ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
              sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
              (determineTargetCore st tid) executingCore ct.faultKind label ct.faultIp
              ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
              ct.faultX5 ct.faultX6 ct.faultX7 layout len m0 m1 m2 m3 sTcb.registerContext
              mi.length
              (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
          | _ => st
        | none => st
      | none => st
    | none => st
  | none => st

/-- **The checked reply-receive answering a faulted caller and taking a queued
caller, over every reply arm**: when the receive leg takes a caller queued by a
routed capability-free call in place on some reply arm
(`replyRecvCallTakeArmCode`) and the reply is at most four words, the take
out of line (`replyRecvCallFaultTakeAnswer`); the fault arm (`replyRecvFaultArmR`)
otherwise (`replyRecvCallFaultArmR_eq`). -/
@[inline] def replyRecvCallFaultArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvCallTakeArmCode st epId tid c rid != 0 &&
        decide (Architecture.regMessageLength layout len ≤ 4) then
      .ok ((), replyRecvCallFaultTakeAnswer epId tid c rid layout
        (Architecture.regLayoutWord layout rf 0)
        (Architecture.regLayoutWord layout rf 1) (Architecture.regLayoutWord layout rf 2)
        (Architecture.regLayoutWord layout rf 3) len label executingCore st)
    else replyRecvFaultArmR epId tid c rid badge grant layout rf len label executingCore st

/-- **The reply-receive whose receive completes the bound notification, in
place** (`replyRecvCompletesSignalArm`, `replyRecvSignalArmR_eq`): seL4's
`doReplyTransfer` alone, run as the `.reply` arm runs it on the reply
capability `rcap` the reply register names (`endpointReplyCheckedArmR`, whose
in-place forms answer every caller shape a reply may write in its slots), then,
when the receive's test holds on the state the reply left, `receiveIPC`'s
`completeSignal` (`notificationWaitGatedR`, the wait's in-place consumption).
No result is built between the legs: the reply arm is inlined and its result
matched where it is made. -/
@[inline] def replyRecvSignalArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (rcap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match endpointReplyCheckedArmR ctx layout rf len extraCaps label tid executingCore rcap true st with
    | .error r => .error r
    | .ok ((), st1) =>
        if receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid then
          match notificationWaitGatedR ctx tid (receiverBoundNotification st1 tid) executingCore
              st1 with
          | .ok r => .ok r
          | .error (e, _) => .error (e, st)
        else .ok ((), st1)

/-- The checked reply-receive once its reply capability resolved to reply object
`rid`, answering caller `c` with badge `badge`: the reply leg's flow gate, then a
caller carrying a fault answered through the specification's path (its fault
reply: `replyRecvCallFaultArmR`, in place when the receive blocks or takes a
queued caller, `replyRecvFaultArmR` when it takes a queued sender), and for any
other caller the in-place path when
it may be taken (a reply of at most four words whose reply leg transfers no
capability, `replyRecvReplyInertW`, on every reply arm whose receive blocks in
place, `replyRecvBlockArmCode` and `performReplyRecvArmDelivered`; the take arms
from `replyRecvArmCallTakeR`, the Call take first; `replyRecvCapsArmR` when the reply leg
installs under the grant right, its transfer run in place between the reply's
writes and the receive),
the specification's otherwise.  Every
in-place path delivers the reply as a message, which is the answer only for a
caller carrying no fault, so the fault test runs first.  A receive that
completes the replier's bound notification (`receiveCompletesSignal`) runs
`signalArm` instead, the reply alone and then the completion: the in-place
`replyRecvSignalArmR` on the reply capability the caller resolved. -/
@[inline] def replyRecvResolvedR (ctx : LabelingContext) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len label : Nat)
    (executingCore : Concurrency.CoreId) (signalArm : RefusalCarrying Unit) :
    RefusalCarrying Unit :=
  fun st =>
      if receiveCompletesSignal ctx st tid then signalArm st
      else if threadHasPendingFault st c then
        replyRecvCallFaultArmR epId tid c rid badge grant layout rf len label executingCore st
      else if decide (Architecture.regMessageLength layout len ≤ 4) &&
          replyRecvBlockArmCode st epId tid c rid != 0 && replyRecvReplyInertW st tid c grant then
        .ok ((), performReplyRecvArmDelivered
          (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
          ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
          (receiveQueueTailCode st epId) layout rf len badge executingCore)
      else replyRecvArmCallTakeR epId tid c rid badge grant layout rf len label executingCore st

/-- The general reply-receive arm on a message read in registers: the reply
capability at the reply register (`layout.replyReg`, x6), its receive half
`handleRecv` with `canReply` true, as `SysReplyRecv` runs it (WS-SX SX7.3). -/
@[inline] def endpointReplyRecvCheckedArmRegsR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  endpointReplyRecvCheckedArmGeneralR ctx
    { length := len, extraCaps := extraCaps, label := label }
    (Architecture.regMessageRegs layout rf)
    (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)) tid executingCore cap

/-- WS-ZA ZA4.7: the checked reply-receive arm (`dispatchWithCapChecked`'s
`.replyRecv` case) on a message read in registers, refusing in the state it was
handed (`endpointReplyRecvCheckedArmR_eq`).  The reply capability at the reply
register (x6, WS-SX SX7.3) is resolved in continuation form; a reply-receive
that may block in place on any reply arm (`replyRecvBlockArmCode`) writes in
place (`performReplyRecvArmDelivered`); one whose reply has no caller to answer
receives alone (WS-SX SX7.2). -/
@[inline] def endpointReplyRecvCheckedArmR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) (cap : Capability) :
    RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
        let replyAddr := SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)
        callerExtraCapsFailK st tid extraCaps
          (fun _ => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st)
          (fun _ =>
            let resolved := fun rcap rid c badge grant =>
              replyRecvResolvedR ctx epId tid c rid badge grant layout rf len label executingCore
                (replyRecvSignalArmR ctx layout rf len extraCaps label tid executingCore rcap) st
            resolveReplyRecvK st tid replyAddr (fun c => replyRecvReplyAnswers ctx st tid c)
              (fun e => .error (e, st))
              (fun _ => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st)
              resolved)
    | _ => .error (.invalidCapability 0, st)

/-- The caller a reply-receive's reply leg reaches, read from the pre-state
before the arm, as its code (`SeLe4n.ThreadId.optCode`): the caller recorded
by the reply object the capability at the reply register (x6, WS-SX SX7.3)
names (`replyRecvReplyLegEdges`).  The slot is resolved in continuation form, so
nothing is built. -/
@[inline] def replyRecvTaintCallerCode (st : SystemState) (tid : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (extraCaps : Nat) :
    Nat :=
  callerExtraCapsFailK st tid extraCaps (fun _ => 0) fun _ =>
    match callerCspaceRoot st tid with
    | none => 0
    | some root =>
    lookupSlotFromK root
      (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf layout.replyReg)) st (fun _ _ _ _ => 0)
      (fun cnode slot =>
        match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
        | some rc =>
            match rc.target with
            | .replyCap rid =>
                match st.getReply? rid with
                | some r => r.callerCode
                | none => 0
            | _ => 0
        | none => 0)

/-- The reply-receive's taint step, without the plan: the receive leg's bound
notification words `wN` and sender words `wS` join the server's, then the server's words `wT` — both captured
before the arm, so the server's are its pre-state's — join the answered
caller's (`replyRecvTaintStep_eq`). -/
@[inline] def replyRecvTaintStep (signalCode sourceCode callerCode : Nat)
    (tid : SeLe4n.ThreadId) (wN wS wT : TaintWords) (post : SystemState) : SystemState :=
  sendTaintStep callerCode tid wT (receiveTaintStep signalCode sourceCode tid wN wS post)

/-- The entry route's refusal step, without the plan
(`replyRecvEntryRefusalTaint`): where the reply answers the caller the code
`answered` names, the receive leg's refusal step, then the reply leg's; the
state as it is where it answers none. -/
@[inline] def replyRecvEntryRefusalTaintStep (answered sourceCode : Nat) (awaited : Bool)
    (tid : SeLe4n.ThreadId) (wT wS : TaintWords) (s : SystemState) : SystemState :=
  match answered with
  | 0 => s
  | c + 1 =>
    replyRecvRefusalTaintStep (c + 1) ⟨c⟩ tid wT
      (receiveLegRefusalTaintStep sourceCode awaited tid wS s)

/-- **The entry route's refusal step, out of line, on words**
(`replyRecvEntryRefusalTaintStep`): the words captured before the arm cross as
scalars, so each refusal site of an arm calls it once, the step compiled once
rather than at every site, and no record is built
(`replyRecvEntryRefusalStepW_fields`). -/
@[noinline] def replyRecvEntryRefusalStepW (answered sourceCode : Nat) (awaited : Bool)
    (tid : SeLe4n.ThreadId) (b0 b1 b2 b3 b4 b5 b6 b7 : UInt64) (bc : Nat) (bs : Bool)
    (a0 a1 a2 a3 a4 a5 a6 a7 : UInt64) (ac : Nat) (as : Bool) (s : SystemState) : SystemState :=
  replyRecvEntryRefusalTaintStep answered sourceCode awaited tid
    ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩ ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ s

/-- The out-of-line refusal step on a record's fields is the step on the
records.  Unconditional. -/
theorem replyRecvEntryRefusalStepW_fields (answered sourceCode : Nat) (awaited : Bool)
    (tid : SeLe4n.ThreadId) (wT wS : TaintWords) (s : SystemState) :
    replyRecvEntryRefusalStepW answered sourceCode awaited tid
        wT.tag0 wT.tag1 wT.tag2 wT.tag3 wT.tag4 wT.tag5 wT.tag6 wT.tag7 wT.count wT.saturated
        wS.tag0 wS.tag1 wS.tag2 wS.tag3 wS.tag4 wS.tag5 wS.tag6 wS.tag7 wS.count wS.saturated s =
      replyRecvEntryRefusalTaintStep answered sourceCode awaited tid wT wS s := rfl

/-- WS-ZA ZA4.7: the reply-receive's slot check, gate, arm and taint step on
the capability its operand resolved to.  A refusal of the arm carries the
state the arm stopped in, with an answering reply-receive's flow taken through
words captured before the arm (`replyRecvEntryRefusalTaint`,
`replyRecvOperandArmThenTaintR_eq`).

A specification: the routed arms run it in continuation form
(`replyRecvOperandArmThenTaintKE`, proven equal by
`replyRecvOperandArmThenTaintKE_eq`), so no compiled path calls it and no code
is generated for it, as for `dispatchReplyRecvCheckedR`. -/
noncomputable def replyRecvOperandArmThenTaintR (ctx : LabelingContext)
    (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat)
    (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
        else if !syscallTargetAccepted .replyRecv st cap then .error (.invalidCapability 0, st)
        else if cap.hasRight requiredRight then
          let signalCode := receiveTaintSignalCode st tid cap
          let sourceCode := receiveTaintSourceCode st cap
          let callerCode := replyRecvTaintCallerCode st tid layout rf extraCaps
          let answered := replyRecvAnsweringCallerCode ctx tid
            (SeLe4n.readRegWord rf layout.replyReg) extraCaps st
          let awaited := senderAwaitsReceiveOfCode st sourceCode
          withTaintWordsAt st (notifObjOfCode signalCode) fun n0 n1 n2 n3 n4 n5 n6 n7 nc ns =>
          withTaintWordsAt st (threadObjOfCode sourceCode) fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          withTaintWordsAt st tid.toObjId fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
          match endpointReplyRecvCheckedArmR ctx layout rf len extraCaps label tid executingCore
              cap st with
          | .error (e, s) =>
              .error (e, replyRecvEntryRefusalStepW answered sourceCode awaited tid
                b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as s)
          | .ok ((), stPost) =>
              .ok ((), replyRecvTaintStep signalCode sourceCode callerCode tid
                ⟨n0, n1, n2, n3, n4, n5, n6, n7, nc, ns⟩ ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩
                stPost)
        else .error (syscallMissingRightError .replyRecv, st)

/-- **The state a refusal of a reply-receive's operand arm reports**: its
arm's (`replyRecvArmReport`) once the operand's slot check and rights pass,
with the flow an answering reply-receive's refusal carries
(`replyRecvEntryRefusalTaint`); the state it was handed otherwise, since every
refusal before the arm writes nothing. -/
def replyRecvOperandReport (ctx : LabelingContext) (tid : SeLe4n.ThreadId)
    (mi : MessageInfo) (regs : Array SeLe4n.RegValue) (replyAddr : SeLe4n.CPtr) (executingCore : Concurrency.CoreId)
    (requiredRight : AccessRight) (operand : Option Capability) (st : SystemState) :
    SystemState :=
  match operand with
  | none => st
  | some cap =>
    if SeLe4n.Kernel.capTargetsReservedKernelObject cap then st
    else if !syscallTargetAccepted .replyRecv st cap then st
    else if cap.hasRight requiredRight then
      replyRecvEntryRefusalTaint ctx tid mi.extraCaps replyAddr cap st
        (replyRecvArmReport ctx tid mi regs replyAddr executingCore cap st)
    else st

/-! ### The long reply-receive -/

/-- The long reply-receive's rendezvous through the specification's path, its
message read in the replier's registers and IPC buffer (`longReplyRecvRegs`), a
refusal reporting the state the refusing step stopped in
(`replyRecvTransferOnCoreR`). -/
@[noinline] def replyRecvLongRendezvousR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool) (rf : SeLe4n.RegisterFile)
    (len label : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    match replyRecvTransferOnCoreR epId tid rid c label
        { registers := longReplyRecvRegs rf st tid len, badge := badge }
        grant executingCore st with
    | .ok (summary, st') =>
        .ok ((), Architecture.stageDeliveredMessage st' tid summary.capInfo)
    | .error es => .error es

/-- Whether the long reply-receive's transferring arm may block in place: the
grant right, an unfaulted caller and `replyRecvBlocksFast`.  Out of line, so
the checks are one call. -/
@[noinline] def replyRecvLongCapsAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (grant : Bool) : Bool :=
  grant && !threadHasPendingFault st c && replyRecvBlockArmCode st epId tid c rid != 0

/-- Whether a long reply-receive answering a caller blocked on this server, the
caller unfaulted, takes a waiting sender in place on some reply arm
(`replyRecvTakeArmCode`).  Out of
line, so the checks are one call. -/
@[noinline] def replyRecvLongTakeAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Bool :=
  !threadHasPendingFault st c && replyRecvTakeArmCode st epId tid c rid != 0

/-- **The long reply-receive whose receive leg takes a waiting sender**
(seL4-MCS's `handleReplyRecv` with a reply of more than four words:
`doReplyTransfer` copying the overflow words, then `receiveIPC` taking a sender
already queued): when `replyRecvLongTakeAdmits` passes and the sender's saved
frame routes as a capability-free send, the reply's writes, the reply leg's
transfer, the take, the caller's long frame and the server's frame, the
sender's six words read from its saved registers before any write.  A reply leg
transferring no capability runs `performReplyRecvArmTakeDeliveredLong`; a granting
one `performReplyRecvArmTakeCapsDeliveredLong`, over the arm.  Any other takes the
specification's path (`replyRecvLongTakeArmR_eq`). -/
@[inline] def replyRecvLongTakeArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  fun st =>
    if replyRecvLongTakeAdmits st epId tid c rid then
      match st.getEndpoint? epId with
      | some ep =>
        match ep.sendQ.head with
        | some s =>
          match st.getTcb? s with
          | some sTcb =>
            match Architecture.RegisterDecode.registerRoutedSyscallOf
                (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
                SeLe4n.arm64DefaultLayout sTcb.registerContext with
            | .send _ mi =>
              let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
              if replyRecvReplyInertW st tid c grant then
                .ok ((), performReplyRecvArmTakeDeliveredLong
                  (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                  ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
                  sTcb.queueNextCode executingCore rf len badge f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
              else if grant then
                match st.getTcb? tid with
                | some stcb =>
                  match st.getTcb? c with
                  | some ct =>
                    .ok ((), performReplyRecvArmTakeCapsDeliveredLong
                      (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                      ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid
                      epId s sTcb.queueNextCode executingCore rf len badge f.x0 f.x1 f.x2 f.x3 f.x4 f.x5
                      stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0] (routedExtraCaps rf)
                      ct.spaceCells[2] ct.ipcBuffer ct.spaceCells[0])
                  | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label
                      executingCore st
                | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label
                    executingCore st
              else replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
            | _ => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
          | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
        | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
      | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
    else replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st

/-- Whether a reply-receive with a reply longer than four words, to a caller
with no pending fault, takes the queued caller in place on some reply arm
(`replyRecvCallTakeArmCode`): its reply leg transferring no capability
(`replyRecvReplyInertW`), or granting with the replier's TCB present.  Out of
line and a `Bool`, so the checks are one call and allocate nothing. -/
@[noinline] def replyRecvLongCallTakeAdmits (st : SystemState) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (grant : Bool) : Bool :=
  !threadHasPendingFault st c && replyRecvCallTakeArmCode st epId tid c rid != 0 &&
    (replyRecvCallTakeReplyInert st tid c grant || grant && (st.getTcb? tid).isSome)

/-- **The reply-receive taking a queued caller, its reply longer than four
words**: the arm's reply leg and pop, the reply leg's transfer, the take, the
arm's lend and the frames, every context, core and word it takes read on the
pre-state.  A reply leg transferring no capability runs
`performReplyRecvArmCallTakeDeliveredLong`; a granting one
`performReplyRecvArmCallTakeCapsDeliveredLong`.  Out of line, it returns the
state, so nothing is built around it; read only where
`replyRecvLongCallTakeAdmits` passes, and the state unchanged on a shape it
does not admit; the granting leg's capability count (`count`) is read of the
replier's frame by the arm too. The reply enters as the four inline words the arm reads of the replier's
message registers on the pre-state (`Architecture.regLayoutWord`), not as its
register file, so nothing outside the server's TCB holds the register file
when the server's frame is written. -/
@[noinline] def replyRecvLongCallTakeAnswer (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (m0 m1 m2 m3 : UInt64) (count len : Nat) (executingCore : Concurrency.CoreId)
    (st : SystemState) : SystemState :=
  match st.getEndpoint? epId with
  | some ep =>
    match ep.sendQ.head with
    | some s =>
      match st.getTcb? s with
      | some sTcb =>
        match Architecture.RegisterDecode.registerRoutedSyscallOf
            (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
            SeLe4n.arm64DefaultLayout sTcb.registerContext with
        | .call _ mi =>
          if replyRecvCallTakeReplyInert st tid c grant then
            performReplyRecvArmCallTakeDeliveredLong
              (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
              (replyRecvCallLendsOfCode (replyRecvCallTakeArmCode st epId tid c rid))
              ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
              sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
              (determineTargetCore st tid) executingCore len badge m0 m1 m2 m3
              sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
              sTcb.ipcBadged
          else
            match st.getTcb? tid with
            | some stcb =>
              match st.getTcb? c with
              | some ct =>
                performReplyRecvArmCallTakeCapsDeliveredLong
                  (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
                  (replyRecvCallLendsOfCode (replyRecvCallTakeArmCode st epId tid c rid))
                  ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid
                  epId s sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩
                  (determineTargetCore st s) (determineTargetCore st tid) executingCore
                  len badge m0 m1 m2 m3 sTcb.registerContext mi.length
                  (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
                  stcb.spaceCells[2] stcb.ipcBuffer stcb.spaceCells[0]
                  count ct.spaceCells[2] ct.ipcBuffer
                  ct.spaceCells[0]
              | none => st
            | none => st
        | _ => st
      | none => st
    | none => st
  | none => st

/-- **The checked reply-receive whose receive leg takes a queued caller, over
every reply arm** (seL4-MCS's `handleReplyRecv`: `doReplyTransfer`, the reply
arm's `reply_pop`, then `receiveIPC` taking a caller queued by a `Call`, and
`reply_push (canDonate)` lending that caller's context to a server holding
none): when a reply longer than four words, to a caller with no pending fault,
takes the caller in place on some reply arm (`replyRecvLongCallTakeAdmits`),
the take out of line (`replyRecvLongCallTakeAnswer`).  Otherwise the long take
arm (`replyRecvLongTakeArmR`); the specification's path
(`replyRecvLongCallTakeArmR_eq`). -/
@[inline] def replyRecvLongCallTakeArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvLongCallTakeAdmits st epId tid c rid grant then
      .ok ((), replyRecvLongCallTakeAnswer epId tid c rid badge grant
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) (routedExtraCaps rf) len executingCore st)
    else replyRecvLongTakeArmR epId tid c rid badge grant rf len label executingCore st

/-- The long reply-receive whose reply leg transfers, its caller unfaulted:
under the grant right, on every reply arm whose receive leg blocks in place
(`replyRecvBlockArmCode`), the arm's reply leg and pop, the transfer in place,
then the receive's block and the long frame
(`performReplyRecvArmCapsDeliveredLong`); the take arm
(`replyRecvLongTakeArmR`) otherwise (`replyRecvLongCapsR_eq`).  Each shape's guard is one out-of-line call, so a
test it shares with the inert arm's is not hoisted into a closure the inert path
builds. -/
@[inline] def replyRecvLongCapsR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  fun st =>
    if replyRecvLongCapsAdmits st epId tid c rid grant then
      match st.getTcb? tid with
      | some stcb =>
          match st.getTcb? c with
          | some ct =>
              .ok ((), performReplyRecvArmCapsDeliveredLong
                (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
                ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
                (receiveQueueTailCode st epId) rf len badge executingCore stcb.spaceCells[2]
                stcb.ipcBuffer stcb.spaceCells[0] (routedExtraCaps rf) ct.spaceCells[2] ct.ipcBuffer
                ct.spaceCells[0])
          | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
      | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
    else replyRecvLongCallTakeArmR epId tid c rid badge grant rf len label executingCore st

/-- The long reply-receive answering a caller carrying a fault: the long fault
answer (`performFaultAnswerLong`, the reply's words past MR0 read in the
replier's registers and IPC buffer) on every reply arm whose receive leg
blocks in place (`replyRecvBlockArmCode`,
`performReplyRecvArmFaultAnswerLong`) and on every reply arm whose receive
takes a waiting sender (`replyRecvTakeArmCode`,
`performReplyRecvArmFaultTakeDeliveredLong`); the specification's path
otherwise (`replyRecvLongFaultArmR_eq`).  The caller's words are read before the writes
and its TCB is not held across them. -/
@[inline] def replyRecvLongFaultArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) :
    RefusalCarrying Unit :=
  fun st =>
    match st.getTcb? c with
    | some ct =>
        if replyRecvBlockArmCode st epId tid c rid != 0 then
          .ok ((), performReplyRecvArmFaultAnswerLong
            (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
            ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
            (receiveQueueTailCode st epId) executingCore ct.faultKind label ct.faultIp ct.faultSp
            ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
            ct.faultX6 ct.faultX7 rf len)
        else if replyRecvTakeArmCode st epId tid c rid != 0 then
          match st.getEndpoint? epId with
          | some ep =>
            match ep.sendQ.head with
            | some s =>
              match st.getTcb? s with
              | some sTcb =>
                match Architecture.RegisterDecode.registerRoutedSyscallOf
                    (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
                    SeLe4n.arm64DefaultLayout sTcb.registerContext with
                | .send _ mi =>
                  let f := Architecture.regMessageFrameW SeLe4n.arm64DefaultLayout
                    sTcb.registerContext mi.length (SeLe4n.Badge.ofWord sTcb.ipcBadge)
                    sTcb.ipcBadged
                  .ok ((), performReplyRecvArmFaultTakeDeliveredLong
                    (ReplyRecvArm.ofCode (replyRecvTakeArmCode st epId tid c rid))
                    ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
                    sTcb.queueNextCode executingCore ct.faultKind label ct.faultIp ct.faultSp
                    ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4 ct.faultX5
                    ct.faultX6 ct.faultX7 rf len f.x0 f.x1 f.x2 f.x3 f.x4 f.x5)
                | _ => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
              | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
            | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
          | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
        else replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st
    | none => replyRecvLongRendezvousR epId tid c rid badge grant rf len label executingCore st

/-- **The fault answered and a queued caller taken, its reply longer than four
words**: the arm's reply leg with no message and pop, the take, the arm's lend,
the fault answered from the caller's words and the reply's registers past MR0
(`performReplyRecvArmCallFaultTakeDeliveredLong`, its words past MR3 read from
the replier's buffer), every word read on the pre-state.  Out of line, it
returns the state, so nothing is built around it; read only where
`replyRecvCallTakeArmCode` admits, and the state unchanged on a shape it does
not. The reply enters as the four inline words the arm reads of the replier's
message registers on the pre-state (`Architecture.regLayoutWord`), not as its
register file, so nothing outside the server's TCB holds the register file
when the server's frame is written. -/
@[noinline] def replyRecvLongCallFaultTakeAnswer (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (m0 m1 m2 m3 : UInt64)
    (len label : Nat) (executingCore : Concurrency.CoreId) (st : SystemState) : SystemState :=
  match st.getTcb? c with
  | some ct =>
    match st.getEndpoint? epId with
    | some ep =>
      match ep.sendQ.head with
      | some s =>
        match st.getTcb? s with
        | some sTcb =>
          match Architecture.RegisterDecode.registerRoutedSyscallOf
              (blockedSenderCode SeLe4n.arm64DefaultLayout sTcb.registerContext)
              SeLe4n.arm64DefaultLayout sTcb.registerContext with
          | .call _ mi =>
            performReplyRecvArmCallFaultTakeDeliveredLong
              (ReplyRecvArm.ofCode (replyRecvCallTakeArmCode st epId tid c rid))
              (replyRecvCallLendsOfCode (replyRecvCallTakeArmCode st epId tid c rid))
              ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId s
              sTcb.queueNextCode ⟨sTcb.scBindingScCode - 1⟩ (determineTargetCore st s)
              (determineTargetCore st tid) executingCore ct.faultKind label ct.faultIp
              ct.faultSp ct.faultLr ct.faultX0 ct.faultX1 ct.faultX2 ct.faultX3 ct.faultX4
              ct.faultX5 ct.faultX6 ct.faultX7 len m0 m1 m2 m3 sTcb.registerContext mi.length
              (SeLe4n.Badge.ofWord sTcb.ipcBadge) sTcb.ipcBadged
          | _ => st
        | none => st
      | none => st
    | none => st
  | none => st

/-- **The checked reply-receive answering a faulted caller and taking a queued
caller, over every reply arm**, its reply longer than four words: when the
receive leg takes a caller queued by a routed capability-free call in place on
some reply arm (`replyRecvCallTakeArmCode`), the take out of line
(`replyRecvLongCallFaultTakeAnswer`); the fault arm (`replyRecvLongFaultArmR`)
otherwise (`replyRecvLongCallFaultArmR_eq`). -/
@[inline] def replyRecvLongCallFaultArmR (epId : SeLe4n.ObjId) (tid c : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  fun st =>
    if replyRecvCallTakeArmCode st epId tid c rid != 0 then
      .ok ((), replyRecvLongCallFaultTakeAnswer epId tid c rid
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 0)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 1)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 2)
        (Architecture.regLayoutWord SeLe4n.arm64DefaultLayout rf 3) len label executingCore st)
    else replyRecvLongFaultArmR epId tid c rid badge grant rf len label executingCore st

/-- **The long reply-receive whose receive completes the bound notification, in
place**: the long `.reply` arm's reply on the reply capability `rcap`
(`endpointReplyLongCheckedArmR`, its overflow words copied in place), then the
completion, as `replyRecvSignalArmR` runs them for a short reply
(`replyRecvLongSignalArmR_eq`). -/
@[inline] def replyRecvLongSignalArmR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len extraCaps label : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (rcap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match endpointReplyLongCheckedArmR ctx rf len extraCaps label tid executingCore rcap true st with
    | .error r => .error r
    | .ok ((), st1) =>
        if receiveCompletesSignal ctx st1 tid && receiverIpcReady st1 tid then
          match notificationWaitGatedR ctx tid (receiverBoundNotification st1 tid) executingCore
              st1 with
          | .ok r => .ok r
          | .error (e, _) => .error (e, st)
        else .ok ((), st1)

/-- The checked long reply-receive once its reply capability resolved to reply
object `rid`, answering caller `c`: the reply leg's flow gate, then a caller
carrying a fault answered by the long fault answer (`replyRecvLongFaultArmR`, in
place when the receive blocks), and for a caller carrying no fault when the
reply-receive may block in place on any reply arm
(`replyRecvBlockArmCode`) and its reply leg transfers no capability
(`replyRecvReplyInertW`), the in-place delivery
(`performReplyRecvArmDeliveredLong`); otherwise the transferring arm
(`replyRecvLongCapsR`), which runs the transfer in place or the
specification's path. -/
@[inline] def replyRecvLongResolvedR (ctx : LabelingContext) (epId : SeLe4n.ObjId)
    (tid c : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) (badge : Option SeLe4n.Badge) (grant : Bool)
    (rf : SeLe4n.RegisterFile) (len label : Nat) (executingCore : Concurrency.CoreId)
    (signalArm : RefusalCarrying Unit) : RefusalCarrying Unit :=
  fun st =>
      if receiveCompletesSignal ctx st tid then signalArm st
      else if threadHasPendingFault st c then
        replyRecvLongCallFaultArmR epId tid c rid badge grant rf len label executingCore st
      else if replyRecvBlockArmCode st epId tid c rid != 0 && replyRecvReplyInertW st tid c grant
          then
        .ok ((), performReplyRecvArmDeliveredLong
          (ReplyRecvArm.ofCode (replyRecvBlockArmCode st epId tid c rid))
          ⟨replyHeadContextCode st rid - 1⟩ (determineTargetCore st c) st c tid rid epId
          (receiveQueueTailCode st epId) rf len badge executingCore)
      else replyRecvLongCapsR epId tid c rid badge grant rf len label executingCore st

/-- The long reply-receive's general arm, its words read where it runs. -/
@[inline] def endpointReplyRecvLongGeneralR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len extraCaps label : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st => endpointReplyRecvCheckedArmGeneralR ctx
    { length := len, extraCaps := extraCaps, label := label } (longReplyRegs st tid rf len)
    (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg)) tid
    executingCore cap st

/-- The checked reply-receive arm for a message of `len` words, more than four,
refusing in the state it was handed (`endpointReplyRecvLongCheckedArmR_eq`).
The reply capability in the reply register is resolved in continuation form; a reply-receive
that answers an unfaulted caller and then blocks writes in place, copying the
replier's overflow words into the caller's buffer
(`replyRecvOnCore_arm_deliveredLong`), as seL4's `doReplyTransfer` does. -/
@[inline] def endpointReplyRecvLongCheckedArmR (ctx : LabelingContext) (rf : SeLe4n.RegisterFile)
    (len extraCaps label : Nat) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (cap : Capability) : RefusalCarrying Unit :=
  fun st =>
    match cap.target with
    | .object epId =>
      if !endpointFlowGate ctx epId (ctx.endpointLabelOf epId) (ctx.threadLabelOf tid) then
        .error (.flowDenied, st)
      else
        let replyAddr := SeLe4n.CPtr.ofWord
          (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg)
        callerExtraCapsFailK st tid extraCaps
          (fun _ => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st)
          (fun _ =>
            resolveReplyRecvK st tid replyAddr (fun c => replyRecvReplyAnswers ctx st tid c)
              (fun e => .error (e, st))
              (fun _ => endpointReceiveCheckedArmR ctx tid true replyAddr executingCore cap st)
              (fun rcap rid c badge grant =>
                replyRecvLongResolvedR ctx epId tid c rid badge grant rf len label executingCore
                  (replyRecvLongSignalArmR ctx rf len extraCaps label tid executingCore rcap) st))
    | _ => .error (.invalidCapability 0, st)

/-- The long reply-receive's slot check, gate, arm and taint step on the
capability its operand resolved to (`endpointReplyRecvLongCheckedArmR`), its
taint the short reply-receive's (`replyRecvTaintStep`), and its refusals the
short one's (`replyRecvEntryRefusalTaint`, `replyRecvLongOperandArmThenTaintR_eq`).

A specification, as the short one is: the routed long arm runs it in
continuation form (`replyRecvLongOperandArmThenTaintKE_eq`), so no code is
generated for it. -/
noncomputable def replyRecvLongOperandArmThenTaintR (ctx : LabelingContext)
    (rf : SeLe4n.RegisterFile) (len extraCaps label : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (requiredRight : AccessRight)
    (operand : Option Capability) : RefusalCarrying Unit :=
  fun st =>
    match operand with
    | none => .error (.invalidCapability 0, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability 0, st)
        else if !syscallTargetAccepted .replyRecv st cap then .error (.invalidCapability 0, st)
        else if cap.hasRight requiredRight then
          let signalCode := receiveTaintSignalCode st tid cap
          let sourceCode := receiveTaintSourceCode st cap
          let callerCode := replyRecvTaintCallerCode st tid SeLe4n.arm64DefaultLayout rf
            extraCaps
          let answered := replyRecvAnsweringCallerCode ctx tid
            (SeLe4n.readRegWord rf SeLe4n.arm64DefaultLayout.replyReg) extraCaps st
          let awaited := senderAwaitsReceiveOfCode st sourceCode
          withTaintWordsAt st (notifObjOfCode signalCode) fun n0 n1 n2 n3 n4 n5 n6 n7 nc ns =>
          withTaintWordsAt st (threadObjOfCode sourceCode) fun a0 a1 a2 a3 a4 a5 a6 a7 ac as =>
          withTaintWordsAt st tid.toObjId fun b0 b1 b2 b3 b4 b5 b6 b7 bc bs =>
          match endpointReplyRecvLongCheckedArmR ctx rf len extraCaps label tid executingCore
              cap st with
          | .error (e, s) =>
              .error (e, replyRecvEntryRefusalStepW answered sourceCode awaited tid
                b0 b1 b2 b3 b4 b5 b6 b7 bc bs a0 a1 a2 a3 a4 a5 a6 a7 ac as s)
          | .ok ((), stPost) =>
              .ok ((), replyRecvTaintStep signalCode sourceCode callerCode tid
                ⟨n0, n1, n2, n3, n4, n5, n6, n7, nc, ns⟩ ⟨a0, a1, a2, a3, a4, a5, a6, a7, ac, as⟩ ⟨b0, b1, b2, b3, b4, b5, b6, b7, bc, bs⟩
                stPost)
        else .error (syscallMissingRightError .replyRecv, st)

end SeLe4n.Kernel
