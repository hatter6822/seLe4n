-- SPDX-License-Identifier: GPL-3.0-or-later
import SeLe4n.Kernel.Concurrency.Locks.LockSetTransitions
-- **WS-RR RR7.11**: the state-resolved IPC footprints. Every one of these
-- modules is production (`EndpointCall`, `EndpointReply` and
-- `NotificationSignal` all carry landing notes, not staging markers), so the
-- resolver stays a production module referencing production footprints — the
-- constraint RR7.10 recorded when it placed the dispatcher here.
import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.NotificationSignal
-- The bound-delivery coverage witnesses for `lockSet_notificationSignalOnCore`
-- live above `NotificationSignal` in the import graph.
import SeLe4n.Kernel.IPC.CrossCore.NotificationBind
/-!
# WS-SM SM3.C.9 — the syscall → lock-set dispatcher

SM3 built the per-object lock discipline: `LockId` (kind level 0..9 ×
object), a proven total order on it, forty-one `lockSet_*` footprints,
`permittedKinds : SyscallId → List LockKind`, and `withLockSet`'s 2PL /
serializability / observer-atomicity theorems. What it never built is
the piece that connects them to a running syscall: a function from *the
syscall the dispatcher is about to run* to *the lock set that syscall's
footprint needs*. Without it the SM3 theorems are statements about an
intended discipline rather than properties of the live path, which is
what SM3.C.9 was deferred to close.

## `Option LockSet`, and why the `none` is the point

Thirty syscalls have footprints; this module declares them one at a
time. The result is `Option LockSet`:

* `some S` — this syscall's footprint **is** `S`, and every write it
  performs is covered by a member of `S` (the `lockSet_*_write_mem`
  families are the per-op proofs of exactly that);
* `none` — not yet declared. The caller must fall back to whatever
  coarser serialisation it already has.

The alternative — returning a "best effort" set for undeclared syscalls
— is the one shape this must not take. A declared lock set that does
not cover a write is not a smaller optimisation, it is a **false
footprint**: the 2PL argument would then rest on exclusion the runtime
never established, and the failure appears as a corrupted object under
contention rather than as a failed proof. `none` cannot be wrong, and
it makes the migration monotone — each future cut converts one `none`
into a `some` together with its coverage proof, and nothing regresses.

## Runtime scope (read this before wiring more callers)

Declaring a footprint does **not** make per-object locks operative.
`Platform.FFI.modifyGetKernelState` is `IO.Ref.modifyGet` over one
global `SystemState` — a whole-state read-then-write — so two cores
holding disjoint per-object locks would still lose one commit whole.
The lock granularity that matters for that is the granularity of the
*commit*, not of the footprint. Until the commit is partitioned, the
SM5.I kernel-entry lock stays, and what this dispatcher buys is the
model-level property: the SM3 theorems apply to the transition the
kernel actually runs. See `rust/sele4n-hal/src/kernel_entry.rs`.
-/


namespace SeLe4n.Kernel.Concurrency

open SeLe4n
open SeLe4n.Model

/-- **WS-SM SM3.C.9**: resolve `tcbSuspend`'s state-dependent footprint
arguments from the pre-state.

The five optional members are exactly the writes the suspend pipeline
can make beyond the victim's own TCB, and each is read here from the
same field the transition branches on:

* the endpoint it is blocked on (`blockedOnSend` / `blockedOnReceive` /
  `blockedOnCall` / `blockedOnReply` all name one) — the cancellation
  sweep unlinks the victim from its queue;
* the notification it is blocked on — same, for the notification queue;
* the Reply object consumed when the victim is `blockedOnReply`;
* its bound or donated SchedContext — the donation teardown writes it;
* the original owner a donated SchedContext returns to.

The CNode member is the **caller's** CSpace root, not the victim's.
`cnodeRootObjId` is the cap-resolution root — the CNode the syscall
actually reads to turn the caller's capability pointer into the target
capability (`syscallLookupCap` builds its gate from the *caller's*
`tcb.cspaceRoot`), which is why it is paired with the caller's TCB read
in every `lockSet_*` that has one. An earlier cut passed
`victim.cspaceRoot`, so whenever caller and victim held different
CSpace roots the declared set locked a CNode the syscall never touches
and omitted the one it reads — a coverage hole in exactly the direction
a declared footprint exists to prevent. Not a live defect (SM3.C.9
still defers `withLockSet` at the `@[export]` bodies), but the whole
value of the declaration is that it covers the operation's accesses.

`none` for the whole set when **either** thread fails to resolve to a
TCB: with no victim there is no transition to bound, and with no caller
there is no CSpace root to name. -/
def suspendFootprintOf (st : SystemState) (callerTid targetTid : ThreadId) :
    Option LockSet :=
  -- Read through the AL2-A typed accessor, not a raw `objects[...]?`
  -- match: the footprint is a statement ABOUT the object store, so it
  -- has no business reading it in a way the AK7 cascade counts as an
  -- un-migrated raw access.
  match st.getTcb? callerTid, st.getTcb? targetTid with
  | some caller, some victim =>
      let blockedEndpoint : Option ObjId :=
        match victim.ipcState with
        | .blockedOnSend ep => some ep
        | .blockedOnReceive ep => some ep
        | .blockedOnCall ep => some ep
        | .blockedOnReply ep _ => some ep
        | _ => none
      let blockedNotification : Option ObjId :=
        match victim.ipcState with
        | .blockedOnNotification n => some n
        | _ => none
      let consumedReply : Option ReplyId :=
        match victim.ipcState with
        | .blockedOnReply _ _ => victim.replyObject
        | _ => none
      let bindingSc : Option SchedContextId :=
        victim.schedContextBinding.scId?
      let donatedOwner : Option ThreadId :=
        match victim.schedContextBinding with
        | .donated _ owner => some owner
        | _ => none
      some (lockSet_tcbSuspend callerTid caller.cspaceRoot targetTid
              blockedEndpoint blockedNotification bindingSc
              donatedOwner consumedReply)
  | _, _ => none

/-- **WS-RR RR7.10**: the operands a declared footprint is resolved from.

The pre-RR7.10 resolver took `(callerTid, targetTid, st)`, and `targetTid` is a
`ThreadId`. That is expressible only for the thread-directed syscalls: an
IPC arm's footprint names an **endpoint** or a **notification**, and a
capability arm's names a **CNode**, none of which is a thread. The one
declared arm happened to be thread-directed, so the signature looked general
while being unable to say what every remaining arm needs — and the caller that
resolved the target for it (`declaredLockSetForEntry`'s `entryCapTarget`)
reinterpreted the capability's `ObjId` *as* a thread id, which for an endpoint
capability is a different object with the same number.

The two are separate fields rather than one, because a syscall is directed at
one or the other and never at both: `.tcbSuspend` names a victim thread,
`.send` names an endpoint. `message` is here because whether an IPC arm's
footprint includes a capability-transfer destination is a property of what the
message carries (WS-RR RR7.7), and the arms that consume it are RR7.11's.

Every field is optional and defaults to absent, so a caller supplies exactly
what its syscall is directed at and an arm that needs something absent answers
`none` — the same fail-closed direction the module docstring describes. -/
structure SyscallLockOperands where
  /-- The invoking thread — its TCB, and through it the CSpace root every
  footprint reads for capability resolution. -/
  caller : ThreadId
  /-- The **thread** a thread-directed syscall targets: `.tcbSuspend`'s victim,
  `.tcbResume`'s target, `.schedContextBind`'s bound thread. -/
  targetThread : Option ThreadId := none
  /-- The **object** an object-directed syscall targets: the endpoint of a
  send / call / receive / reply, the notification of a signal / wait, the CNode
  of a capability operation, the SchedContext of a `.schedContext*` arm. -/
  targetObject : Option ObjId := none
  /-- The **Reply object** a reply-shaped syscall names — `.reply`'s and
  `.replyRecv`'s reply capability (`cap.target = .replyCap rid`), and
  `.receive`'s server-supplied `RecvArgs.replyCPtr`.

  A third field rather than a reinterpretation of `targetObject`, for the reason
  RR7.10 separated the first two: `ReplyId` and `ObjId` are different typed
  identifiers, and a syscall that names both — `.replyRecv` names an endpoint
  *and* a reply object — cannot express itself with one slot at all. -/
  targetReply : Option ReplyId := none
  /-- The message an IPC arm carries, for the footprints whose members depend
  on it — a caps-carrying rendezvous declares the receiver's CSpace root and
  the state-level lock its CDT write needs, and a capless one must not. -/
  message : Option IpcMessage := none

/-- **WS-RR RR7.10**: the operands of a thread-directed syscall. -/
def SyscallLockOperands.ofThreadTarget (caller target : ThreadId) :
    SyscallLockOperands :=
  { caller := caller, targetThread := some target }

/-- **WS-RR RR7.10**: the operands of an object-directed syscall, with the
message it carries. -/
def SyscallLockOperands.ofObjectTarget (caller : ThreadId) (target : ObjId)
    (message : Option IpcMessage := none) : SyscallLockOperands :=
  { caller := caller, targetObject := some target, message := message }

/-- **WS-RR RR7.11**: the operands of a reply-shaped syscall.

`.reply` names a reply object and nothing else; `.replyRecv` names one *and* the
endpoint it receives on next, which is why the endpoint is an argument here
rather than a second constructor. -/
def SyscallLockOperands.ofReplyTarget (caller : ThreadId) (reply : ReplyId)
    (endpoint : Option ObjId := none) : SyscallLockOperands :=
  { caller := caller, targetObject := endpoint, targetReply := some reply }

/-- **WS-SM SM3.C.9**: the declared lock-set footprint of a syscall, or
`none` where one has not been established yet.

Total over `SyscallId` by construction — a new syscall variant makes
this fail to compile rather than silently inherit a neighbour's
footprint. See the module docstring for why undeclared arms return
`none` instead of an approximation. -/
def lockSetForSyscall (sid : SyscallId) (ops : SyscallLockOperands)
    (st : SystemState) : Option LockSet :=
  match sid with
  -- WS-RR RR7.10: the victim is the operands' thread target. With none
  -- supplied there is no suspend to bound, so the arm answers `none` — the
  -- same fail-closed direction as an unresolvable victim.
  | .tcbSuspend =>
      ops.targetThread.bind (fun victim => suspendFootprintOf st ops.caller victim)
  -- **WS-RR RR7.11: the IPC hot path.** Seven arms, each resolved through the
  -- SM6 state-resolved footprint the cross-core transition itself is declared
  -- against, so the declaration and the transition read one expression rather
  -- than two that have to be kept in step. Every arm opens on the caller's own
  -- TCB, because a footprint's CNode member is the *caller's* CSpace root — the
  -- root `syscallLookupCap` resolves the invoked capability through — and a
  -- caller that does not resolve to a TCB has no root to name.
  --
  -- `.send` and `.call` additionally require the **message**: whether the
  -- rendezvous installs capabilities (and so whether the receiver's CSpace root
  -- and the state-level lock the CDT write needs are members) is a property of
  -- what the message carries, RR7.7's optional. With no message supplied the
  -- arm cannot tell a capless send from an unknown one, so it declares nothing
  -- — the module docstring's direction, not a defaulted guess: defaulting to
  -- the empty message would declare the *capless* footprint for a send that may
  -- carry capabilities, which is the false-footprint failure this file exists
  -- to refuse.
  | .send =>
      (st.getTcb? ops.caller).bind fun caller =>
        ops.targetObject.bind fun endpointId =>
          ops.message.map fun msg =>
            lockSet_endpointSendOnCore st endpointId ops.caller caller.cspaceRoot msg
  | .call =>
      (st.getTcb? ops.caller).bind fun caller =>
        ops.targetObject.bind fun endpointId =>
          ops.message.map fun msg =>
            lockSet_endpointCallOnCore st endpointId ops.caller caller.cspaceRoot msg
  -- `.receive` needs no message: what a receive installs comes from the *parked
  -- sender's* message, which `receiveInstallsCaps` reads from the endpoint.
  -- The reply object is the server-supplied one (`RecvArgs.replyCPtr`), a
  -- decoded operand, so it travels in `targetReply`; `none` is the plain
  -- receive and declares no reply lock, which is right — a plain receive links
  -- none.
  | .receive =>
      (st.getTcb? ops.caller).bind fun caller =>
        ops.targetObject.map fun endpointId =>
          lockSet_endpointReceiveOnCore st endpointId ops.caller caller.cspaceRoot
            ops.targetReply
  -- `.reply` and `.replyRecv` name their answered caller the way the live arms
  -- do: authority flows from *holding* the reply capability, so the thread
  -- being answered is `reply.caller`, read from the Reply object the capability
  -- names. A dangling reply (`getReply? = none`) or an unlinked one
  -- (`caller = none`) is what the live arms reject with `.replyCapInvalid`, and
  -- declaring a footprint for a syscall that cannot execute is exactly what the
  -- entry resolver's sentinel guard exists to prevent — so both answer `none`.
  | .reply =>
      (st.getTcb? ops.caller).bind fun caller =>
        ops.targetReply.bind fun rid =>
          (replyAnsweredCaller? st rid).map fun answered =>
            lockSet_endpointReplyOnCore st ops.caller caller.cspaceRoot answered
  | .replyRecv =>
      (st.getTcb? ops.caller).bind fun caller =>
        ops.targetObject.bind fun endpointId =>
          ops.targetReply.bind fun rid =>
            (replyAnsweredCaller? st rid).map fun prevCaller =>
              lockSet_endpointReplyRecvOnCore st ops.caller caller.cspaceRoot prevCaller
                endpointId
  -- The two notification arms. The signal's footprint is bound-delivery aware
  -- (`boundDeliveryTarget?` folds the bound TCB's endpoint and TCB writes in);
  -- the wait's has no state-dependent member at all beyond the caller's root,
  -- which is why its resolver takes no state.
  | .notificationSignal =>
      (st.getTcb? ops.caller).bind fun caller =>
        ops.targetObject.map fun notificationId =>
          lockSet_notificationSignalOnCore st notificationId ops.caller caller.cspaceRoot
  | .notificationWait =>
      (st.getTcb? ops.caller).bind fun caller =>
        ops.targetObject.map fun notificationId =>
          lockSet_notificationWaitOnCore notificationId ops.caller caller.cspaceRoot
  -- Undeclared: the caller keeps its existing serialisation. Each of
  -- these becomes a `some` in a later cut, paired with the coverage
  -- proof that its footprint contains every write the op performs.
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete
  | .mintReplyCap
  | .lifecycleRetype
  | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction
  | .serviceRegister | .serviceRevoke | .serviceQuery
  | .schedContextConfigure | .schedContextBind | .schedContextUnbind
  | .tcbResume | .tcbSetPriority | .tcbSetMCPriority
  | .tcbSetIPCBuffer | .tcbSetAffinity | .tcbSetFaultHandler
  | .tcbBindNotification | .tcbUnbindNotification
  | .declassify
  -- WS-SM SM9.C.8: `.declassifySignal` is undeclared here for the same reason,
  -- and its per-object footprint (`lockSet_declassifySignal`) is the ordinary
  -- signal's set plus the state-level write its trail append needs. The
  -- caller TCB stays `.read` — the syscall is `.unit`-shaped, so unlike the
  -- audit pair the committed dispatch stages nothing into the caller's TCB.
  | .declassifySignal
  -- WS-SM SM9.A.12: the audit reader and the drain are undeclared here for the
  -- same reason as every other arm — the declared-footprint bracket is SM3.C.9
  -- work, not SM9.A work. Their per-object footprints (`lockSet_auditRead` /
  -- `lockSet_auditDrain`) carry the caller TCB in **write** mode (PR #870
  -- round 6): the transitions write no object, but the committed dispatch
  -- stages the returned word into the caller's TCB via WS-RA's
  -- `writeReturnFrameToTcb`, and a footprint covers the committed dispatch.
  | .auditRead | .auditDrain => none

/-- **WS-SM SM3.C.9**: the `tcbSuspend` arm is wired to the resolver.

Pins the dispatch itself, so a future edit that redirects the arm or
drops the resolver fails here rather than silently returning `none` and
sending the caller back to coarse serialisation without anyone noticing
the footprint stopped being declared. -/
@[simp] theorem lockSetForSyscall_tcbSuspend
    (ops : SyscallLockOperands) (st : SystemState) :
    lockSetForSyscall .tcbSuspend ops st
      = ops.targetThread.bind (fun victim => suspendFootprintOf st ops.caller victim) := rfl

/-- **WS-RR RR7.10**: at a supplied thread target the arm is exactly the
pre-RR7.10 answer, so the generalisation is a signature change and not a
behaviour change. -/
@[simp] theorem lockSetForSyscall_tcbSuspend_ofThreadTarget
    (callerTid targetTid : ThreadId) (st : SystemState) :
    lockSetForSyscall .tcbSuspend (.ofThreadTarget callerTid targetTid) st
      = suspendFootprintOf st callerTid targetTid := rfl

/-- **WS-RR RR7.10**: and with no thread target it declares nothing. -/
@[simp] theorem lockSetForSyscall_tcbSuspend_no_target
    (ops : SyscallLockOperands) (st : SystemState)
    (h : ops.targetThread = none) :
    lockSetForSyscall .tcbSuspend ops st = none := by
  unfold lockSetForSyscall
  rw [h]; rfl

/-! ## WS-RR RR7.11 — the seven IPC arms

Two theorems per arm. The **dispatch pin** (`lockSetForSyscall_<arm>`) says
which resolver the arm is wired to, so a future edit that redirects an arm or
drops a resolver fails here rather than silently returning `none` and sending
the caller back to coarse serialisation. The **resolution characterisation**
(`lockSetForSyscall_<arm>_isSome_iff`) says exactly when the arm declares — the
question a bracket consumer asks before it decides whether it has a footprint
to acquire — and it is what closes `declaredFootprintSyscall`'s otherwise-silent
drift direction: an arm listed as declared while answering `none`
unconditionally could not satisfy its own `iff`.
-/

/-- **WS-RR RR7.11**: `.send` is wired to the resolved send footprint. -/
@[simp] theorem lockSetForSyscall_send
    (ops : SyscallLockOperands) (st : SystemState) :
    lockSetForSyscall .send ops st
      = (st.getTcb? ops.caller).bind fun caller =>
          ops.targetObject.bind fun endpointId =>
            ops.message.map fun msg =>
              lockSet_endpointSendOnCore st endpointId ops.caller caller.cspaceRoot msg := rfl

/-- **WS-RR RR7.11**: and it declares exactly when the caller resolves, an
endpoint is named, and the message is known.

The message conjunct is the load-bearing one: without it the arm would have to
guess whether capabilities travel, and the capless guess is a footprint that
omits the receiver's CSpace root and the state-level lock on precisely the path
that writes them. -/
theorem lockSetForSyscall_send_isSome_iff
    (ops : SyscallLockOperands) (st : SystemState) :
    (lockSetForSyscall .send ops st).isSome
      ↔ (st.getTcb? ops.caller).isSome ∧ ops.targetObject.isSome ∧ ops.message.isSome := by
  unfold lockSetForSyscall
  cases st.getTcb? ops.caller <;> cases ops.targetObject <;> cases ops.message <;> simp

/-- **WS-RR RR7.11**: `.call` is wired to the resolved call footprint. -/
@[simp] theorem lockSetForSyscall_call
    (ops : SyscallLockOperands) (st : SystemState) :
    lockSetForSyscall .call ops st
      = (st.getTcb? ops.caller).bind fun caller =>
          ops.targetObject.bind fun endpointId =>
            ops.message.map fun msg =>
              lockSet_endpointCallOnCore st endpointId ops.caller caller.cspaceRoot msg := rfl

/-- **WS-RR RR7.11**: and it declares under the same three conditions as
`.send`, because it carries capabilities under the same rule. -/
theorem lockSetForSyscall_call_isSome_iff
    (ops : SyscallLockOperands) (st : SystemState) :
    (lockSetForSyscall .call ops st).isSome
      ↔ (st.getTcb? ops.caller).isSome ∧ ops.targetObject.isSome ∧ ops.message.isSome := by
  unfold lockSetForSyscall
  cases st.getTcb? ops.caller <;> cases ops.targetObject <;> cases ops.message <;> simp

/-- **WS-RR RR7.11**: `.receive` is wired to the resolved receive footprint. -/
@[simp] theorem lockSetForSyscall_receive
    (ops : SyscallLockOperands) (st : SystemState) :
    lockSetForSyscall .receive ops st
      = (st.getTcb? ops.caller).bind fun caller =>
          ops.targetObject.map fun endpointId =>
            lockSet_endpointReceiveOnCore st endpointId ops.caller caller.cspaceRoot
              ops.targetReply := rfl

/-- **WS-RR RR7.11**: and it declares without a message, because what a receive
installs comes from the parked sender the endpoint already names.

`targetReply` is *not* a condition: a plain receive supplies none and its
footprint correctly declares no reply lock, since a plain receive links no
Reply object. -/
theorem lockSetForSyscall_receive_isSome_iff
    (ops : SyscallLockOperands) (st : SystemState) :
    (lockSetForSyscall .receive ops st).isSome
      ↔ (st.getTcb? ops.caller).isSome ∧ ops.targetObject.isSome := by
  unfold lockSetForSyscall
  cases st.getTcb? ops.caller <;> cases ops.targetObject <;> simp

/-- **WS-RR RR7.11**: `.reply` is wired to the resolved reply footprint, at the
thread the reply capability answers. -/
@[simp] theorem lockSetForSyscall_reply
    (ops : SyscallLockOperands) (st : SystemState) :
    lockSetForSyscall .reply ops st
      = (st.getTcb? ops.caller).bind fun caller =>
          ops.targetReply.bind fun rid =>
            (replyAnsweredCaller? st rid).map fun answered =>
              lockSet_endpointReplyOnCore st ops.caller caller.cspaceRoot answered := rfl

/-- **WS-RR RR7.11**: and it declares exactly when the reply capability resolves
to a *linked* Reply object — the same condition the live arm admits, which is
why a dangling or unlinked reply declares nothing rather than a footprint for a
syscall that will answer `.replyCapInvalid`. -/
theorem lockSetForSyscall_reply_isSome_iff
    (ops : SyscallLockOperands) (st : SystemState) :
    (lockSetForSyscall .reply ops st).isSome
      ↔ (st.getTcb? ops.caller).isSome ∧
        (ops.targetReply.bind (replyAnsweredCaller? st)).isSome := by
  unfold lockSetForSyscall
  cases st.getTcb? ops.caller with
  | none => simp
  | some _ =>
    cases hR : ops.targetReply with
    | none => simp
    | some rid => cases replyAnsweredCaller? st rid <;> simp

/-- **WS-RR RR7.11**: `.replyRecv` is wired to the resolved fused footprint. -/
@[simp] theorem lockSetForSyscall_replyRecv
    (ops : SyscallLockOperands) (st : SystemState) :
    lockSetForSyscall .replyRecv ops st
      = (st.getTcb? ops.caller).bind fun caller =>
          ops.targetObject.bind fun endpointId =>
            ops.targetReply.bind fun rid =>
              (replyAnsweredCaller? st rid).map fun prevCaller =>
                lockSet_endpointReplyRecvOnCore st ops.caller caller.cspaceRoot prevCaller
                  endpointId := rfl

/-- **WS-RR RR7.11**: and it declares when *both* of its operands resolve — the
endpoint it will receive on next and the reply object it answers first. A
syscall that names two objects needs both, which is the reason
`SyscallLockOperands` carries them in separate fields. -/
theorem lockSetForSyscall_replyRecv_isSome_iff
    (ops : SyscallLockOperands) (st : SystemState) :
    (lockSetForSyscall .replyRecv ops st).isSome
      ↔ (st.getTcb? ops.caller).isSome ∧ ops.targetObject.isSome ∧
        (ops.targetReply.bind (replyAnsweredCaller? st)).isSome := by
  unfold lockSetForSyscall
  cases st.getTcb? ops.caller with
  | none => simp
  | some _ =>
    cases ops.targetObject with
    | none => simp
    | some _ =>
      cases hR : ops.targetReply with
      | none => simp
      | some rid => cases replyAnsweredCaller? st rid <;> simp

/-- **WS-RR RR7.11**: `.notificationSignal` is wired to the bound-delivery-aware
resolved signal footprint. -/
@[simp] theorem lockSetForSyscall_notificationSignal
    (ops : SyscallLockOperands) (st : SystemState) :
    lockSetForSyscall .notificationSignal ops st
      = (st.getTcb? ops.caller).bind fun caller =>
          ops.targetObject.map fun notificationId =>
            lockSet_notificationSignalOnCore st notificationId ops.caller
              caller.cspaceRoot := rfl

/-- **WS-RR RR7.11**: and it declares whenever the caller resolves and a
notification is named. -/
theorem lockSetForSyscall_notificationSignal_isSome_iff
    (ops : SyscallLockOperands) (st : SystemState) :
    (lockSetForSyscall .notificationSignal ops st).isSome
      ↔ (st.getTcb? ops.caller).isSome ∧ ops.targetObject.isSome := by
  unfold lockSetForSyscall
  cases st.getTcb? ops.caller <;> cases ops.targetObject <;> simp

/-- **WS-RR RR7.11**: `.notificationWait` is wired to the resolved wait
footprint — the one IPC footprint with no state-dependent member, so its
resolver takes no state. -/
@[simp] theorem lockSetForSyscall_notificationWait
    (ops : SyscallLockOperands) (st : SystemState) :
    lockSetForSyscall .notificationWait ops st
      = (st.getTcb? ops.caller).bind fun caller =>
          ops.targetObject.map fun notificationId =>
            lockSet_notificationWaitOnCore notificationId ops.caller caller.cspaceRoot := rfl

/-- **WS-RR RR7.11**: and it declares under the same two conditions. -/
theorem lockSetForSyscall_notificationWait_isSome_iff
    (ops : SyscallLockOperands) (st : SystemState) :
    (lockSetForSyscall .notificationWait ops st).isSome
      ↔ (st.getTcb? ops.caller).isSome ∧ ops.targetObject.isSome := by
  unfold lockSetForSyscall
  cases st.getTcb? ops.caller <;> cases ops.targetObject <;> simp

/-- **WS-RR RR7.11**: every declared arm needs the caller's own TCB.

The one condition all eight share, and the reason is structural rather than
incidental: a footprint's CNode member is the **caller's** CSpace root — the
root `syscallLookupCap` resolves the invoked capability through — so a caller
that does not resolve to a TCB leaves the footprint unable to name the CNode the
syscall reads. Declaring the rest of the members anyway would be a footprint
with a hole in it exactly where capability resolution happens. -/
theorem lockSetForSyscall_isSome_implies_caller_resolves
    (sid : SyscallId) (ops : SyscallLockOperands) (st : SystemState)
    (h : (lockSetForSyscall sid ops st).isSome) :
    (st.getTcb? ops.caller).isSome := by
  cases hTcb : st.getTcb? ops.caller with
  | some _ => simp
  | none =>
    exfalso
    cases sid <;>
      simp_all [lockSetForSyscall, suspendFootprintOf, Option.bind]
    all_goals
      first
        | exact h
        | (cases hT : ops.targetThread <;> simp_all)

/-! ## WS-RR RR7.11 — coverage: the declared footprint contains the writes

The dispatch pins above say *which* footprint each arm declares. These say what
that footprint is worth: for each arm, the objects the transition writes have
their locks in the set a bracket would acquire. That is the property a 2PL
consumer needs, and without it a declaration is a set of locks with no stated
relation to the operation — which is exactly the "false footprint" the module
docstring refuses.

Stated as "the resolved set contains this member", one member per write, because
that is the form the consumer asks in: it holds a set and is about to write an
object. The two capability-transfer arms additionally get the contrapositive
*changed ⇒ declared* form from RR7.8, which is stronger — it quantifies over
every object rather than over the members someone listed.
-/

/-- **WS-RR RR7.11**: at resolved operands, `.send` declares exactly the send
footprint of the endpoint it names. -/
theorem lockSetForSyscall_send_eq
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (msg : IpcMessage)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hMsg : ops.message = some msg) :
    lockSetForSyscall .send ops st
      = some (lockSet_endpointSendOnCore st endpointId ops.caller caller.cspaceRoot msg) := by
  unfold lockSetForSyscall
  rw [hTcb, hEp, hMsg]; rfl

/-- **WS-RR RR7.11**: and its declared set covers the two writes every send
performs — the sender's own TCB (it blocks, or is left runnable, on its own
core) and the endpoint queue the rendezvous mutates. -/
theorem lockSetForSyscall_send_covers_writes
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (msg : IpcMessage) (S : LockSet)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hMsg : ops.message = some msg)
    (hDecl : lockSetForSyscall .send ops st = some S) :
    (tcbLock ops.caller, AccessMode.write) ∈ S.pairs ∧
    (endpointLock endpointId, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_send_eq ops st caller endpointId msg hTcb hEp hMsg] at hDecl
  cases hDecl
  exact ⟨lockSet_endpointSend_caller_tcb_write_mem _ _ _ _ _,
         lockSet_endpointSend_endpoint_write_mem _ _ _ _ _⟩

/-- **WS-RR RR7.11**: and, when the message carries capabilities, the receiver's
CSpace root and the state-level lock the CDT edge needs. -/
theorem lockSetForSyscall_send_covers_capsWrites
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (msg : IpcMessage) (S : LockSet) (recvRoot : ObjId)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hMsg : ops.message = some msg)
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot)
    (hDecl : lockSetForSyscall .send ops st = some S) :
    (cnodeLock recvRoot, AccessMode.write) ∈ S.pairs ∧
    (stateLevelLock, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_send_eq ops st caller endpointId msg hTcb hEp hMsg] at hDecl
  cases hDecl
  exact ⟨lockSet_endpointSendOnCore_covers_capsDestination _ _ _ _ _ _ hDest,
         lockSet_endpointSendOnCore_covers_cdt _ _ _ _ _ _ hDest⟩

/-- **WS-RR RR7.11**: at resolved operands, `.call` declares the call
footprint. -/
theorem lockSetForSyscall_call_eq
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (msg : IpcMessage)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hMsg : ops.message = some msg) :
    lockSetForSyscall .call ops st
      = some (lockSet_endpointCallOnCore st endpointId ops.caller caller.cspaceRoot msg) := by
  unfold lockSetForSyscall
  rw [hTcb, hEp, hMsg]; rfl

/-- **WS-RR RR7.11**: `.call`'s two unconditional writes. -/
theorem lockSetForSyscall_call_covers_writes
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (msg : IpcMessage) (S : LockSet)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hMsg : ops.message = some msg)
    (hDecl : lockSetForSyscall .call ops st = some S) :
    (tcbLock ops.caller, AccessMode.write) ∈ S.pairs ∧
    (endpointLock endpointId, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_call_eq ops st caller endpointId msg hTcb hEp hMsg] at hDecl
  cases hDecl
  exact ⟨lockSet_endpointCall_caller_tcb_write_mem_unconditional _ _ _ _ _ _ _,
         lockSet_endpointCall_endpoint_write_mem _ _ _ _ _ _ _⟩

/-- **WS-RR RR7.11**: and `.call`'s capability-transfer writes. -/
theorem lockSetForSyscall_call_covers_capsWrites
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (msg : IpcMessage) (S : LockSet) (recvRoot : ObjId)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hMsg : ops.message = some msg)
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot)
    (hDecl : lockSetForSyscall .call ops st = some S) :
    (cnodeLock recvRoot, AccessMode.write) ∈ S.pairs ∧
    (stateLevelLock, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_call_eq ops st caller endpointId msg hTcb hEp hMsg] at hDecl
  cases hDecl
  exact ⟨lockSet_endpointCallOnCore_covers_capsDestination _ _ _ _ _ _ hDest,
         lockSet_endpointCallOnCore_covers_cdt _ _ _ _ _ _ hDest⟩

/-- **WS-RR RR7.11**: at resolved operands, `.receive` declares the receive
footprint. -/
theorem lockSetForSyscall_receive_eq
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB) (endpointId : ObjId)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId) :
    lockSetForSyscall .receive ops st
      = some (lockSet_endpointReceiveOnCore st endpointId ops.caller caller.cspaceRoot
                ops.targetReply) := by
  unfold lockSetForSyscall
  rw [hTcb, hEp]; rfl

/-- **WS-RR RR7.11**: `.receive`'s two unconditional writes. -/
theorem lockSetForSyscall_receive_covers_writes
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (S : LockSet)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hDecl : lockSetForSyscall .receive ops st = some S) :
    (tcbLock ops.caller, AccessMode.write) ∈ S.pairs ∧
    (endpointLock endpointId, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_receive_eq ops st caller endpointId hTcb hEp] at hDecl
  cases hDecl
  exact ⟨lockSet_endpointReceive_caller_tcb_write_mem _ _ _ _ _ _,
         lockSet_endpointReceive_endpoint_write_mem _ _ _ _ _ _⟩

/-- **WS-RR RR7.11**: and the receive-side capability install's two writes — the
receiver's own CSpace root, and the state-level lock the CDT edge needs.

The second is this cut's finding: `ipcTransferSingleCap` is one function, so a
receive that dequeues a caps-bearing sender writes the same derivation structure
a send does, and the receiving footprints declared it on neither. -/
theorem lockSetForSyscall_receive_covers_capsWrites
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (S : LockSet)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hCaps : receiveInstallsCaps st endpointId = true)
    (hDecl : lockSetForSyscall .receive ops st = some S) :
    (cnodeLock caller.cspaceRoot, AccessMode.write) ∈ S.pairs ∧
    (stateLevelLock, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_receive_eq ops st caller endpointId hTcb hEp] at hDecl
  cases hDecl
  exact ⟨lockSet_endpointReceiveOnCore_covers_capsDestination _ _ _ _ _ hCaps,
         lockSet_endpointReceiveOnCore_covers_cdt _ _ _ _ _ hCaps⟩

/-- **WS-RR RR7.11**: at resolved operands, `.reply` declares the reply
footprint at the thread its capability answers. -/
theorem lockSetForSyscall_reply_eq
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (rid : ReplyId) (answered : ThreadId)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hRid : ops.targetReply = some rid)
    (hAns : replyAnsweredCaller? st rid = some answered) :
    lockSetForSyscall .reply ops st
      = some (lockSet_endpointReplyOnCore st ops.caller caller.cspaceRoot answered) := by
  simp only [lockSetForSyscall, hTcb, hRid, Option.bind_some, hAns, Option.map_some]

/-- **WS-RR RR7.11**: `.reply` declares the answered caller's TCB (woken out of
`blockedOnReply`) and the Reply object the delivery consumes. -/
theorem lockSetForSyscall_reply_covers_writes
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (rid : ReplyId) (answered : ThreadId) (S : LockSet)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hRid : ops.targetReply = some rid)
    (hAns : replyAnsweredCaller? st rid = some answered)
    (hDecl : lockSetForSyscall .reply ops st = some S) :
    (tcbLock answered, AccessMode.write) ∈ S.pairs ∧
    (∀ linked, (st.getTcb? answered).bind (·.replyObject) = some linked →
      (replyLock linked, AccessMode.write) ∈ S.pairs) := by
  rw [lockSetForSyscall_reply_eq ops st caller rid answered hTcb hRid hAns] at hDecl
  cases hDecl
  refine ⟨lockSet_endpointReply_target_tcb_write_mem _ _ _ _ _ _, ?_⟩
  intro linked hLinked
  simp only [lockSet_endpointReplyOnCore, hLinked]
  exact lockSet_endpointReply_reply_write_mem _ _ _ _ _ _

/-- **WS-RR RR7.11**: at resolved operands, `.replyRecv` declares the fused
footprint. -/
theorem lockSetForSyscall_replyRecv_eq
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (rid : ReplyId) (prevCaller : ThreadId)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hRid : ops.targetReply = some rid)
    (hAns : replyAnsweredCaller? st rid = some prevCaller) :
    lockSetForSyscall .replyRecv ops st
      = some (lockSet_endpointReplyRecvOnCore st ops.caller caller.cspaceRoot prevCaller
                endpointId) := by
  simp only [lockSetForSyscall, hTcb, hEp, hRid, Option.bind_some, hAns, Option.map_some]

/-- **WS-RR RR7.11**: `.replyRecv`'s three unconditional writes — its own TCB
(it replies, then receives), the answered caller's, and the endpoint. -/
theorem lockSetForSyscall_replyRecv_covers_writes
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (rid : ReplyId) (prevCaller : ThreadId) (S : LockSet)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hRid : ops.targetReply = some rid)
    (hAns : replyAnsweredCaller? st rid = some prevCaller)
    (hDecl : lockSetForSyscall .replyRecv ops st = some S) :
    (tcbLock ops.caller, AccessMode.write) ∈ S.pairs ∧
    (tcbLock prevCaller, AccessMode.write) ∈ S.pairs ∧
    (endpointLock endpointId, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_replyRecv_eq ops st caller endpointId rid prevCaller
    hTcb hEp hRid hAns] at hDecl
  cases hDecl
  exact ⟨lockSet_replyRecv_caller_tcb_write_mem _ _ _ _ _ _ _ _ _,
         lockSet_replyRecv_target_tcb_write_mem _ _ _ _ _ _ _ _ _,
         lockSet_replyRecv_endpoint_write_mem _ _ _ _ _ _ _ _ _⟩

/-- **WS-RR RR7.11**: and its receive leg's capability install, which writes the
same CDT structure a send's does. -/
theorem lockSetForSyscall_replyRecv_covers_capsWrites
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (rid : ReplyId) (prevCaller : ThreadId) (S : LockSet)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hRid : ops.targetReply = some rid)
    (hAns : replyAnsweredCaller? st rid = some prevCaller)
    (hCaps : receiveInstallsCaps st endpointId = true)
    (hDecl : lockSetForSyscall .replyRecv ops st = some S) :
    (cnodeLock caller.cspaceRoot, AccessMode.write) ∈ S.pairs ∧
    (stateLevelLock, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_replyRecv_eq ops st caller endpointId rid prevCaller
    hTcb hEp hRid hAns] at hDecl
  cases hDecl
  refine ⟨?_, lockSet_endpointReplyRecvOnCore_covers_cdt _ _ _ _ _ hCaps⟩
  simp only [lockSet_endpointReplyRecvOnCore, hCaps]
  exact lockSet_replyRecv_capsInstall_write_mem _ _ _ _ _ _ _ _

/-- **WS-RR RR7.11**: at resolved operands, `.notificationSignal` declares the
bound-delivery-aware signal footprint. -/
theorem lockSetForSyscall_notificationSignal_eq
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB) (notificationId : ObjId)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hNtfn : ops.targetObject = some notificationId) :
    lockSetForSyscall .notificationSignal ops st
      = some (lockSet_notificationSignalOnCore st notificationId ops.caller
                caller.cspaceRoot) := by
  unfold lockSetForSyscall
  rw [hTcb, hNtfn]; rfl

/-- **WS-RR RR7.11**: the signal's own write — the notification whose waiter
list or badge it mutates — is declared on both delivery paths. -/
theorem lockSetForSyscall_notificationSignal_covers_writes
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (notificationId : ObjId) (S : LockSet)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hNtfn : ops.targetObject = some notificationId)
    (hDecl : lockSetForSyscall .notificationSignal ops st = some S) :
    (notificationLock notificationId, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_notificationSignal_eq ops st caller notificationId hTcb hNtfn] at hDecl
  cases hDecl
  unfold lockSet_notificationSignalOnCore
  cases boundDeliveryTarget? st notificationId with
  | none => exact lockSet_notificationSignal_notification_write_mem _ _ _ _ _ _
  | some _ => exact lockSet_notificationSignal_notification_write_mem _ _ _ _ _ _

/-- **WS-RR RR7.11**: and the bound-delivery pair, on the path that takes it —
the bound TCB the badge is delivered to, and the endpoint it is dequeued from.

`lockSet_notificationSignalOnCore` folds these in from `boundDeliveryTarget?`;
this is the statement that the fold reaches the resolver's output, which is
where a bracket reads it. -/
theorem lockSetForSyscall_notificationSignal_covers_boundDelivery
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (notificationId : ObjId) (S : LockSet) (boundTcb : ThreadId) (epId : ObjId)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hNtfn : ops.targetObject = some notificationId)
    (hBound : boundDeliveryTarget? st notificationId = some (boundTcb, epId))
    (hDecl : lockSetForSyscall .notificationSignal ops st = some S) :
    (tcbLock boundTcb, AccessMode.write) ∈ S.pairs ∧
    (endpointLock epId, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_notificationSignal_eq ops st caller notificationId hTcb hNtfn] at hDecl
  cases hDecl
  exact ⟨lockSet_notificationSignalOnCore_bound_tcb_write_mem _ _ _ _ _ _ hBound,
         lockSet_notificationSignalOnCore_bound_endpoint_write_mem _ _ _ _ _ _ hBound⟩

/-- **WS-RR RR7.11**: at resolved operands, `.notificationWait` declares the
wait footprint. -/
theorem lockSetForSyscall_notificationWait_eq
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB) (notificationId : ObjId)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hNtfn : ops.targetObject = some notificationId) :
    lockSetForSyscall .notificationWait ops st
      = some (lockSet_notificationWaitOnCore notificationId ops.caller caller.cspaceRoot) := by
  unfold lockSetForSyscall
  rw [hTcb, hNtfn]; rfl

/-- **WS-RR RR7.11**: the wait's two writes — the caller's own TCB (it blocks,
or consumes a pending badge into its message field) and the notification. -/
theorem lockSetForSyscall_notificationWait_covers_writes
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (notificationId : ObjId) (S : LockSet)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hNtfn : ops.targetObject = some notificationId)
    (hDecl : lockSetForSyscall .notificationWait ops st = some S) :
    (tcbLock ops.caller, AccessMode.write) ∈ S.pairs ∧
    (notificationLock notificationId, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_notificationWait_eq ops st caller notificationId hTcb hNtfn] at hDecl
  cases hDecl
  exact ⟨lockSet_notificationWait_caller_tcb_write_mem _ _ _,
         lockSet_notificationWait_notification_write_mem _ _ _⟩

/-- **WS-RR RR7.11, the capstone: every object a caps-carrying `.send` changes
has its lock declared write-mode in the footprint this resolver hands the
bracket.**

RR7.8's `endpointSendDualWithCaps_object_writes_declared` stated this at
`lockSet_endpointSendOnCore`; this is the same fact where a consumer meets it —
at `lockSetForSyscall`'s output, which is what a bracket actually acquires.
Stated *changed ⇒ declared* rather than member-by-member, so it quantifies over
every object rather than over the ones someone remembered to list. -/
theorem lockSetForSyscall_send_object_writes_declared
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (msg : IpcMessage) (S : LockSet)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : Slot) (st' st'' : SystemState) (recvRoot : ObjId)
    (summary : CapTransferSummary) (oid : ObjId)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hMsg : ops.message = some msg)
    (hDecl : lockSetForSyscall .send ops st = some S)
    (hSend : endpointSendDual endpointId ops.caller
        { msg with capsGranted := endpointRights.mem .grant } st = .ok ((), st'))
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot)
    (hObjInv : st'.objects.invExt)
    (hStep : endpointSendDualWithCaps endpointId ops.caller msg endpointRights
        receiverSlotBase st = .ok (summary, st''))
    (hChanged : st''.objects[oid]? ≠ st'.objects[oid]?) :
    (cnodeLock oid, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_send_eq ops st caller endpointId msg hTcb hEp hMsg] at hDecl
  cases hDecl
  exact endpointSendDualWithCaps_object_writes_declared endpointId ops.caller msg
    endpointRights caller.cspaceRoot receiverSlotBase st st' st''
    recvRoot summary oid hSend hDest hObjInv hStep hChanged

/-- **WS-RR RR7.11**: and the same capstone on `.call` — the same transfer,
reached through the same resolver, declared in the same members. -/
theorem lockSetForSyscall_call_object_writes_declared
    (ops : SyscallLockOperands) (st : SystemState) (caller : TCB)
    (endpointId : ObjId) (msg : IpcMessage) (S : LockSet)
    (endpointRights : AccessRightSet)
    (receiverSlotBase : Slot) (st' st'' : SystemState) (recvRoot : ObjId)
    (summary : CapTransferSummary) (oid : ObjId)
    (hTcb : st.getTcb? ops.caller = some caller)
    (hEp : ops.targetObject = some endpointId)
    (hMsg : ops.message = some msg)
    (hDecl : lockSetForSyscall .call ops st = some S)
    (hCall : endpointCall endpointId ops.caller
        { msg with capsGranted := endpointRights.mem .grant } st = .ok ((), st'))
    (hDest : rendezvousCapsDestination? st endpointId msg = some recvRoot)
    (hObjInv : st'.objects.invExt)
    (hStep : endpointCallWithCaps endpointId ops.caller msg endpointRights
        receiverSlotBase st = .ok (summary, st''))
    (hChanged : st''.objects[oid]? ≠ st'.objects[oid]?) :
    (cnodeLock oid, AccessMode.write) ∈ S.pairs := by
  rw [lockSetForSyscall_call_eq ops st caller endpointId msg hTcb hEp hMsg] at hDecl
  cases hDecl
  exact endpointCallWithCaps_object_writes_declared endpointId ops.caller msg
    endpointRights caller.cspaceRoot receiverSlotBase st st' st''
    recvRoot summary oid hCall hDest hObjInv hStep hChanged

/-! ## The declared arms, and the negative that keeps the rest honest -/

/-- **WS-RR RR7.11**: the syscalls whose footprint this module declares.

A second enumeration beside `lockSetForSyscall`'s own `match`, and it is here
because the negative below has to name a set — so what matters is which way it
can drift. Converting an arm to `some` without listing it here breaks
`lockSetForSyscall_undeclared_none` at elaboration, so that direction is
mechanically closed. The other direction — listing an arm that still answers
`none` — is closed by the per-arm characterisations that follow
(`lockSetForSyscall_*_isSome_iff`): each states the exact condition on operands
and pre-state under which its arm declares, so an arm that had quietly become
unconditionally `none` could not satisfy its own `iff`.

There are `SyscallId.count = 35` arms; eight are declared and twenty-seven
answer `none`. -/
def declaredFootprintSyscall : SyscallId → Bool
  | .tcbSuspend
  | .send | .receive | .call | .reply | .replyRecv
  | .notificationSignal | .notificationWait => true
  | .cspaceMint | .cspaceCopy | .cspaceMove | .cspaceDelete
  | .mintReplyCap
  | .lifecycleRetype
  | .vspaceMap | .vspaceUnmap | .vspaceUnifyInstruction
  | .serviceRegister | .serviceRevoke | .serviceQuery
  | .schedContextConfigure | .schedContextBind | .schedContextUnbind
  | .tcbResume | .tcbSetPriority | .tcbSetMCPriority
  | .tcbSetIPCBuffer | .tcbSetAffinity | .tcbSetFaultHandler
  | .tcbBindNotification | .tcbUnbindNotification
  | .declassify | .declassifySignal
  | .auditRead | .auditDrain => false

/-- **WS-RR RR7.11**: at *thread-directed* operands only `.tcbSuspend` declares.

The seven IPC arms are object- or reply-directed, so `ofThreadTarget` leaves
every operand they read absent and each answers `none` — the fail-closed
direction, reached without any of them having to be listed.

This is what a caller that resolves only a thread target gets, and it is the
shape SM8.D's `declaredLockSetForEntry` is in: that entry resolver turns a
capability into a `ThreadId`, so the arms it can declare are exactly the
thread-directed ones. Supplying the endpoint, reply and message operands at the
**production** entry is WS-RR RR7.12's row, which is where the `withLockSet`
bracket that consumes them lands. -/
theorem lockSetForSyscall_ofThreadTarget_undeclared
    (sid : SyscallId) (callerTid targetTid : ThreadId) (st : SystemState)
    (h : sid ≠ .tcbSuspend) :
    lockSetForSyscall sid (.ofThreadTarget callerTid targetTid) st = none := by
  cases sid <;>
    first
      | rfl
      | exact absurd rfl h
      | simp [lockSetForSyscall, SyscallLockOperands.ofThreadTarget]

/-- **WS-SM SM3.C.9 / WS-RR RR7.11**: every arm this module has not declared is
undeclared, whatever the operands and whatever the state.

The load-bearing direction. A caller reading `some S` treats `S` as the
complete set of objects the transition writes, so an arm that returned a
footprint before its coverage proof existed would hand out exclusion the
runtime never established. This is the negative that keeps the migration
honest: adding the next declared arm must change `declaredFootprintSyscall`,
and forgetting to stops this elaborating.

RR7.11 restated it over the boolean rather than over `sid ≠ .tcbSuspend`: with
eight declared arms the inequality form would take eight hypotheses, and a
caller that supplied seven of them would be proving something weaker while
looking the same. -/
theorem lockSetForSyscall_undeclared_none
    (sid : SyscallId) (ops : SyscallLockOperands) (st : SystemState)
    (h : declaredFootprintSyscall sid = false) :
    lockSetForSyscall sid ops st = none := by
  cases sid <;> first | rfl | exact absurd h (by simp [declaredFootprintSyscall])

/-- **WS-RR RR7.11**: and the eight declared arms are exactly the ones the
kernel's hot path runs — the seven IPC syscalls plus SM3.C.9's suspend.

Stated by evaluation over the boolean, so a cut that widens or narrows the
declared set has to come here and say so. -/
theorem declaredFootprintSyscall_declared_set :
    declaredFootprintSyscall .tcbSuspend = true ∧
    declaredFootprintSyscall .send = true ∧
    declaredFootprintSyscall .receive = true ∧
    declaredFootprintSyscall .call = true ∧
    declaredFootprintSyscall .reply = true ∧
    declaredFootprintSyscall .replyRecv = true ∧
    declaredFootprintSyscall .notificationSignal = true ∧
    declaredFootprintSyscall .notificationWait = true ∧
    ((List.range SyscallId.count).filterMap SyscallId.ofNat?).countP
      declaredFootprintSyscall = 8 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  decide

/-- **WS-SM SM3.C.9**: the suspend footprint resolves exactly when the
target names a TCB.

`none` is not a failure mode here — a target that is not a TCB has no
suspend transition to bound, so there is no footprint to declare and the
caller correctly falls back. -/
theorem suspendFootprintOf_isSome_iff
    (st : SystemState) (callerTid targetTid : ThreadId) :
    (suspendFootprintOf st callerTid targetTid).isSome
      ↔ (∃ caller, st.getTcb? callerTid = some caller) ∧
        ∃ victim, st.getTcb? targetTid = some victim := by
  unfold suspendFootprintOf
  constructor
  · intro h
    split at h
    · next caller victim hc hv => exact ⟨⟨caller, hc⟩, victim, hv⟩
    · simp at h
  · rintro ⟨⟨caller, hc⟩, victim, hv⟩
    rw [hc, hv]
    simp

end SeLe4n.Kernel.Concurrency
