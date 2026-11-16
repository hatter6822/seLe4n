-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations

/-!
# The operation a syscall selects (WS-SX SX6)

seL4 selects what a syscall does in two steps.  `handleSyscall` dispatches on
the syscall number, one of seL4-MCS's eleven (`Syscall`).  An invoking
syscall (`Call`, `Send`, `NBSend`, and the send half of `ReplyRecv`,
`NBSendRecv` and `NBSendWait`) then looks the capability up
(`lookupCapAndSlot`) and `decodeInvocation` switches on its type: an
endpoint is sent to, a notification signalled, a reply capability replied
through, and every other object is decoded by the message label
(`invocation_label`).  A receiving syscall (`Recv`, `NBRecv`, `Wait`,
`NBWait`, and the receive half of the compound ones) looks the capability up
and `handleRecv` switches on its type: an endpoint is received on and a
notification waited on.

`selectOperation` is that selection, a function of the syscall, the invoked
capability's type (`CapType`) and the label alone; `invokedCapType` reads the
type after the lookup.  No register value names an operation: the router and
the decode branch on the operation this selection answers
(`operationOf`).  A lookup that fails, or finds an empty slot, selects the
syscall's own IPC operation, whose gate then refuses it as seL4 does: a
capability fault for a failed lookup, `seL4_InvalidCapability` for an empty
slot.  A label no operation of the capability's type takes selects nothing,
and the entry refuses it as seL4's `decodeInvocation` does
(`seL4_IllegalOperation`, the model's `invalidSyscallNumber`).
-/

namespace SeLe4n.Model

open SeLe4n.Kernel

/-- **The invoked capability's type**, seL4's `cap_get_capType`: the
capability's target constructor and, for an object capability, the kind of
object it names (`none` when the store holds none). -/
inductive CapType where
  | object (kind : Option KernelObjectType)
  | replyCap
  | auditTrail
  | schedControl
  | irqControl
  | irqHandler
  | cnodeSlot
  deriving Repr, DecidableEq

/-- The type of a capability, its object's kind read in place. -/
@[inline] def CapType.ofCap (st : SystemState) (cap : Capability) : CapType :=
  match cap.target with
  | .object id => .object ((st.getObject? id).map KernelObject.objectType)
  | .replyCap _ => .replyCap
  | .auditTrail _ => .auditTrail
  | .schedControl _ => .schedControl
  | .irqControl _ => .irqControl
  | .irqHandler _ => .irqHandler
  | .cnodeSlotWord _ => .cnodeSlot

/-- The object kind each labelled operation invokes, by capability type: the
operation a label names is selected only on a capability of the type it takes
(seL4's per-object `decode*Invocation`). -/
def labelledOperationTakes (sid : SyscallId) : CapType → Bool
  | .object (some .cnode) => sid == .cspaceMint || sid == .cspaceCopy || sid == .cspaceMove ||
      sid == .cspaceDelete || sid == .cspaceRevoke || sid == .mintReplyCap || sid == .declassify
  | .object (some .untyped) => sid == .untypedRetype || sid == .declassify
  | .object (some .vspaceRoot) => sid == .vspaceMap || sid == .vspaceUnmap ||
      sid == .vspaceUnifyInstruction || sid == .declassify
  | .object (some .schedContext) => sid == .schedContextBind || sid == .schedContextUnbind ||
      sid == .schedContextConsumed || sid == .schedContextYieldTo || sid == .declassify
  | .object (some .tcb) => sid == .tcbSuspend || sid == .tcbResume || sid == .tcbSetPriority ||
      sid == .tcbSetMCPriority || sid == .tcbSetIPCBuffer || sid == .tcbSetFaultHandler ||
      sid == .tcbSetAffinity ||
      sid == .tcbSetSpace || sid == .tcbBindNotification || sid == .tcbUnbindNotification ||
      sid == .declassify
  | .object (some .pageTable) => sid == .pageTableMap || sid == .pageTableUnmap ||
      sid == .declassify
  | .object (some .reply) | .object (some .frame) => sid == .declassify
  | .object (some .endpoint) => sid == .serviceRegister || sid == .serviceRevoke ||
      sid == .serviceQuery || sid == .declassify
  | .object (some .notification) => sid == .declassifySignal || sid == .declassify
  | .object none => true
  | .replyCap => false
  | .auditTrail => sid == .auditRead || sid == .auditDrain
  | .schedControl => sid == .schedContextConfigure
  | .irqControl => sid == .irqControlGet
  | .irqHandler => sid == .irqHandlerAck || sid == .irqHandlerSetNotification ||
      sid == .irqHandlerClear
  | .cnodeSlot => false

/-- **seL4's `decodeInvocation` switch** for an invoking syscall whose IPC
operation is `base` (`.send` or `.call`): an endpoint is sent to and a
notification signalled, unless the label names a model-only operation that
capability takes (the service calls and the declassifications); a reply
capability is replied through; a failed lookup, an empty slot and a slot
capability select `base`, whose gate refuses them; every other type is decoded
by the label. -/
def invocationOperation (base : SyscallId) (ty : Option CapType) (label : Nat) :
    Option SyscallId :=
  match ty with
  | none | some .cnodeSlot => some base
  | some .replyCap => some .reply
  | some (.object (some .endpoint)) =>
      match SyscallId.ofLabel? label with
      | some op => if labelledOperationTakes op (.object (some .endpoint)) then some op else some base
      | none => some base
  | some (.object (some .notification)) =>
      match SyscallId.ofLabel? label with
      | some op =>
          if labelledOperationTakes op (.object (some .notification)) then some op
          else some .notificationSignal
      | none => some .notificationSignal
  | some t =>
      match SyscallId.ofLabel? label with
      | some op => if labelledOperationTakes op t then some op else none
      | none => none

/-- **seL4's `handleRecv` switch**: a notification is waited on; every other
type, a failed lookup and an empty slot select the receive, whose gate faults
on all but an endpoint. -/
def receiveOperation (ty : Option CapType) : SyscallId :=
  match ty with
  | some (.object (some .notification)) => .notificationWait
  | _ => .receive

/-- **The operation a syscall selects**, from the syscall, the type of the
capability its first phase invokes or receives on, and the label.  The
compound syscalls select their receive phase here; their invoking phase is
`invocationOperation` at the capability it names (`compoundSendPhase`), except
a `ReplyRecv` whose reply register names a reply capability (or none the
lookup finds) and whose capability register names an endpoint, which is the
model's fused reply-receive. -/
def Syscall.selectOperation (sys : Syscall) (ty : Option CapType) (label : Nat) :
    Option SyscallId :=
  match sys with
  | .yield => some .yield
  | .call => invocationOperation .call ty label
  | .send | .nbSend => invocationOperation .send ty label
  | .recv | .nbRecv | .wait | .nbWait | .nbSendRecv | .nbSendWait =>
      some (receiveOperation ty)
  | .replyRecv =>
      match receiveOperation ty with
      | .receive => some .replyRecv
      | op => some op

/-- **The capability type an address names** for the thread `tcb`: seL4's
`lookupSlot` at 64 bits from the thread's CSpace root, then the slot's
capability.  `none` when the lookup fails or the slot is empty. -/
def invokedCapType (st : SystemState) (tcb : TCB) (cptr : SeLe4n.CPtr) : Option CapType :=
  match lookupSlot tcb cptr st with
  | .error _ => none
  | .ok ref => (st.lookupSlotCap ref).map (CapType.ofCap st)

/-- The fused reply-receive applies when the reply register names a reply
capability or nothing the lookup finds. -/
@[inline] def replyRegisterFused (ty : Option CapType) : Bool :=
  match ty with
  | none | some .replyCap => true
  | _ => false

end SeLe4n.Model
