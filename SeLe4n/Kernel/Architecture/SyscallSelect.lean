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
# The operation a syscall selects (WS-SX SX7)

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
  | serviceRegistry
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
  | .serviceRegistry _ => .serviceRegistry
  | .cnodeSlotWord _ => .cnodeSlot

/-- The object kind each labelled operation invokes, by capability type: the
operation a label names is selected only on a capability of the type it takes
(seL4's per-object `decode*Invocation`). -/
def labelledOperationTakes (sid : SyscallId) : CapType → Bool
  | .object (some .cnode) => sid == .cspaceMint || sid == .cspaceCopy || sid == .cspaceMove ||
      sid == .cspaceDelete || sid == .cspaceRevoke || sid == .mintReplyCap
  | .object (some .untyped) => sid == .untypedRetype
  | .object (some .vspaceRoot) => sid == .vspaceUnmap || sid == .vspaceUnifyInstruction
  | .object (some .schedContext) => sid == .schedContextBind || sid == .schedContextUnbind ||
      sid == .schedContextConsumed || sid == .schedContextYieldTo
  | .object (some .tcb) => sid == .tcbSuspend || sid == .tcbResume || sid == .tcbSetPriority ||
      sid == .tcbSetMCPriority || sid == .tcbSetIPCBuffer || sid == .tcbSetAffinity ||
      sid == .tcbSetSpace || sid == .tcbBindNotification || sid == .tcbUnbindNotification
  | .object (some .pageTable) => sid == .pageTableMap || sid == .pageTableUnmap
  -- seL4's `seL4_ARM_Page_Map` is invoked on the frame capability (WS-SX SX6.3).
  | .object (some .frame) => sid == .vspaceMap
  | .object (some .reply) => false
  -- seL4: Send or Call on an endpoint is IPC and Send on a notification
  -- signals, whatever the label; the label is the receiver's data.  No label
  -- selects an operation on either (`invocationOperation_endpoint`,
  -- `invocationOperation_notification`).
  | .object (some .endpoint) | .object (some .notification) => false
  | .object none => true
  | .replyCap => false
  -- The declassifications are invoked on the audit-trail capability, their
  -- target extra capability 0 (WS-SX SX6.7).
  | .auditTrail => sid == .auditRead || sid == .auditDrain || sid == .declassify ||
      sid == .declassifySignal
  | .serviceRegistry => sid == .serviceRegister || sid == .serviceRevoke || sid == .serviceQuery
  | .schedControl => sid == .schedContextConfigure
  | .irqControl => sid == .irqControlGet
  | .irqHandler => sid == .irqHandlerAck || sid == .irqHandlerSetNotification ||
      sid == .irqHandlerClear
  | .cnodeSlot => false

/-- **seL4's `decodeInvocation` switch** for an invoking syscall whose IPC
operation is `base` (`.send` or `.call`): an endpoint is sent to and a
notification signalled, whatever the label, which is message data the
receiver reads; a reply
capability is replied through; a failed lookup, an empty slot and a slot
capability select `base`, whose gate refuses them; every other type is decoded
by the label. -/
def invocationOperation (base : SyscallId) (ty : Option CapType) (label : Nat) :
    Option SyscallId :=
  match ty with
  | none | some .cnodeSlot => some base
  | some .replyCap => some .reply
  | some (.object (some .endpoint)) => some base
  | some (.object (some .notification)) => some .notificationSignal
  | some t =>
      match SyscallId.ofLabel? label with
      | some op => if labelledOperationTakes op t then some op else none
      | none => none

/-- **The label selects nothing on an endpoint**: Send, NBSend and Call on an
endpoint capability are IPC whatever the label (seL4's `decodeInvocation`,
`performInvocation_Endpoint`), so a message cannot be turned into a kernel
operation by its label. -/
theorem invocationOperation_endpoint (base : SyscallId) (label : Nat) :
    invocationOperation base (some (.object (some .endpoint))) label = some base := rfl

/-- **The label selects nothing on a notification**: Send, NBSend and Call on a
notification capability signal it whatever the label (`sendSignal`). -/
theorem invocationOperation_notification (base : SyscallId) (label : Nat) :
    invocationOperation base (some (.object (some .notification))) label =
      some .notificationSignal := rfl

/-- `labelledOperationTakes` answers `false` on both IPC object kinds, so no
labelled operation (model-only ones included) is ever selected on them. -/
theorem labelledOperationTakes_ipc (sid : SyscallId) :
    labelledOperationTakes sid (.object (some .endpoint)) = false ∧
      labelledOperationTakes sid (.object (some .notification)) = false := ⟨rfl, rfl⟩

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

/-- On an endpoint or a notification capability the operation every syscall
selects is independent of the label: Send/NBSend/Call send IPC, Send on a
notification signals, and the receiving syscalls receive or wait. -/
theorem selectOperation_label_independent_ipc (sys : Syscall) (k : KernelObjectType)
    (hk : k = .endpoint ∨ k = .notification) (l₁ l₂ : Nat) :
    sys.selectOperation (some (.object (some k))) l₁ =
      sys.selectOperation (some (.object (some k))) l₂ := by
  rcases hk with rfl | rfl <;> cases sys <;> rfl

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

/-- The label a message-info word carries: bits 12 and up (seL4's
`seL4_MessageInfo_t`), read as a number below `2 ^ 52`. -/
@[inline] def msgInfoWordLabel (w : UInt64) : Nat := (w >>> 12).toNat

/-- **The operation the trapped registers select** for the thread `tcb`
(seL4's `handleSyscall`, then `handleInvocation`'s `decodeInvocation` or
`handleRecv`'s capability switch): the syscall `x7` names (`Syscall.ofWord?`),
the type of the capability `x0` names, and the label `x1` carries.  `none`
when `x7` names none of the eleven syscalls or the label names no operation of
the capability's type. -/
@[inline] def selectedOperation (st : SystemState) (tcb : TCB)
    (layout : SeLe4n.SyscallRegisterLayout) (regs : SeLe4n.RegisterFile) : Option SyscallId :=
  match Syscall.ofWord? (SeLe4n.readRegWord regs layout.syscallNumReg) with
  | none => none
  | some sys =>
      sys.selectOperation
        (invokedCapType st tcb (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord regs layout.capPtrReg)))
        (msgInfoWordLabel (SeLe4n.readRegWord regs layout.msgInfoReg))

/-- **The internal code of the selected operation**, the number the router and
the decode branch on (`SyscallId.toNat`); `SyscallId.encodingBound`, which names
no operation, when nothing is selected, so the decode refuses the call
`invalidSyscallNumber`, as seL4's `decodeInvocation` refuses a label its
object does not take (`seL4_IllegalOperation`). -/
@[inline] def selectedOperationCode (st : SystemState) (tcb : TCB)
    (layout : SeLe4n.SyscallRegisterLayout) (regs : SeLe4n.RegisterFile) : Nat :=
  match selectedOperation st tcb layout regs with
  | some op => op.toNat
  | none => SyscallId.encodingBound

/-- A selected code names the operation selected, and no code names an
operation when none is selected. -/
theorem ofNat?_selectedOperationCode (st : SystemState) (tcb : TCB)
    (layout : SeLe4n.SyscallRegisterLayout) (regs : SeLe4n.RegisterFile) :
    SyscallId.ofNat? (selectedOperationCode st tcb layout regs) =
      selectedOperation st tcb layout regs := by
  unfold selectedOperationCode
  cases selectedOperation st tcb layout regs with
  | some op => exact SyscallId.ofNat_toNat op
  | none => rfl

/-- **The operation the thread `tid`'s trapped registers `regs` select**
(`selectedOperationCode`), read off its TCB in `st`; a thread the store holds no
TCB for selects nothing. -/
@[inline] def threadOperationCode (st : SystemState) (tid : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (regs : SeLe4n.RegisterFile) : Nat :=
  match st.getTcb? tid with
  | some tcb => selectedOperationCode st tcb layout regs
  | none => SyscallId.encodingBound

end SeLe4n.Model
