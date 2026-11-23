-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Capability.Operations
import SeLe4n.Kernel.Architecture.RegisterDecode

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

/-- The operations a label selects on an object of kind `k` (seL4's per-object
`decode*Invocation`). -/
def kindTakesLabel (sid : SyscallId) : KernelObjectType → Bool
  | .cnode => sid == .cspaceMint || sid == .cspaceCopy || sid == .cspaceMove ||
      sid == .cspaceDelete || sid == .cspaceRevoke || sid == .mintReplyCap
  | .untyped => sid == .untypedRetype
  | .vspaceRoot => sid == .vspaceUnifyInstruction
  | .schedContext => sid == .schedContextBind || sid == .schedContextUnbind ||
      sid == .schedContextUnbindObject || sid == .schedContextConsumed ||
      sid == .schedContextYieldTo
  | .tcb => sid == .tcbSuspend || sid == .tcbResume || sid == .tcbSetPriority ||
      sid == .tcbSetMCPriority || sid == .tcbSetIPCBuffer || sid == .tcbSetAffinity ||
      sid == .tcbSetSpace || sid == .tcbBindNotification || sid == .tcbUnbindNotification
  | .pageTable => sid == .pageTableMap || sid == .pageTableUnmap
  -- seL4's `seL4_ARM_Page_Map` and `seL4_ARM_Page_Unmap` are invoked on the
  -- frame capability (WS-SX SX6.3, `decodeARMFrameInvocation`).
  | .frame => sid == .vspaceMap || sid == .vspaceUnmap
  | .reply => false
  -- seL4: Send or Call on an endpoint is IPC and Send on a notification
  -- signals, whatever the label; the label is the receiver's data.  No label
  -- selects an operation on either (`invocationOperation_endpoint`,
  -- `invocationOperation_notification`).
  | .endpoint | .notification => false

/-- The object kind each labelled operation invokes, by capability type: the
operation a label names is selected only on a capability of the type it takes
(seL4's per-object `decode*Invocation`). -/
def labelledOperationTakes (sid : SyscallId) : CapType → Bool
  | .object (some k) => kindTakesLabel sid k
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

/-! ## The selection as compiled

`selectedOperationCode` builds an `Option CapType` around the invoked
capability's type and an `Option SyscallId` around the operation, and its
lookup returns an `Except`; a kernel entry allocates nothing, so the compiled
entry runs `selectedOperationCodeK` instead (`@[csimp]`
`selectedOperationCode_eq_k`).  It answers the code itself: the lookup in
continuation form (`lookupSlotK`), the capability's type read in place, and
the selection written over codes, an object's kind passed as the kind
(`selectionCodeOfKind`) so no `CapType.object` is built. -/

/-- **The code `Syscall.selectOperation` answers**: the selected operation's
code, `SyscallId.encodingBound` when it selects none. -/
def selectionCode (sys : Syscall) (ty : Option CapType) (label : Nat) : Nat :=
  match sys.selectOperation ty label with
  | some op => op.toNat
  | none => SyscallId.encodingBound

/-- The code a label selects on a capability of type `t`. -/
def labelCode (t : CapType) (label : Nat) : Nat :=
  match SyscallId.ofLabel? label with
  | some op => if labelledOperationTakes op t then op.toNat else SyscallId.encodingBound
  | none => SyscallId.encodingBound

/-- `invocationOperation`'s code. -/
def invocationCode (base : SyscallId) (ty : Option CapType) (label : Nat) : Nat :=
  match ty with
  | none | some .cnodeSlot => base.toNat
  | some .replyCap => SyscallId.reply.toNat
  | some (.object (some .endpoint)) => base.toNat
  | some (.object (some .notification)) => SyscallId.notificationSignal.toNat
  | some t => labelCode t label

/-- **`selectionCode` written over codes**, so no `Option` is built. -/
def selectionCodeImpl (sys : Syscall) (ty : Option CapType) (label : Nat) : Nat :=
  match sys with
  | .yield => SyscallId.yield.toNat
  | .call => invocationCode .call ty label
  | .send | .nbSend => invocationCode .send ty label
  | .recv | .nbRecv | .wait | .nbWait | .nbSendRecv | .nbSendWait =>
      (receiveOperation ty).toNat
  | .replyRecv =>
      match receiveOperation ty with
      | .receive => SyscallId.replyRecv.toNat
      | op => op.toNat

theorem selectionCodeImpl_eq (sys : Syscall) (ty : Option CapType) (label : Nat) :
    selectionCodeImpl sys ty label = selectionCode sys ty label := by
  have hInv : ∀ base, invocationCode base ty label =
      match invocationOperation base ty label with
      | some op => op.toNat
      | none => SyscallId.encodingBound := by
    intro base
    unfold invocationCode invocationOperation labelCode
    split <;> try rfl
    split <;> try rfl
    split <;> rfl
  unfold selectionCode selectionCodeImpl Syscall.selectOperation
  cases sys <;> simp only [hInv]
  split <;> rfl

/-- The code a label selects on an object of kind `k`. -/
def labelCodeOfKind (k : KernelObjectType) (label : Nat) : Nat :=
  match SyscallId.ofLabel? label with
  | some op => if kindTakesLabel op k then op.toNat else SyscallId.encodingBound
  | none => SyscallId.encodingBound

/-- `invocationCode` on an object of kind `k`, the kind passed alone. -/
def invocationCodeOfKind (base : SyscallId) (k : KernelObjectType) (label : Nat) : Nat :=
  match k with
  | .endpoint => base.toNat
  | .notification => SyscallId.notificationSignal.toNat
  | k => labelCodeOfKind k label

/-- **`selectionCode` on an object of kind `k`**, the kind passed alone so no
`CapType.object` is built (`selectionCodeOfKind_eq`). -/
def selectionCodeOfKind (sys : Syscall) (k : KernelObjectType) (label : Nat) : Nat :=
  match sys with
  | .yield => SyscallId.yield.toNat
  | .call => invocationCodeOfKind .call k label
  | .send | .nbSend => invocationCodeOfKind .send k label
  | .recv | .nbRecv | .wait | .nbWait | .nbSendRecv | .nbSendWait =>
      match k with
      | .notification => SyscallId.notificationWait.toNat
      | _ => SyscallId.receive.toNat
  | .replyRecv =>
      match k with
      | .notification => SyscallId.notificationWait.toNat
      | _ => SyscallId.replyRecv.toNat

theorem selectionCodeOfKind_eq (sys : Syscall) (k : KernelObjectType) (label : Nat) :
    selectionCodeOfKind sys k label = selectionCode sys (some (.object (some k))) label := by
  rw [← selectionCodeImpl_eq]
  cases sys <;> cases k <;> rfl

/-- **The selected operation's code from the three words it reads**: the
syscall word (`x7`), the invoked capability's address (`x0`) and the
message-info word (`x1`), the thread's CSpace read on `st`.  No `Option`, no
`Except`, no `CapType` is built.  The compiled selection
(`selectedOperationCodeK`) reads its words from a register file; the entry's
capture reads them from the trapped frame before it is saved. -/
def operationCodeOfWords (st : SystemState) (tcb : TCB) (sysWord capWord infoWord : UInt64) :
    Nat :=
  match Syscall.ofWord? sysWord with
  | none => SyscallId.encodingBound
  | some sys =>
    let label := msgInfoWordLabel infoWord
    lookupSlotK tcb (SeLe4n.CPtr.ofWord capWord) st
      (fun _ _ _ _ => selectionCodeImpl sys none label)
      (fun cnode slot =>
        match SystemState.lookupSlotCap st { cnode := cnode, slot := slot } with
        | none => selectionCodeImpl sys none label
        | some cap =>
          match cap.target with
          | .object id =>
            match st.getObject? id with
            | some o => selectionCodeOfKind sys o.objectType label
            | none => selectionCodeImpl sys (some (.object none)) label
          | .replyCap _ => selectionCodeImpl sys (some .replyCap) label
          | .auditTrail _ => selectionCodeImpl sys (some .auditTrail) label
          | .schedControl _ => selectionCodeImpl sys (some .schedControl) label
          | .irqControl _ => selectionCodeImpl sys (some .irqControl) label
          | .irqHandler _ => selectionCodeImpl sys (some .irqHandler) label
          | .serviceRegistry _ => selectionCodeImpl sys (some .serviceRegistry) label
          | .cnodeSlotWord _ => selectionCodeImpl sys (some .cnodeSlot) label)

/-- **`selectedOperationCode` as compiled** (`selectedOperationCode_eq_k`):
`operationCodeOfWords` on the register file's three words. -/
@[inline] def selectedOperationCodeK (st : SystemState) (tcb : TCB)
    (layout : SeLe4n.SyscallRegisterLayout) (regs : SeLe4n.RegisterFile) : Nat :=
  operationCodeOfWords st tcb (SeLe4n.readRegWord regs layout.syscallNumReg)
    (SeLe4n.readRegWord regs layout.capPtrReg) (SeLe4n.readRegWord regs layout.msgInfoReg)

@[csimp] theorem selectedOperationCode_eq_k : @selectedOperationCode = @selectedOperationCodeK := by
  funext st tcb layout regs
  unfold selectedOperationCode selectedOperation selectedOperationCodeK operationCodeOfWords
  cases Syscall.ofWord? (SeLe4n.readRegWord regs layout.syscallNumReg) with
  | none => rfl
  | some sys =>
    simp only [lookupSlotK_eq, selectionCodeImpl_eq, selectionCodeOfKind_eq]
    unfold invokedCapType
    cases lookupSlot tcb (SeLe4n.CPtr.ofWord (SeLe4n.readRegWord regs layout.capPtrReg)) st with
    | error f => rfl
    | ok ref =>
      rcases ref with ⟨cn, sl⟩
      simp only
      cases SystemState.lookupSlotCap st ⟨cn, sl⟩ with
      | none => rfl
      | some cap =>
        simp only [Option.map, CapType.ofCap]
        cases cap.target with
        | object id => simp only; cases st.getObject? id <;> rfl
        | _ => rfl

/-- **The operation the thread `tid`'s trapped registers `regs` select**
(`selectedOperationCode`), read off its TCB in `st`; a thread the store holds no
TCB for selects nothing. -/
@[inline] def threadOperationCode (st : SystemState) (tid : SeLe4n.ThreadId)
    (layout : SeLe4n.SyscallRegisterLayout) (regs : SeLe4n.RegisterFile) : Nat :=
  match st.getTcb? tid with
  | some tcb => selectedOperationCode st tcb layout regs
  | none => SyscallId.encodingBound


/-- No label names the send or the call: both are IPC, selected by the
syscall and an endpoint capability, never by a message label. -/
theorem SyscallId.ofLabel?_ne_ipc {l : Nat} {sid : SyscallId} (h : SyscallId.ofLabel? l = some sid) :
    sid ≠ .send ∧ sid ≠ .call := by
  have hl := SyscallId.label?_ofLabel? h
  constructor <;> (rintro rfl; simp [SyscallId.label?] at hl)

/-- An invocation selects the send or the call only as its own IPC operation
`base`. -/
theorem invocationOperation_ipc {base : SyscallId} {ty : Option CapType} {label : Nat}
    {op : SyscallId} (h : invocationOperation base ty label = some op)
    (hop : op = .send ∨ op = .call) : op = base := by
  unfold invocationOperation at h
  split at h
  all_goals first
    | (injection h with h; subst h
       first | rfl | (rcases hop with h | h <;> cases h <;> rfl))
    | skip
  all_goals
    split at h
    · rename_i o ho
      split at h
      · injection h with h; subst h
        exact absurd hop (by
          have := SyscallId.ofLabel?_ne_ipc ho
          rintro (h | h) <;> simp_all)
      · cases h
    · cases h

/-- **A selected send or call is the blocked-sender code of the same frame**:
the send is selected only by Send or NBSend and the call only by Call, so the
frame's syscall word answers the same operation the selection answered
(`RegisterDecode.blockedSenderCode`).  This is the bridge between the entry's
route and the sender-frame reads a rendezvous makes of that frame. -/
theorem blockedSenderCode_of_selected {st : SystemState} {tcb : TCB}
    {layout : SeLe4n.SyscallRegisterLayout} {regs : SeLe4n.RegisterFile}
    (h : selectedOperationCode st tcb layout regs = SyscallId.send.toNat ∨
      selectedOperationCode st tcb layout regs = SyscallId.call.toNat) :
    SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode layout regs =
      selectedOperationCode st tcb layout regs := by
  have hS : ∃ op, selectedOperation st tcb layout regs = some op ∧ (op = .send ∨ op = .call) ∧
      selectedOperationCode st tcb layout regs = op.toNat := by
    unfold selectedOperationCode at h ⊢
    cases hO : selectedOperation st tcb layout regs with
    | none => simp only [hO] at h; rcases h with h | h <;> cases h
    | some op =>
      simp only [hO] at h ⊢
      refine ⟨op, rfl, ?_, rfl⟩
      rcases h with h | h
      · exact .inl (SyscallId.toNat_injective h)
      · exact .inr (SyscallId.toNat_injective h)
  obtain ⟨op, hO, hop, hC⟩ := hS
  rw [hC]
  unfold selectedOperation at hO
  unfold SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode
  cases hW : Syscall.ofWord? (SeLe4n.readRegWord regs layout.syscallNumReg) with
  | none => simp only [hW] at hO; cases hO
  | some sys =>
    simp only [hW] at hO
    have hR : ∀ ty, receiveOperation ty ≠ .send ∧ receiveOperation ty ≠ .call := by
      intro ty; unfold receiveOperation; split <;> exact ⟨by decide, by decide⟩
    cases sys <;> simp only [Syscall.selectOperation] at hO
    all_goals first
      | (have := invocationOperation_ipc hO hop; subst this; rfl)
      | (injection hO with hO; subst hO
         first
           | (rcases hop with h | h <;> cases h)
           | (exact absurd hop (by rintro (h | h) <;> simp_all)))
      | (split at hO
         · injection hO with hO; subst hO; rcases hop with h | h <;> cases h
         · rename_i o heq
           injection hO with hO; subst hO
           exact absurd hop (by rintro (h | h) <;> simp_all))

/-- **A thread's selected send or call is the blocked-sender code of its
frame** (`blockedSenderCode_of_selected`, read off the thread's TCB): a thread
the store holds no TCB for selects nothing, never a send or a call. -/
theorem blockedSenderCode_of_threadOperationCode {st : SystemState} {tid : SeLe4n.ThreadId}
    {layout : SeLe4n.SyscallRegisterLayout} {regs : SeLe4n.RegisterFile}
    (h : threadOperationCode st tid layout regs = SyscallId.send.toNat ∨
      threadOperationCode st tid layout regs = SyscallId.call.toNat) :
    SeLe4n.Kernel.Architecture.RegisterDecode.blockedSenderCode layout regs =
      threadOperationCode st tid layout regs := by
  unfold threadOperationCode at h ⊢
  cases hT : st.getTcb? tid with
  | none => simp only [hT] at h; rcases h with h | h <;> exact absurd h (by decide)
  | some tcb => simp only [hT] at h ⊢; exact blockedSenderCode_of_selected h

end SeLe4n.Model
