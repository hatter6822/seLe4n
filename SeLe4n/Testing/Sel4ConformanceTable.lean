-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.API

/-!
# The seL4 conformance table

One row per seL4 syscall and per invocation label, each sourced from the seL4
source: **seL4 release 17.0.0** (commit
`62e345c240a15671484530b4e6e069ce266c28d7`), the aarch64 tree configured with
`CONFIG_KERNEL_MCS` and `CONFIG_ENABLE_SMP_SUPPORT` (no hypervisor, no SMMU, no
hardware debug API).  Labels are numbered as that tree's
`invocation_header_gen.py` numbers `object-api.xml`,
`object-api-sel4-arch.xml` and `object-api-arch.xml`.  Each row cites the
decode function (and the perform function where it is not the decode's tail)
with its file and line in that release.

Each row records what seL4 reads (registers, message words past the label,
extra capabilities), what a successful Call writes back, the seL4 errors the
decode raises (each with its payload, `setMRs_syscall_error`), whether the
invocation blocks, and seLe4n's status: implemented as the operation that
answers it, a deliberate seLe4n hardening, a deviation a later WS-SX row owns,
or absent.

`conformanceRowAgrees` checks a row against the kernel: the label round trip
(`SyscallId.label?` / `ofLabel?`), the selection (`Syscall.selectOperation`
under Call and Send on the capability type the row names), the decode's word
count (`truncationMinimum`), and the return (`syscallReturnShape`).  The
agreement is decided over every row (`sel4LabelRows_agree`,
`sel4SyscallRows_agree`), and `tests/Sel4ConformanceSuite.lean` runs the same
checks with the register reads and the error frames, so a change to an
operation's decode, selection or return changes its row in the same cut.
-/

namespace SeLe4n.Testing.Sel4Conformance

open SeLe4n.Model
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Architecture.SyscallArgDecode

/-- seL4's `seL4_Error` (`libsel4/include/sel4/errors.h`), with its number. -/
inductive Sel4Error where
  | invalidArgument | invalidCapability | illegalOperation | rangeError
  | alignmentError | failedLookup | truncatedMessage | deleteFirst | revokeFirst
  | notEnoughMemory
  deriving Repr, DecidableEq

namespace Sel4Error

/-- The code seL4 writes as the error reply's label (`replyFromKernel_error`). -/
def code : Sel4Error → Nat
  | .invalidArgument => 1 | .invalidCapability => 2 | .illegalOperation => 3
  | .rangeError => 4 | .alignmentError => 5 | .failedLookup => 6
  | .truncatedMessage => 7 | .deleteFirst => 8 | .revokeFirst => 9
  | .notEnoughMemory => 10

/-- The payload words `setMRs_syscall_error` (`src/object/tcb.c:2091`) writes:
the argument's number, the capability's number, the range's two ends, the
lookup's `wasSource` and one lookup-fault word at least, the memory left. -/
def payloadWords : Sel4Error → Nat
  | .invalidArgument | .invalidCapability | .notEnoughMemory => 1
  | .rangeError | .failedLookup => 2
  | _ => 0

/-- seLe4n's error for each seL4 code, with a representative payload.  The
label seLe4n writes for it is `errorLabelBase` plus its discriminant until
WS-SX SX18 (D1) writes seL4's code; the payload words are seL4's already. -/
def kernelError : Sel4Error → KernelError
  | .invalidArgument => .invalidArgument 1
  | .invalidCapability => .invalidCapability 1
  | .illegalOperation => .illegalState
  | .rangeError => .rangeError 1 2
  | .alignmentError => .alignmentError
  | .failedLookup => .failedLookup true .invalidRoot
  | .truncatedMessage => .truncatedMessage
  | .deleteFirst => .targetSlotOccupied
  | .revokeFirst => .revocationRequired
  | .notEnoughMemory => .untypedRegionExhausted 1

end Sel4Error

/-- A function of the seL4 source: its name, file (under the tree's root) and
line in release 17.0.0. -/
structure SourceRef where
  fn : String
  file : String
  line : Nat
  deriving Repr

/-- seLe4n's answer to a row. -/
inductive Status where
  /-- seL4's behaviour, through the operation named. -/
  | implemented (op : SyscallId)
  /-- Implemented, with a deliberate seLe4n hardening the note names (W^X,
  memory-type refusals, flow gates); recorded as seLe4n behaviour. -/
  | hardening (op : SyscallId) (note : String)
  /-- Implemented with a deviation from seL4 that the named later WS-SX row
  removes; `minLength` is then seLe4n's word count where it differs. -/
  | deviation (op : SyscallId) (owner : String) (minLength : Option Nat) (note : String)
  /-- No seLe4n operation: the label selects nothing, and seLe4n answers it as
  an unknown label (`invalidSyscallNumber`, seL4's `IllegalOperation`).  The
  owner is the WS-SX row that adds it, or names why seL4's default build has
  none (`ARM_SMC_Call`, compiled only with `CONFIG_ALLOW_SMC_CALLS`). -/
  | absent (owner : String)
  /-- A seLe4n operation with no seL4 counterpart (a label after seL4's last). -/
  | modelOnly (op : SyscallId)
  deriving Repr

/-- The operation a status names, when it names one. -/
def Status.op? : Status → Option SyscallId
  | .implemented op | .hardening op _ | .deviation op _ _ _ | .modelOnly op => some op
  | .absent _ => none

/-- **One invocation label.** -/
structure LabelRow where
  label : Nat
  /-- seL4's generated `invocation_label` name. -/
  name : String
  decode : SourceRef
  /-- The capability type it is invoked on, in seLe4n's terms; `none` where
  seLe4n has no capability of seL4's type (VCPU, SMC, ASID control and pool,
  domain set). -/
  capType : Option CapType
  /-- seL4's `length <` check: the message words the decode reads. -/
  minLength : Nat
  /-- The extra capabilities the decode reads (`excaprefs`). -/
  extraCaps : Nat
  /-- What a successful Call writes back. -/
  returns : ReturnShape
  /-- The seL4 errors the decode and perform raise, in source order. -/
  errors : List Sel4Error
  /-- Whether the invoking thread blocks. -/
  blocks : Bool
  status : Status
  deriving Repr

/-- **One syscall** (`libsel4/include/api/syscall.xml`, `src/api/syscall.c`). -/
structure SyscallRow where
  sys : Syscall
  name : String
  handler : SourceRef
  /-- The registers read, as indices `xN` (x8 is `getNBSendRecvDest`'s). -/
  regsRead : List Nat
  /-- `handleInvocation`'s `isCall`: an error or a success is replied. -/
  isCall : Bool
  /-- It invokes a capability first (`handleInvocation`). -/
  invokes : Bool
  /-- `handleInvocation`'s `isBlocking`: a failed lookup faults. -/
  invocationBlocks : Bool
  /-- It receives (`handleRecv`), and with `isBlocking`. -/
  receives : Bool
  receiveBlocks : Bool
  /-- `handleRecv`'s `canReply`: x6 names the reply capability. -/
  canReply : Bool
  /-- A success writes no register of the caller. -/
  returnsNothing : Bool
  deriving Repr

/-- `src/api/syscall.c` at a line. -/
def syscallC (fn : String) (line : Nat) : SourceRef := ⟨fn, "src/api/syscall.c", line⟩

/-- **The eleven syscalls** of seL4-MCS (`handleSyscall`, `syscall.c:562`).
Call and the sends read the capability (x0), the message info (x1) and the
inline message registers (x2–x5; the rest from the IPC buffer, with the extra
capabilities' `caps_or_badges`); the receives read the capability (x0) and,
with `canReply`, the reply capability (x6, `lookupReply`); the compound
syscalls invoke the capability in x6 (ReplyRecv, NBSendWait) or x8
(NBSendRecv, `getNBSendRecvDest`) first; Yield reads nothing. -/
def sel4SyscallRows : List SyscallRow := [
  { sys := .call, name := "Call", handler := syscallC "handleSyscall SysCall" 585,
    regsRead := [0, 1, 2, 3, 4, 5, 7], isCall := true, invokes := true,
    invocationBlocks := true, receives := false, receiveBlocks := false,
    canReply := false, returnsNothing := false },
  { sys := .replyRecv, name := "ReplyRecv", handler := syscallC "handleSyscall SysReplyRecv" 614,
    regsRead := [0, 1, 2, 3, 4, 5, 6, 7], isCall := false, invokes := true,
    invocationBlocks := false, receives := true, receiveBlocks := true,
    canReply := true, returnsNothing := false },
  { sys := .nbSendRecv, name := "NBSendRecv", handler := syscallC "handleSyscall SysNBSendRecv" 627,
    regsRead := [0, 1, 2, 3, 4, 5, 6, 7, 8], isCall := false, invokes := true,
    invocationBlocks := false, receives := true, receiveBlocks := true,
    canReply := true, returnsNothing := false },
  { sys := .nbSendWait, name := "NBSendWait", handler := syscallC "handleSyscall SysNBSendWait" 639,
    regsRead := [0, 1, 2, 3, 4, 5, 6, 7], isCall := false, invokes := true,
    invocationBlocks := false, receives := true, receiveBlocks := true,
    canReply := false, returnsNothing := false },
  { sys := .send, name := "Send", handler := syscallC "handleSyscall SysSend" 568,
    regsRead := [0, 1, 2, 3, 4, 5, 7], isCall := false, invokes := true,
    invocationBlocks := true, receives := false, receiveBlocks := false,
    canReply := false, returnsNothing := true },
  { sys := .nbSend, name := "NBSend", handler := syscallC "handleSyscall SysNBSend" 577,
    regsRead := [0, 1, 2, 3, 4, 5, 7], isCall := false, invokes := true,
    invocationBlocks := false, receives := false, receiveBlocks := false,
    canReply := false, returnsNothing := true },
  { sys := .recv, name := "Recv", handler := syscallC "handleRecv" 448,
    regsRead := [0, 6, 7], isCall := false, invokes := false,
    invocationBlocks := false, receives := true, receiveBlocks := true,
    canReply := true, returnsNothing := false },
  { sys := .nbRecv, name := "NBRecv", handler := syscallC "handleSyscall SysNBRecv" 649,
    regsRead := [0, 6, 7], isCall := false, invokes := false,
    invocationBlocks := false, receives := true, receiveBlocks := false,
    canReply := true, returnsNothing := false },
  { sys := .wait, name := "Wait", handler := syscallC "handleSyscall SysWait" 607,
    regsRead := [0, 7], isCall := false, invokes := false,
    invocationBlocks := false, receives := true, receiveBlocks := true,
    canReply := false, returnsNothing := false },
  { sys := .nbWait, name := "NBWait", handler := syscallC "handleSyscall SysNBWait" 611,
    regsRead := [0, 7], isCall := false, invokes := false,
    invocationBlocks := false, receives := true, receiveBlocks := false,
    canReply := false, returnsNothing := false },
  { sys := .yield, name := "Yield", handler := syscallC "handleYield" 546,
    regsRead := [7], isCall := false, invokes := false,
    invocationBlocks := false, receives := false, receiveBlocks := false,
    canReply := false, returnsNothing := true } ]

/-- A syscall row agrees with seLe4n's `Syscall` predicates. -/
def syscallRowAgrees (r : SyscallRow) : Bool :=
  r.sys.isCall == r.isCall && r.sys.invokes == r.invokes &&
    r.sys.invocationBlocks == r.invocationBlocks &&
    (!r.receives || r.sys.receiveBlocks == r.receiveBlocks) &&
    r.sys.receiveCanReply == r.canReply && r.sys.returnsNothing == r.returnsNothing &&
    r.sys.dropsInvocationFault == (r.invokes && !r.invocationBlocks) &&
    -- The receive of a receiving syscall selects the receive or the wait on the
    -- capability's type (`handleRecv`); Call and the sends select IPC on an
    -- endpoint and a signal on a notification (`decodeInvocation`).
    (if r.receives then
        r.sys.selectOperation (some (.object (some .notification))) 0 == some .notificationWait
      else if r.invokes then
        r.sys.selectOperation (some (.object (some .notification))) 0 == some .notificationSignal &&
          r.sys.selectOperation (some .replyCap) 0 == some .reply
      else r.sys.selectOperation none 0 == some .yield)

/-- Every syscall row agrees, and every syscall has exactly one row. -/
theorem sel4SyscallRows_agree :
    sel4SyscallRows.all syscallRowAgrees = true ∧
      (sel4SyscallRows.map (·.sys.number)) = (List.range 11).map (· + 1) := by
  decide

/-! ## The invocation labels -/

/-- A source reference under `src/`. -/
def src (fn file : String) (line : Nat) : SourceRef := ⟨fn, "src/" ++ file, line⟩

/-- A label row that writes nothing on success and does not block, the shape
of most of them. -/
def unitRow (label : Nat) (name : String) (decode : SourceRef) (capType : Option CapType)
    (minLength extraCaps : Nat) (errors : List Sel4Error) (status : Status) : LabelRow :=
  { label, name, decode, capType, minLength, extraCaps, returns := .unit, errors,
    blocks := false, status }

/-- The capability type of an object of kind `k`. -/
def obj (k : KernelObjectType) : Option CapType := some (.object (some k))

open Sel4Error in
/-- Labels 1–29: Untyped, TCB, CNode and IRQ. -/
def sel4LabelRowsCore : List LabelRow := [
  unitRow 1 "UntypedRetype" (src "decodeUntypedInvocation" "object/untyped.c" 26) (obj .untyped)
    6 1 [illegalOperation, truncatedMessage, invalidArgument, rangeError, failedLookup,
      deleteFirst, notEnoughMemory]
    (.deviation .untypedRetype "SX19.1" (some 7)
      "seLe4n reads a seventh word, the carved object's id (MR6); seL4 places the object at the untyped's free index"),
  { label := 2, name := "TCBReadRegisters",
    decode := src "decodeReadRegisters" "object/tcb.c" 1001, capType := obj .tcb,
    minLength := 2, extraCaps := 0, returns := .message,
    errors := [truncatedMessage, invalidArgument, rangeError, illegalOperation], blocks := false,
    status := .absent "SX19.1" },
  unitRow 3 "TCBWriteRegisters" (src "decodeWriteRegisters" "object/tcb.c" 1046) (obj .tcb)
    2 0 [truncatedMessage, invalidArgument, illegalOperation] (.absent "SX19.1"),
  unitRow 4 "TCBCopyRegisters" (src "decodeCopyRegisters" "object/tcb.c" 958) (obj .tcb)
    1 1 [truncatedMessage, invalidArgument, invalidCapability] (.absent "SX19.1"),
  unitRow 5 "TCBConfigure" (src "decodeTCBConfigure" "object/tcb.c" 1101) (obj .tcb)
    3 3 [truncatedMessage, illegalOperation, invalidCapability, alignmentError] (.absent "SX19.1"),
  unitRow 6 "TCBSetPriority" (src "decodeSetPriority" "object/tcb.c" 1217) (obj .tcb)
    1 1 [truncatedMessage, invalidCapability, rangeError] (.implemented .tcbSetPriority),
  unitRow 7 "TCBSetMCPriority" (src "decodeSetMCPriority" "object/tcb.c" 1261) (obj .tcb)
    1 1 [truncatedMessage, invalidCapability, rangeError] (.implemented .tcbSetMCPriority),
  unitRow 8 "TCBSetSchedParams" (src "decodeSetSchedParams" "object/tcb.c" 1338) (obj .tcb)
    2 3 [truncatedMessage, invalidCapability, rangeError, illegalOperation] (.absent "SX16.2"),
  unitRow 9 "TCBSetTimeoutEndpoint" (src "decodeSetTimeoutEndpoint" "object/tcb.c" 1306) (obj .tcb)
    0 1 [truncatedMessage, invalidCapability] (.absent "SX16.1"),
  unitRow 10 "TCBSetIPCBuffer" (src "decodeSetIPCBuffer" "object/tcb.c" 1457) (obj .tcb)
    1 1 [truncatedMessage, alignmentError, illegalOperation, invalidCapability]
    (.implemented .tcbSetIPCBuffer),
  unitRow 11 "TCBSetSpace" (src "decodeSetSpace" "object/tcb.c" 1517) (obj .tcb)
    2 3 [truncatedMessage, illegalOperation, invalidCapability] (.implemented .tcbSetSpace),
  unitRow 12 "TCBSuspend" (src "decodeTCBInvocation" "object/tcb.c" 868) (obj .tcb)
    0 0 [] (.implemented .tcbSuspend),
  unitRow 13 "TCBResume" (src "decodeTCBInvocation" "object/tcb.c" 874) (obj .tcb)
    0 0 [] (.implemented .tcbResume),
  unitRow 14 "TCBBindNotification" (src "decodeBindNotification" "object/tcb.c" 1627) (obj .tcb)
    0 1 [truncatedMessage, illegalOperation] (.implemented .tcbBindNotification),
  unitRow 15 "TCBUnbindNotification" (src "decodeUnbindNotification" "object/tcb.c" 1675)
    (obj .tcb) 0 0 [illegalOperation] (.implemented .tcbUnbindNotification),
  unitRow 16 "TCBSetTLSBase" (src "decodeSetTLSBase" "object/tcb.c" 785) (obj .tcb)
    1 0 [truncatedMessage] (.absent "SX19.1"),
  { label := 17, name := "TCBSetFlags", decode := src "decodeSetFlags" "object/tcb.c" 829,
    capType := obj .tcb, minLength := 2, extraCaps := 0, returns := .message,
    errors := [truncatedMessage], blocks := false, status := .absent "SX19.1" },
  unitRow 18 "CNodeRevoke" (src "decodeCNodeInvocation" "object/cnode.c" 195) (obj .cnode)
    2 0 [truncatedMessage, failedLookup] (.deviation .cspaceRevoke "SX17.1" (some 1)
      "seLe4n names the target by a slot word; seL4 by index and depth"),
  unitRow 19 "CNodeDelete" (src "decodeCNodeInvocation" "object/cnode.c" 200) (obj .cnode)
    2 0 [truncatedMessage, failedLookup] (.deviation .cspaceDelete "SX17.1" (some 1)
      "seLe4n names the target by a slot word; seL4 by index and depth"),
  unitRow 20 "CNodeCancelBadgedSends" (src "decodeCNodeInvocation" "object/cnode.c" 218)
    (obj .cnode) 2 0 [truncatedMessage, failedLookup, illegalOperation] (.absent "SX17.4"),
  unitRow 21 "CNodeCopy" (src "decodeCNodeInvocation" "object/cnode.c" 116) (obj .cnode)
    5 1 [truncatedMessage, failedLookup, deleteFirst, illegalOperation] (.implemented .cspaceCopy),
  unitRow 22 "CNodeMint" (src "decodeCNodeInvocation" "object/cnode.c" 136) (obj .cnode)
    6 1 [truncatedMessage, failedLookup, deleteFirst, illegalOperation] (.implemented .cspaceMint),
  unitRow 23 "CNodeMove" (src "decodeCNodeInvocation" "object/cnode.c" 157) (obj .cnode)
    4 1 [truncatedMessage, failedLookup, deleteFirst] (.implemented .cspaceMove),
  unitRow 24 "CNodeMutate" (src "decodeCNodeInvocation" "object/cnode.c" 163) (obj .cnode)
    5 1 [truncatedMessage, failedLookup, deleteFirst, illegalOperation] (.absent "SX17.2"),
  unitRow 25 "CNodeRotate" (src "decodeCNodeInvocation" "object/cnode.c" 232) (obj .cnode)
    8 2 [truncatedMessage, failedLookup, deleteFirst, illegalOperation] (.absent "SX17.3"),
  unitRow 26 "IRQIssueIRQHandler" (src "decodeIRQControlInvocation" "object/interrupt.c" 23)
    (some .irqControl) 3 1 [truncatedMessage, rangeError, failedLookup, deleteFirst, revokeFirst]
    (.implemented .irqControlGet),
  unitRow 27 "IRQAckIRQ" (src "decodeIRQHandlerInvocation" "object/interrupt.c" 89)
    (some .irqHandler) 0 0 [] (.implemented .irqHandlerAck),
  unitRow 28 "IRQSetIRQHandler" (src "decodeIRQHandlerInvocation" "object/interrupt.c" 94)
    (some .irqHandler) 0 1 [truncatedMessage, invalidCapability]
    (.implemented .irqHandlerSetNotification),
  unitRow 29 "IRQClearIRQHandler" (src "decodeIRQHandlerInvocation" "object/interrupt.c" 122)
    (some .irqHandler) 0 0 [] (.implemented .irqHandlerClear) ]

open Sel4Error in
/-- Labels 30–56: domains, scheduling, the VSpace and the ARM objects. -/
def sel4LabelRowsArch : List LabelRow := [
  unitRow 30 "DomainSetSet" (src "decodeDomainSetSetInvocation" "object/domain.c" 24) none
    1 1 [truncatedMessage, invalidArgument] (.absent "SX19.1"),
  unitRow 31 "DomainScheduleConfigure" (src "decodeDomainScheduleConfigure" "object/domain.c" 67)
    none 3 0 [truncatedMessage, invalidArgument, rangeError] (.absent "SX19.1"),
  unitRow 32 "DomainScheduleSetStart" (src "decodeDomainScheduleSetStart" "object/domain.c" 130)
    none 1 0 [truncatedMessage, rangeError] (.absent "SX19.1"),
  unitRow 33 "SchedControlConfigureFlags"
    (src "decodeSchedControl_ConfigureFlags" "object/schedcontrol.c" 80) (some .schedControl)
    5 1 [truncatedMessage, rangeError, invalidCapability] (.implemented .schedContextConfigure),
  unitRow 34 "SchedContextBind" (src "decodeSchedContext_Bind" "object/schedcontext.c" 87)
    (obj .schedContext) 0 1 [truncatedMessage, illegalOperation, invalidCapability]
    (.hardening .schedContextBind
      "flow gate: a context heading a reply stack binds only to a thread its label flows to (D25, D27)"),
  unitRow 35 "SchedContextUnbind" (src "decodeSchedContextInvocation" "object/schedcontext.c" 283)
    (obj .schedContext) 0 0 [illegalOperation] (.implemented .schedContextUnbind),
  unitRow 36 "SchedContextUnbindObject"
    (src "decodeSchedContext_UnbindObject" "object/schedcontext.c" 29) (obj .schedContext)
    0 1 [truncatedMessage, illegalOperation, invalidCapability]
    (.implemented .schedContextUnbindObject),
  { label := 37, name := "SchedContextConsumed",
    decode := src "decodeSchedContextInvocation" "object/schedcontext.c" 275,
    capType := obj .schedContext, minLength := 0, extraCaps := 0, returns := .message,
    errors := [], blocks := false, status := .implemented .schedContextConsumed },
  { label := 38, name := "SchedContextYieldTo",
    decode := src "decodeSchedContext_YieldTo" "object/schedcontext.c" 233,
    capType := obj .schedContext, minLength := 0, extraCaps := 0, returns := .message,
    errors := [illegalOperation], blocks := false, status := .implemented .schedContextYieldTo },
  unitRow 39 "ARMVSpaceClean_Data"
    (src "decodeARMVSpaceRootInvocation" "arch/arm/64/kernel/vspace.c" 1420) (obj .vspaceRoot)
    2 0 [truncatedMessage, invalidArgument, illegalOperation, failedLookup, rangeError]
    (.absent "SX19.1"),
  unitRow 40 "ARMVSpaceInvalidate_Data"
    (src "decodeARMVSpaceRootInvocation" "arch/arm/64/kernel/vspace.c" 1421) (obj .vspaceRoot)
    2 0 [truncatedMessage, invalidArgument, illegalOperation, failedLookup, rangeError]
    (.absent "SX19.1"),
  unitRow 41 "ARMVSpaceCleanInvalidate_Data"
    (src "decodeARMVSpaceRootInvocation" "arch/arm/64/kernel/vspace.c" 1422) (obj .vspaceRoot)
    2 0 [truncatedMessage, invalidArgument, illegalOperation, failedLookup, rangeError]
    (.absent "SX19.1"),
  unitRow 42 "ARMVSpaceUnify_Instruction"
    (src "decodeARMVSpaceRootInvocation" "arch/arm/64/kernel/vspace.c" 1423) (obj .vspaceRoot)
    2 0 [truncatedMessage, invalidArgument, illegalOperation, failedLookup, rangeError]
    (.implemented .vspaceUnifyInstruction),
  { label := 43, name := "ARMSMCCall", decode := src "decodeARMSMCInvocation" "arch/arm/object/smc.c" 67,
    capType := none, minLength := 8, extraCaps := 0, returns := .message,
    errors := [truncatedMessage, invalidArgument], blocks := false,
    status := .absent "not in seL4's default build" },
  unitRow 44 "ARMPageTableMap"
    (src "decodeARMPageTableInvocation" "arch/arm/64/kernel/vspace.c" 1558) (obj .pageTable)
    2 1 [truncatedMessage, invalidCapability, invalidArgument, failedLookup, deleteFirst]
    (.implemented .pageTableMap),
  unitRow 45 "ARMPageTableUnmap"
    (src "decodeARMPageTableInvocation" "arch/arm/64/kernel/vspace.c" 1545) (obj .pageTable)
    0 0 [revokeFirst, illegalOperation]
    (.deviation .pageTableUnmap "SX12.1" none
      "seLe4n refuses a table with live mappings (revocationRequired); seL4 unmaps and clears it"),
  unitRow 46 "ARMPageMap" (src "decodeARMFrameInvocation" "arch/arm/64/kernel/vspace.c" 1626)
    (obj .frame) 3 1
    [truncatedMessage, invalidCapability, failedLookup, alignmentError, invalidArgument, deleteFirst]
    (.hardening .vspaceMap "W^X and memory-type refusals (writable and executable, device executable)"),
  unitRow 47 "ARMPageUnmap" (src "decodeARMFrameInvocation" "arch/arm/64/kernel/vspace.c" 1721)
    (obj .frame) 0 0 [] (.implemented .vspaceUnmap),
  unitRow 48 "ARMPageClean_Data" (src "decodeARMFrameInvocation" "arch/arm/64/kernel/vspace.c" 1725)
    (obj .frame) 2 0 [truncatedMessage, illegalOperation, failedLookup, invalidArgument]
    (.absent "SX19.1"),
  unitRow 49 "ARMPageInvalidate_Data"
    (src "decodeARMFrameInvocation" "arch/arm/64/kernel/vspace.c" 1726)
    (obj .frame) 2 0 [truncatedMessage, illegalOperation, failedLookup, invalidArgument]
    (.absent "SX19.1"),
  unitRow 50 "ARMPageCleanInvalidate_Data"
    (src "decodeARMFrameInvocation" "arch/arm/64/kernel/vspace.c" 1727)
    (obj .frame) 2 0 [truncatedMessage, illegalOperation, failedLookup, invalidArgument]
    (.absent "SX19.1"),
  unitRow 51 "ARMPageUnify_Instruction"
    (src "decodeARMFrameInvocation" "arch/arm/64/kernel/vspace.c" 1728)
    (obj .frame) 2 0 [truncatedMessage, illegalOperation, failedLookup, invalidArgument]
    (.absent "SX19.1"),
  { label := 52, name := "ARMPageGetAddress",
    decode := src "decodeARMFrameInvocation" "arch/arm/64/kernel/vspace.c" 1813,
    capType := obj .frame, minLength := 0, extraCaps := 0, returns := .message, errors := [],
    blocks := false, status := .absent "SX19.1" },
  unitRow 53 "ARMASIDControlMakePool"
    (src "decodeARMMMUInvocation" "arch/arm/64/kernel/vspace.c" 1851) none 2 2
    [truncatedMessage, invalidCapability, failedLookup, deleteFirst, illegalOperation]
    (.absent "SX19.1"),
  unitRow 54 "ARMASIDPoolAssign" (src "decodeARMMMUInvocation" "arch/arm/64/kernel/vspace.c" 1823)
    none 0 1 [truncatedMessage, invalidCapability, deleteFirst] (.absent "SX19.1"),
  unitRow 55 "ARMIRQIssueIRQHandlerTrigger"
    (src "Arch_decodeIRQControlInvocation" "arch/arm/object/interrupt.c" 36) (some .irqControl)
    4 1 [truncatedMessage, rangeError, failedLookup, deleteFirst, revokeFirst] (.absent "SX19.1"),
  unitRow 56 "ARMIRQIssueIRQHandlerTriggerCore"
    (src "Arch_decodeIRQControlInvocation" "arch/arm/object/interrupt.c" 150) (some .irqControl)
    0 1 [rangeError, failedLookup, deleteFirst, revokeFirst, invalidArgument] (.absent "SX19.1") ]

/-- A model-only label: no seL4 source. -/
def modelRow (label : Nat) (name : String) (capType : CapType) (minLength : Nat)
    (returns : ReturnShape) (op : SyscallId) : LabelRow :=
  { label, name, decode := ⟨"(no seL4 counterpart)", "seLe4n", 0⟩, capType := some capType,
    minLength, extraCaps := 0, returns, errors := [], blocks := false, status := .modelOnly op }

/-- The model-only labels, after seL4's last (56): the service registry, the
reply-capability mint, the declassification audit and the affinity call. -/
def modelLabelRows : List LabelRow := [
  modelRow 57 "ServiceRegister" .serviceRegistry 5 .unit .serviceRegister,
  modelRow 58 "ServiceRevoke" .serviceRegistry 0 .unit .serviceRevoke,
  modelRow 59 "ServiceQuery" .serviceRegistry 0 .word .serviceQuery,
  modelRow 60 "MintReplyCap" (.object (some .cnode)) 2 .unit .mintReplyCap,
  modelRow 61 "Declassify" .auditTrail 0 .unit .declassify,
  modelRow 62 "AuditRead" .auditTrail 3 .word .auditRead,
  modelRow 63 "AuditDrain" .auditTrail 1 .word .auditDrain,
  modelRow 64 "DeclassifySignal" .auditTrail 0 .unit .declassifySignal,
  modelRow 66 "TCBSetAffinity" (.object (some .tcb)) 1 .unit .tcbSetAffinity ]

/-- Every label row: seL4's 56, then the model's. -/
def sel4LabelRows : List LabelRow := sel4LabelRowsCore ++ sel4LabelRowsArch ++ modelLabelRows

/-- The message words seLe4n's decode reads for a row: seL4's, except where a
deviation states its own. -/
def LabelRow.seLe4nMinLength (r : LabelRow) : Nat :=
  match r.status with
  | .deviation _ _ (some n) _ => n
  | _ => r.minLength

/-- **A label row agrees with the kernel.**  For a row seLe4n answers: the
label round trip, the selection under Call and Send on the row's capability
type, the decode's word count and the success return.  For an absent row: no
operation takes the label, and the selection on its capability type answers
nothing (the entry refuses it as an unknown label). -/
def labelRowAgrees (r : LabelRow) : Bool :=
  match r.status.op? with
  | some op =>
      op.label? == some r.label && SyscallId.ofLabel? r.label == some op &&
        (match r.capType with
          | some t => Syscall.call.selectOperation (some t) r.label == some op &&
              Syscall.send.selectOperation (some t) r.label == some op &&
              Syscall.nbSend.selectOperation (some t) r.label == some op
          | none => false) &&
        truncationMinimum op == r.seLe4nMinLength && syscallReturnShape op == r.returns
  | none =>
      SyscallId.ofLabel? r.label == none &&
        (match r.capType with
          | some t => Syscall.call.selectOperation (some t) r.label == none
          | none => true)

/-- **The table's agreement, decided over every row**, and the rows are
seL4's labels 1–56 in order with the model's after them. -/
theorem sel4LabelRows_agree :
    sel4LabelRows.all labelRowAgrees = true ∧
      (sel4LabelRowsCore ++ sel4LabelRowsArch).map (·.label) = (List.range 56).map (· + 1) := by
  decide

/-- Every operation a label selects has its row: no labelled operation is
missing from the table. -/
theorem sel4LabelRows_cover (sid : SyscallId) (l : Nat) (h : sid.label? = some l) :
    ∃ r ∈ sel4LabelRows, r.label = l ∧ r.status.op? = some sid := by
  cases sid <;> simp [SyscallId.label?] at h <;> subst h <;> decide

/-- **One seL4 behaviour past a decode**: what an operation does that no label
row shows (a lend, a return, an unbind), the seL4 function it follows, and
seLe4n's status for it.  `tests/Sel4ConformanceSuite.lean` holds one scenario
per row, run against the kernel, and checks that the scenarios and the rows
name the same behaviours. -/
structure BehaviourRow where
  name : String
  source : SourceRef
  status : Status
  deriving Repr

/-- `src/object/<file>` at a line. -/
def objectC (fn file : String) (line : Nat) : SourceRef := ⟨fn, "src/object/" ++ file, line⟩

/-- **The scheduling-context lends, returns and unbinds** (WS-SX SX8, SX9.2):
seL4-MCS's `maybeDonateSchedContext` in `sendSignal` and `completeSignal`, its
`maybeReturnSchedContext` on a blocking `Wait` and a blocking receive,
`sendIPC`'s donation to a passive server, `finaliseCap`'s unbind of a destroyed
thread's context, `reply_pop`'s arm for a caller holding a context of its own,
SchedContext_Unbind of a lent context (`schedContext_unbindReply`), `suspend`,
which leaves the binding, and SchedContext_Bind of a thread whose Call frame is
on a live reply stack. -/
def sel4BehaviourRows : List BehaviourRow := [
  { name := "signal-lends-context",
    source := objectC "sendSignal (maybeDonateSchedContext)" "notification.c" 62,
    status := .hardening .notificationSignal
      "flow gate: the notification's context is lent only where its label and the woken thread's are equal" },
  { name := "wait-consume-lends-context",
    source := objectC "completeSignal (maybeDonateSchedContext)" "notification.c" 325,
    status := .hardening .notificationWait
      "flow gate: the notification's context is lent only where its label and the waiter's are equal" },
  { name := "wait-block-returns-context",
    source := objectC "receiveSignal (maybeReturnSchedContext)" "notification.c" 225,
    status := .implemented .notificationWait },
  { name := "call-lends-context",
    source := objectC "sendIPC (schedContext_donate)" "endpoint.c" 101,
    status := .hardening .call
      "flow gate: a caller lends only a context its own label flows to; the call goes on either way" },
  { name := "destroy-unbinds-context",
    source := objectC "finaliseCap (schedContext_unbindTCB)" "objecttype.c" 195,
    status := .implemented .cspaceDelete },
  { name := "reply-pop-held-keeps-context",
    source := objectC "reply_pop (the caller holds a context)" "reply.c" 56,
    status := .implemented .reply },
  { name := "unbind-donated-holder",
    source := objectC "invokeSchedContext_Unbind (schedContext_unbindReply)" "schedcontext.c" 142,
    status := .implemented .schedContextUnbind },
  { name := "suspend-keeps-binding",
    source := ⟨"suspend", "src/kernel/thread.c", 72⟩,
    status := .implemented .tcbSuspend },
  { name := "receive-block-returns-context",
    source := objectC "receiveIPC (maybeReturnSchedContext)" "endpoint.c" 171,
    status := .implemented .receive },
  { name := "bind-lender",
    source := objectC "decodeSchedContext_Bind" "schedcontext.c" 87,
    status := .implemented .schedContextBind } ]

end SeLe4n.Testing.Sel4Conformance
