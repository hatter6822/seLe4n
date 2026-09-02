-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Fault
import SeLe4n.Kernel.IPC.Invariant.FaultPreservation
import SeLe4n.Kernel.IPC.Invariant.FaultProgress
import SeLe4n.Kernel.InformationFlow.FaultFlow
import SeLe4n.Kernel.Architecture.ExceptionModel
import SeLe4n.Kernel.FaultEntry
import SeLe4n.Testing.StateBuilder

/-!
# WS-RR RR4.26 — the fault-handling suite

Everything RR4 promises, exercised end to end: the wire format's round trip,
handler resolution and its rights gate, delivery across cores, the fail-closed
no-handler suspend, reply-based **resume** and **restart**, and the negative
the whole phase exists for — *a fault never returns the thread to the faulting
instruction*.

The suite is three layers, in the project's usual order:

* **§1 surface anchors** — `#check` on every name the phase's callers depend
  on, so a rename or a deletion breaks this file at elaboration rather than
  silently thinning the surface.
* **§2 elaboration-time witnesses** — the headline theorems applied to typed
  inputs.  A theorem whose statement drifts stops type-checking here.
* **§3–§9 runtime scenarios** — a deterministic 4-core fault workload, with
  §9 pinning its trace byte-for-byte against
  `tests/fixtures/fault_handling_4core.expected` (RR4.27).

## The workload

Four cores, four threads:

| thread | core | fault handler |
|---|---|---|
| `faulter` | 0 | slot 0 — an endpoint cap with send **and** grant |
| `handler` | 1 | (the server; receives the fault message) |
| `orphan`  | 2 | **none** — takes the fail-closed suspend |
| `weak`    | 3 | slot 1 — a **read-only** endpoint cap: rights refused |

The handler is homed on a *different* core from the faulter on purpose: that
is what makes the delivery surface a cross-core `.reschedule` SGI, which is
the half a single-core fixture cannot exercise.
-/

namespace SeLe4n.Testing.FaultHandling

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Architecture
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (elaboration-time: rename/removal breaks this suite)
-- ============================================================================

-- RR4.1–RR4.6: the fault value, the syndrome classification, the wire format.
#check @SeLe4n.Model.Fault
#check @SeLe4n.Model.FaultContext
#check @SeLe4n.Model.ThreadFault
#check @classifySynchronousException
#check @faultOfExceptionContext
#check @faultContextOfThread
#check @faultLabel
#check @faultMessageLength
#check @encodeFault
#check @decodeFault
#check @decodeFault_encodeFault
#check @encodeFault_within_budget
#check @encodeFault_messageInfo_wellFormed
-- RR4.7–RR4.11: resolution, rights, message, dispositions, delivery.
#check @faultHandlerRights
#check @faultHandlerCapAuthorized
#check @faultHandlerCapAuthorized_iff
#check @faultHandlerCapAuthorized_false_of_no_send
#check @faultHandlerCapAuthorized_false_of_no_grant
#check @resolveFaultHandler
#check @resolveFaultHandler_authorized
#check @resolveFaultHandler_names_endpoint
#check @faultMessage
#check @faultMessage_bounded
#check @recordPendingFault
#check @faultSuspend
#check @faultSuspendOnCore
#check @faultAbandonOnCore
#check @faultDeliverOnCore
-- RR4.13–RR4.16: reply, restart frame, register writeback.
#check @decodeFaultReply
#check @faultRestartFrameOfContext
#check @FaultRestartFrame
#check @SeLe4n.RegisterFile.stageRestartFrame
#check @SeLe4n.Model.TCB.withRestartFrame
#check @writeRestartFrameToTcb
#check @applyFaultRestart
#check @faultReplyOnCore
-- RR4.17–RR4.20: preservation, progress, non-interference.
#check @faultDeliverOnCore_preserves_ipcInvariantFull
#check @faultReplyOnCore_preserves_ipcInvariantFull
#check @faultSuspendOnCore_preserves_ipcInvariantFull
#check @faultAbandonOnCore_preserves_ipcInvariantFull
#check @applyFaultRestart_preserves_ipcInvariantFull
#check @dispatchableOnCore
#check @faultDeliverOnCore_not_dispatchable
#check @faultDeliverOnCoreChecked
#check @faultDeliverOnCoreChecked_flow_denied
#check @faultDeliverOnCoreChecked_flow_allowed
#check @faultDeliverOnCoreChecked_not_dispatchable
#check @faultDeliverOnCoreChecked_preserves_ipcInvariantFull
#check @faultMessage_transfers_no_authority
-- RR4.21–RR4.25: the live wiring.
#check @dispatchSynchronousException
#check @dispatchSynchronousException_dataAbort
#check @dispatchSynchronousException_nonSvc_thread_not_dispatchable
#check @syncExceptionClassTag
#check @classifySynchronousExceptionExport
#check @faultEntryStep
#check @faultEntry
#check @faultEntryStep_not_dispatchable
-- Audit round: the trap-frame window the entry spills, and the ABI v3 label range.
#check @SeLe4n.Model.FaultRegisterWindow
#check @SeLe4n.Model.FaultRegisterWindow.spill
#check @SeLe4n.Model.FaultRegisterWindow.ofRegisterFile_spill
#check @writeFaultRegistersToTcb
#check @faultContextOfThread_writeFaultRegistersToTcb
#check @errorLabelBase
#check @faultLabel_lt_errorLabelBase
#check @faultLabel_ne_timeout
#check @faultLabel_ne_debugException
-- PR #887 review round: kernel-origin exceptions, the unknown-syscall producer,
-- the woken handler's staged frame, resume retiring a fault, and the
-- fault-handler configuration syscall.
#check @ExceptionContext.takenFromEl0
#check @classifySynchronousException_currentEl_abort
#check @faultOfExceptionContext_kernelAbort
#check @faultEntryDeliver
#check @faultEntryStep_kernel_origin_inert
#check @faultEntryStep_kernelAbort_inert
#check @unknownSyscallEntryStep
#check @unknownSyscallEntry
#check @unknownSyscallEntryStep_not_dispatchable
#check @unknownSyscallEntryStep_kernel_origin_inert
#check @resolveFaultHandlerCPtr
#check @resolveFaultHandlerCPtr_ok_inv
#check @setThreadFaultHandlerOp
#check @setThreadFaultHandlerOp_validated
#check @setThreadFaultHandlerOp_faultHandler
#check @setThreadFaultHandlerOp_rejects
#check @retirePendingFaultForResume
#check @retirePendingFaultForResume_pendingFault_none
#check @retirePendingFaultForResume_of_no_fault
#check @stageWokenDelivery_preserves_objects_invExt
#check @retirePendingFaultForResume_preserves_ipcInvariantFull
#check @setThreadFaultHandlerOp_preserves_ipcInvariantFull
#check @setThreadFaultHandlerOp_preserves_projection

-- ============================================================================
-- §2  Elaboration-time witnesses (headline theorems applied to typed inputs)
-- ============================================================================

/-- RR4.5: the round trip, at a concrete fault. -/
example (ctx : FaultContext) :
    decodeFault (encodeFault (.vmFault 0x4000 0x9600_0007 false) ctx).1
        (encodeFault (.vmFault 0x4000 0x9600_0007 false) ctx).2
      = some (.vmFault 0x4000 0x9600_0007 false) :=
  decodeFault_encodeFault _ ctx

/-- RR4.19: the progress theorem, at a concrete core. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (f : Fault) (fctx : FaultContext) :
    ¬ dispatchableOnCore (faultDeliverOnCore st tid f fctx bootCoreId).1 tid bootCoreId :=
  faultDeliverOnCore_not_dispatchable st tid f fctx bootCoreId

/-- RR4.20: a policy-refused fault suspends rather than errors, so the refusal
inherits the progress guarantee instead of punching a hole in it. -/
example (lctx : LabelingContext) (st : SystemState) (tid : SeLe4n.ThreadId)
    (f : Fault) (fctx : FaultContext) (tgt : FaultHandlerTarget)
    (hRes : resolveFaultHandler st tid = .ok tgt)
    (hDeny : endpointFlowGate lctx tgt.endpoint (lctx.threadLabelOf tid)
      (lctx.endpointLabelOf tgt.endpoint) = false) :
    tid ∉ (faultDeliverOnCoreChecked lctx st tid f fctx bootCoreId).1.scheduler.runQueueOnCore
        bootCoreId ∧
    (faultDeliverOnCoreChecked lctx st tid f fctx bootCoreId).1.scheduler.currentOnCore bootCoreId
      ≠ some tid :=
  faultDeliverOnCoreChecked_denied_not_runnable lctx st tid f fctx bootCoreId tgt hRes hDeny

/-- RR4.8: a resolved handler capability carries send **and** one of the two
grant rights — seL4's `sendFaultIPC` predicate, over the result. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (tgt : FaultHandlerTarget)
    (hOk : resolveFaultHandler st tid = .ok tgt) :
    tgt.cap.hasRight .write = true ∧
      (tgt.cap.hasRight .grant = true ∨ tgt.cap.hasRight .grantReply = true) :=
  resolveFaultHandler_authorized st tid tgt hOk

/-- Audit round (ABI v3): a fault message's label is a delivery label, never a
kernel-status one — a handler's decoder reads a successful receive. -/
example (f : Fault) : faultLabel f < errorLabelBase :=
  faultLabel_lt_errorLabelBase f

/-- Audit round: the context the fault entry delivers is the trap frame's
window, not the register mirror's stale contents. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (w : FaultRegisterWindow) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) (hObjInv : st.objects.invExt) (ip spsr : UInt64) :
    (faultContextOfThread (writeFaultRegistersToTcb st tid w) tid ip spsr).sp = w.sp :=
  by rw [faultContextOfThread_writeFaultRegistersToTcb st tid w tcb hTcb hObjInv ip spsr]

/-- RR4.21: a data abort no longer *returns* a VM fault to the thread that
took it — it delivers one, and the thread is not dispatchable afterwards. -/
example (ectx : ExceptionContext) (st : SystemState) (c : CoreId)
    (tid : SeLe4n.ThreadId) (sgi? : Option (CoreId × SgiKind)) (st' : SystemState)
    (hCls : classifySynchronousException ectx ≠ .svc)
    (hK : classifySynchronousException ectx ≠ .kernelAbort)
    (hCur : st.scheduler.currentOnCore c = some tid)
    (hStep : dispatchSynchronousException ectx st c = .ok (sgi?, st')) :
    ¬ dispatchableOnCore st' tid c :=
  dispatchSynchronousException_nonSvc_thread_not_dispatchable ectx st c tid sgi? st'
    hCls hK hCur hStep

-- ============================================================================
-- §3  Runtime fixture — four cores, four threads
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- The four RPi5 cores. -/
private def c0 : CoreId := bootCoreId
private def c1 : CoreId := ⟨1, by decide⟩
private def c2 : CoreId := ⟨2, by decide⟩
private def c3 : CoreId := ⟨3, by decide⟩

-- Fixture OIDs (range 1100–1140 — see the range table in SeLe4n/Testing/Helpers.lean).
private def cnRoot : SeLe4n.ObjId := ⟨1100⟩
private def vsRoot : SeLe4n.ObjId := ⟨1101⟩
private def epHandler : SeLe4n.ObjId := ⟨1110⟩
private def faulter : SeLe4n.ThreadId := ⟨1121⟩
private def handler : SeLe4n.ThreadId := ⟨1122⟩
private def orphan : SeLe4n.ThreadId := ⟨1123⟩
private def weak : SeLe4n.ThreadId := ⟨1124⟩
/-- A second client on core 0 whose handler capability carries send and
**grant-reply** (no full grant) — the idiomatic seL4 fault-handler shape. -/
private def grantReplyFaulter : SeLe4n.ThreadId := ⟨1125⟩
private def replyH : SeLe4n.ReplyId := ⟨1131⟩

/-- Slot 0 of the root CNode: the fault-handler capability, carrying send
(`.write`) and grant — one satisfying shape of `faultHandlerCapAuthorized`. -/
private def handlerCPtr : SeLe4n.CPtr := SeLe4n.CPtr.ofNat 0
/-- Slot 1: the **same endpoint**, read-only.  A thread pointed here has a
resolvable handler that is refused on rights alone, which is the negative that
distinguishes "no handler" from "an unusable one". -/
private def weakCPtr : SeLe4n.CPtr := SeLe4n.CPtr.ofNat 1
/-- Slot 2: the same endpoint with send and **grant-reply** only —
`seL4_CapRights_new(0, 1, 0, 1)`, the shape seL4 documents for a fault
handler, which withholds full grant.  seL4's `sendFaultIPC` admits it; a
send-and-grant reading refused it. -/
private def grantReplyCPtr : SeLe4n.CPtr := SeLe4n.CPtr.ofNat 2

private def rootCnode : CNode :=
  { depth := 2
    guardWidth := 0
    guardValue := 0
    radixWidth := 2
    slots := SeLe4n.UniqueSlotMap.ofListWF [
      (SeLe4n.Slot.ofNat 0,
        { target := .object epHandler
          rights := AccessRightSet.ofList [.read, .write, .grant]
          badge := some (SeLe4n.Badge.ofNat 7) }),
      (SeLe4n.Slot.ofNat 1,
        { target := .object epHandler
          rights := AccessRightSet.ofList [.read]
          badge := none }),
      (SeLe4n.Slot.ofNat 2,
        { target := .object epHandler
          rights := AccessRightSet.ofList [.write, .grantReply]
          badge := some (SeLe4n.Badge.ofNat 9) })
    ] }

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId)
    (fh : Option SeLe4n.CPtr) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := vsRoot, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
    threadState := .Ready, cpuAffinity := aff, faultHandler := fh,
    registerContext :=
      { pc := ⟨0⟩, sp := ⟨0x7000⟩,
        gpr := fun r => if r.val = 30 then ⟨0xF00D⟩ else ⟨r.val * 100⟩ } }

/-- The 4-core fault workload's pre-state. -/
private def stFault : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject cnRoot (.cnode rootCnode)
      |>.withObject epHandler (.endpoint {})
      |>.withObject faulter.toObjId (.tcb (mkTcb 1121 40 none (some handlerCPtr)))
      |>.withObject handler.toObjId (.tcb (mkTcb 1122 50 (some c1) none))
      |>.withObject orphan.toObjId (.tcb (mkTcb 1123 40 (some c2) none))
      |>.withObject weak.toObjId (.tcb (mkTcb 1124 40 (some c3) (some weakCPtr)))
      |>.withObject grantReplyFaulter.toObjId
          (.tcb (mkTcb 1125 30 none (some grantReplyCPtr)))
      |>.withObject replyH.toObjId (.reply { replyId := replyH })
      |>.build)
  { base with scheduler :=
      ((((base.scheduler.setRunQueueOnCore c0
            (RunQueue.ofList [(faulter, ⟨40⟩), (grantReplyFaulter, ⟨30⟩)])).setRunQueueOnCore
        c1 (RunQueue.ofList [(handler, ⟨50⟩)])).setRunQueueOnCore
        c2 (RunQueue.ofList [(orphan, ⟨40⟩)])).setRunQueueOnCore
        c3 (RunQueue.ofList [(weak, ⟨40⟩)])) }

/-- The state with each core's current thread set — a faulting thread is by
definition the one its core was running. -/
private def stRunning : SystemState :=
  { stFault with scheduler :=
      ((((stFault.scheduler.setCurrentOnCore c0 (some faulter)).setCurrentOnCore
        c1 (some handler)).setCurrentOnCore
        c2 (some orphan)).setCurrentOnCore
        c3 (some weak)) }

/-- The syndrome of a data abort on an unmapped page: EC 0x24 (data abort from
a lower EL), a fault address, and an ELR addressing the faulting instruction. -/
private def dataAbortCtx : ExceptionContext :=
  { esr := UInt64.ofNat ((0x24 <<< 26) ||| 0x7), elr := 0x4_0000, spsr := 0x3C0,
    far := 0xDEAD_0000 }

/-- The fault that syndrome classifies to. -/
private def theFault : Fault := .vmFault 0xDEAD_0000 (UInt64.ofNat ((0x24 <<< 26) ||| 0x7)) false


-- Fail-closed plumbing: a failed step names itself, so a pipeline break
-- reports the exact failing transition instead of a blanket failure.
private def stepPair {α : Type} (label : String)
    (r : SystemState × Except KernelError α) : Except String (SystemState × α) :=
  match r with
  | (st, .ok a) => .ok (st, a)
  | (_, .error e) => .error s!"{label}: {repr e}"

/-- The error an `Except` carried, if any — `Except` has no `BEq` for these
payload types, and a decidable comparison on the *error* is all the negative
assertions need. -/
private def errorOf {α : Type} (r : Except KernelError α) : Option KernelError :=
  match r with
  | .error e => some e
  | .ok _ => none

private def resolveErr (st : SystemState) (tid : SeLe4n.ThreadId) : Option KernelError :=
  errorOf (resolveFaultHandler st tid)

private def ipcStateOf (st : SystemState) (tid : SeLe4n.ThreadId) : Option ThreadIpcState :=
  (st.getTcb? tid).map (·.ipcState)

private def threadStateOf (st : SystemState) (tid : SeLe4n.ThreadId) : Option ThreadState :=
  (st.getTcb? tid).map (·.threadState)

private def pendingFaultOf (st : SystemState) (tid : SeLe4n.ThreadId) : Option ThreadFault :=
  (st.getTcb? tid).bind (·.pendingFault)

private def savedPcOf (st : SystemState) (tid : SeLe4n.ThreadId) : Option Nat :=
  (st.getTcb? tid).map (·.registerContext.pc.val)

private def deliveredMessageOf (st : SystemState) (tid : SeLe4n.ThreadId) : Option IpcMessage :=
  (st.getTcb? tid).bind (·.pendingMessage)

/-- Is `tid` dispatchable on core `c` — in its run queue or its current thread?
The runtime reading of `dispatchableOnCore`, which RR4.19 forbids of a thread
that has just faulted. -/
private def dispatchableOn (st : SystemState) (tid : SeLe4n.ThreadId) (c : CoreId) : Bool :=
  (st.scheduler.runQueueOnCore c).contains tid ||
    (st.scheduler.currentOnCore c == some tid)

-- ============================================================================
-- §4  The wire format (RR4.4–RR4.6)
-- ============================================================================

private def sampleCtx : FaultContext :=
  { faultIP := 0x4_0000, sp := 0x7000, lr := 0xF00D, spsr := 0x3C0,
    gprs := #[1, 2, 3, 4, 5, 6, 7, 8] }

/-- Every fault kind, so the round trip is checked on the whole inductive
rather than on a representative. -/
private def allFaultKinds : List Fault :=
  [ .vmFault 0xDEAD_0000 0x9600_0007 false
  , .vmFault 0xBEEF_1000 0x8200_000F true
  , .capFault 0x2A false .invalidCapability
  , .capFault 0x2B true .objectNotFound
  , .unknownSyscall 0xFFFF
  , .userException 0x22 0x0100_0000 ]

private def runEncodingChecks : IO Unit := do
  IO.println "--- §4 fault wire format (RR4.4-RR4.6) ---"
  for f in allFaultKinds do
    let (mi, regs) := encodeFault f sampleCtx
    assertBool s!"round trip: {repr f}" (decodeFault mi regs == some f)
    assertBool s!"declared length is the real one: {repr f}" (regs.size == mi.length)
    assertBool s!"inside the message-register budget: {repr f}"
      (decide (regs.size ≤ maxMessageRegisters))
    assertBool s!"carries no capabilities: {repr f}" (mi.extraCaps == 0)
    assertBool s!"label is never the null/success tag: {repr f}"
      (mi.label != FaultLabel.nullFault)
    assertBool s!"label is neither reserved MCS tag (timeout 5, debug 4): {repr f}"
      (mi.label != FaultLabel.timeout && mi.label != FaultLabel.debugException)
  -- PR #887 review round 2: the tags are seL4's MCS layout — `Timeout` is 5,
  -- `VMFault` 6 — not the non-MCS layout in which the VM fault is 5.
  assertBool "MCS layout: DebugException = 4, Timeout = 5, VMFault = 6"
    (FaultLabel.debugException == 4 && FaultLabel.timeout == 5 && FaultLabel.vmFault == 6)
  assertBool "a VM fault is delivered under tag 6, never under the timeout tag"
    (faultLabel (.vmFault 0 0 false) == 6 &&
      faultLabel (.vmFault 0 0 false) != FaultLabel.timeout)
  -- The contextual words reach the handler, at the seL4 indices.
  let (_, vmRegs) := encodeFault (.vmFault 0xDEAD_0000 0x9600_0007 true) sampleCtx
  assertBool "vmFault MR0 is the restart PC" (wordAt vmRegs 0 == sampleCtx.faultIP)
  assertBool "vmFault MR1 is the fault address" (wordAt vmRegs 1 == 0xDEAD_0000)
  assertBool "vmFault MR2 is the prefetch flag" (wordAt vmRegs 2 == 1)
  assertBool "vmFault MR3 is the syndrome" (wordAt vmRegs 3 == 0x9600_0007)
  let (_, usRegs) := encodeFault (.unknownSyscall 0x1234) sampleCtx
  assertBool "unknownSyscall MR0-MR7 are the argument window"
    (List.range 8 |>.all (fun i => wordAt usRegs i == sampleCtx.gprAt i))
  assertBool "unknownSyscall MR8 is the restart PC" (wordAt usRegs 8 == sampleCtx.faultIP)
  assertBool "unknownSyscall MR9 is the stack pointer" (wordAt usRegs 9 == sampleCtx.sp)
  assertBool "unknownSyscall MR10 is the link register" (wordAt usRegs 10 == sampleCtx.lr)
  assertBool "unknownSyscall MR12 is the syscall number" (wordAt usRegs 12 == 0x1234)
  -- Distinct kinds are distinguishable by label alone — the property a handler
  -- reads first, and the reason `IpcMessage` had to gain one.
  assertBool "vmFault and userException carry different labels"
    (faultLabel (.vmFault 0 0 false) != faultLabel (.userException 0 0))

private def runClassificationChecks : IO Unit := do
  IO.println "--- §4b ESR classification (RR4.3 / RR4.25) ---"
  let mk (ec : Nat) : ExceptionContext :=
    { esr := UInt64.ofNat (ec <<< 26), elr := 0, spsr := 0, far := 0xFACE }
  assertBool "EC 0x15 is SVC, and SVC yields no fault"
    (faultOfExceptionContext (mk 0x15) == none)
  assertBool "EC 0x24 is a non-prefetch VM fault"
    (faultOfExceptionContext (mk 0x24) ==
      some (.vmFault 0xFACE (UInt64.ofNat (0x24 <<< 26)) false))
  assertBool "EC 0x20 is a prefetch VM fault"
    (faultOfExceptionContext (mk 0x20) ==
      some (.vmFault 0xFACE (UInt64.ofNat (0x20 <<< 26)) true))
  assertBool "EC 0x22 is a user exception"
    (faultOfExceptionContext (mk 0x22) ==
      some (.userException 0x22 (UInt64.ofNat (0x22 <<< 26))))
  -- RR4.25: the exported tags are the classification the Rust router matches.
  assertBool "exported tag: SVC = 0" (classifySynchronousExceptionExport (UInt64.ofNat (0x15 <<< 26)) == 0)
  assertBool "exported tag: dataAbort = 1" (classifySynchronousExceptionExport (UInt64.ofNat (0x24 <<< 26)) == 1)
  assertBool "exported tag: instrAbort = 2" (classifySynchronousExceptionExport (UInt64.ofNat (0x20 <<< 26)) == 2)
  assertBool "exported tag: pcAlignment = 3" (classifySynchronousExceptionExport (UInt64.ofNat (0x22 <<< 26)) == 3)
  assertBool "exported tag: spAlignment = 4" (classifySynchronousExceptionExport (UInt64.ofNat (0x26 <<< 26)) == 4)
  assertBool "exported tag: unknownReason = 5" (classifySynchronousExceptionExport (UInt64.ofNat (0x3F <<< 26)) == 5)
  -- PR #887 review: a current-EL abort is the kernel's own fault — its own
  -- class, its own tag, and never a user fault.
  assertBool "exported tag: kernelAbort = 6 (EC 0x25, data abort from the current EL)"
    (classifySynchronousExceptionExport (UInt64.ofNat (0x25 <<< 26)) == 6)
  assertBool "exported tag: kernelAbort = 6 (EC 0x21, instruction abort from the current EL)"
    (classifySynchronousExceptionExport (UInt64.ofNat (0x21 <<< 26)) == 6)
  assertBool "a current-EL data abort yields no user fault"
    (faultOfExceptionContext (mk 0x25) == none)
  assertBool "a current-EL instruction abort yields no user fault"
    (faultOfExceptionContext (mk 0x21) == none)
  assertBool "the EL0 origin predicate reads SPSR_EL1.M[3:2]"
    (ExceptionContext.takenFromEl0 { esr := 0, elr := 0, spsr := 0x3C0, far := 0 } &&
     ExceptionContext.takenFromEl0 { esr := 0, elr := 0, spsr := 0x10, far := 0 } &&
     !ExceptionContext.takenFromEl0 { esr := 0, elr := 0, spsr := 0x3C5, far := 0 } &&
     !ExceptionContext.takenFromEl0 { esr := 0, elr := 0, spsr := 0x3C4, far := 0 })
  -- Every one of the 64 EC values agrees with the tag table `trap.rs` mirrors.
  let expected (ec : Nat) : UInt32 :=
    if ec == 0x15 then 0
    else if ec == 0x24 then 1
    else if ec == 0x20 then 2
    else if ec == 0x25 || ec == 0x21 then 6
    else if ec == 0x22 then 3
    else if ec == 0x26 then 4
    else 5
  assertBool "all 64 EC values classify to the tag table trap.rs mirrors"
    ((List.range 64).all (fun ec =>
      classifySynchronousExceptionExport (UInt64.ofNat (ec <<< 26)) == expected ec))

-- ============================================================================
-- §5  Handler resolution and its rights gate (RR4.7 / RR4.8 / RR4.10)
-- ============================================================================

private def runResolutionChecks : IO Unit := do
  IO.println "--- §5 handler resolution (RR4.7/RR4.8/RR4.10) ---"
  match resolveFaultHandler stRunning faulter with
  | .ok tgt =>
      assertBool "faulter's handler resolves to the handler endpoint" (tgt.endpoint == epHandler)
      assertBool "the resolved capability carries send" (tgt.cap.hasRight .write)
      assertBool "the resolved capability carries grant" (tgt.cap.hasRight .grant)
      assertBool "the resolved capability's badge rides the fault message"
        (tgt.cap.badge == some (SeLe4n.Badge.ofNat 7))
      assertBool "the caller's own CSpace root is threaded" (tgt.cspaceRoot == cnRoot)
  | .error e =>
      assertBool s!"faulter's handler must resolve (got {repr e})" false
  assertBool "a thread with no faultHandler does not resolve"
    (resolveErr stRunning orphan == some .invalidCapability)
  assertBool "a read-only handler capability is refused on rights"
    (resolveErr stRunning weak == some .illegalAuthority)
  assertBool "a thread that is not a TCB does not resolve"
    (resolveErr stRunning ⟨1199⟩ == some .objectNotFound)
  -- Audit round (RR4.8): the gate is seL4's `sendFaultIPC` predicate — send,
  -- and grant OR grant-reply.  The idiomatic handler capability withholds full
  -- grant and carries grant-reply; a send-and-grant reading refused it.
  let capWith (rs : List AccessRight) : Capability :=
    { target := .object epHandler, rights := AccessRightSet.ofList rs }
  assertBool "send + grant-reply is an authorised fault-handler capability"
    (faultHandlerCapAuthorized (capWith [.write, .grantReply]))
  assertBool "send + grant is authorised too"
    (faultHandlerCapAuthorized (capWith [.write, .grant]))
  assertBool "send alone is refused — the handler could not be handed reply authority"
    (!faultHandlerCapAuthorized (capWith [.write]))
  assertBool "grant + grant-reply without send is refused — nothing could be delivered"
    (!faultHandlerCapAuthorized (capWith [.grant, .grantReply]))
  assertBool "read alone is refused" (!faultHandlerCapAuthorized (capWith [.read]))
  match resolveFaultHandler stRunning grantReplyFaulter with
  | .ok tgt =>
      assertBool "a send + grant-reply handler capability resolves through the CSpace"
        (tgt.endpoint == epHandler && tgt.cap.badge == some (SeLe4n.Badge.ofNat 9))
      assertBool "…and it is the grant-reply right, not grant, that admitted it"
        (tgt.cap.hasRight .grantReply && !tgt.cap.hasRight .grant)
  | .error e =>
      assertBool s!"the grant-reply handler must resolve (got {repr e})" false
  -- …and the delivery through such a capability works end to end: the Call
  -- chain links the reply structurally, so withholding full grant costs the
  -- handler nothing it needs.
  match endpointReceiveDualOnCore epHandler handler (some replyH) c1 stRunning with
  | (stRecv, .ok _) =>
      let fctxG := faultContextOfThread stRecv grantReplyFaulter 0x4_0100 0x3C0
      let (stG, resG) := faultDeliverOnCore stRecv grantReplyFaulter theFault fctxG c0
      assertBool "a fault delivered through a send + grant-reply capability reaches the handler"
        (resG.disposition == .delivered epHandler)
      assertBool "…and the reply object links the faulting thread as its caller"
        ((stG.getReply? replyH).bind (·.caller) == some grantReplyFaulter)
      assertBool "…carrying that capability's own badge"
        ((deliveredMessageOf stG handler).bind (·.badge) == some (SeLe4n.Badge.ofNat 9))
  | (_, .error e) =>
      assertBool s!"handler recv must succeed (got {repr e})" false

-- ============================================================================
-- §6  Delivery across cores (RR4.11 / RR4.12) and the fail-closed path (RR4.9)
-- ============================================================================

/-- The delivered-fault pipeline: the handler blocks on its endpoint from core
1, the faulter takes a data abort on core 0, and the resulting cross-core
`.reschedule` SGI is handled on core 1. -/
private structure Delivery where
  afterRecv : SystemState
  afterFault : SystemState
  result : FaultDeliveryResult
  afterSgi : SystemState

private def deliveryE : Except String Delivery := do
  let (afterRecv, _) ← stepPair "step1: handler recv on core 1"
    (endpointReceiveDualOnCore epHandler handler (some replyH) c1 stRunning)
  let fctx := faultContextOfThread afterRecv faulter dataAbortCtx.elr dataAbortCtx.spsr
  let (afterFault, result) := faultDeliverOnCore afterRecv faulter theFault fctx c0
  let afterSgi ←
    match handleRescheduleSgiOnCore afterFault c1 with
    | .ok st => .ok st
    | .error e => .error s!"step3: core 1 SGI handler: {repr e}"
  pure { afterRecv := afterRecv, afterFault := afterFault, result := result,
         afterSgi := afterSgi }

private def delivery? : Option Delivery := deliveryE.toOption

private def runDeliveryChecks : IO Unit := do
  IO.println "--- §6 fault delivery across cores (RR4.11/RR4.12) ---"
  match deliveryE with
  | .error e => assertBool s!"delivery pipeline: {e}" false
  | .ok d =>
      assertBool "handler blocks on its endpoint from core 1"
        (ipcStateOf d.afterRecv handler == some (.blockedOnReceive epHandler))
      assertBool "the fault is delivered to the handler endpoint"
        (d.result.disposition == .delivered epHandler)
      assertBool "the delivery surfaces a .reschedule SGI to the handler's core"
        (d.result.sgi == some (c1, SgiKind.reschedule))
      assertBool "the faulter blocks awaiting the handler's reply"
        (ipcStateOf d.afterFault faulter == some (.blockedOnReply epHandler (some handler)))
      assertBool "the faulter carries the fault it took (seL4's tcbFault)"
        (pendingFaultOf d.afterFault faulter ==
          some { fault := theFault,
                 context := faultContextOfThread d.afterRecv faulter dataAbortCtx.elr
                   dataAbortCtx.spsr })
      assertBool "the handler is woken with the fault message"
        ((deliveredMessageOf d.afterFault handler).isSome)
      -- The delivered message is the encoded fault, register for register,
      -- with the handler capability's badge and the fault's `seL4_Fault_tag`.
      -- Compared field-wise rather than whole: the Call chain re-stamps
      -- `capsGranted` from the *endpoint capability's* rights (a fault handler
      -- capability carries `.grant`, so the bit arrives set), which authorises
      -- nothing on a message with no capabilities — see
      -- `faultMessage_grant_is_inert`, and the `caps.isEmpty` assertion below.
      let expectedMsg := faultMessage theFault
        (faultContextOfThread d.afterRecv faulter dataAbortCtx.elr dataAbortCtx.spsr)
        (some (SeLe4n.Badge.ofNat 7))
      assertBool "the delivered message's registers are the encoded fault"
        ((deliveredMessageOf d.afterFault handler).map (·.registers) ==
          some expectedMsg.registers)
      assertBool "the delivered message's label is the fault's seL4_Fault_tag"
        ((deliveredMessageOf d.afterFault handler).map (·.label) ==
          some (faultLabel theFault))
      assertBool "the delivered message carries the handler capability's badge"
        ((deliveredMessageOf d.afterFault handler).bind (·.badge) ==
          some (SeLe4n.Badge.ofNat 7))
      assertBool "the handler can recover the fault from the message it received"
        (match deliveredMessageOf d.afterFault handler with
         | some m => decodeFault
             { length := faultMessageLength theFault, extraCaps := 0, label := m.label }
             m.registers == some theFault
         | none => false)
      assertBool "the message carries no capabilities across the boundary"
        (match deliveredMessageOf d.afterFault handler with
         | some m => m.caps.isEmpty
         | none => false)
      assertBool "core 1 dispatches the handler after the SGI"
        (d.afterSgi.scheduler.currentOnCore c1 == some handler)
      -- PR #887 review: the woken handler's **return frame** is staged by the
      -- delivery — `x0` the badge, `x1` the MessageInfo carrying the fault
      -- tag, `x2`-`x5` the first four fault words — so the context restore
      -- hands it the message, not its stale receive-syscall registers.
      let fr := SeLe4n.Kernel.Architecture.readReturnFrame d.afterFault handler
      assertBool "the woken handler's staged x0 is the handler capability's badge"
        (fr.x0 == 7)
      assertBool "the woken handler's staged x1 carries the fault tag, length 4"
        (fr.x1 == (MessageInfo.encode { length := 4, extraCaps := 0, label := 6 }).toUInt64)
      assertBool "the woken handler's staged x2-x5 are MR0-MR3 of the fault message"
        (fr.x2 == dataAbortCtx.elr && fr.x3 == 0xDEAD_0000 && fr.x4 == 0 &&
          fr.x5 == dataAbortCtx.esr)
      assertBool "control: before the delivery those registers held the mirror's stale values"
        ((SeLe4n.Kernel.Architecture.readReturnFrame d.afterRecv handler).x2 == 200)

private def runNoHandlerChecks : IO Unit := do
  IO.println "--- §6b the fail-closed no-handler policy (RR4.9/RR4.10) ---"
  let fctxO := faultContextOfThread stRunning orphan 0x5_0000 0x3C0
  let (stO, resO) := faultDeliverOnCore stRunning orphan theFault fctxO c2
  assertBool "a thread with no fault handler is suspended, not delivered"
    (resO.disposition == .suspended)
  assertBool "the fail-closed path fires no SGI" (resO.sgi == none)
  assertBool "the suspended thread is marked .Inactive"
    (threadStateOf stO orphan == some .Inactive)
  assertBool "the suspended thread keeps the fault that stopped it (the diagnostic)"
    ((pendingFaultOf stO orphan).isSome)
  assertBool "the suspended thread is out of its core's run queue"
    (!dispatchableOn stO orphan c2)
  -- A resolvable-but-unusable handler takes the same path, which is what
  -- distinguishes "no handler" from "one that could never reply".
  let fctxW := faultContextOfThread stRunning weak 0x6_0000 0x3C0
  let (stW, resW) := faultDeliverOnCore stRunning weak theFault fctxW c3
  assertBool "a read-only handler capability also suspends, fail-closed"
    (resW.disposition == .suspended)
  assertBool "the rights-refused thread is marked .Inactive"
    (threadStateOf stW weak == some .Inactive)
  assertBool "the rights-refused thread is out of its core's run queue"
    (!dispatchableOn stW weak c3)

-- ============================================================================
-- §6c  The flow gate on the live delivery (RR4.20)
-- ============================================================================

/-- Everything `publicLabel`: the lattice admits the flow and no endpoint
override exists, so the gate is `true` and the checked delivery is the
unchecked one. -/
private def permissiveCtx : LabelingContext :=
  { objectLabelOf := fun _ => SecurityLabel.publicLabel
    threadLabelOf := fun _ => SecurityLabel.publicLabel
    endpointLabelOf := fun _ => SecurityLabel.publicLabel
    serviceLabelOf := fun _ => SecurityLabel.publicLabel }

/-- The faulting thread is `kernelTrusted` (high confidentiality) and the
handler endpoint is `publicLabel` (low): the **global lattice** denies the
flow, so no endpoint override can rescue it. -/
private def latticeDenyingCtx : LabelingContext :=
  { permissiveCtx with
    threadLabelOf := fun tid =>
      if tid == faulter then SecurityLabel.kernelTrusted else SecurityLabel.publicLabel }

/-- The two label functions disagree, and only `endpointLabelOf` denies: the
faulting thread is `kernelTrusted` (high), `objectLabelOf` calls the handler
endpoint `kernelTrusted` too (high → high: **admitted**), and `endpointLabelOf`
calls it `publicLabel` (high → low: **denied**).  A delivery here would mean the
fault path consults a label no other endpoint-keyed gate uses. -/
private def endpointLabelDenyingCtx : LabelingContext :=
  { permissiveCtx with
    threadLabelOf := fun tid =>
      if tid == faulter then SecurityLabel.kernelTrusted else SecurityLabel.publicLabel
    objectLabelOf := fun _ => SecurityLabel.kernelTrusted
    endpointLabelOf := fun _ => SecurityLabel.publicLabel }

/-- The mirror control: `objectLabelOf` denies (high → low) while
`endpointLabelOf` admits (high → high).  A *suspend* here would mean the gate is
reading `objectLabelOf`, so this arm has to deliver. -/
private def objectLabelDenyingCtx : LabelingContext :=
  { permissiveCtx with
    threadLabelOf := fun tid =>
      if tid == faulter then SecurityLabel.kernelTrusted else SecurityLabel.publicLabel
    objectLabelOf := fun _ => SecurityLabel.publicLabel
    endpointLabelOf := fun _ => SecurityLabel.kernelTrusted }

/-- Labels the lattice admits, but the handler endpoint carries an override
that denies every pair — the second conjunct of the gate, exercised on its
own. -/
private def overrideDenyingCtx : LabelingContext :=
  { permissiveCtx with
    endpointPolicy :=
      { endpointPolicy := fun oid =>
          if oid == epHandler then some { canFlow := fun _ _ => false } else none } }

/-- The fault window the trap frame carries into the entry — values chosen to
differ from every register the fixture's TCB mirror holds (`gpr r = r * 100`,
`x30 = 0xF00D`, `sp = 0x7000`), so a context built from the mirror instead of
the window is distinguishable at every word. -/
private def trapWindow : FaultRegisterWindow :=
  { gprs := #[0x11, 0x12, 0x13, 0x14, 0x15, 0x16, 0x17, 0x18], sp := 0x7770, lr := 0xBEEF }

private def runFlowGateChecks : IO Unit := do
  IO.println "--- §6c the flow gate on the live delivery (RR4.20) ---"
  let fctx := faultContextOfThread stRunning faulter 0x4_0000 0x3C0
  -- A permitted flow delivers, and delivers exactly what the unchecked arm
  -- would: the gate is a precondition, not a second transition.
  let (stP, resP) := faultDeliverOnCoreChecked permissiveCtx stRunning faulter theFault fctx c0
  let (stU, resU) := faultDeliverOnCore stRunning faulter theFault fctx c0
  assertBool "a permitted flow delivers to the handler endpoint"
    (resP.disposition == .delivered epHandler)
  assertBool "and the permitted arm is state-identical to the unchecked delivery"
    (threadStateOf stP handler == threadStateOf stU handler &&
     threadStateOf stP faulter == threadStateOf stU faulter &&
     resP.sgi == resU.sgi)
  -- A flow the global lattice denies takes the fail-closed suspend.
  let (stL, resL) := faultDeliverOnCoreChecked latticeDenyingCtx stRunning faulter theFault fctx c0
  assertBool "a lattice-denied flow does not deliver" (resL.disposition == .suspended)
  assertBool "the lattice-denied fault fires no SGI" (resL.sgi == none)
  assertBool "the lattice-denied faulting thread is .Inactive, not resumed"
    (threadStateOf stL faulter == some .Inactive)
  assertBool "the lattice-denied faulting thread keeps its fault as a diagnostic"
    ((pendingFaultOf stL faulter).isSome)
  assertBool "the lattice-denied faulting thread is not dispatchable on the core it faulted on"
    (!dispatchableOn stL faulter c0)
  assertBool "the handler learns nothing: it is still blocked in its receive"
    (threadStateOf stL handler == threadStateOf stRunning handler)
  -- The gate reads the endpoint label, not the object label: this context
  -- leaves every `objectLabelOf` permissive and denies only through
  -- `endpointLabelOf`, so a delivery here would mean the fault path is
  -- consulting a label no other endpoint gate uses.
  let (stE, resE) :=
    faultDeliverOnCoreChecked endpointLabelDenyingCtx stRunning faulter theFault fctx c0
  assertBool "the gate reads endpointLabelOf: an endpoint-label denial suspends"
    (resE.disposition == .suspended)
  assertBool "…even though objectLabelOf would have admitted that same flow"
    (securityFlowsTo (endpointLabelDenyingCtx.threadLabelOf faulter)
       (endpointLabelDenyingCtx.objectLabelOf epHandler) &&
     !dispatchableOn stE faulter c0 && threadStateOf stE faulter == some .Inactive)
  let (_, resB) :=
    faultDeliverOnCoreChecked objectLabelDenyingCtx stRunning faulter theFault fctx c0
  assertBool "and the mirror: an objectLabelOf denial the endpoint label admits still delivers"
    (!securityFlowsTo (objectLabelDenyingCtx.threadLabelOf faulter)
        (objectLabelDenyingCtx.objectLabelOf epHandler) &&
     resB.disposition == .delivered epHandler)
  -- …and so does one only the endpoint's own override denies.
  let (stO, resO) := faultDeliverOnCoreChecked overrideDenyingCtx stRunning faulter theFault fctx c0
  assertBool "an endpoint-override-denied flow does not deliver either"
    (resO.disposition == .suspended)
  assertBool "the override-denied faulting thread is not dispatchable"
    (!dispatchableOn stO faulter c0)
  -- The live entry is the gated arm, not the bare transition: the same denial
  -- reached through `faultEntryStep` must suspend rather than deliver.  The
  -- pre-state assertion is what keeps the two below from passing vacuously —
  -- `.Inactive` and "not dispatchable" are only evidence if the thread was
  -- running on that core to begin with.
  assertBool "pre-state: the faulting thread is current on core 0 and not yet .Inactive"
    (stRunning.scheduler.currentOnCore c0 == some faulter &&
     threadStateOf stRunning faulter != some .Inactive)
  let (sgisD, stD) := faultEntryStep latticeDenyingCtx stRunning dataAbortCtx trapWindow 0
  assertBool "the live fault entry applies the flow gate: a denied fault fires no SGI"
    (sgisD.isEmpty)
  assertBool "the live fault entry's denied arm suspends the faulting thread"
    (threadStateOf stD faulter == some .Inactive)
  assertBool "the live fault entry's denied arm leaves it undispatchable"
    (!dispatchableOn stD faulter c0)
  assertBool "the live fault entry's denied arm records the fault as a diagnostic"
    ((pendingFaultOf stD faulter).isSome)
  -- …and the gate is not a no-op: the same syndrome under a permitting context
  -- takes the delivery arm, which parks the faulter awaiting the handler rather
  -- than deactivating it.
  let (_, stA) := faultEntryStep permissiveCtx stRunning dataAbortCtx trapWindow 0
  assertBool "under a permitting context the same entry delivers instead of suspending"
    (threadStateOf stA faulter != some .Inactive &&
     (ipcStateOf stA faulter).isSome && ipcStateOf stA faulter != ipcStateOf stRunning faulter)
  assertBool "the two arms of the gate really do produce different states"
    (ipcStateOf stA faulter != ipcStateOf stD faulter)
  assertBool "but both arms honour RR4.19: the faulting thread is undispatchable either way"
    (!dispatchableOn stA faulter c0 && !dispatchableOn stD faulter c0)

-- The reply shapes §6d-§7c share.
/-- A payload-free, label-`0` reply: the ordinary VM-fault answer, "I mapped
the page, retry". -/
private def resumeInfo : MessageInfo := { length := 0, extraCaps := 0, label := 0 }
/-- A label-`0` unknown-syscall reply that overrides the restart PC (MR8) and
the argument window. -/
private def restartInfo : MessageInfo := { length := 13, extraCaps := 0, label := 0 }
private def restartRegs : Array SeLe4n.RegValue :=
  (Array.range 13).map (fun i =>
    if i == 8 then SeLe4n.RegValue.ofNat 0x9_9000        -- the new PC
    else if i == 9 then SeLe4n.RegValue.ofNat 0x7FF0     -- the new SP
    else if i == 10 then SeLe4n.RegValue.ofNat 0xABBA    -- the new LR
    else SeLe4n.RegValue.ofNat (0xA0 + i))               -- x0..x7 and the syscall word
/-- A **nonzero**-label reply: the handler's "do not continue". -/
private def abandonInfo : MessageInfo := { length := 13, extraCaps := 0, label := 1 }

-- ============================================================================
-- §6d  The other ordering: the fault arrives before the handler receives
-- ============================================================================

/-- The queued-fault pipeline: the faulter takes its abort on core 0 while the
handler is still *running* on core 1 (no receiver waiting), so the fault Call
parks on the endpoint's send queue; the handler then receives it, and answers.
The delivered pipeline (§6) covers only the receiver-waiting rendezvous; a
handler loop that is busy when its client faults is the common case, and the
message — its `seL4_Fault_tag` label above all — has to survive the queue. -/
private structure QueuedDelivery where
  afterFault : SystemState
  result : FaultDeliveryResult
  afterRecv : SystemState
  afterReply : SystemState
  outcome : FaultReplyOutcome

private def queuedDeliveryE : Except String QueuedDelivery := do
  let fctx := faultContextOfThread stRunning faulter dataAbortCtx.elr dataAbortCtx.spsr
  let (afterFault, result) := faultDeliverOnCore stRunning faulter theFault fctx c0
  let (afterRecv, _) ← stepPair "step2: handler recv on core 1 (dequeues the fault)"
    (endpointReceiveDualOnCore epHandler handler (some replyH) c1 afterFault)
  let (afterReply, outcome) ←
    match faultReplyOnCore handler faulter resumeInfo #[] c1 afterRecv with
    | (st, .ok (o, _)) => .ok (st, o)
    | (_, .error e) => .error s!"step3: handler reply: {repr e}"
  pure { afterFault := afterFault, result := result, afterRecv := afterRecv,
         afterReply := afterReply, outcome := outcome }

private def queuedDelivery? : Option QueuedDelivery := queuedDeliveryE.toOption

private def runQueuedDeliveryChecks : IO Unit := do
  IO.println "--- §6d fault queued ahead of the handler's receive ---"
  match queuedDeliveryE with
  | .error e => assertBool s!"queued pipeline: {e}" false
  | .ok q =>
      assertBool "pre: no receiver is waiting when the fault is taken"
        (ipcStateOf stRunning handler == some .ready)
      assertBool "the fault is still 'delivered' — it is queued on the handler endpoint"
        (q.result.disposition == .delivered epHandler)
      assertBool "no receiver was woken, so the delivery surfaces no SGI"
        (q.result.sgi == none)
      assertBool "the queued faulter is blocked on the endpoint as a Call sender"
        (ipcStateOf q.afterFault faulter == some (.blockedOnCall epHandler))
      assertBool "the queued faulter carries its fault while it waits"
        ((pendingFaultOf q.afterFault faulter).isSome)
      assertBool "the queued faulter is not dispatchable on the core it faulted on"
        (!dispatchableOn q.afterFault faulter c0)
      assertBool "the handler is untouched until it asks"
        (deliveredMessageOf q.afterFault handler == none)
      -- The receive dequeues the fault: the message the handler gets is the
      -- one the kernel built, label included.
      assertBool "the handler's receive dequeues the fault message"
        ((deliveredMessageOf q.afterRecv handler).isSome)
      assertBool "the dequeued message's label is the fault's seL4_Fault_tag"
        ((deliveredMessageOf q.afterRecv handler).map (·.label) == some (faultLabel theFault))
      assertBool "the dequeued message's registers are the encoded fault"
        ((deliveredMessageOf q.afterRecv handler).map (·.registers) ==
          some (faultMessage theFault
            (faultContextOfThread stRunning faulter dataAbortCtx.elr dataAbortCtx.spsr)
            (some (SeLe4n.Badge.ofNat 7))).registers)
      assertBool "the dequeued faulter now awaits the handler's reply"
        (ipcStateOf q.afterRecv faulter == some (.blockedOnReply epHandler (some handler)))
      assertBool "the reply object links the dequeued faulter as its caller"
        ((q.afterRecv.getReply? replyH).bind (·.caller) == some faulter)
      -- …and the reply resumes it exactly as in the rendezvous ordering.
      assertBool "the handler's reply resumes the queued faulter at the faulting instruction"
        (q.outcome.restartPC? == some dataAbortCtx.elr &&
          savedPcOf q.afterReply faulter == some dataAbortCtx.elr.toNat)
      assertBool "the resumed faulter is ready and its fault retired"
        (ipcStateOf q.afterReply faulter == some .ready &&
          pendingFaultOf q.afterReply faulter == none)

-- ============================================================================
-- §6e  The entry delivers the trap frame's window and every cross-core poke
-- ============================================================================

/-- A PC-alignment fault: EC 0x22, a `userException` whose message reports
`SP_EL0` at MR1 — the word that distinguishes a context built from the trap
frame from one built off the stale mirror. -/
private def pcAlignCtx : ExceptionContext :=
  { esr := UInt64.ofNat (0x22 <<< 26), elr := 0x4_0004, spsr := 0x3C0, far := 0 }

private def runEntryWindowChecks : IO Unit := do
  IO.println "--- §6e the live entry spills the trap frame's window (audit round) ---"
  match endpointReceiveDualOnCore epHandler handler (some replyH) c1 stRunning with
  | (_, .error e) => assertBool s!"handler recv must succeed (got {repr e})" false
  | (stRecv, .ok _) =>
      -- The control: what the mirror holds is NOT what the trap frame carries,
      -- so a context read off the mirror is distinguishable at every word.
      let stale := faultContextOfThread stRecv faulter pcAlignCtx.elr pcAlignCtx.spsr
      assertBool "control: the register mirror's sp/lr/x0..x7 differ from the trap window"
        (stale.sp != trapWindow.sp && stale.lr != trapWindow.lr &&
          (List.range 8).all (fun i => stale.gprAt i != trapWindow.gprAt i))
      let (sgis, stE) := faultEntryStep permissiveCtx stRecv pcAlignCtx trapWindow 0
      assertBool "the entry delivers the alignment fault"
        (ipcStateOf stE faulter == some (.blockedOnReply epHandler (some handler)))
      -- The recorded context is the window, word for word.
      let expectedCtx : FaultContext :=
        { faultIP := pcAlignCtx.elr, sp := trapWindow.sp, lr := trapWindow.lr,
          spsr := pcAlignCtx.spsr, gprs := trapWindow.gprs }
      assertBool "the recorded fault context is the trap frame's window, not the mirror's"
        ((pendingFaultOf stE faulter).map (·.context) == some expectedCtx)
      assertBool "the delivered message's MR1 (SP_EL0) is the trap frame's stack pointer"
        ((deliveredMessageOf stE handler).map (fun m => wordAt m.registers 1) ==
          some trapWindow.sp)
      assertBool "the delivered message's MR0 is the restart PC from ELR_EL1"
        ((deliveredMessageOf stE handler).map (fun m => wordAt m.registers 0) ==
          some pcAlignCtx.elr)
      -- The spill also fixes the mirror, so the SVC seam's partial spill is
      -- overwritten with the fault-time values.
      assertBool "the faulter's saved x0..x7, sp and lr are now the trap frame's"
        ((List.range 8).all (fun i =>
            (stE.getTcb? faulter).map (·.registerContext.gpr ⟨i⟩ |>.val) ==
              some (trapWindow.gprAt i).toNat) &&
          (stE.getTcb? faulter).map (·.registerContext.sp.val) == some trapWindow.sp.toNat &&
          (stE.getTcb? faulter).map (·.registerContext.gpr ⟨30⟩ |>.val) ==
            some trapWindow.lr.toNat)
      assertBool "…while the mirror's other registers are untouched"
        ((stE.getTcb? faulter).map (·.registerContext.gpr ⟨9⟩ |>.val) == some 900)
      -- The pokes come from the state diff, exactly as the syscall seam
      -- derives them: the handler woken on core 1 is a `.reschedule` to core 1.
      assertBool "the entry fires the .reschedule poke the handler's wake requires"
        (sgis == [(c1, SgiKind.reschedule)])
      assertBool "…and it is the same list the syscall seam's diff would derive"
        (sgis == PriorityInheritance.computeCrossCoreSgis stRecv stE c0)
      -- A resume reply reinstalls the window the thread actually had, not the
      -- last syscall's arguments: the defect the spill closes.
      match faultReplyOnCore handler faulter resumeInfo #[] c1 stE with
      | (stR, .ok (outcome, _)) =>
          assertBool "the resume restarts at the aligned-fault PC"
            (outcome.restartPC? == some pcAlignCtx.elr)
          assertBool "the resume reinstalls the trap frame's x0..x7 — not the stale mirror"
            ((List.range 8).all (fun i =>
              (stR.getTcb? faulter).map (·.registerContext.gpr ⟨i⟩ |>.val) ==
                some (trapWindow.gprAt i).toNat))
          assertBool "the resume reinstalls the trap frame's sp and lr"
            ((stR.getTcb? faulter).map (·.registerContext.sp.val) == some trapWindow.sp.toNat &&
              (stR.getTcb? faulter).map (·.registerContext.gpr ⟨30⟩ |>.val) ==
                some trapWindow.lr.toNat)
      | (_, .error e) =>
          assertBool s!"the resume reply must succeed (got {repr e})" false
      -- The entry's progress guarantee holds on the spilled state too.
      assertBool "the entry leaves the faulter undispatchable on core 0"
        (!dispatchableOn stE faulter c0)
      -- PR #887 review: **a kernel-origin exception is never delivered.**  The
      -- same syndrome taken from EL1 (SPSR_EL1.M = EL1h) commits nothing, and
      -- neither does a current-EL abort syndrome claiming EL0.
      let el1Ctx : ExceptionContext := { pcAlignCtx with spsr := 0x3C5 }
      let (sgisK, stK) := faultEntryStep permissiveCtx stRecv el1Ctx trapWindow 0
      assertBool "an exception taken from EL1 fires no SGI"
        (sgisK.isEmpty)
      assertBool "an exception taken from EL1 delivers nothing to the current thread"
        (ipcStateOf stK faulter == ipcStateOf stRecv faulter &&
          (pendingFaultOf stK faulter).isNone &&
          deliveredMessageOf stK handler == deliveredMessageOf stRecv handler)
      assertBool "…and does not even spill: the current thread's registers are untouched"
        ((stK.getTcb? faulter).map (·.registerContext.sp.val) == some 0x7000)
      let kernelAbortCtx : ExceptionContext :=
        { esr := UInt64.ofNat ((0x25 <<< 26) ||| 0x7), elr := 0xFFFF_0000_0000_1000,
          spsr := 0x3C0, far := 0xFFFF_0000_DEAD_0000 }
      let (sgisA, stA) := faultEntryStep permissiveCtx stRecv kernelAbortCtx trapWindow 0
      assertBool "a current-EL abort syndrome is inert even with an EL0 PSTATE"
        (sgisA.isEmpty && (pendingFaultOf stA faulter).isNone &&
          ipcStateOf stA faulter == ipcStateOf stRecv faulter)

-- ============================================================================
-- §6f  The unknown-syscall producer (PR #887 review)
-- ============================================================================

/-- An `SVC` whose syscall number (`x7`) names no `SyscallId`: the prefilter
rejects it and the trap layer routes it to the unknown-syscall seam instead of
handing the thread an error frame.  The ELR of an `SVC` addresses the
instruction *after* it. -/
private def svcCtx : ExceptionContext :=
  { esr := UInt64.ofNat (0x15 <<< 26), elr := 0x4_0008, spsr := 0x3C0, far := 0 }

private def runUnknownSyscallChecks : IO Unit := do
  IO.println "--- §6f the unknown-syscall fault has a live producer ---"
  match endpointReceiveDualOnCore epHandler handler (some replyH) c1 stRunning with
  | (_, .error e) => assertBool s!"handler recv must succeed (got {repr e})" false
  | (stRecv, .ok _) =>
      -- The generic entry is inert on an SVC: that class is the syscall path.
      let (sgisG, stG) := faultEntryStep permissiveCtx stRecv svcCtx trapWindow 0
      assertBool "the syndrome-classified entry is inert on an SVC"
        (sgisG.isEmpty && (pendingFaultOf stG faulter).isNone)
      -- The unknown-syscall entry delivers `unknownSyscall x7`.
      let (sgis, stU) := unknownSyscallEntryStep permissiveCtx stRecv svcCtx trapWindow 0
      assertBool "the unknown-syscall entry delivers the fault"
        (ipcStateOf stU faulter == some (.blockedOnReply epHandler (some handler)))
      assertBool "the fault is seL4's UnknownSyscall, carrying the trap frame's x7"
        ((pendingFaultOf stU faulter).map (·.fault) == some (.unknownSyscall trapWindow.lr) ||
          (pendingFaultOf stU faulter).map (·.fault) == some (.unknownSyscall (trapWindow.gprAt 7)))
      assertBool "the fault's syscall number is x7 of the window, not the link register"
        ((pendingFaultOf stU faulter).map (·.fault) == some (.unknownSyscall 0x18))
      match deliveredMessageOf stU handler with
      | none => assertBool "the handler must receive the unknown-syscall message" false
      | some m =>
          assertBool "the message carries the UnknownSyscall tag"
            (m.label == FaultLabel.unknownSyscall)
          assertBool "the message is thirteen words" (m.registers.size == 13)
          assertBool "MR0-MR7 are the trap frame's argument window"
            ((List.range 8).all (fun i => wordAt m.registers i == trapWindow.gprAt i))
          assertBool "MR8 is the restart PC — the instruction after the SVC"
            (wordAt m.registers 8 == svcCtx.elr)
          assertBool "MR9 is SP_EL0 and MR10 is the link register, from the trap frame"
            (wordAt m.registers 9 == trapWindow.sp && wordAt m.registers 10 == trapWindow.lr)
          assertBool "MR12 is the syscall number" (wordAt m.registers 12 == 0x18)
          assertBool "the handler can recover the fault from the message"
            (decodeFault { length := 13, extraCaps := 0, label := m.label } m.registers ==
              some (.unknownSyscall 0x18))
      assertBool "the delivery pokes the handler's core"
        (sgis == [(c1, SgiKind.reschedule)])
      assertBool "the thread that issued the unknown syscall is not dispatchable on core 0"
        (!dispatchableOn stU faulter c0)
      -- A payload-free reply — "emulated, continue" — resumes after the SVC.
      match faultReplyOnCore handler faulter resumeInfo #[] c1 stU with
      | (stR, .ok (outcome, _)) =>
          assertBool "an emulating handler's payload-free reply continues after the SVC"
            (outcome.restartPC? == some svcCtx.elr && savedPcOf stR faulter == some svcCtx.elr.toNat)
          assertBool "…with the argument window the thread had at the trap"
            ((List.range 8).all (fun i =>
              (stR.getTcb? faulter).map (·.registerContext.gpr ⟨i⟩ |>.val) ==
                some (trapWindow.gprAt i).toNat))
      | (_, .error e) =>
          assertBool s!"the emulating reply must succeed (got {repr e})" false
      -- An SVC issued at EL1 is a kernel bug, not a user fault.
      let (sgisK, stK) :=
        unknownSyscallEntryStep permissiveCtx stRecv { svcCtx with spsr := 0x3C5 } trapWindow 0
      assertBool "an SVC taken from EL1 is inert at the unknown-syscall entry"
        (sgisK.isEmpty && (pendingFaultOf stK faulter).isNone)

-- ============================================================================
-- §7d  Configuring a handler, and resuming past a fault (PR #887 review)
-- ============================================================================

/-- A TCB capability on the orphan (no handler configured), held by the
handler thread, with the write right every thread-configuration syscall
demands. -/
private def orphanTcbCap : Capability :=
  { target := .object orphan.toObjId, rights := AccessRightSet.ofList [.read, .write] }

private def configGate : SyscallGate :=
  { callerId := handler, cspaceRoot := cnRoot, capAddr := SeLe4n.CPtr.ofNat 0,
    capDepth := 2, requiredRight := .write }

/-- `tcbSetFaultHandler` with MR0 = the CPtr, in the target's CSpace. -/
private def setHandlerDecoded (cptr : Nat) : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0,
    msgInfo := { length := 1, extraCaps := 0, label := 0 },
    syscallId := .tcbSetFaultHandler,
    msgRegs := #[SeLe4n.RegValue.ofNat cptr] }

private def resumeTcbDecoded : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0,
    msgInfo := { length := 0, extraCaps := 0, label := 0 },
    syscallId := .tcbResume, msgRegs := #[] }

private def runConfigureAndResumeChecks : IO Unit := do
  IO.println "--- §7d configure a fault handler, resume past a double fault ---"
  -- The fault-handler CPtr is validated at set time by the same resolution
  -- the fault path runs: send + grant (slot 0) and send + grant-reply (slot 2)
  -- are admitted, a read-only capability (slot 1) is refused on rights, and an
  -- empty slot (3) is refused as no capability at all.
  assertBool "pre: the orphan has no fault handler"
    (resolveErr stRunning orphan == some .invalidCapability)
  match dispatchWithCap (setHandlerDecoded 0) handler configGate orphanTcbCap stRunning with
  | .ok (_, st1) =>
      assertBool "the live tcbSetFaultHandler arm installs the CPtr on the target"
        ((st1.getTcb? orphan).bind (·.faultHandler) == some (SeLe4n.CPtr.ofNat 0))
      assertBool "…and the target's handler now resolves to the handler endpoint"
        (match resolveFaultHandler st1 orphan with
         | .ok tgt => tgt.endpoint == epHandler
         | .error _ => false)
      assertBool "configuring touches no scheduler state"
        (st1.scheduler.currentOnCore c2 == stRunning.scheduler.currentOnCore c2 &&
          (st1.scheduler.runQueueOnCore c2).toList == (stRunning.scheduler.runQueueOnCore c2).toList)
      -- The configured thread's next fault is delivered, not suspended.
      match endpointReceiveDualOnCore epHandler handler (some replyH) c1 st1 with
      | (st2, .ok _) =>
          let fctx := faultContextOfThread st2 orphan 0x5_0000 0x3C0
          let (_, res) := faultDeliverOnCore st2 orphan theFault fctx c2
          assertBool "a fault on the freshly configured thread is delivered"
            (res.disposition == .delivered epHandler)
      | (_, .error e) => assertBool s!"handler recv must succeed (got {repr e})" false
  | .error e => assertBool s!"tcbSetFaultHandler must succeed (got {repr e})" false
  assertBool "a send + grant-reply capability is admitted as a handler"
    (match dispatchWithCap (setHandlerDecoded 2) handler configGate orphanTcbCap stRunning with
     | .ok (_, st') => (st'.getTcb? orphan).bind (·.faultHandler) == some (SeLe4n.CPtr.ofNat 2)
     | .error _ => false)
  assertBool "a read-only capability is refused at set time on rights"
    (errorOf (dispatchWithCap (setHandlerDecoded 1) handler configGate orphanTcbCap stRunning)
      == some .illegalAuthority)
  assertBool "an empty slot is refused at set time as no capability"
    (errorOf (dispatchWithCap (setHandlerDecoded 3) handler configGate orphanTcbCap stRunning)
      == some .invalidCapability)
  assertBool "a refused configuration leaves the field as it was"
    (match dispatchWithCap (setHandlerDecoded 1) handler configGate orphanTcbCap stRunning with
     | .ok _ => false
     | .error _ => (stRunning.getTcb? orphan).bind (·.faultHandler) == none)
  -- The write right is checked by the real lookup path (`syscallLookupCap`
  -- against `requiredRight .tcbSetFaultHandler = .write`), so it is exercised
  -- through `dispatchSyscall` with a TCB capability parked in the caller's
  -- CSpace: slot 3 of the handler's root CNode holds a capability to the
  -- orphan, once read-only and once read + write.
  let orphanCapAt3 (rights : List AccessRight) : SystemState :=
    let cap : Capability :=
      { target := .object orphan.toObjId, rights := AccessRightSet.ofList rights }
    let cn : KernelObject := .cnode (rootCnode.insert (SeLe4n.Slot.ofNat 3) cap)
    { stRunning with objects := stRunning.objects.insert cnRoot cn }
  let viaLookup (st : SystemState) :=
    dispatchSyscall { setHandlerDecoded 0 with capAddr := SeLe4n.CPtr.ofNat 3 } handler st
  assertBool "a capability without the write right cannot configure a handler"
    (errorOf (viaLookup (orphanCapAt3 [.read])) == some .illegalAuthority)
  assertBool "…and with the write right the real lookup path installs it"
    (match viaLookup (orphanCapAt3 [.read, .write]) with
     | .ok (_, st') => (st'.getTcb? orphan).bind (·.faultHandler) == some (SeLe4n.CPtr.ofNat 0)
     | .error _ => false)
  -- **Resuming past a double fault.**  The orphan faults with no handler and
  -- is suspended, keeping its fault as a diagnostic.  Resuming it must retire
  -- that fault — restart at the faulting instruction — or its next ordinary
  -- Call would be answered through the reply seam's fault branch.
  let fctxO := faultContextOfThread stRunning orphan 0x5_0000 0x3C0
  let (stSusp, resO) := faultDeliverOnCore stRunning orphan theFault fctxO c2
  assertBool "pre: the orphan is suspended with its fault recorded"
    (resO.disposition == .suspended && (pendingFaultOf stSusp orphan).isSome &&
      threadStateOf stSusp orphan == some .Inactive)
  assertBool "pre: the reply seam would take the fault branch on it"
    (threadHasPendingFault stSusp orphan)
  match dispatchWithCap resumeTcbDecoded handler configGate orphanTcbCap stSusp with
  | .ok (_, stRes) =>
      assertBool "resuming a double-faulted thread retires its fault"
        (pendingFaultOf stRes orphan == none && !threadHasPendingFault stRes orphan)
      assertBool "…and restarts it at the faulting instruction"
        (savedPcOf stRes orphan == some 0x5_0000)
      assertBool "…with the register window it held at the trap"
        ((List.range 8).all (fun i =>
          (stRes.getTcb? orphan).map (·.registerContext.gpr ⟨i⟩ |>.val) ==
            some (fctxO.gprAt i).toNat))
      assertBool "the resumed thread is Ready again"
        (threadStateOf stRes orphan == some .Ready)
      -- The recovery story: repair the configuration, resume, fault again —
      -- and this time it is delivered.
      match dispatchWithCap (setHandlerDecoded 0) handler configGate orphanTcbCap stSusp with
      | .ok (_, stCfg) =>
          match dispatchWithCap resumeTcbDecoded handler configGate orphanTcbCap stCfg with
          | .ok (_, stRes2) =>
              match endpointReceiveDualOnCore epHandler handler (some replyH) c1 stRes2 with
              | (stRecv2, .ok _) =>
                  let fctx2 := faultContextOfThread stRecv2 orphan 0x5_0000 0x3C0
                  let (stD, resD) := faultDeliverOnCore stRecv2 orphan theFault fctx2 c2
                  assertBool "after repair + resume, the re-executed fault is delivered"
                    (resD.disposition == .delivered epHandler)
                  assertBool "…to a handler that receives the fresh fault, not the retired one"
                    ((deliveredMessageOf stD handler).map (·.label) == some (faultLabel theFault))
              | (_, .error e) => assertBool s!"handler recv must succeed (got {repr e})" false
          | .error e => assertBool s!"resume after repair must succeed (got {repr e})" false
      | .error e => assertBool s!"repairing the handler must succeed (got {repr e})" false
  | .error e => assertBool s!"resuming the suspended thread must succeed (got {repr e})" false
  -- Control: resuming a thread that carries no fault leaves its registers alone.
  let stPlain := faultSuspendOnCore stRunning weak c3
  assertBool "control: a plain suspend records no fault"
    ((pendingFaultOf stPlain weak).isNone)
  match dispatchWithCap resumeTcbDecoded handler configGate
      { orphanTcbCap with target := .object weak.toObjId } stPlain with
  | .ok (_, stW) =>
      assertBool "control: resuming an unfaulted thread does not touch its saved pc"
        (savedPcOf stW weak == some 0)
      assertBool "control: nor its registers"
        ((stW.getTcb? weak).map (·.registerContext.gpr ⟨3⟩ |>.val) == some 300)
  | .error e => assertBool s!"resuming the unfaulted thread must succeed (got {repr e})" false

-- ============================================================================
-- §7  Reply-based resume and restart (RR4.14 / RR4.15 / RR4.16)
-- ============================================================================


private def runResumeChecks : IO Unit := do
  IO.println "--- §7 reply-based resume (RR4.14) ---"
  match deliveryE with
  | .error e => assertBool s!"delivery pipeline: {e}" false
  | .ok d =>
      let (stR, res) := faultReplyOnCore handler faulter resumeInfo #[] c1 d.afterSgi
      match res with
      | .error e => assertBool s!"the fault reply must succeed (got {repr e})" false
      | .ok (outcome, sgi?) =>
          assertBool "a payload-free reply restarts the thread at the faulting instruction"
            (outcome.restartPC? == some dataAbortCtx.elr)
          assertBool "the restarted thread's saved pc is the faulting instruction"
            (savedPcOf stR faulter == some dataAbortCtx.elr.toNat)
          assertBool "the answered fault is retired (seL4 clears tcbFault)"
            (pendingFaultOf stR faulter == none)
          assertBool "the resumed thread is ready again"
            (ipcStateOf stR faulter == some .ready)
          assertBool "the reply surfaces the cross-core wake to the faulter's core"
            (sgi? == some (c0, SgiKind.reschedule))
          -- The resume is only reachable *through* the handler's reply: a
          -- second reply finds no fault to answer.
          let (_, res2) := faultReplyOnCore handler faulter resumeInfo #[] c1 stR
          assertBool "a second reply finds no outstanding fault to answer"
            (errorOf res2 == some .illegalState)

private def runRestartChecks : IO Unit := do
  IO.println "--- §7b reply-based restart (RR4.15/RR4.16) ---"
  -- An unknown-syscall fault, so the reply carries a register payload.
  let (afterRecv, _) ←
    match endpointReceiveDualOnCore epHandler handler (some replyH) c1 stRunning with
    | (st, .ok a) => pure (st, a)
    | (_, .error e) => do
        assertBool s!"handler recv must succeed (got {repr e})" false
        throw (IO.userError "handler recv failed")
  let fctx := faultContextOfThread afterRecv faulter 0x4_0000 0x3C0
  let (afterFault, resD) := faultDeliverOnCore afterRecv faulter (.unknownSyscall 0x2A) fctx c0
  assertBool "the unknown-syscall fault is delivered" (resD.disposition == .delivered epHandler)
  let (stR, res) := faultReplyOnCore handler faulter restartInfo restartRegs c1 afterFault
  match res with
  | .error e => assertBool s!"the restart reply must succeed (got {repr e})" false
  | .ok (outcome, _) =>
      assertBool "the reply's MR8 becomes the restart PC"
        (outcome.restartPC? == some 0x9_9000)
      assertBool "the restarted thread's saved pc is the handler's choice"
        (savedPcOf stR faulter == some 0x9_9000)
      assertBool "the restart does NOT resume at the faulting instruction"
        (savedPcOf stR faulter != some 0x4_0000)
      assertBool "the reply's MR9 becomes the stack pointer"
        ((stR.getTcb? faulter).map (·.registerContext.sp.val) == some 0x7FF0)
      assertBool "the reply's MR10 becomes the link register"
        ((stR.getTcb? faulter).map (·.registerContext.gpr ⟨30⟩ |>.val) == some 0xABBA)
      assertBool "the reply's MR0-MR7 become the argument window"
        ((List.range 8).all (fun i =>
          (stR.getTcb? faulter).map (·.registerContext.gpr ⟨i⟩ |>.val) == some (0xA0 + i)))
      assertBool "the answered fault is retired" (pendingFaultOf stR faulter == none)
  -- A nonzero reply label abandons the thread instead.
  let (stA, resA) := faultReplyOnCore handler faulter abandonInfo restartRegs c1 afterFault
  match resA with
  | .error e => assertBool s!"the abandon reply must succeed (got {repr e})" false
  | .ok (outcomeA, _) =>
      assertBool "a nonzero reply label abandons the thread" (outcomeA == .abandon)
      assertBool "the abandoned thread is marked .Inactive"
        (threadStateOf stA faulter == some .Inactive)
      assertBool "the abandoned thread is not dispatchable on its home core"
        (!dispatchableOn stA faulter c0)
      assertBool "the abandoned thread's saved pc is untouched — it does not resume"
        (savedPcOf stA faulter == some 0)

-- ============================================================================
-- §7c  The reply seam is live: `dispatchWithCap` reaches the fault reply
-- ============================================================================

/-- The `.reply` decode a fault handler issues: seL4's `seL4_Reply` on the reply
capability the fault Call gave it, carrying the restart frame. -/
private def replyDecoded : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := restartInfo, syscallId := .reply,
    msgRegs := restartRegs }

private def resumeDecoded : SyscallDecodeResult :=
  { capAddr := SeLe4n.CPtr.ofNat 0, msgInfo := resumeInfo, syscallId := .reply,
    msgRegs := #[] }

private def replyGate : SyscallGate :=
  { callerId := handler, cspaceRoot := cnRoot, capAddr := SeLe4n.CPtr.ofNat 0,
    capDepth := 2, requiredRight := .write }

private def replyCapH : Capability :=
  { target := .replyCap replyH, rights := AccessRightSet.ofList [.read, .write] }

/-- WS-RR RR4.14/RR4.15: the seam under test — a fault handler answers through
the **ordinary reply syscall**, which is the only reply a handler has.  Before
this seam existed, `dispatchWithCap` woke the faulted thread `.ready` with its
saved PC still addressing the faulting instruction and its fault never retired:
the fault-reply mechanism was verified and unreachable. -/
private def runReplySeamChecks : IO Unit := do
  IO.println "--- §7c the live .reply dispatch reaches the fault reply (RR4.14/RR4.15) ---"
  match endpointReceiveDualOnCore epHandler handler (some replyH) c1 stRunning with
  | (afterRecv, .ok _) =>
      let fctx := faultContextOfThread afterRecv faulter 0x4_0000 0x3C0
      let (afterFault, resD) :=
        faultDeliverOnCore afterRecv faulter (.unknownSyscall 0x2A) fctx c0
      assertBool "pre: the fault is delivered and the faulter carries it"
        (resD.disposition == .delivered epHandler && (pendingFaultOf afterFault faulter).isSome)
      assertBool "pre: the reply object the handler holds names the faulted thread"
        ((afterFault.getReply? replyH).bind (·.caller) == some faulter)
      assertBool "pre: the seam's own predicate agrees"
        (threadHasPendingFault afterFault faulter)
      -- The restart reply, through the live dispatch.
      match dispatchWithCap replyDecoded handler replyGate replyCapH afterFault with
      | .ok (_, stD) =>
          assertBool "the live .reply dispatch moves the faulted thread's pc to the handler's choice"
            (savedPcOf stD faulter == some 0x9_9000)
          assertBool "…and NOT back to the instruction that faulted"
            (savedPcOf stD faulter != some 0x4_0000)
          assertBool "the live .reply dispatch retires the answered fault"
            (pendingFaultOf stD faulter == none)
          assertBool "…so the seam's predicate is false afterwards"
            (!threadHasPendingFault stD faulter)
          assertBool "the restart frame's argument window is installed by the live dispatch"
            ((List.range 8).all (fun i =>
              (stD.getTcb? faulter).map (·.registerContext.gpr ⟨i⟩ |>.val) == some (0xA0 + i)))
      | .error e =>
          assertBool s!"the live .reply dispatch must succeed (got {repr e})" false
      -- A payload-free reply through the same seam is the plain resume.
      match dispatchWithCap resumeDecoded handler replyGate replyCapH afterFault with
      | .ok (_, stR) =>
          assertBool "a payload-free live reply resumes at the faulting instruction"
            (savedPcOf stR faulter == some 0x4_0000)
          assertBool "and retires the fault all the same"
            (pendingFaultOf stR faulter == none)
      | .error e =>
          assertBool s!"the payload-free live reply must succeed (got {repr e})" false
      -- The control: an **unfaulted** caller takes the ordinary branch, so the
      -- seam is not a blanket redirect of every reply.
      assertBool "control: an unfaulted thread has no pending fault in the same state"
        (!threadHasPendingFault afterFault handler)
      assertBool "control: on such a thread the seam answers exactly as the pre-RR4 reply did"
        (errorOf (replyTransferOnCore handler handler restartInfo restartRegs
            IpcMessage.empty c1 afterFault) ==
          errorOf
            (match endpointReplyCrossCoreDispatch handler handler IpcMessage.empty c1
                afterFault with
             | (st', .ok _) => .ok ((), Architecture.stageDeliveredMessage st' handler 0)
             | (_, .error e) => .error e))
  | (_, .error e) =>
      assertBool s!"handler recv failed ({repr e})" false

-- ============================================================================
-- §8  The negative: a fault never returns to the faulting instruction
-- ============================================================================

private def runProgressChecks : IO Unit := do
  IO.println "--- §8 the fault never returns to the faulting instruction (RR4.19) ---"
  match deliveryE with
  | .error e => assertBool s!"delivery pipeline: {e}" false
  | .ok d =>
      assertBool "the faulter was dispatchable on core 0 before the fault"
        (dispatchableOn d.afterRecv faulter c0)
      assertBool "after delivery the faulter is NOT in core 0's run queue"
        (!(d.afterFault.scheduler.runQueueOnCore c0).contains faulter)
      assertBool "after delivery the faulter is NOT core 0's current thread"
        (d.afterFault.scheduler.currentOnCore c0 != some faulter)
      assertBool "after delivery the faulter is not dispatchable on ANY core"
        (!(dispatchableOn d.afterFault faulter c0 || dispatchableOn d.afterFault faulter c1 ||
           dispatchableOn d.afterFault faulter c2 || dispatchableOn d.afterFault faulter c3))
      assertBool "and its saved pc was never advanced past the faulting instruction"
        (savedPcOf d.afterFault faulter == some 0)
  -- The same, on the fail-closed arm: a thread with no handler is contained too.
  let fctxO := faultContextOfThread stRunning orphan 0x5_0000 0x3C0
  let (stO, _) := faultDeliverOnCore stRunning orphan theFault fctxO c2
  assertBool "a suspended faulter is not dispatchable on any core"
    (!(dispatchableOn stO orphan c0 || dispatchableOn stO orphan c1 ||
       dispatchableOn stO orphan c2 || dispatchableOn stO orphan c3))
  -- And through the live exception dispatch (RR4.21), which is what the trap
  -- path runs: the abort arm no longer returns `.error .vmFault` with the
  -- thread left runnable.
  match endpointReceiveDualOnCore epHandler handler (some replyH) c1 stRunning with
  | (stRecv, .ok _) =>
      match dispatchSynchronousException dataAbortCtx stRecv c0 with
      | .ok (_, stD) =>
          assertBool "dispatchSynchronousException delivers the abort rather than erroring" true
          assertBool "and leaves the faulter undispatchable on the core it faulted on"
            (!dispatchableOn stD faulter c0)
      | .error e =>
          assertBool s!"the abort arm must deliver, not error (got {repr e})" false
  | (_, .error e) =>
      assertBool s!"handler recv must succeed (got {repr e})" false
  -- An abort the kernel cannot attribute (no current thread) is still reported.
  assertBool "an unattributable data abort is reported as .vmFault"
    (errorOf (dispatchSynchronousException dataAbortCtx stFault c0) == some .vmFault)

-- ============================================================================
-- §9  Golden trace (RR4.27)
-- ============================================================================

private def traceLine (s : String) : String := "[fault-4core] " ++ s

/-- The deterministic 4-core fault trace, as the golden fixture records it. -/
private def faultTraceLines : List String :=
  match delivery? with
  | none => [traceLine "PIPELINE FAILED"]
  | some d =>
      let resume :=
        match (faultReplyOnCore handler faulter resumeInfo #[] c1 d.afterSgi).2 with
        | .ok (outcome, sgi?) =>
            [ traceLine s!"handler reply on core 1 emits SGI {repr sgi?}"
            , traceLine s!"faulter restart PC = {repr outcome.restartPC?}" ]
        | .error e => [traceLine s!"handler reply FAILED {repr e}"]
      let resumeState := (faultReplyOnCore handler faulter resumeInfo #[] c1 d.afterSgi).1
      [ traceLine s!"handler recv on core 1 leaves handler {repr (ipcStateOf d.afterRecv handler)}"
      , traceLine s!"faulter data abort on core 0 disposition = {repr d.result.disposition}"
      , traceLine s!"fault delivery emits SGI {repr d.result.sgi}"
      , traceLine s!"faulter awaits reply as {repr (ipcStateOf d.afterFault faulter)}"
      , traceLine s!"faulter is dispatchable on core 0: {dispatchableOn d.afterFault faulter c0}"
      , traceLine s!"handler receives fault label {repr ((deliveredMessageOf d.afterFault handler).map (·.label))}"
      , traceLine s!"core 1 handler dispatches current = {repr (d.afterSgi.scheduler.currentOnCore c1)}"
      ] ++ resume ++
      [ traceLine s!"faulter resumes with saved pc {repr (savedPcOf resumeState faulter)}"
      , traceLine s!"faulter outstanding fault after reply = {repr (pendingFaultOf resumeState faulter |>.isSome)}"
      ] ++ queuedLines ++ windowLines ++ reviewLines
where
  /-- PR #887 review: the unknown-syscall producer, the staged handler frame,
  and resume retiring a double fault. -/
  reviewLines : List String :=
    match endpointReceiveDualOnCore epHandler handler (some replyH) c1 stRunning with
    | (_, .error _) => [traceLine "REVIEW PIPELINE FAILED"]
    | (stRecv, .ok _) =>
        let (sgis, stU) := unknownSyscallEntryStep permissiveCtx stRecv svcCtx trapWindow 0
        let fr := SeLe4n.Kernel.Architecture.readReturnFrame stU handler
        let (stSusp, _) :=
          faultDeliverOnCore stRunning orphan theFault (faultContextOfThread stRunning orphan 0x5_0000 0x3C0) c2
        let resumed :=
          match dispatchWithCap resumeTcbDecoded handler configGate orphanTcbCap stSusp with
          | .ok (_, stRes) =>
              s!"resume of double-faulted orphan: fault retired = {repr (pendingFaultOf stRes orphan |>.isNone)} pc = {repr (savedPcOf stRes orphan)}"
          | .error e => s!"resume of double-faulted orphan FAILED {repr e}"
        [ traceLine s!"unknown syscall x7=0x18 on core 0: faulter {repr (ipcStateOf stU faulter)} SGIs {repr sgis}"
        , traceLine s!"unknown syscall handler frame: x0={repr fr.x0} x1={repr fr.x1} x2={repr fr.x2}"
        , traceLine s!"kernel-origin abort (EL1 SPSR) at the entry: SGIs {repr (faultEntryStep permissiveCtx stRecv { pcAlignCtx with spsr := 0x3C5 } trapWindow 0).1}"
        , traceLine resumed
        ]
  /-- The queued ordering (§6d): the fault parks on the endpoint until the
  handler asks, and the label survives the queue. -/
  queuedLines : List String :=
    match queuedDelivery? with
    | none => [traceLine "QUEUED PIPELINE FAILED"]
    | some q =>
        [ traceLine s!"queued: faulter aborts while handler runs, disposition = {repr q.result.disposition} SGI {repr q.result.sgi}"
        , traceLine s!"queued: faulter waits as {repr (ipcStateOf q.afterFault faulter)}"
        , traceLine s!"queued: handler recv dequeues label {repr ((deliveredMessageOf q.afterRecv handler).map (·.label))}"
        , traceLine s!"queued: faulter after reply pc = {repr (savedPcOf q.afterReply faulter)} state = {repr (ipcStateOf q.afterReply faulter)}"
        ]
  /-- The entry with the trap frame's window (§6e): the context and the pokes
  the live seam commits. -/
  windowLines : List String :=
    match endpointReceiveDualOnCore epHandler handler (some replyH) c1 stRunning with
    | (_, .error _) => [traceLine "WINDOW PIPELINE FAILED"]
    | (stRecv, .ok _) =>
        let (sgis, stE) := faultEntryStep permissiveCtx stRecv pcAlignCtx trapWindow 0
        [ traceLine s!"entry: PC-alignment fault with window sp={repr trapWindow.sp} fires SGIs {repr sgis}"
        , traceLine s!"entry: recorded context sp={repr ((pendingFaultOf stE faulter).map (·.context.sp))} lr={repr ((pendingFaultOf stE faulter).map (·.context.lr))}"
        , traceLine s!"entry: delivered MR1 = {repr ((deliveredMessageOf stE handler).map (fun m => wordAt m.registers 1))}"
        ]

private def fixturePath : String := "tests/fixtures/fault_handling_4core.expected"

/-- §9: print the deterministic 4-core fault trace and verify it byte-for-byte
against the golden fixture.  The lines print before the (strict) verification,
so the fixture is regenerable via
`lake exe fault_handling_suite | grep '^\[fault-4core\]'` (the brackets MUST be
escaped — unescaped they form a regex character class that also matches the
suite's `---` section headers, corrupting the regenerated fixture). -/
private def runTraceFixtureCheck : IO Unit := do
  IO.println "--- §9 deterministic 4-core fault trace (RR4.27 fixture) ---"
  for l in faultTraceLines do
    IO.println l
  let expectedContent := String.intercalate "\n" faultTraceLines ++ "\n"
  let fixtureExists ← System.FilePath.pathExists fixturePath
  if !fixtureExists then
    IO.println s!"  FAIL: golden fixture {fixturePath} not found"
    IO.println s!"        regenerate: lake exe fault_handling_suite | grep '^\\[fault-4core\\]' > {fixturePath}"
    throw (IO.userError s!"missing fixture {fixturePath}")
  let actual ← IO.FS.readFile fixturePath
  if actual == expectedContent then
    IO.println s!"  PASS: 4-core fault trace matches golden fixture {fixturePath}"
  else
    IO.println s!"  FAIL: 4-core fault trace differs from golden fixture {fixturePath}"
    IO.println s!"        the live trace is printed above; regenerate the golden fixture with:"
    IO.println s!"          lake exe fault_handling_suite | grep '^\\[fault-4core\\]' > {fixturePath}"
    IO.println s!"          (then refresh {fixturePath}.sha256 — see tests/fixtures/README.md)"
    throw (IO.userError "4-core fault trace fixture mismatch")

def runFaultHandlingChecks : IO Unit := do
  IO.println "WS-RR RR4.26 — Fault handling suite (fault IPC, resume, restart, progress)"
  IO.println "===================================="
  runEncodingChecks
  runClassificationChecks
  runResolutionChecks
  runDeliveryChecks
  runNoHandlerChecks
  runFlowGateChecks
  runQueuedDeliveryChecks
  runEntryWindowChecks
  runUnknownSyscallChecks
  runConfigureAndResumeChecks
  runResumeChecks
  runRestartChecks
  runReplySeamChecks
  runProgressChecks
  runTraceFixtureCheck
  IO.println "===================================="

end SeLe4n.Testing.FaultHandling

def main : IO UInt32 := do
  try
    SeLe4n.Testing.FaultHandling.runFaultHandlingChecks
    IO.println "fault_handling_suite: ALL PASS"
    return 0
  catch e =>
    IO.println s!"fault_handling_suite: FAILURES ({e})"
    return 1
