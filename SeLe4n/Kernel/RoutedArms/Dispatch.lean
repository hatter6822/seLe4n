-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RoutedArms.Signal
import SeLe4n.Kernel.RoutedArms.Wait
import SeLe4n.Kernel.RoutedArms.Yield
import SeLe4n.Kernel.RoutedArms.Send
import SeLe4n.Kernel.RoutedArms.Call
import SeLe4n.Kernel.RoutedArms.Reply
import SeLe4n.Kernel.RoutedArms.Receive
import SeLe4n.Kernel.RoutedArms.ReplyRecv
import SeLe4n.Kernel.RoutedArms.Invocation
import SeLe4n.Kernel.RoutedArms.OverflowOne
import SeLe4n.Kernel.RoutedArms.SendLong
import SeLe4n.Kernel.RoutedArms.CallLong
import SeLe4n.Kernel.RoutedArms.ReplyLong
import SeLe4n.Kernel.RoutedArms.Audited
import SeLe4n.Kernel.RoutedArms.Overflowed
import SeLe4n.Kernel.RoutedArms.Decoded

/-!
# The routed entry, a dispatch over out-of-line arms

`syscallEntryRoutedK` is the continued entry `syscallEntryCheckedK` compiled
as a small dispatch: the same checks before the route, the same route, and
each route's arm a call (`RoutedArms.*`) that takes machine words and the state
owned and returns the state with its report pushed, which one join point pops
and hands to the continuation the report names (`entryReportOutcome`).  The
continued entry is the specification, and this its compiled form
(`syscallEntryCheckedK_eq_routed`), so an entry that inlines the continued
entry holds one dispatch and one copy of its continuations rather than the
whole kernel.
-/

namespace SeLe4n.Kernel

open SeLe4n.Model

/-- **The routed entry, dispatched**: `syscallEntryCheckedK`'s checks and
route, each arm called out of line and its report handed on at one join
point (`finish`).  The entry's own refusals are reported the same way, so the
continuations are compiled once. -/
@[inline] def syscallEntryRoutedK {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β) : β :=
  let finish := fun (sid : SyscallId) (capWord : UInt64) (s : SystemState) =>
    entryReportOutcome kGen kRes (kLook sid (SeLe4n.CPtr.ofWord capWord)) s
  if isInsecureDefaultContext ctx then
    finish .yield 0 (entryReportGeneral (.error (.policyDenied, st)))
  else
  match st.scheduler.currentOnCore executingCore with
  | none => finish .yield 0 (entryReportGeneral (.error (.illegalState, st)))
  | some tid =>
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) =>
      match SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
              SeLe4n.arm64DefaultLayout tcb.registerContext 32 with
      | .signal capAddr badge =>
        finish .notificationSignal capAddr.word
          (signalRoutedArm ctx executingCore tid capAddr.word badge.word st)
      | .wait capAddr =>
        finish .notificationWait capAddr.word (waitRoutedArm ctx executingCore tid capAddr.word st)
      | .yield => finish .yield 0 (yieldRoutedArm executingCore st)
      | .send capAddr msgInfo =>
        finish .send capAddr.word
          (sendRoutedArm ctx executingCore tid capAddr.word msgInfo.length st)
      | .call capAddr msgInfo =>
        finish .call capAddr.word
          (callRoutedArm ctx executingCore tid capAddr.word msgInfo.length st)
      | .reply capAddr msgInfo =>
        finish .reply capAddr.word
          (replyRoutedArm ctx executingCore tid capAddr.word msgInfo.length msgInfo.extraCaps
            msgInfo.label st)
      | .receive capAddr len replyAddr =>
        finish .receive capAddr.word
          (receiveRoutedArm ctx executingCore tid capAddr.word len replyAddr.word st)
      | .replyRecv capAddr msgInfo =>
        finish .replyRecv capAddr.word
          (replyRecvRoutedArm ctx executingCore tid capAddr.word msgInfo.length
            msgInfo.extraCaps msgInfo.label st)
      | .invoke sid capAddr =>
        finish sid capAddr.word (invocationRoutedArm ctx executingCore tid sid capAddr.word st)
      | .overflowOne sid capAddr =>
        finish sid capAddr.word (overflowOneRoutedArm ctx executingCore tid sid capAddr.word st)
      | .sendLong capAddr msgInfo =>
        finish .send capAddr.word
          (sendLongRoutedArm ctx executingCore tid capAddr.word msgInfo.length st)
      | .callLong capAddr msgInfo =>
        finish .call capAddr.word
          (callLongRoutedArm ctx executingCore tid capAddr.word msgInfo.length st)
      | .replyLong capAddr msgInfo =>
        finish .reply capAddr.word
          (replyLongRoutedArm ctx executingCore tid capAddr.word msgInfo.length msgInfo.extraCaps
            msgInfo.label st)
      | .audited sid capAddr =>
        finish sid capAddr.word (auditedRoutedArm ctx executingCore tid sid capAddr.word st)
      | .overflowed sid capAddr len =>
        finish sid capAddr.word
          (overflowedRoutedArm ctx executingCore tid sid capAddr.word len st)
      | .shortArgs sid capAddr =>
        finish sid capAddr.word (shortArgsRoutedArm executingCore tid sid capAddr.word st)
      | .refused e => finish .yield 0 (entryReportGeneral (.error (e, st)))
      | .viaDecode | .replyRecvLong _ _ => finish .yield 0 (decodedRoutedArm ctx executingCore st)
    | some _ => finish .yield 0 (entryReportGeneral (.error (.illegalState, st)))
    | none => finish .yield 0 (entryReportGeneral (.error (.objectNotFound, st)))

/-- An operand route's arm, reported and handed on, is the continued entry's
operand dispatch into its own continuations. -/
private theorem entryReportOutcome_operand {β : Type}
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : KernelError → SystemState → β) (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (arm : Option Capability → RefusalCarrying Unit)
    (st : SystemState) :
    entryReportOutcome kGen kRes kLook
        (dispatchOperandCheckedK capAddr tid executingCore arm st entryReportGeneral
          entryReportResolved entryReportLookup) =
      dispatchOperandCheckedK capAddr tid executingCore arm st kGen kRes kLook := by
  rw [dispatchOperandCheckedK_map (entryReportOutcome kGen kRes kLook)]
  simp only [entryReportOutcome_general, entryReportOutcome_resolved, entryReportOutcome_lookup]

/-- **The routed entry is the continued entry**, for every continuation: the
compiled form `syscallEntryCheckedK` runs as. -/
@[csimp] theorem syscallEntryCheckedK_eq_routed :
    @syscallEntryCheckedK = @syscallEntryRoutedK := by
  funext β ctx executingCore st kGen kRes kLook
  unfold syscallEntryRoutedK syscallEntryCheckedK
  dsimp only
  by_cases hI : isInsecureDefaultContext ctx = true
  · simp only [hI, if_true, entryReportOutcome_general]
  simp only [hI, Bool.false_eq_true, if_false]
  cases hC : st.scheduler.currentOnCore executingCore with
  | none => simp only [entryReportOutcome_general]
  | some tid =>
  cases hO : st.getObject? tid.toObjId with
  | none => simp only [hO, entryReportOutcome_general]
  | some o =>
  simp only [hO]
  cases o with
  | tcb tcb =>
    dsimp only
    cases Architecture.RegisterDecode.registerRoutedSyscall SeLe4n.arm64DefaultLayout tcb.registerContext 32 with
    | signal capAddr badge =>
      simp only [signalRoutedArm, entryReportOutcome_operand]; rfl
    | wait capAddr => simp only [waitRoutedArm, entryReportOutcome_operand]; rfl
    | yield =>
      simp only [yieldRoutedArm, entryReportOutcome_general]
      cases yieldOnCoreR st executingCore <;> rfl
    | send capAddr msgInfo =>
      simp only [sendRoutedArm, hO, entryReportOutcome_operand]; rfl
    | call capAddr msgInfo =>
      simp only [callRoutedArm, hO, entryReportOutcome_operand]; rfl
    | reply capAddr msgInfo =>
      simp only [replyRoutedArm, hO, entryReportOutcome_operand]; rfl
    | receive capAddr len replyAddr =>
      simp only [receiveRoutedArm, entryReportOutcome_operand]; rfl
    | replyRecv capAddr msgInfo =>
      simp only [replyRecvRoutedArm, hO, entryReportOutcome_operand]; rfl
    | invoke sid capAddr =>
      simp only [invocationRoutedArm, hO, entryReportOutcome_operand]; rfl
    | overflowOne sid capAddr =>
      simp only [overflowOneRoutedArm, hO]
      rw [ipcBufferReadMrK_comp (entryReportOutcome kGen kRes _)]
      simp only [entryReportOutcome_general]; rfl
    | sendLong capAddr msgInfo =>
      simp only [sendLongRoutedArm, hO, ipcBufferReadMrK_comp (entryReportOutcome kGen kRes _),
        entryReportOutcome_general]
      rfl
    | callLong capAddr msgInfo =>
      simp only [callLongRoutedArm, hO, ipcBufferReadMrK_comp (entryReportOutcome kGen kRes _),
        entryReportOutcome_general]
      rfl
    | replyLong capAddr msgInfo =>
      simp only [replyLongRoutedArm, hO, ipcBufferReadMrK_comp (entryReportOutcome kGen kRes _),
        entryReportOutcome_general]
      rfl
    | audited sid capAddr =>
      simp only [auditedRoutedArm, hO, entryReportOutcome_operand]; rfl
    | overflowed sid capAddr len =>
      simp only [overflowedRoutedArm_eq, overflowedArmWith_eq_spec, overflowedArmSpec, hO]
      simp only [ipcBufferReadMrK_comp (entryReportOutcome kGen kRes _),
        entryReportOutcome_general, overflowedOperandR_eq]
      rfl
    | shortArgs sid capAddr =>
      simp only [shortArgsRoutedArm, entryReportOutcome_operand]; rfl
    | refused e => simp only [entryReportOutcome_general]
    | viaDecode | replyRecvLong _ _ => simp only [decodedRoutedArm, entryReportOutcome_general]
  | _ => simp only [entryReportOutcome_general]

end SeLe4n.Kernel
