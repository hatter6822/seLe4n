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
import SeLe4n.Kernel.RoutedArms.ReplyRecvLong
import SeLe4n.Kernel.RoutedArms.Transferring
import SeLe4n.Kernel.RoutedArms.Audited
import SeLe4n.Kernel.RoutedArms.Overflowed

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
@[inline] def syscallEntryRoutedWith {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (finish : SyscallId → UInt64 → SystemState → β) : β :=
  if isInsecureDefaultContext ctx then
    finish .yield 0 (entryReportGeneral (.error (.policyDenied, st)))
  else
  match st.scheduler.currentOnCore executingCore with
  | none => finish .yield 0 (entryReportGeneral (.error (.illegalState, st)))
  | some tid =>
    match st.getObject? tid.toObjId with
    | some (.tcb tcb) =>
      match hRt : SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall
              SeLe4n.arm64DefaultLayout tcb.registerContext 32 with
      | .signal capAddr =>
        finish .notificationSignal capAddr.word
          (signalRoutedArm ctx executingCore tid capAddr.word st)
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
      | .replyRecvLong capAddr msgInfo =>
        finish .replyRecv capAddr.word
          (replyRecvLongRoutedArm ctx executingCore tid capAddr.word msgInfo.length
            msgInfo.extraCaps msgInfo.label st)
      | .transferring sid capAddr msgInfo =>
        finish sid capAddr.word
          (transferringRoutedArm ctx executingCore tid sid capAddr.word msgInfo.length st)
      | .audited sid capAddr =>
        finish sid capAddr.word (auditedRoutedArm ctx executingCore tid sid capAddr.word st)
      | .overflowed sid capAddr len =>
        finish sid capAddr.word
          (overflowedRoutedArm ctx executingCore tid sid capAddr.word len st)
      | .shortArgs sid capAddr =>
        finish sid capAddr.word (shortArgsRoutedArm executingCore tid sid capAddr.word st)
      | .refused e => finish .yield 0 (entryReportGeneral (.error (e, st)))
      | .viaDecode =>
        absurd hRt (SeLe4n.Kernel.Architecture.RegisterDecode.registerRoutedSyscall_viaDecode _)
    | some _ => finish .yield 0 (entryReportGeneral (.error (.illegalState, st)))
    | none => finish .yield 0 (entryReportGeneral (.error (.objectNotFound, st)))

/-- **The routed entry**, its reports handed on by `entryReportOutcome` into
continuations on results. -/
@[inline] def syscallEntryRoutedK {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β) : β :=
  syscallEntryRoutedWith ctx executingCore st fun sid capWord s =>
    entryReportOutcome kGen kRes (kLook sid (SeLe4n.CPtr.ofWord capWord)) s

/-- An operand route's arm, reported and handed on by any `finish` that hands
each report to its continuation, is the continued entry's operand dispatch into
those continuations. -/
private theorem finish_operand {β : Type} (finish : SyscallId → UInt64 → SystemState → β)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (hG : ∀ sid w r, finish sid w (entryReportGeneral r) = kGen r)
    (hR : ∀ sid w r, finish sid w (entryReportResolved r) = kRes r)
    (hL : ∀ sid w e s, finish sid w (entryReportLookup e s) = kLook sid (SeLe4n.CPtr.ofWord w) e s)
    (sid sid' : SyscallId) (w : UInt64) (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (arm : Option Capability → RefusalCarrying Unit)
    (st : SystemState) :
    finish sid w
        (dispatchOperandCheckedK sid' capAddr tid executingCore arm st entryReportGeneral
          entryReportResolved entryReportLookup) =
      dispatchOperandCheckedK sid' capAddr tid executingCore arm st kGen kRes
        (kLook sid (SeLe4n.CPtr.ofWord w)) := by
  rw [dispatchOperandCheckedK_map (finish sid w)]
  simp only [hG, hR, hL]

/-- A long route's arm, reported and handed on, is the continued entry's
filled operand dispatch into its own continuations. -/
private theorem finish_long {β : Type} (finish : SyscallId → UInt64 → SystemState → β)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (hG : ∀ sid w r, finish sid w (entryReportGeneral r) = kGen r)
    (hR : ∀ sid w r, finish sid w (entryReportResolved r) = kRes r)
    (hL : ∀ sid w e s, finish sid w (entryReportLookup e s) = kLook sid (SeLe4n.CPtr.ofWord w) e s)
    (sid sid' : SyscallId) (w : UInt64) (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (arm : Option Capability → RefusalCarrying Unit)
    (n : Nat) (st : SystemState) :
    finish sid w
        (longOperandK sid' capAddr tid executingCore arm n st entryReportGeneral
          entryReportResolved entryReportLookup) =
      longOperandK sid' capAddr tid executingCore arm n st kGen kRes
        (kLook sid (SeLe4n.CPtr.ofWord w)) := by
  rw [longOperandK_map (finish sid w)]
  simp only [hG, hR, hL]

private theorem finish_overflowOne {β : Type} (finish : SyscallId → UInt64 → SystemState → β)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (hG : ∀ sid w r, finish sid w (entryReportGeneral r) = kGen r)
    (hR : ∀ sid w r, finish sid w (entryReportResolved r) = kRes r)
    (hL : ∀ sid w e s, finish sid w (entryReportLookup e s) = kLook sid (SeLe4n.CPtr.ofWord w) e s)
    (sid sid' : SyscallId) (w : UInt64) (capAddr : SeLe4n.CPtr) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (arm : Option Capability → RefusalCarrying Unit)
    (st : SystemState) :
    finish sid w
        (overflowOneOperandK sid' capAddr tid executingCore arm st entryReportGeneral
          entryReportResolved entryReportLookup) =
      overflowOneOperandK sid' capAddr tid executingCore arm st kGen kRes
        (kLook sid (SeLe4n.CPtr.ofWord w)) := by
  rw [overflowOneOperandK_map (finish sid w)]
  simp only [hG, hR, hL]

/-- **The routed entry is the continued entry**, for every `finish` that hands
each report to its continuation: the routed dispatch with its reports handed on
is the continued entry into those continuations. -/
theorem syscallEntryRoutedWith_eq {β : Type} (ctx : LabelingContext)
    (executingCore : Concurrency.CoreId) (st : SystemState)
    (finish : SyscallId → UInt64 → SystemState → β)
    (kGen kRes : Except (KernelError × SystemState) (Unit × SystemState) → β)
    (kLook : SyscallId → SeLe4n.CPtr → KernelError → SystemState → β)
    (hG : ∀ sid w r, finish sid w (entryReportGeneral r) = kGen r)
    (hR : ∀ sid w r, finish sid w (entryReportResolved r) = kRes r)
    (hL : ∀ sid w e s, finish sid w (entryReportLookup e s) = kLook sid (SeLe4n.CPtr.ofWord w) e s) :
    syscallEntryRoutedWith ctx executingCore st finish =
      syscallEntryCheckedK ctx executingCore st kGen kRes kLook := by
  symm
  unfold syscallEntryRoutedWith syscallEntryCheckedK
  by_cases hI : isInsecureDefaultContext ctx = true
  · simp only [hI, if_true, hG]
  simp only [hI, Bool.false_eq_true, if_false]
  cases hC : st.scheduler.currentOnCore executingCore with
  | none => simp only [hG]
  | some tid =>
  cases hO : st.getObject? tid.toObjId with
  | none => simp only [hO, hG]
  | some o =>
  simp only [hO]
  cases o with
  | tcb tcb =>
    dsimp only
    symm
    split
    next capAddr hRt =>
      rw [hRt]; symm
      simp only [signalRoutedArm, dispatchOperandCheckedKW_report,
        finish_operand finish kGen kRes kLook hG hR hL]; rfl
    next capAddr hRt =>
      rw [hRt]; symm
      simp only [waitRoutedArm, dispatchOperandCheckedKW_report,
        finish_operand finish kGen kRes kLook hG hR hL]; rfl
    next hRt =>
      rw [hRt]; symm
      simp only [yieldRoutedArm, hG]
      cases yieldOnCoreR st executingCore <;> rfl
    next capAddr msgInfo hRt =>
      rw [hRt]; symm
      simp only [sendRoutedArm, dispatchOperandCheckedKW_report,
        hO, finish_operand finish kGen kRes kLook hG hR hL]; rfl
    next capAddr msgInfo hRt =>
      rw [hRt]; symm
      simp only [callRoutedArm, dispatchOperandCheckedKW_report,
        hO, finish_operand finish kGen kRes kLook hG hR hL]; rfl
    next capAddr msgInfo hRt =>
      rw [hRt]; symm
      simp only [replyRoutedArm, dispatchOperandCheckedKW_report,
        hO, finish_operand finish kGen kRes kLook hG hR hL]; rfl
    next capAddr len replyAddr hRt =>
      rw [hRt]; symm
      simp only [receiveRoutedArm, dispatchOperandCheckedKW_report,
        finish_operand finish kGen kRes kLook hG hR hL]; rfl
    next capAddr msgInfo hRt =>
      rw [hRt]; symm
      simp only [replyRecvRoutedArm, dispatchOperandCheckedKW_report,
        hO, finish_operand finish kGen kRes kLook hG hR hL]; rfl
    next sid capAddr hRt =>
      rw [hRt]; symm
      simp only [invocationRoutedArm, dispatchOperandCheckedKW_report,
        hO,
        finish_operand finish kGen kRes kLook hG hR hL]; rfl
    next sid capAddr hRt =>
      rw [hRt]; symm
      simp only [overflowOneRoutedArm,
        overflowOneOperandKW_report, hO]
      rw [ipcBufferReadMrK_comp (finish _ _)]
      simp only [shortArgsRoutedArm, dispatchOperandCheckedKW_report,
        finish_operand finish kGen kRes kLook hG hR hL, finish_overflowOne finish kGen kRes kLook hG hR hL]
      rfl
    next capAddr msgInfo hRt =>
      rw [hRt]; symm
      simp only [sendLongRoutedArm, dispatchOperandCheckedKW_report, longOperandKW_report,
        sendRoutedArm, hO, ipcBufferReadMrK_comp (finish _ _),
        finish_operand finish kGen kRes kLook hG hR hL, finish_long finish kGen kRes kLook hG hR hL]
      rfl
    next capAddr msgInfo hRt =>
      rw [hRt]; symm
      simp only [callLongRoutedArm, dispatchOperandCheckedKW_report, longOperandKW_report,
        callRoutedArm, hO, ipcBufferReadMrK_comp (finish _ _),
        finish_operand finish kGen kRes kLook hG hR hL, finish_long finish kGen kRes kLook hG hR hL]
      rfl
    next capAddr msgInfo hRt =>
      rw [hRt]; symm
      simp only [replyLongRoutedArm, dispatchOperandCheckedKW_report, longOperandKW_report,
        replyRoutedArm, hO, ipcBufferReadMrK_comp (finish _ _),
        finish_operand finish kGen kRes kLook hG hR hL, finish_long finish kGen kRes kLook hG hR hL]
      rfl
    next capAddr msgInfo hRt =>
      rw [hRt]; symm
      simp only [replyRecvLongRoutedArm, dispatchOperandCheckedKW_report, longOperandKW_report,
        replyRecvRoutedArm, hO, ipcBufferReadMrK_comp (finish _ _),
        finish_operand finish kGen kRes kLook hG hR hL, finish_long finish kGen kRes kLook hG hR hL]
      rfl
    next sid capAddr msgInfo hRt =>
      rw [hRt]; symm
      by_cases hS : msgInfo.length ≤ 4
      · simp only [transferringRoutedArm, dispatchOperandCheckedKW_report,
        hO, hS, ↓reduceIte, finish_operand finish kGen kRes kLook hG hR hL]; rfl
      · simp only [transferringRoutedArm, dispatchOperandCheckedKW_report, longOperandKW_report,
        hO, hS, ↓reduceIte,
          ipcBufferReadMrK_comp (finish _ _), finish_operand finish kGen kRes kLook hG hR hL,
          finish_long finish kGen kRes kLook hG hR hL]
        rfl
    next sid capAddr hRt =>
      rw [hRt]; symm
      simp only [auditedRoutedArm, dispatchOperandCheckedKW_report,
        hO, finish_operand finish kGen kRes kLook hG hR hL]; rfl
    next sid capAddr len hRt =>
      rw [hRt]; symm
      obtain ⟨-, -, -, -, -, hOv, -⟩ :=
        Architecture.RegisterDecode.decodeSyscallArgsFromState_of_routedOverflowed st tid _ _ 32
          sid capAddr len hRt
      dsimp only
      rw [overflowedRoutedArm_eq ctx executingCore tid sid capAddr.word len st hOv]
      simp only [overflowedLongArmWith, dispatchOperandCheckedKW_report, longOperandKW_report,
        shortArgsRoutedArm, hO,
        ipcBufferReadMrK_comp (finish _ _), finish_operand finish kGen kRes kLook hG hR hL,
        finish_long finish kGen kRes kLook hG hR hL]
      rfl
    next sid capAddr hRt =>
      rw [hRt]; symm
      simp only [shortArgsRoutedArm, dispatchOperandCheckedKW_report,
        finish_operand finish kGen kRes kLook hG hR hL]; rfl
    next e hRt =>
      rw [hRt]; symm
      simp only [hG]
    next hRt =>
      exact absurd hRt (Architecture.RegisterDecode.registerRoutedSyscall_viaDecode _)
  | _ => simp only [hG]

/-- **The routed entry is the continued entry**, for every continuation: the
compiled form `syscallEntryCheckedK` runs as. -/
@[csimp] theorem syscallEntryCheckedK_eq_routed :
    @syscallEntryCheckedK = @syscallEntryRoutedK := by
  funext β ctx executingCore st kGen kRes kLook
  unfold syscallEntryRoutedK
  exact (syscallEntryRoutedWith_eq ctx executingCore st _ kGen kRes kLook
    (fun _ _ r => entryReportOutcome_general _ _ _ r)
    (fun _ _ r => entryReportOutcome_resolved _ _ _ r)
    (fun _ _ e s => entryReportOutcome_lookup _ _ _ e s)).symm

end SeLe4n.Kernel
