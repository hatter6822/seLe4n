-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingEndpoint
import SeLe4n.Kernel.RefusalCarryingInvocation
import SeLe4n.Kernel.RefusalCarryingDeclassification

/-!
# Calls past their inline words, or short of their arguments, refusing in their own state

A five-word invocation whose message-info length runs past the layout's
message registers (`RegisterRoutedSyscall.overflowed`): a configure or a
service register, whose fifth argument is slot 0.  Only a syscall that reads
its overflow words is routed past the inline registers
(`syscallReadsOverflow`); every other long message is read as its inline words,
as seL4 reads only the words a syscall uses.  The decode reads the caller's
overflow slots.  When the slots lie on one page, the decode reads them exactly
when it reads the first, and its TLB walk is that one page's, so the call is
the short route's dispatch on the decode the long message reads to
(`overflowedDecode`), which refuses in the state it was handed
(`dispatchOverflowedCheckedR_eq`).  A slot that does not read clamps the
message to its inline words (`clampedFrameDecode`), as seL4's
`handleInvocation` clamps a message with no IPC buffer, and the invocation is
then short of its fifth argument.

An invocation whose message is shorter than its arguments
(`RegisterRoutedSyscall.shortArgs`, `truncationMinimum`) is refused
`.truncatedMessage` once its capability is found and checked, before any
argument word is read, as seL4's decode refuses `seL4_TruncatedMessage`
(`dispatchShortArgsCheckedR_eq`).
-/

namespace SeLe4n.Kernel

open SeLe4n.Model
open Architecture.RegisterDecode
open Architecture.SyscallArgDecode

/-- The decode an overflowed frame reads to: the inline words and then its
overflow slots' words, as `sid`. -/
def overflowedDecode (st : SystemState) (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile)
    (sid : SyscallId) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) : SyscallDecodeResult :=
  { capAddr, msgInfo := mi, syscallId := sid,
    msgRegs := Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf ++
      (overflowRegsFrom st tid 0 (mi.length - 4)).toArray,
    inlineCount := 4, overflowCount := mi.length - 4 }

@[simp] theorem overflowedDecode_overflowCount (st : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (sid : SyscallId) (capAddr : SeLe4n.CPtr) (mi : MessageInfo) :
    (overflowedDecode st tid rf sid capAddr mi).overflowCount = mi.length - 4 := rfl

/-- **An overflowed frame whose overflow slots all read decodes** to the inline
words and then those slots' words (`overflowedDecode`). -/
theorem decodeSyscallArgsFromState_of_routedOverflowed_ok (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (mi : MessageInfo)
    (hMI : decodeMsgInfo (readReg rf SeLe4n.arm64DefaultLayout.msgInfoReg) = .ok mi)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .overflowed sid capAddr mi.length)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (overflowedDecode st tid rf sid capAddr mi) := by
  obtain ⟨mi', hMI', -, _, _, hOv, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedOverflowed st tid _ rf 32 sid capAddr mi.length hR
  obtain rfl : mi = mi' := Except.ok.inj (hMI.symm.trans hMI')
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  have hM := mapM_readOverflowWord st tid (mi.length - 4) 0
    (fun j _ h2 => hRead j (by omega))
  rw [hDec]
  unfold mergeOverflowWords
  simp only [syscallReadsOverflow_of_routedOverflowOne hOv, ↓reduceIte, Array.size_map, hSz, List.range_eq_range', hM, overflowRegsFrom_eq_map, List.map_map,
    bind, Except.bind, pure, Except.pure, overflowedDecode]
  rfl

/-- …and one with an overflow slot that does not read is clamped to its inline
words (`clampedFrameDecode`), as seL4 clamps a message with no IPC buffer. -/
theorem decodeSyscallArgsFromState_of_routedOverflowed_clamped (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (mi : MessageInfo)
    (hMI : decodeMsgInfo (readReg rf SeLe4n.arm64DefaultLayout.msgInfoReg) = .ok mi)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .overflowed sid capAddr mi.length)
    (j : Nat) (hj : j < mi.length - 4) (e : Architecture.IpcBufferRead.IpcBufferReadError)
    (h0 : Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .error e) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (clampedFrameDecode sid rf capAddr mi) := by
  obtain ⟨mi', hMI', -, hGt, _, hOv, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedOverflowed st tid _ rf 32 sid capAddr mi.length hR
  obtain rfl : mi = mi' := Except.ok.inj (hMI.symm.trans hMI')
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  rw [hDec]
  rw [mergeOverflowWords_clamped st tid rf _ capAddr mi (syscallReadsOverflow_of_routedOverflowOne hOv)
    ⟨_, by rw [List.range_eq_range']
           exact mapM_readOverflowWord_error st tid (mi.length - 4) 0
             ⟨j, e, Nat.zero_le _, by omega, h0⟩⟩]

/-- **The overflowed dispatch**: a five-word invocation's refusal-carrying
dispatch, read off the inline words and the overflow word `w` in slot 0.  Only
a syscall that reads its overflow words is routed past the inline registers
(`syscallReadsOverflow`), so no other kind is routed here (`routedOverflowOne`).
A specification: the compiled entry runs the routed arm
(`RoutedArms.Overflowed`). -/
noncomputable def dispatchOverflowedCheckedR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (rf : SeLe4n.RegisterFile) (w : UInt64)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  match sid with
  | .schedContextConfigure => dispatchConfigureCheckedR capAddr rf w tid executingCore
  | .serviceRegister => dispatchServiceRegisterCheckedR ctx capAddr rf w tid executingCore
  | .cspaceMint => dispatchMintCheckedR ctx capAddr rf w tid executingCore
  | _ => fun st => .error (.illegalState, st)

/-- The syscalls `routedOverflowOne` admits: the five-word invocations. -/
theorem routedOverflowOne_cases {sid : SyscallId} (h : routedOverflowOne sid = true) :
    sid = .schedContextConfigure ∨ sid = .serviceRegister ∨ sid = .cspaceMint := by
  cases sid <;> simp_all [routedOverflowOne]

/-- **The overflowed route's operand arm**: the arm `dispatchOverflowedCheckedR`
runs behind the operand check (`dispatchOverflowedCheckedR_eq_operand`).  A
specification: the compiled entry runs it out of line
(`RoutedArms.Overflowed`). -/
noncomputable def overflowedArmOf (ctx : LabelingContext) (sid : SyscallId)
    (rf : SeLe4n.RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId) :
    Option Capability → RefusalCarrying Unit :=
  match sid with
  | .schedContextConfigure => configureOperandArmR rf w tid
  | .serviceRegister => serviceRegisterOperandArmR ctx tid rf w
  | .cspaceMint => mintOperandArmR ctx tid rf w
  | _ => fun _ st => .error (.invalidCapability, st)

/-- Every overflowed call is the operand dispatch of its arm. -/
theorem dispatchOverflowedCheckedR_eq_operand (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (rf : SeLe4n.RegisterFile) (w : UInt64)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (h : routedOverflowOne sid = true) :
    dispatchOverflowedCheckedR ctx sid capAddr rf w tid executingCore =
      dispatchOperandCheckedR capAddr tid executingCore (overflowedArmOf ctx sid rf w tid) := by
  rcases routedOverflowOne_cases h with rfl | rfl | rfl <;> rfl

/-- The overflowed arm refuses a missing operand as the operand check does. -/
theorem overflowedArmOf_none (ctx : LabelingContext) (sid : SyscallId)
    (rf : SeLe4n.RegisterFile) (w : UInt64) (tid : SeLe4n.ThreadId) (s : SystemState) :
    overflowedArmOf ctx sid rf w tid none s = .error (.invalidCapability, s) := by
  unfold overflowedArmOf
  cases sid <;> rfl

/-- An overflowed decode's words read as the inline words and then slot 0's
word below five. -/
theorem overflowedDecode_agree (S : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (sid : SyscallId) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hLen : 4 < mi.length) :
    MsgRegsAgreeBelow (overflowedDecode S tid rf sid capAddr mi).msgRegs
        (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg rf) ++
          #[(⟨(overflowWordAt S tid 0).toNat⟩ : RegValue)]) 5 := by
  have hSz : (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf).size = 4 := by
    simp [Architecture.regMessageRegs, SeLe4n.arm64DefaultLayout]
  obtain ⟨m, hm⟩ : ∃ m, mi.length - 4 = m + 1 := ⟨mi.length - 5, by omega⟩
  have h := MsgRegsAgreeBelow.append_cons
    (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf)
    ⟨(overflowWordAt S tid 0).toNat⟩ (overflowRegsFrom S tid 1 m)
  rw [hSz] at h
  simp only [overflowedDecode, hm]
  exact h

/-- **The overflowed dispatch is the checked dispatch of the decode the long
message reads to**, refusing in the state it was handed: a five-word
invocation's fifth argument is slot 0's word. -/
theorem dispatchOverflowedCheckedR_eq (ctx : LabelingContext) (S : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (mi : MessageInfo) (executingCore : Concurrency.CoreId)
    (hRt : routedOverflowOne sid = true) (hLen : 4 < mi.length) (st : SystemState) :
    dispatchOverflowedCheckedR ctx sid capAddr rf (overflowWordAt S tid 0) tid
        executingCore st =
      RefusalCarrying.ofKernel
        (dispatchSyscallChecked ctx (overflowedDecode S tid rf sid capAddr mi) tid executingCore)
        st := by
  refine congrFun ?_ st
  have hA5 := overflowedDecode_agree S tid rf sid capAddr mi hLen
  rcases routedOverflowOne_cases hRt with rfl | rfl | rfl
  · exact dispatchConfigureCheckedR_eq ctx (overflowedDecode S tid rf _ capAddr mi) rf _ tid
      executingCore rfl hA5 (show 5 ≤ mi.length by omega)
  · exact dispatchServiceRegisterCheckedR_eq ctx (overflowedDecode S tid rf _ capAddr mi) rf _ tid
      executingCore rfl hA5 (show 5 ≤ mi.length by omega)
  · exact dispatchMintCheckedR_eq ctx (overflowedDecode S tid rf _ capAddr mi) rf _ tid
      executingCore rfl hA5 (show 5 ≤ mi.length by omega)

/-! ## An invocation short of its arguments (seL4's `seL4_TruncatedMessage`) -/

/-- The target an invocation reads its arguments under: a core's scheduling
control for the configure, the interrupt control for the handler issue, an
interrupt handler for its notification binding, and an object for every other
invocation.  Any other target is refused `.invalidCapability` before the
arguments are read, as seL4's capability kind chooses the decode before the
decode checks the length. -/
@[inline] def truncationTarget (sid : SyscallId) (t : CapTarget) : Bool :=
  match sid, t with
  | .schedContextConfigure, .schedControl _ => true
  | .schedContextConfigure, _ => false
  | .irqControlGet, .irqControl _ => true
  | .irqControlGet, _ => false
  | .irqHandlerSetNotification, .irqHandler _ => true
  | .irqHandlerSetNotification, _ => false
  | _, .object _ => true
  | _, _ => false

/-- `dispatchWithCapChecked` at an invocation whose message is shorter than its
arguments (`truncationMinimum`): refused `.truncatedMessage` where the target is
the one it reads its arguments under, and as the wrong capability otherwise. -/
theorem dispatchWithCapChecked_eq_truncated (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState)
    (hR : (routedInvocation decoded.syscallId || routedOverflowOne decoded.syscallId) = true)
    (hT : decoded.msgInfo.length < truncationMinimum decoded.syscallId) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      .error (if truncationTarget decoded.syscallId cap.target then .truncatedMessage
        else .invalidCapability) := by
  rcases cap with ⟨target, rights, badge, mapping⟩
  unfold dispatchWithCapChecked dispatchCapabilityOnly
  cases hS : decoded.syscallId <;> rw [hS] at hR hT <;>
    simp only [routedInvocation, routedOverflowOne, Bool.false_eq_true, Bool.or_false,
      Bool.false_or, truncationMinimum, Nat.not_lt_zero] at hR hT <;>
    have hL := fun k => @requireMessageLength_of_lt decoded k <;>
    cases target <;>
    simp only [hS, truncationTarget, ↓reduceIte, Bool.false_eq_true, Option.some.injEq,
      decodeCSpaceMintArgs, decodeCSpaceCopyArgs, decodeCSpaceMoveArgs, decodeMintReplyCapArgs,
      decodeCSpaceDeleteArgs,
      decodeUntypedRetypeArgs, decodeVSpaceMapArgs, decodeVSpaceUnmapArgs,
      decodeVSpaceUnifyInstructionArgs, decodeServiceRegisterArgs,
      decodeSchedContextConfigureArgsChecked, decodeSchedContextConfigureArgs,
      decodeSchedContextBindArgs, decodeTcbBindNotificationArgs, decodeIrqControlGetArgs,
      decodeIrqHandlerSetNotificationArgs, decodeSetPriorityArgs, decodeSetMCPriorityArgs,
      decodeSetIPCBufferArgs, decodeSetAffinityArgs, decodeSetFaultHandlerArgs,
      decodeSetSpaceArgs, decodePageTableMapArgs, truncationMinimum, hL _ hT, bind,
      Except.bind, dispatchCapabilityOnlyChecked]
  all_goals first | rfl | skip

/-- A capability of the type of a routed invocation that reads arguments is one
its arguments are read under, so a short message reaching the arm is refused
`.truncatedMessage`. -/
theorem truncationTarget_of_accepted (sid : SyscallId) (st : SystemState) (cap : Capability)
    (hR : (routedInvocation sid || routedOverflowOne sid) = true)
    (hM : 0 < truncationMinimum sid)
    (hA : syscallTargetAccepted sid st cap = true) :
    truncationTarget sid cap.target = true := by
  rcases cap with ⟨target, rights, badge, mapping⟩
  cases sid <;> first | (cases hR; done) | skip
  all_goals cases target <;>
    simp_all [syscallTargetAccepted, syscallObjectKind?, truncationTarget, truncationMinimum]

/-- An invocation short of its arguments, behind the operand check: the gate's
type, then its right, then the refusal, `.truncatedMessage` — the order seL4's
decode reads them in, the capability's type first and the length checked
before any argument word. -/
@[inline] def shortArgsOperandArmR (sid : SyscallId) : Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability, st)
        else if !syscallTargetAccepted sid st cap then .error (.invalidCapability, st)
        else if cap.hasRight (syscallRequiredRight sid) then .error (.truncatedMessage, st)
        else .error (syscallMissingRightError sid, st)

/-- `dispatchSyscallChecked` for an invocation whose message is shorter than its
arguments (`dispatchShortArgsCheckedR_eq`). -/
@[inline] def dispatchShortArgsCheckedR (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore (shortArgsOperandArmR sid)

theorem dispatchShortArgsCheckedR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hR : (routedInvocation decoded.syscallId || routedOverflowOne decoded.syscallId) = true)
    (hT : decoded.msgInfo.length < truncationMinimum decoded.syscallId) :
    dispatchShortArgsCheckedR decoded.syscallId decoded.capAddr tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  have hNotYield : decoded.syscallId ≠ .yield := by
    intro h; rw [h] at hR; cases hR
  have hTaint : ∀ st pe pl pt post,
      applySyscallTaintAfter (syscallTaintPlan st tid decoded) pe pl pt post = post := by
    intro st pe pl pt post
    cases hI : routedInvocation decoded.syscallId
    · rw [hI, Bool.false_or] at hR
      cases h : decoded.syscallId <;> rw [h] at hR <;> first | (cases hR; done) | skip
      all_goals first
        | exact applySyscallTaintAfter_configure st tid decoded h pe pl pt post
        | exact applySyscallTaintAfter_serviceRegister st tid decoded h pe pl pt post
        | exact applySyscallTaintAfter_cspaceMint st tid decoded h pe pl pt post
    · exact applySyscallTaintAfter_routed st tid decoded hI pe pl pt post
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
  intro st tcb rootCn ref _ _ hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel,
    syscallInvokeTyped, syscallResolveCap, hRef, hTaint]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [shortArgsOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hType : syscallTargetAccepted decoded.syscallId st cap = false
      · simp only [hIdle, hType, Bool.not_false, Bool.false_eq_true, ↓reduceIte]
      replace hType : syscallTargetAccepted decoded.syscallId st cap = true := by simpa using hType
      by_cases hRight : cap.hasRight (syscallRequiredRight decoded.syscallId) = true
      · simp only [hIdle, hType, Bool.not_true, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [dispatchWithCapChecked_eq_truncated ctx decoded tid executingCore _ cap st hR hT,
          truncationTarget_of_accepted _ st cap hR (Nat.lt_of_le_of_lt (Nat.zero_le _) hT) hType]
        rfl
      · simp only [hIdle, hType, Bool.not_true, hRight, ↓reduceIte, Bool.false_eq_true]

end SeLe4n.Kernel
