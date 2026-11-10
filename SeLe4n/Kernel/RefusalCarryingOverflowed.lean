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

A call whose message-info length runs past the layout's message registers and
whose dispatch reads no word past overflow slot 0
(`RegisterRoutedSyscall.overflowed`): a signal, a wait or a receive, which read
only the inline words; an invocation or an audited call, whose arguments are the
inline words; and a configure or a service register, whose fifth argument is
slot 0.  The decode reads the caller's overflow slots.  When the slots lie on
one page, the decode reads them exactly when it reads the first, and its TLB
walk is that one page's, so the call is the short route's dispatch on the
decode the long message reads to (`overflowedDecode`), which refuses in the
state it was handed (`dispatchOverflowedCheckedR_eq`).

A configure or a service register whose message fits the inline words
(`RegisterRoutedSyscall.shortArgs`) is short of its fifth argument: its
argument decode refuses once its capability is found and checked
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
  obtain ⟨mi', hMI', -, _, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedOverflowed st tid _ rf 32 sid capAddr mi.length hR
  obtain rfl : mi = mi' := Except.ok.inj (hMI.symm.trans hMI')
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  have hM := mapM_readOverflowWord st tid (mi.length - 4) 0
    (fun j _ h2 => hRead j (by omega))
  rw [hDec]
  unfold mergeOverflowWords
  simp only [Array.size_map, hSz, List.range_eq_range', hM, overflowRegsFrom_eq_map, List.map_map,
    bind, Except.bind, pure, Except.pure, overflowedDecode]
  rfl

/-- …and one with an overflow slot that does not read is refused as the decode
refuses it. -/
theorem decodeSyscallArgsFromState_of_routedOverflowed_error (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (mi : MessageInfo)
    (hMI : decodeMsgInfo (readReg rf SeLe4n.arm64DefaultLayout.msgInfoReg) = .ok mi)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .overflowed sid capAddr mi.length)
    (j : Nat) (hj : j < mi.length - 4) (e : Architecture.IpcBufferRead.IpcBufferReadError)
    (h0 : Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .error e) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .error .invalidMessageInfo := by
  obtain ⟨mi', hMI', -, hGt, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedOverflowed st tid _ rf 32 sid capAddr mi.length hR
  obtain rfl : mi = mi' := Except.ok.inj (hMI.symm.trans hMI')
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  rw [hDec]
  unfold mergeOverflowWords
  simp only [Array.size_map, hSz, List.range_eq_range',
    mapM_readOverflowWord_error st tid (mi.length - 4) 0 ⟨j, e, Nat.zero_le _, by omega, h0⟩,
    bind, Except.bind]

/-- **The overflowed dispatch**: the short route's refusal-carrying dispatch,
read off the inline words and, for a five-word invocation, the overflow word `w`
in slot 0.  No other syscall is routed here (`routedOverflowed`).  A
specification: the compiled entry runs the routed arm (`RoutedArms.Overflowed`).
A yield reads no operand, and refuses in the state it was handed
(`yieldOnCoreR`). -/
noncomputable def dispatchOverflowedCheckedR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (rf : SeLe4n.RegisterFile) (len : Nat) (w : UInt64)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  if routedInvocation sid then dispatchInvocationCheckedR ctx sid capAddr rf tid executingCore
  else if routedAudited sid then dispatchAuditedCheckedR ctx sid capAddr rf tid executingCore
  else
  match sid with
  | .notificationSignal =>
    dispatchSignalCheckedR ctx capAddr tid executingCore
  | .notificationWait => dispatchWaitCheckedR ctx capAddr tid executingCore
  | .receive =>
    dispatchReceiveCheckedR ctx capAddr len (SeLe4n.CPtr.ofWord (readRegWord rf ⟨2⟩)) tid
      executingCore
  | .schedContextConfigure => dispatchConfigureCheckedR capAddr rf w tid executingCore
  | .serviceRegister => dispatchServiceRegisterCheckedR ctx capAddr rf w tid executingCore
  | .yield => fun st =>
    match yieldOnCoreR st executingCore with
    | .error r => .error r
    | .ok st' => .ok ((), st')
  | _ => fun st => .error (.illegalState, st)

/-- The syscalls `routedOverflowed` admits besides the invocations and the
audited calls. -/
theorem routedOverflowed_cases {sid : SyscallId} (h : routedOverflowed sid = true)
    (hI : routedInvocation sid = false) (hA : routedAudited sid = false) :
    sid = .notificationSignal ∨ sid = .notificationWait ∨ sid = .receive ∨
      sid = .schedContextConfigure ∨ sid = .serviceRegister ∨ sid = .yield := by
  cases sid <;> simp_all [routedOverflowed, routedOverflowOne]

/-- An overflowed decode's words read as the inline words below four, and as
the inline words and then slot 0's word below five. -/
theorem overflowedDecode_agree (S : SystemState) (tid : SeLe4n.ThreadId)
    (rf : SeLe4n.RegisterFile) (sid : SyscallId) (capAddr : SeLe4n.CPtr) (mi : MessageInfo)
    (hLen : 4 < mi.length) :
    MsgRegsAgreeBelow (overflowedDecode S tid rf sid capAddr mi).msgRegs
        (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg rf)) 4 ∧
    MsgRegsAgreeBelow (overflowedDecode S tid rf sid capAddr mi).msgRegs
        (SeLe4n.arm64DefaultLayout.msgRegs.map (readReg rf) ++
          #[(⟨(overflowWordAt S tid 0).toNat⟩ : RegValue)]) 5 := by
  have hSz : (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf).size = 4 := by
    simp [Architecture.regMessageRegs, SeLe4n.arm64DefaultLayout]
  obtain ⟨m, hm⟩ : ∃ m, mi.length - 4 = m + 1 := ⟨mi.length - 5, by omega⟩
  refine ⟨?_, ?_⟩
  · have h := MsgRegsAgreeBelow.append (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf)
      (overflowRegsFrom S tid 0 (mi.length - 4)).toArray
    rw [hSz] at h
    exact h
  · have h := MsgRegsAgreeBelow.append_cons
      (Architecture.regMessageRegs SeLe4n.arm64DefaultLayout rf)
      ⟨(overflowWordAt S tid 0).toNat⟩ (overflowRegsFrom S tid 1 m)
    rw [hSz] at h
    simp only [overflowedDecode, hm]
    exact h

/-- **The overflowed dispatch is the checked dispatch of the decode the long
message reads to**, refusing in the state it was handed: the signal reads no
word (its badge is its capability's); the receive's reply address is the first
inline word, as the decode's; an
invocation's and an audited call's arguments the inline words; and a five-word
invocation's fifth argument slot 0's word. -/
theorem dispatchOverflowedCheckedR_eq (ctx : LabelingContext) (S : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (mi : MessageInfo) (executingCore : Concurrency.CoreId)
    (hRt : routedOverflowed sid = true) (hLen : 4 < mi.length) (st : SystemState)
    (hCur : st.scheduler.currentOnCore executingCore = some tid) :
    dispatchOverflowedCheckedR ctx sid capAddr rf mi.length (overflowWordAt S tid 0) tid
        executingCore st =
      RefusalCarrying.ofKernel
        (dispatchSyscallChecked ctx (overflowedDecode S tid rf sid capAddr mi) tid executingCore)
        st := by
  by_cases hY : sid = .yield
  · -- the yield, which reads no word: the entry's caller is current
    subst hY
    simp only [dispatchOverflowedCheckedR, routedInvocation, routedAudited, Bool.or_false,
      Bool.false_eq_true, ↓reduceIte, RefusalCarrying.ofKernel, dispatchSyscallChecked,
      overflowedDecode, hCur, ne_eq, not_true_eq_false, dispatchYield, yieldOnCoreR_eq]
    cases yieldOnCore st executingCore <;> rfl
  refine congrFun ?_ st
  obtain ⟨hA4, hA5⟩ := overflowedDecode_agree S tid rf sid capAddr mi hLen
  by_cases hI : routedInvocation sid = true
  · unfold dispatchOverflowedCheckedR
    rw [if_pos hI]
    exact dispatchInvocationCheckedR_eq ctx (overflowedDecode S tid rf sid capAddr mi) rf tid
      executingCore hI hA4
  by_cases hAu : routedAudited sid = true
  · unfold dispatchOverflowedCheckedR
    rw [if_neg hI, if_pos hAu]
    exact dispatchAuditedCheckedR_eq ctx (overflowedDecode S tid rf sid capAddr mi) rf tid
      executingCore hAu hA4
  have h0 : (overflowedDecode S tid rf sid capAddr mi).msgRegs[0]? = some (readReg rf ⟨2⟩) := by
    simp only [overflowedDecode, Architecture.regMessageRegs]
    rw [Array.getElem?_append_left (by simp [SeLe4n.arm64DefaultLayout])]
    simp [SeLe4n.arm64DefaultLayout]
  rcases routedOverflowed_cases hRt (Bool.eq_false_iff.mpr hI) (Bool.eq_false_iff.mpr hAu) with
    rfl | rfl | rfl | rfl | rfl | rfl
  · -- the signal
    unfold dispatchOverflowedCheckedR
    rw [if_neg hI, if_neg hAu]
    exact dispatchSignalCheckedR_eq ctx (overflowedDecode S tid rf .notificationSignal capAddr mi)
      tid executingCore rfl
  · -- the wait
    unfold dispatchOverflowedCheckedR
    rw [if_neg hI, if_neg hAu]
    exact dispatchWaitCheckedR_eq ctx (overflowedDecode S tid rf .notificationWait capAddr mi)
      tid executingCore rfl
  · -- the receive
    have hA : mi.length ≠ 0 →
        (overflowedDecode S tid rf .receive capAddr mi).msgRegs[0]? =
          some ⟨(SeLe4n.CPtr.ofWord (readRegWord rf ⟨2⟩)).toNat⟩ := by
      intro _
      rw [h0, readReg_eq_word, SeLe4n.CPtr.ofWord_eq_ofNat,
        SeLe4n.CPtr.toNat_ofNat (by
          have := (readRegWord rf ⟨2⟩).toNat_lt
          unfold machineWordMax machineWordBits
          exact this)]
    unfold dispatchOverflowedCheckedR
    rw [if_neg hI, if_neg hAu]
    exact dispatchReceiveCheckedR_eq ctx (overflowedDecode S tid rf .receive capAddr mi)
      tid executingCore mi.length _ rfl rfl hA
  · -- the configure
    unfold dispatchOverflowedCheckedR
    rw [if_neg hI, if_neg hAu]
    exact dispatchConfigureCheckedR_eq ctx (overflowedDecode S tid rf _ capAddr mi) rf _ tid
      executingCore rfl hA5
  · -- the service register
    unfold dispatchOverflowedCheckedR
    rw [if_neg hI, if_neg hAu]
    exact dispatchServiceRegisterCheckedR_eq ctx (overflowedDecode S tid rf _ capAddr mi) rf _ tid
      executingCore rfl hA5
  · exact absurd rfl hY

/-! ## A five-word invocation short of its fifth word -/

/-- The target a five-word invocation reads its arguments under: a core's
scheduling control for the configure, an object for the service register.  Any
other is refused before its arguments are read. -/
@[inline] def fiveWordArgsTarget (sid : SyscallId) (t : CapTarget) : Bool :=
  match sid, t with
  | .schedContextConfigure, .schedControl _ => true
  | .serviceRegister, .object _ => true
  | _, _ => false

/-- A five-word invocation's argument decode refuses a message of the inline
words alone: the four words read, and the fifth is past them. -/
theorem decodeFiveWordArgs_short (decoded : SyscallDecodeResult) (rf : SeLe4n.RegisterFile)
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg rf)) :
    decodeSchedContextConfigureArgsChecked decoded = .error .invalidMessageInfo ∧
    decodeServiceRegisterArgs decoded = .error .invalidMessageInfo := by
  constructor
  · unfold decodeSchedContextConfigureArgsChecked decodeSchedContextConfigureArgs
    rw [hRegs]
    simp [requireMsgReg, SeLe4n.arm64DefaultLayout, bind, Except.bind]
  · unfold decodeServiceRegisterArgs
    rw [hRegs]
    simp [requireMsgReg, SeLe4n.arm64DefaultLayout, bind, Except.bind]

/-- `dispatchWithCapChecked` at a five-word invocation of the inline words alone:
refused, as missing its argument where the target is the one it reads its
arguments under, and as the wrong capability otherwise. -/
theorem dispatchWithCapChecked_eq_shortArgs (ctx : LabelingContext)
    (decoded : SyscallDecodeResult) (rf : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) (gate : SyscallGate) (cap : Capability)
    (st : SystemState) (hR : routedOverflowOne decoded.syscallId = true)
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg rf)) :
    dispatchWithCapChecked ctx decoded tid executingCore gate cap st =
      .error (if fiveWordArgsTarget decoded.syscallId cap.target then .invalidMessageInfo
        else .invalidCapability) := by
  obtain ⟨hC, hS⟩ := decodeFiveWordArgs_short decoded rf hRegs
  rcases decoded with ⟨capAddr, msgInfo, sid, msgRegs, inlineCount, overflowCount⟩
  rcases cap with ⟨target, rights, badge, mapping⟩
  simp only at hR
  cases sid <;> simp only [routedOverflowOne, Bool.false_eq_true] at hR <;>
    cases target <;>
    simp only [dispatchWithCapChecked, dispatchCapabilityOnly, hC, hS, fiveWordArgsTarget]
  all_goals rfl

/-- A five-word invocation short of its fifth word, behind the operand check:
the rights gate `syscallLookupCap` applies, then the refusal. -/
@[inline] def shortArgsOperandArmR (sid : SyscallId) : Option Capability → RefusalCarrying Unit :=
  fun operand st =>
    match operand with
    | none => .error (.invalidCapability, st)
    | some cap =>
        if SeLe4n.Kernel.capTargetsReservedKernelObject cap then .error (.invalidCapability, st)
        else if cap.hasRight (syscallRequiredRight sid) then
          .error (if fiveWordArgsTarget sid cap.target then .invalidMessageInfo
            else .invalidCapability, st)
        else .error (.illegalAuthority, st)

/-- `dispatchSyscallChecked` for a five-word invocation of the inline words alone
(`dispatchShortArgsCheckedR_eq`). -/
@[inline] def dispatchShortArgsCheckedR (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  dispatchOperandCheckedR capAddr tid executingCore (shortArgsOperandArmR sid)

theorem dispatchShortArgsCheckedR_eq (ctx : LabelingContext) (decoded : SyscallDecodeResult)
    (rf : SeLe4n.RegisterFile) (tid : SeLe4n.ThreadId) (executingCore : Concurrency.CoreId)
    (hR : routedOverflowOne decoded.syscallId = true)
    (hRegs : decoded.msgRegs = SeLe4n.arm64DefaultLayout.msgRegs.map (readReg rf)) :
    dispatchShortArgsCheckedR decoded.syscallId decoded.capAddr tid executingCore =
      RefusalCarrying.ofKernel (dispatchSyscallChecked ctx decoded tid executingCore) := by
  have hFirst : syscallChecksTargetFirst decoded.syscallId = false := by
    cases h : decoded.syscallId <;> rw [h] at hR <;> first | (cases hR; done) | rfl
  have hNotYield : decoded.syscallId ≠ .yield := by
    intro h; rw [h] at hR; cases hR
  have hTaint : ∀ st pe pl pt post,
      applySyscallTaintAfter (syscallTaintPlan st tid decoded) pe pl pt post = post := by
    intro st pe pl pt post
    cases h : decoded.syscallId <;> rw [h] at hR <;> first | (cases hR; done) | skip
    all_goals first
      | exact applySyscallTaintAfter_configure st tid decoded h pe pl pt post
      | exact applySyscallTaintAfter_serviceRegister st tid decoded h pe pl pt post
  apply dispatchOperandCheckedR_eq ctx decoded tid executingCore _ hNotYield
  intro st tcb rootCn ref _ _ hRef
  simp only [dispatchCheckedArmThenTaint, RefusalCarrying.ofKernel, hFirst,
    Bool.false_eq_true, ↓reduceIte, syscallInvoke, syscallLookupCap, syscallResolveCap, hRef,
    hTaint]
  generalize SystemState.lookupSlotCap st ref = operand
  rcases operand with _ | cap
  · rfl
  · simp only [shortArgsOperandArmR]
    by_cases hIdle : SeLe4n.Kernel.capTargetsReservedKernelObject cap = true
    · simp only [hIdle, ↓reduceIte]
    · by_cases hRight : cap.hasRight (syscallRequiredRight decoded.syscallId) = true
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]
        rw [dispatchWithCapChecked_eq_shortArgs ctx decoded rf tid executingCore _ cap st hR hRegs]
      · simp only [hIdle, hRight, ↓reduceIte, Bool.false_eq_true]

end SeLe4n.Kernel
