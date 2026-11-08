-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.RefusalCarryingEndpoint

/-!
# A signal, wait or receive past the inline words, refusing in its own state

A signal, a wait or a receive whose message-info length runs past the layout's
message registers (`RegisterRoutedSyscall.overflowed`): the decode reads the
caller's overflow slots, and the dispatch reads only the inline words.  When the
slots lie on one page, the decode reads them exactly when it reads the first,
and its TLB walk is that one page's, so the call is the short route's dispatch
on the decode the long message reads to (`overflowedDecode`), which refuses in
the state it was handed (`dispatchOverflowedCheckedR_eq`).
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
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .overflowed sid capAddr mi)
    (hRead : ∀ j, j < mi.length - 4 →
      ∃ w, Architecture.IpcBufferRead.ipcBufferReadMr st tid j = .ok w) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .ok (overflowedDecode st tid rf sid capAddr mi) := by
  obtain ⟨_, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedOverflowed st tid _ rf 32 sid capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  have hM := mapM_readOverflowWord st tid (mi.length - 4) 0
    (fun j _ h2 => hRead j (by omega))
  rw [hDec]
  unfold mergeOverflowWords
  simp only [Array.size_map, hSz, List.range_eq_range', hM, overflowRegsFrom_eq_map, List.map_map,
    bind, Except.bind, pure, Except.pure, overflowedDecode]
  rfl

/-- …and one whose first overflow slot does not read is refused as the decode
refuses it. -/
theorem decodeSyscallArgsFromState_of_routedOverflowed_error (st : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (mi : MessageInfo)
    (hR : registerRoutedSyscall SeLe4n.arm64DefaultLayout rf 32 = .overflowed sid capAddr mi)
    (e : Architecture.IpcBufferRead.IpcBufferReadError)
    (h0 : Architecture.IpcBufferRead.ipcBufferReadMr st tid 0 = .error e) :
    decodeSyscallArgsFromState st tid SeLe4n.arm64DefaultLayout rf 32 =
      .error .invalidMessageInfo := by
  obtain ⟨hGt, _, _, hDec⟩ :=
    decodeSyscallArgsFromState_of_routedOverflowed st tid _ rf 32 sid capAddr mi hR
  have hSz : SeLe4n.arm64DefaultLayout.msgRegs.size = 4 := rfl
  rw [hSz] at hGt
  obtain ⟨m, hm⟩ : ∃ m, mi.length - 4 = m + 1 := ⟨mi.length - 5, by omega⟩
  rw [hDec]
  unfold mergeOverflowWords
  simp only [Array.size_map, hSz, hm, List.range_eq_range', List.range'_succ, List.mapM_cons,
    readOverflowWord, h0, bind, Except.bind]

/-- **The overflowed dispatch**: the short route's refusal-carrying dispatch for
the signal, the wait and the receive, read off the inline words.  No other
syscall is routed here (`routedOverflowed`).  A specification: the compiled
entry runs the routed arm (`RoutedArms.Overflowed`). -/
noncomputable def dispatchOverflowedCheckedR (ctx : LabelingContext) (sid : SyscallId)
    (capAddr : SeLe4n.CPtr) (rf : SeLe4n.RegisterFile) (len : Nat) (tid : SeLe4n.ThreadId)
    (executingCore : Concurrency.CoreId) : RefusalCarrying Unit :=
  match sid with
  | .notificationSignal =>
    dispatchSignalCheckedR ctx capAddr (.ok { badge := Badge.ofWord (readRegWord rf ⟨2⟩) }) tid
      executingCore
  | .notificationWait => dispatchWaitCheckedR ctx capAddr tid executingCore
  | .receive =>
    dispatchReceiveCheckedR ctx capAddr len (SeLe4n.CPtr.ofWord (readRegWord rf ⟨2⟩)) tid
      executingCore
  | _ => fun st => .error (.illegalState, st)

/-- The syscalls `routedOverflowed` admits. -/
theorem routedOverflowed_cases {sid : SyscallId} (h : routedOverflowed sid = true) :
    sid = .notificationSignal ∨ sid = .notificationWait ∨ sid = .receive := by
  cases sid <;> simp_all [routedOverflowed]

/-- **The overflowed dispatch is the checked dispatch of the decode the long
message reads to**, refusing in the state it was handed: the signal's badge and
the receive's reply address are the first inline word, as the decode's. -/
theorem dispatchOverflowedCheckedR_eq (ctx : LabelingContext) (S : SystemState)
    (tid : SeLe4n.ThreadId) (rf : SeLe4n.RegisterFile) (sid : SyscallId) (capAddr : SeLe4n.CPtr)
    (mi : MessageInfo) (executingCore : Concurrency.CoreId)
    (hRt : routedOverflowed sid = true) :
    dispatchOverflowedCheckedR ctx sid capAddr rf mi.length tid executingCore =
      RefusalCarrying.ofKernel
        (dispatchSyscallChecked ctx (overflowedDecode S tid rf sid capAddr mi) tid executingCore) := by
  have h0 : (overflowedDecode S tid rf sid capAddr mi).msgRegs[0]? = some (readReg rf ⟨2⟩) := by
    simp only [overflowedDecode, Architecture.regMessageRegs]
    rw [Array.getElem?_append_left (by simp [SeLe4n.arm64DefaultLayout])]
    simp [SeLe4n.arm64DefaultLayout]
  rcases routedOverflowed_cases hRt with rfl | rfl | rfl
  · -- the signal
    have hS : 0 < (overflowedDecode S tid rf .notificationSignal capAddr mi).msgRegs.size := by
      simp only [overflowedDecode, Architecture.regMessageRegs, Array.size_append, Array.size_map]
      exact Nat.lt_of_lt_of_le (by decide) (Nat.le_add_right _ _)
    have hG : (overflowedDecode S tid rf .notificationSignal capAddr mi).msgRegs[0]'hS =
        readReg rf ⟨2⟩ := by
      rw [Array.getElem?_eq_getElem hS] at h0
      exact Option.some.inj h0
    have hArgs : (.ok { badge := Badge.ofWord (readRegWord rf ⟨2⟩) } : Except KernelError
          Architecture.SyscallArgDecode.NotificationSignalArgs) =
        Architecture.SyscallArgDecode.decodeNotificationSignalArgs
          (overflowedDecode S tid rf .notificationSignal capAddr mi) := by
      simp only [Architecture.SyscallArgDecode.decodeNotificationSignalArgs,
        Architecture.SyscallArgDecode.requireMsgReg, dif_pos hS, hG, readReg_eq_word, bind,
        Except.bind, pure, Except.pure, SeLe4n.Badge.ofWord_eq_ofNatMasked]
    unfold dispatchOverflowedCheckedR
    exact dispatchSignalCheckedR_eq ctx (overflowedDecode S tid rf .notificationSignal capAddr mi)
      _ tid executingCore rfl hArgs
  · -- the wait
    unfold dispatchOverflowedCheckedR
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
    exact dispatchReceiveCheckedR_eq ctx (overflowedDecode S tid rf .receive capAddr mi)
      tid executingCore mi.length _ rfl rfl rfl hA

end SeLe4n.Kernel
