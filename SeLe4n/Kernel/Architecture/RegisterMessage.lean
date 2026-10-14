/-
Copyright (C) 2026 seLe4n contributors
SPDX-License-Identifier: GPL-3.0-or-later
-/
import SeLe4n.Kernel.Architecture.RegisterDecode
import SeLe4n.Kernel.Architecture.SyscallReturn

/-!
# A message read in the sender's registers

WS-ZA ZA4.7.  A send, call or reply whose words all sit in registers carries
the body `regMessageBody`: the layout's message registers, read and cut to the
declared length.  Its length (`regMessageBody_size`), each word
(`regMessageBody_word`) and the frame it delivers
(`returnFrameOfMessage_regMessageBody`) are read straight from the register
file, so a delivery that needs only those builds no array.
-/

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

/-- The layout's message registers, read. -/
@[inline] def regMessageRegs (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile) :
    Array SeLe4n.RegValue :=
  layout.msgRegs.map (SeLe4n.readReg rf)

/-- The body of a register-routed message: the layout's message registers,
read and cut to the declared length (`extractMessageRegisters`,
`regMessageBody_eq_extract`).  It takes the message info's length field, the
only one it reads. -/
@[inline] def regMessageBody (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) : Array SeLe4n.RegValue :=
  (regMessageRegs layout rf).extract 0
    (min len (min maxMessageRegisters (regMessageRegs layout rf).size))

theorem regMessageBody_eq_extract (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (mi : MessageInfo) :
    regMessageBody layout rf mi.length =
      RegisterDecode.extractMessageRegisters (regMessageRegs layout rf) mi := rfl

/-- The body's length, from the declared length and the layout alone.  It takes
the message info's length field rather than the record, so a path that needs
only the length never holds the record. -/
@[inline] def regMessageLength (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) : Nat :=
  min len (min maxMessageRegisters layout.msgRegs.size)

/-- A general-purpose register's word, `x31` and beyond reading `0`
(`RegisterFile.gpr` without the round trip through `Nat`). -/
@[inline] def regWord (rf : SeLe4n.RegisterFile) (r : SeLe4n.RegName) : UInt64 :=
  if r.val < 31 then rf.word r.val else 0

/-- Word `i` of the body, `0` past its length.  Out of line: it returns a bare
machine word, so a frame built from such words is built after every branch, not
at a join of them. -/
@[noinline] def regMessageWord (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (i : Nat) : UInt64 :=
  if h : i < regMessageLength layout len then
    regWord rf (layout.msgRegs[i]'(Nat.lt_of_lt_of_le h
      (Nat.le_trans (Nat.min_le_right _ _) (Nat.min_le_right _ _))))
  else 0

theorem regMessageBody_size (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) : (regMessageBody layout rf len).size = regMessageLength layout len := by
  simp only [regMessageBody, regMessageRegs, regMessageLength,
    Array.size_extract, Array.size_map]
  omega

theorem regMessageBody_word (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (i : Nat) :
    ((((regMessageBody layout rf len)[i]?).map SeLe4n.RegValue.val).getD 0).toUInt64 =
      regMessageWord layout rf len i := by
  unfold regMessageWord
  split
  · next h =>
    have hs : i < (regMessageBody layout rf len).size := by
      rw [regMessageBody_size]; exact h
    rw [Array.getElem?_eq_getElem hs]
    simp only [regMessageBody, regMessageRegs, Array.getElem_extract,
      Nat.zero_add, Array.getElem_map, Option.map_some, Option.getD_some, SeLe4n.readReg,
      SeLe4n.RegisterFile.gpr, regWord]
    split <;> simp
  · next h =>
    have hs : (regMessageBody layout rf len).size ≤ i := by
      rw [regMessageBody_size]; omega
    rw [Array.getElem?_eq_none hs]
    rfl

/-- The badge word a frame carries, `0` for none.  Out of line, as
`regMessageWord`. -/
@[noinline] def badgeWordOrZero (badge : Option SeLe4n.Badge) : UInt64 :=
  (badge.map SeLe4n.Badge.word).getD 0

/-- The message-info word a frame of a register-routed message carries.  Out of
line, as `regMessageWord`. -/
@[noinline] def regMessageInfoWord (layout : SeLe4n.SyscallRegisterLayout) (len : Nat) :
    UInt64 :=
  (({ length := min (min (regMessageLength layout len) 4) maxMessageRegisters
      extraCaps := min 0 Model.maxExtraCaps
      label := min 0 (errorLabelBase - 1) } : MessageInfo).encode).toUInt64

/-- The frame a register-routed message of at most four words delivers:
`returnFrameOfMessage` of its body (`returnFrameOfMessage_regMessageBody`), each
word read from the register file. -/
@[inline] def regMessageFrame (layout : SeLe4n.SyscallRegisterLayout) (rf : SeLe4n.RegisterFile)
    (len : Nat) (badge : Option SeLe4n.Badge) : SyscallReturnFrame :=
  { x0 := badgeWordOrZero badge
    x1 := regMessageInfoWord layout len
    x2 := regMessageWord layout rf len 0
    x3 := regMessageWord layout rf len 1
    x4 := regMessageWord layout rf len 2
    x5 := regMessageWord layout rf len 3 }

theorem returnFrameOfMessage_regMessageBody (layout : SeLe4n.SyscallRegisterLayout)
    (rf : SeLe4n.RegisterFile) (len : Nat) (badge : Option SeLe4n.Badge) (g : Bool) :
    returnFrameOfMessage
        { registers := regMessageBody layout rf len, caps := #[], badge := badge,
          capsGranted := g } 0 0 =
      regMessageFrame layout rf len badge := by
  simp only [returnFrameOfMessage, returnMessageInfo, regMessageFrame, badgeWordOrZero,
    regMessageInfoWord, regMessageBody_size,
    regMessageBody_word, Nat.add_zero]

end SeLe4n.Kernel.Architecture
