-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine

/-!
# The context of the trap in flight

The HAL hands every kernel entry the frame the executing core trapped with
(`Platform.FFI.ffiTrapContext`).  It writes the frame's thirty-five words into
the core's **persistent** object — one per core, outside the heap, never freed
— and answers that object, so a trap allocates nothing to hand its context
over (WS-CV CV3.1).

The object is rewritten by the core's next trap, so nothing may keep it past
the entry that read it.  That is enforced by its type: `InFlightContext` is
not `RegisterFile`, no field of `SystemState` or of any kernel object has this
type, and the only way its words reach the state is `snapshotInto` (or its
specification `snapshot`), which copies them into a register file the state
owns.  An entry can read the trap's argument words straight from its fields.

The fields are `RegisterFile`'s, in the same order, so the object's layout is
the trap frame's: word `i` at byte offset `8 · i` after the header.
-/

namespace SeLe4n.Kernel.Architecture

/-- **The register words of the trap in flight**: `x0`–`x30`, `SP_EL0`,
`ELR_EL1`, `SPSR_EL1` and `TPIDR_EL0`, in the trap frame's order.  The HAL's
per-core object, read during one kernel entry and copied, never kept. -/
structure InFlightContext where
  /-- `x0`. -/
  x0 : UInt64
  /-- `x1`. -/
  x1 : UInt64
  /-- `x2`. -/
  x2 : UInt64
  /-- `x3`. -/
  x3 : UInt64
  /-- `x4`. -/
  x4 : UInt64
  /-- `x5`. -/
  x5 : UInt64
  /-- `x6`. -/
  x6 : UInt64
  /-- `x7`. -/
  x7 : UInt64
  /-- `x8`. -/
  x8 : UInt64
  /-- `x9`. -/
  x9 : UInt64
  /-- `x10`. -/
  x10 : UInt64
  /-- `x11`. -/
  x11 : UInt64
  /-- `x12`. -/
  x12 : UInt64
  /-- `x13`. -/
  x13 : UInt64
  /-- `x14`. -/
  x14 : UInt64
  /-- `x15`. -/
  x15 : UInt64
  /-- `x16`. -/
  x16 : UInt64
  /-- `x17`. -/
  x17 : UInt64
  /-- `x18`. -/
  x18 : UInt64
  /-- `x19`. -/
  x19 : UInt64
  /-- `x20`. -/
  x20 : UInt64
  /-- `x21`. -/
  x21 : UInt64
  /-- `x22`. -/
  x22 : UInt64
  /-- `x23`. -/
  x23 : UInt64
  /-- `x24`. -/
  x24 : UInt64
  /-- `x25`. -/
  x25 : UInt64
  /-- `x26`. -/
  x26 : UInt64
  /-- `x27`. -/
  x27 : UInt64
  /-- `x28`. -/
  x28 : UInt64
  /-- `x29`. -/
  x29 : UInt64
  /-- `x30`. -/
  x30 : UInt64
  /-- `SP_EL0` (word 31). -/
  sp : UInt64
  /-- `ELR_EL1` (word 32). -/
  pc : UInt64
  /-- `SPSR_EL1` (word 33). -/
  pstate : UInt64
  /-- `TPIDR_EL0` (word 34). -/
  tpidr : UInt64
  deriving DecidableEq, Inhabited

namespace InFlightContext

/-- **The words as a register file** — a new object, the specification of
`snapshotInto`. -/
def snapshot (c : @& InFlightContext) : SeLe4n.RegisterFile :=
  ⟨c.x0, c.x1, c.x2, c.x3, c.x4, c.x5, c.x6, c.x7, c.x8, c.x9, c.x10, c.x11, c.x12, c.x13, c.x14, c.x15, c.x16, c.x17, c.x18, c.x19, c.x20, c.x21, c.x22, c.x23, c.x24, c.x25, c.x26, c.x27, c.x28, c.x29, c.x30, c.sp, c.pc, c.pstate, c.tpidr⟩

/-- **The words written into `rf`**: the file `snapshot` answers, built in
`rf`'s object when `rf` is the only reference to it, so an exclusively owned
destination is written in place and nothing is allocated.  `rf`'s words are
all replaced; the test on `x0` only keeps `rf`'s constructor live for the
compiler to reuse (both branches are `snapshot`, `snapshotInto_eq`). -/
def snapshotInto (c : @& InFlightContext) (rf : SeLe4n.RegisterFile) : SeLe4n.RegisterFile :=
  if rf.x0 = c.x0 then { rf with x1 := c.x1, x2 := c.x2, x3 := c.x3, x4 := c.x4, x5 := c.x5, x6 := c.x6, x7 := c.x7, x8 := c.x8, x9 := c.x9, x10 := c.x10, x11 := c.x11, x12 := c.x12, x13 := c.x13, x14 := c.x14, x15 := c.x15, x16 := c.x16, x17 := c.x17, x18 := c.x18, x19 := c.x19, x20 := c.x20, x21 := c.x21, x22 := c.x22, x23 := c.x23, x24 := c.x24, x25 := c.x25, x26 := c.x26, x27 := c.x27, x28 := c.x28, x29 := c.x29, x30 := c.x30, sp := c.sp, pc := c.pc, pstate := c.pstate, tpidr := c.tpidr }
  else { rf with x0 := c.x0, x1 := c.x1, x2 := c.x2, x3 := c.x3, x4 := c.x4, x5 := c.x5, x6 := c.x6, x7 := c.x7, x8 := c.x8, x9 := c.x9, x10 := c.x10, x11 := c.x11, x12 := c.x12, x13 := c.x13, x14 := c.x14, x15 := c.x15, x16 := c.x16, x17 := c.x17, x18 := c.x18, x19 := c.x19, x20 := c.x20, x21 := c.x21, x22 := c.x22, x23 := c.x23, x24 := c.x24, x25 := c.x25, x26 := c.x26, x27 := c.x27, x28 := c.x28, x29 := c.x29, x30 := c.x30, sp := c.sp, pc := c.pc, pstate := c.pstate, tpidr := c.tpidr }

/-- `snapshotInto` is `snapshot`, whatever the destination held. -/
theorem snapshotInto_eq (c : InFlightContext) (rf : SeLe4n.RegisterFile) :
    c.snapshotInto rf = c.snapshot := by
  unfold snapshotInto snapshot
  split
  · next h => cases rf; simp only at h; subst h; rfl
  · rfl

/-- Word `i` of the context, in the register file's layout. -/
def word (c : InFlightContext) (i : Nat) : UInt64 :=
  c.snapshot.word i

/-- The snapshot holds the context's words. -/
theorem snapshot_word (c : InFlightContext) (i : Nat) : c.snapshot.word i = c.word i := rfl

/-- …and so does the destination `snapshotInto` writes. -/
theorem snapshotInto_word (c : InFlightContext) (rf : SeLe4n.RegisterFile) (i : Nat) :
    (c.snapshotInto rf).word i = c.word i := by
  rw [snapshotInto_eq]; rfl

/-- The context holding a register file's words — the form a test or a probe
builds an in-flight context from. -/
def ofRegisterFile (rf : SeLe4n.RegisterFile) : InFlightContext :=
  ⟨rf.x0, rf.x1, rf.x2, rf.x3, rf.x4, rf.x5, rf.x6, rf.x7, rf.x8, rf.x9, rf.x10, rf.x11, rf.x12, rf.x13, rf.x14, rf.x15, rf.x16, rf.x17, rf.x18, rf.x19, rf.x20, rf.x21, rf.x22, rf.x23, rf.x24, rf.x25, rf.x26, rf.x27, rf.x28, rf.x29, rf.x30, rf.sp, rf.pc, rf.pstate, rf.tpidr⟩

/-- A context built from a file snapshots back to that file. -/
@[simp] theorem snapshot_ofRegisterFile (rf : SeLe4n.RegisterFile) :
    (ofRegisterFile rf).snapshot = rf := by
  cases rf; rfl

end InFlightContext

end SeLe4n.Kernel.Architecture
