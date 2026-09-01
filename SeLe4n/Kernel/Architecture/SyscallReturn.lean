-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-!
# Syscall return convention (WS-RA)

The model of the seL4 ARM64 syscall **return** convention — the direction the
kernel never had.  The argument direction lives in the sibling modules
`RegisterDecode.lean` / `SyscallArgDecode.lean`; this module is their dual:

* `x0` — the primary return value: a full-width badge, a queried word, or `0`
  for `Unit`-returning syscalls.
* `x1` — a `MessageInfo` whose **label** carries the error status:
  label `0` = success, label `d + 1` = `KernelError` discriminant `d`.
  The `+ 1` is load-bearing: discriminant `0` is `.invalidCapability`, so a
  label carrying the discriminant directly would alias the first error with
  success — the silent-aliasing class WS-RA exists to remove
  (`errorLabel_never_zero`).
* `x2`-`x5` — message registers (the inline window; a delivered message
  longer than 4 registers keeps its full payload in `pendingMessage`, and the
  frame reports the window — `returnFrame_message_window`).

Nothing in this module is live until the WS-RA flip: the FFI boundary keeps
the bit-63 `encodeOk` / `encodeError` protocol until `Platform/FFI.lean` and
the Rust mirror move together (plan §5, the migration window).

Plan: `docs/planning/SYSCALL_RETURN_ABI_PLAN.md` §3 (RA.A.1-RA.A.8).
-/

namespace SeLe4n.Model.KernelError

/-- The canonical numeric discriminant of each `KernelError` — the 55-arm
table that previously lived only in `Platform.FFI.KernelError.toUInt32`
(which becomes this function's `UInt32` instance, so the table exists
exactly once).  Mirrors `rust/sele4n-types/src/error.rs` exactly;
`tests/SyscallDispatchSuite.lean` round-trips the pairing. -/
def toDiscriminant : KernelError → Nat
  | .invalidCapability             => 0
  | .objectNotFound                => 1
  | .illegalState                  => 2
  | .illegalAuthority              => 3
  | .policyDenied                  => 4
  | .dependencyViolation           => 5
  | .schedulerInvariantViolation   => 6
  | .endpointStateMismatch         => 7
  | .endpointQueueEmpty            => 8
  | .asidNotBound                  => 9
  | .vspaceRootInvalid             => 10
  | .mappingConflict               => 11
  | .translationFault              => 12
  | .flowDenied                    => 13
  | .declassificationDenied        => 14
  | .alreadyWaiting                => 15
  | .cyclicDependency              => 16
  | .notImplemented                => 17
  | .targetSlotOccupied            => 18
  | .replyCapInvalid               => 19
  | .untypedRegionExhausted        => 20
  | .untypedTypeMismatch           => 21
  | .untypedDeviceRestriction      => 22
  | .untypedAllocSizeTooSmall      => 23
  | .childIdSelfOverwrite          => 24
  | .childIdCollision              => 25
  | .addressOutOfBounds            => 26
  | .ipcMessageTooLarge            => 27
  | .ipcMessageTooManyCaps         => 28
  | .backingObjectMissing          => 29
  | .invalidRegister               => 30
  | .invalidSyscallNumber          => 31
  | .invalidMessageInfo            => 32
  | .invalidTypeTag                => 33
  | .resourceExhausted             => 34
  | .invalidCapPtr                 => 35
  | .objectStoreCapacityExceeded   => 36
  | .allocationMisaligned          => 37
  | .revocationRequired            => 38
  | .invalidArgument               => 39
  | .mmioUnaligned                 => 40
  | .invalidSyscallArgument        => 41
  | .ipcTimeout                    => 42
  | .alignmentError                => 43
  | .vmFault                       => 44
  | .userException                 => 45
  | .hardwareFault                 => 46
  | .notSupported                  => 47
  | .invalidIrq                    => 48
  | .invalidObjectType             => 49
  | .nullCapability                => 50
  | .partialResolution             => 51
  | .missingSchedContext           => 52
  | .threadOnDifferentCore         => 53
  | .auditLogCapacityExceeded      => 54
  | .auditFieldTooLarge            => 55
  | .declassificationDeniedAtReceiver => 56

/-- The inverse the tree never had: `Platform.FFI.KernelError.toUInt32` is
one-directional, and the Rust side decodes with its own
`KernelError::from_u32`.  WS-RA's error-label carriage needs the Lean-side
round trip (RA.A.5).  Fail-closed: out-of-range discriminants map to
`none`, exactly as `from_u32` yields its `UnknownKernelError` sentinel. -/
def ofDiscriminant? : Nat → Option KernelError
  | 0  => some .invalidCapability
  | 1  => some .objectNotFound
  | 2  => some .illegalState
  | 3  => some .illegalAuthority
  | 4  => some .policyDenied
  | 5  => some .dependencyViolation
  | 6  => some .schedulerInvariantViolation
  | 7  => some .endpointStateMismatch
  | 8  => some .endpointQueueEmpty
  | 9  => some .asidNotBound
  | 10 => some .vspaceRootInvalid
  | 11 => some .mappingConflict
  | 12 => some .translationFault
  | 13 => some .flowDenied
  | 14 => some .declassificationDenied
  | 15 => some .alreadyWaiting
  | 16 => some .cyclicDependency
  | 17 => some .notImplemented
  | 18 => some .targetSlotOccupied
  | 19 => some .replyCapInvalid
  | 20 => some .untypedRegionExhausted
  | 21 => some .untypedTypeMismatch
  | 22 => some .untypedDeviceRestriction
  | 23 => some .untypedAllocSizeTooSmall
  | 24 => some .childIdSelfOverwrite
  | 25 => some .childIdCollision
  | 26 => some .addressOutOfBounds
  | 27 => some .ipcMessageTooLarge
  | 28 => some .ipcMessageTooManyCaps
  | 29 => some .backingObjectMissing
  | 30 => some .invalidRegister
  | 31 => some .invalidSyscallNumber
  | 32 => some .invalidMessageInfo
  | 33 => some .invalidTypeTag
  | 34 => some .resourceExhausted
  | 35 => some .invalidCapPtr
  | 36 => some .objectStoreCapacityExceeded
  | 37 => some .allocationMisaligned
  | 38 => some .revocationRequired
  | 39 => some .invalidArgument
  | 40 => some .mmioUnaligned
  | 41 => some .invalidSyscallArgument
  | 42 => some .ipcTimeout
  | 43 => some .alignmentError
  | 44 => some .vmFault
  | 45 => some .userException
  | 46 => some .hardwareFault
  | 47 => some .notSupported
  | 48 => some .invalidIrq
  | 49 => some .invalidObjectType
  | 50 => some .nullCapability
  | 51 => some .partialResolution
  | 52 => some .missingSchedContext
  | 53 => some .threadOnDifferentCore
  | 54 => some .auditLogCapacityExceeded
  | 55 => some .auditFieldTooLarge
  | 56 => some .declassificationDeniedAtReceiver
  | _  => none

/-- The discriminant map is a section of its inverse: every `KernelError`
survives the numeric round trip.  With `toDiscriminant_lt` this pins the
map as a bijection onto `0..56`. -/
theorem ofDiscriminant?_toDiscriminant (e : KernelError) :
    ofDiscriminant? (toDiscriminant e) = some e := by
  cases e <;> rfl

/-- Every discriminant is inside the 57-entry table. -/
theorem toDiscriminant_lt (e : KernelError) : toDiscriminant e < 57 := by
  cases e <;> decide

/-- The other direction of the round trip, over the whole in-range domain:
below 57 the inverse hits and maps back to the same discriminant; 57 itself
(the first out-of-range value) is rejected. -/
theorem toDiscriminant_ofDiscriminant? :
    (∀ n, n < 57 → ((ofDiscriminant? n).map toDiscriminant) = some n) ∧
      ofDiscriminant? 57 = none := by
  constructor
  · decide
  · rfl

end SeLe4n.Model.KernelError

namespace SeLe4n.Kernel.Architecture

open SeLe4n.Model

-- ============================================================================
-- §1  ReturnShape — what each syscall puts in the return frame (RA.A.1)
-- ============================================================================

/-- The four return shapes (plan §3.4).  Deliberately **no `slot` shape** —
`cspaceMint` / `cspaceCopy` and the retype family select their destination
slot in their arguments, so no syscall returns one, and a shape with no
inhabiting syscall would be a hand-maintained fiction.  `message` carries no
static arity: a receive's length is dynamic (0..4 inline) and rides the
returned `MessageInfo` where seL4 puts it. -/
inductive ReturnShape where
  /-- `x0 = 0`, no message — 26 of the 31 syscalls. -/
  | unit
  /-- `x0` = full-width badge, no message registers (`.notificationWait`). -/
  | badge
  /-- `x0` = a queried scalar (`.serviceQuery`; SM9.A's audit reads join
  here).  Distinct from `.badge` because the Rust conformance layer types
  them differently (`Badge` vs `u64`), not because the frames differ. -/
  | word
  /-- `x0` = badge, `x1` = `MessageInfo`, `x2`-`x5` = message registers
  (`.receive`, `.call`, `.replyRecv`). -/
  | message
  deriving Repr, DecidableEq, Inhabited

-- ============================================================================
-- §2  syscallReturnShape — a total function, not a list (RA.A.2)
-- ============================================================================

/-- What each syscall returns — **total over `SyscallId` with no wildcard**,
so a new syscall is a missing case at elaboration rather than a silent
omission (plan §3.4; the lesson the SM9 plan learned three times:
`ReadableStructure`, `ContentFlowSite`, `declassificationSyscalls`).

`.call`'s `.message` classifies the frame its *reply* delivers: a successful
call always leaves the caller `blockedOnReply` (plan §3.5), so the frame is
staged by `endpointReplyOnCore` and delivered at the context restore, never
composed at the call's own boundary. -/
def syscallReturnShape : SyscallId → ReturnShape
  | .send                  => .unit
  | .receive               => .message
  | .call                  => .message
  | .reply                 => .unit
  | .cspaceMint            => .unit
  | .cspaceCopy            => .unit
  | .cspaceMove            => .unit
  | .cspaceDelete          => .unit
  | .lifecycleRetype       => .unit
  | .vspaceMap             => .unit
  | .vspaceUnmap           => .unit
  | .serviceRegister       => .unit
  | .serviceRevoke         => .unit
  | .serviceQuery          => .word
  | .notificationSignal    => .unit
  | .notificationWait      => .badge
  | .replyRecv             => .message
  | .schedContextConfigure => .unit
  | .schedContextBind      => .unit
  | .schedContextUnbind    => .unit
  | .tcbSuspend            => .unit
  | .tcbResume             => .unit
  | .tcbSetPriority        => .unit
  | .tcbSetMCPriority      => .unit
  | .tcbSetIPCBuffer       => .unit
  | .tcbSetAffinity        => .unit
  | .tcbBindNotification   => .unit
  | .tcbUnbindNotification => .unit
  | .mintReplyCap          => .unit
  | .vspaceUnifyInstruction => .unit
  | .declassify            => .unit
  -- WS-SM SM9.A.10: the audit reads are the second and third `.word` syscalls.
  -- `.word` rather than `.badge` for the reason the shape exists: the Rust
  -- conformance layer types a badge and a queried scalar differently, and an
  -- audit word is a scalar the kernel computed, not a badge a sender chose.
  | .auditRead             => .word
  | .auditDrain            => .word
  -- WS-SM SM9.C.8: a declassifying signal returns nothing, exactly like the
  -- ordinary `.notificationSignal` it wraps — the badge it moves is delivered
  -- to the *receiver*, not returned to the signaller, so there is no value at
  -- this boundary to shape.
  | .declassifySignal      => .unit

/-- Totality anchor (RA.A.2).  The *mechanism* is the definition itself —
an exhaustive match with no wildcard, so elaboration rejects a tree where a
new `SyscallId` variant lacks a shape.  The theorem is the named surface
anchor for that fact. -/
theorem syscallReturnShape_total (sid : SyscallId) :
    ∃ shape, syscallReturnShape sid = shape :=
  ⟨_, rfl⟩

/-- The value-returning surface, pinned by enumeration over the ABI's own
`SyscallId.all` (plan §1.3): seven syscalls return a value — the five WS-RA
classified, plus WS-SM SM9.A's two audit reads. -/
theorem syscallReturnShape_value_returning :
    SyscallId.all.filter (fun sid => syscallReturnShape sid != .unit) =
      [.receive, .call, .serviceQuery, .notificationWait, .replyRecv,
       .auditRead, .auditDrain] := by
  decide

/-- The refuted design, kept refuted (plan §3.4): a hand-maintained list of
value-returning syscalls plus a "everything listed has a shape" gate stays
satisfied by a list that misses a value-returning syscall — membership
cannot force a new member to join.  Witness: `[.receive]` passes the gate
while `.call` is value-returning and absent. -/
theorem returnShape_list_gate_insufficient :
    ∃ l : List SyscallId,
      (∀ sid ∈ l, syscallReturnShape sid ≠ .unit) ∧
      ∃ sid, syscallReturnShape sid ≠ .unit ∧ sid ∉ l := by
  exact ⟨[.receive], by decide, .call, by decide, by decide⟩

-- ============================================================================
-- §3  SyscallReturnFrame — the six-register result (RA.A.3)
-- ============================================================================

/-- The six registers a syscall returns, in the §3.1 layout.  All-zero by
default, which is exactly the `Unit`-syscall success frame: `x0 = 0` (no
value) and `x1 = 0`, which decodes as `MessageInfo {length 0, extraCaps 0,
label 0}` — label `0` meaning success. -/
structure SyscallReturnFrame where
  x0 : UInt64 := 0
  x1 : UInt64 := 0
  x2 : UInt64 := 0
  x3 : UInt64 := 0
  x4 : UInt64 := 0
  x5 : UInt64 := 0
  deriving Repr, DecidableEq, Inhabited

namespace SyscallReturnFrame

/-- The `Unit`-syscall success frame. -/
def zero : SyscallReturnFrame := {}

/-- Encode a frame as the raw register array in register order — the shape
the trap layer writes back and the conformance vectors compare. -/
def toRegs (f : SyscallReturnFrame) : Array UInt64 :=
  #[f.x0, f.x1, f.x2, f.x3, f.x4, f.x5]

/-- Decode a raw register array (missing entries read as zero, matching a
zero-initialised trap frame). -/
def ofRegs (a : Array UInt64) : SyscallReturnFrame :=
  { x0 := a[0]?.getD 0, x1 := a[1]?.getD 0, x2 := a[2]?.getD 0,
    x3 := a[3]?.getD 0, x4 := a[4]?.getD 0, x5 := a[5]?.getD 0 }

/-- RA.A.4 — the round trip is lossless at full 64-bit width in every
register.  Under the retired bit-63 protocol this was false for `x0`
(`encodeOk` masked bit 63; `bit63Encoding_not_injective_on_badges`); the
separation of the value and status channels is what makes it provable. -/
theorem decodeReturnFrame_encodeReturnFrame (f : SyscallReturnFrame) :
    ofRegs (toRegs f) = f := rfl

/-- The unit frame is all zeroes, register for register. -/
theorem returnFrame_unit_is_zero :
    zero.toRegs = #[0, 0, 0, 0, 0, 0] := rfl

end SyscallReturnFrame

-- ============================================================================
-- §4  Message-frame synthesis (RA.A.3) — the single IpcMessage → frame place
-- ============================================================================

/-- The `MessageInfo` a delivered message returns in `x1`.  `IpcMessage`
carries no `MessageInfo` (it is discarded at decode time), so the return
word is synthesized — here, once, for every delivery site: `length` is the
inline window actually delivered in `x2`-`x5`, `extraCaps` the number of
capabilities **actually installed** in the receiver's CSpace, clamped to
the protocol bound, `label` `0` (success).

**`installedCaps` is the transfer summary's `installedCount`, never the
requested `msg.caps.size`** (PR #866 round-2 review): `ipcUnwrapCaps`
succeeds with zero installs when the endpoint lacks `Grant` or the
receiver's CNode has no free slot, and the delivered message's `caps`
array keeps the *requested* caps either way — so a count read off the
message tells the receiver capabilities arrived when none did, and it
would interpret whatever its receive slots already held as freshly
delivered authority.  The parameter is deliberately **not defaulted**: a
site that cannot name its installed count has no business synthesizing a
message frame.  Arms whose path runs no unwrap at all (the receive legs
— tracked debt, see the plan — the reply delivery, and badge-only
notification wakes) pass `0`, the honest count for a path that installs
nothing. -/
def returnMessageInfo (msg : IpcMessage) (installedCaps : Nat) : MessageInfo :=
  { length    := min msg.registers.size 4
    extraCaps := min installedCaps Model.maxExtraCaps
    label     := min msg.label MessageInfo.maxLabel }

/-- The §3.7 window bound, stated: the returned length never exceeds the
four inline message registers. -/
theorem returnFrame_message_window (msg : IpcMessage) (installedCaps : Nat) :
    (returnMessageInfo msg installedCaps).length ≤ 4 :=
  Nat.min_le_right _ _

/-- The synthesized word is well-formed for the 20-bit-label encoding:
length ≤ 120, extraCaps ≤ 3, label ≤ 2^20 − 1. -/
theorem returnMessageInfo_wellFormed (msg : IpcMessage) (installedCaps : Nat) :
    (returnMessageInfo msg installedCaps).wellFormed := by
  refine ⟨Nat.le_trans (Nat.min_le_right _ _) (by decide), ?_, ?_⟩
  · exact Nat.min_le_right _ _
  · exact Nat.min_le_right _ _

/-- WS-RR RR4.4: the delivered label is the message's own whenever it is
in range — the clamp above is the fail-closed guard for an out-of-range
label, never a rewrite of a real one.  Every kernel-emitted label satisfies
the hypothesis (`Architecture.encodeFault_messageInfo_wellFormed` for a fault
message; `MessageInfo.decode_wellFormed` for a user send), so on every live
path this reads as the identity. -/
@[simp] theorem returnMessageInfo_label_of_le (msg : IpcMessage) (installedCaps : Nat)
    (h : msg.label ≤ MessageInfo.maxLabel) :
    (returnMessageInfo msg installedCaps).label = msg.label :=
  Nat.min_eq_left h

/-- WS-RR RR4.4: a message carrying no label (the default, and every message
built before RR4) delivers the `0` label the pre-RR4 synthesis hard-coded —
the backward-compatibility bridge. -/
@[simp] theorem returnMessageInfo_label_zero (msg : IpcMessage) (installedCaps : Nat)
    (h : msg.label = 0) : (returnMessageInfo msg installedCaps).label = 0 := by
  simp [returnMessageInfo, h]

/-- The honesty bound (PR #866 round-2): the returned `extraCaps` never
exceeds the installed count — in particular, a path that installed
nothing reports zero, whatever the delivered message's `caps` array
still carries. -/
theorem returnMessageInfo_extraCaps_le_installed
    (msg : IpcMessage) (installedCaps : Nat) :
    (returnMessageInfo msg installedCaps).extraCaps ≤ installedCaps :=
  Nat.min_le_left _ _

@[simp] theorem returnMessageInfo_extraCaps_zero (msg : IpcMessage) :
    (returnMessageInfo msg 0).extraCaps = 0 := rfl

/-- A delivered `IpcMessage` as a return frame — badge to `x0`, synthesized
`MessageInfo` to `x1`, the inline register window to `x2`-`x5` (RA.A.3).
The **single** place a message becomes a frame, used by every RA.B.5b
staging site, so the synthesis cannot drift between sites.
`installedCaps` per `returnMessageInfo`: the count of caps actually
installed by this delivery's transfer, `0` for paths that run none. -/
def returnFrameOfMessage (msg : IpcMessage) (installedCaps : Nat) :
    SyscallReturnFrame :=
  { x0 := ((msg.badge.map Badge.val).getD 0).toUInt64
    x1 := (returnMessageInfo msg installedCaps).encode.toUInt64
    x2 := ((msg.registers[0]?.map RegValue.val).getD 0).toUInt64
    x3 := ((msg.registers[1]?.map RegValue.val).getD 0).toUInt64
    x4 := ((msg.registers[2]?.map RegValue.val).getD 0).toUInt64
    x5 := ((msg.registers[3]?.map RegValue.val).getD 0).toUInt64 }

/-- A badge-only frame — `.notificationWait`'s shape: the badge in `x0`,
success `MessageInfo` (all-zero word) in `x1`, no message registers. -/
def returnFrameOfBadge (b : Badge) : SyscallReturnFrame :=
  { x0 := b.val.toUInt64 }

-- ============================================================================
-- §4b  Staging a frame into a register context (RA.B.1's pure core)
-- ============================================================================

/-- Stage a return frame into a register file: `x0`-`x5` overwritten with
the frame, every other register (including `x7`, `pc`, `sp`) untouched.
The dual of the argument spill's register writes. -/
def _root_.SeLe4n.RegisterFile.stageReturnFrame
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) : SeLe4n.RegisterFile :=
  let rf := SeLe4n.writeReg rf ⟨0⟩ ⟨f.x0.toNat⟩
  let rf := SeLe4n.writeReg rf ⟨1⟩ ⟨f.x1.toNat⟩
  let rf := SeLe4n.writeReg rf ⟨2⟩ ⟨f.x2.toNat⟩
  let rf := SeLe4n.writeReg rf ⟨3⟩ ⟨f.x3.toNat⟩
  let rf := SeLe4n.writeReg rf ⟨4⟩ ⟨f.x4.toNat⟩
  SeLe4n.writeReg rf ⟨5⟩ ⟨f.x5.toNat⟩

/-- Staging touches `gpr` only — `pc` and `sp` survive. -/
@[simp] theorem _root_.SeLe4n.RegisterFile.stageReturnFrame_pc
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) :
    (rf.stageReturnFrame f).pc = rf.pc := rfl

@[simp] theorem _root_.SeLe4n.RegisterFile.stageReturnFrame_sp
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) :
    (rf.stageReturnFrame f).sp = rf.sp := rfl

/-- Registers outside the frame window are untouched — in particular `x7`
(the staged syscall number) and the callee-saved range. -/
theorem _root_.SeLe4n.RegisterFile.stageReturnFrame_gpr_high
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) (r : SeLe4n.RegName)
    (h : 5 < r.val) : (rf.stageReturnFrame f).gpr r = rf.gpr r := by
  unfold SeLe4n.RegisterFile.stageReturnFrame SeLe4n.writeReg
  simp only
  have h0 : r.val ≠ 0 := by omega
  have h1 : r.val ≠ 1 := by omega
  have h2 : r.val ≠ 2 := by omega
  have h3 : r.val ≠ 3 := by omega
  have h4 : r.val ≠ 4 := by omega
  have h5 : r.val ≠ 5 := by omega
  simp [h0, h1, h2, h3, h4, h5]

/-- The staged registers read back as the frame, register for register —
the pure core of RA.B.2's `readReturnFrame_writeReturnFrame` round trip. -/
theorem _root_.SeLe4n.RegisterFile.stageReturnFrame_reads_back
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) :
    (rf.stageReturnFrame f).gpr ⟨0⟩ = ⟨f.x0.toNat⟩ ∧
    (rf.stageReturnFrame f).gpr ⟨1⟩ = ⟨f.x1.toNat⟩ ∧
    (rf.stageReturnFrame f).gpr ⟨2⟩ = ⟨f.x2.toNat⟩ ∧
    (rf.stageReturnFrame f).gpr ⟨3⟩ = ⟨f.x3.toNat⟩ ∧
    (rf.stageReturnFrame f).gpr ⟨4⟩ = ⟨f.x4.toNat⟩ ∧
    (rf.stageReturnFrame f).gpr ⟨5⟩ = ⟨f.x5.toNat⟩ := by
  unfold SeLe4n.RegisterFile.stageReturnFrame SeLe4n.writeReg
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Stage a return frame into a TCB's saved register context — the single
record update every staging site goes through (`registerContext` moves,
all 25 other TCB fields definitionally unchanged). -/
def _root_.SeLe4n.Model.TCB.withReturnFrame (tcb : TCB) (f : SyscallReturnFrame) : TCB :=
  { tcb with registerContext := tcb.registerContext.stageReturnFrame f }

/-- The fields the IPC and scheduler invariants read, pinned unchanged.
Each is `rfl` — the update touches `registerContext` only — but naming
them keeps downstream `simp` sets one identifier long. -/
@[simp] theorem _root_.SeLe4n.Model.TCB.withReturnFrame_ipcState
    (tcb : TCB) (f : SyscallReturnFrame) :
    (tcb.withReturnFrame f).ipcState = tcb.ipcState := rfl

@[simp] theorem _root_.SeLe4n.Model.TCB.withReturnFrame_tid
    (tcb : TCB) (f : SyscallReturnFrame) :
    (tcb.withReturnFrame f).tid = tcb.tid := rfl

@[simp] theorem _root_.SeLe4n.Model.TCB.withReturnFrame_pendingMessage
    (tcb : TCB) (f : SyscallReturnFrame) :
    (tcb.withReturnFrame f).pendingMessage = tcb.pendingMessage := rfl

@[simp] theorem _root_.SeLe4n.Model.TCB.withReturnFrame_registerContext
    (tcb : TCB) (f : SyscallReturnFrame) :
    (tcb.withReturnFrame f).registerContext
      = tcb.registerContext.stageReturnFrame f := rfl

-- ============================================================================
-- §4c  Staging into and reading out of a SystemState (RA.B.1, RA.B.2)
-- ============================================================================

/-- WS-RA RA.B.1: stage a syscall return frame into a thread's saved
register context — the dual of `Platform.FFI.writeFfiRegistersToTcb`, low
enough in the import graph that the dispatch arms can call it.

Writes `x0`-`x5` of `tcb.registerContext` from the frame and touches
nothing else: not `x7`, not `pc`/`sp`, no other TCB field
(`TCB.withReturnFrame`), and **deliberately not `machine.regs` /
`regsOnCore`** — that mirror is already stale for x6, x8..x30 after the
argument spill (the `ContextRestoreSeam` note), the SM10.1 outgoing-frame
save is the registered closure for the whole staleness class, and keeping
the write out of `machine` is part of what makes the RA.B.10 projection
preservation hold for every observer.

Total: a non-TCB target returns the state unchanged, mirroring
`writeFfiRegistersToTcb`'s posture (the caller surfaces the error). -/
def writeReturnFrameToTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      { st with objects := st.objects.insert tid.toObjId (.tcb (tcb.withReturnFrame frame)) }
  | none => st

/-- WS-RA RA.B.2: read the staged return frame back out of a thread's
register context — `Platform.FFI.readReturnValue` generalised to the
`x0`-`x5` range (that function remains this one's `x0` projection).  A
non-TCB target reads as the zero frame, the same totality posture. -/
def readReturnFrame (st : SystemState) (tid : SeLe4n.ThreadId) :
    SyscallReturnFrame :=
  match st.getTcb? tid with
  | some tcb =>
      { x0 := (tcb.registerContext.gpr ⟨0⟩).val.toUInt64
        x1 := (tcb.registerContext.gpr ⟨1⟩).val.toUInt64
        x2 := (tcb.registerContext.gpr ⟨2⟩).val.toUInt64
        x3 := (tcb.registerContext.gpr ⟨3⟩).val.toUInt64
        x4 := (tcb.registerContext.gpr ⟨4⟩).val.toUInt64
        x5 := (tcb.registerContext.gpr ⟨5⟩).val.toUInt64 }
  | none => .zero

/-- WS-RA RA.B.2: the staging round trip — what `writeReturnFrameToTcb`
stages, `readReturnFrame` reads back exactly, at full 64-bit width in
every register (`RegValue` truncates nothing below `2^64`). -/
theorem readReturnFrame_writeReturnFrame
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt) :
    readReturnFrame (writeReturnFrameToTcb st tid frame) tid = frame := by
  unfold writeReturnFrameToTcb readReturnFrame
  rw [hTcb]
  simp only
  unfold SystemState.getTcb?
  rw [RHTable_getElem?_eq_get?,
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId
        (KernelObject.tcb (tcb.withReturnFrame frame)) hObjInv]
  have hReads := (tcb.registerContext).stageReturnFrame_reads_back frame
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hReads
  simp only [SeLe4n.Model.TCB.withReturnFrame_registerContext, h0, h1, h2, h3, h4, h5]
  cases frame
  simp [UInt64.ofNat_toNat]

/-- WS-RA RA.B.1 frame lemma: objects off the target are untouched. -/
theorem writeReturnFrameToTcb_objects_ne
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hObjInv : st.objects.invExt) :
    (writeReturnFrameToTcb st tid frame).objects[oid]? = st.objects[oid]? := by
  have hNe' : ¬(tid.toObjId == oid) = true := by
    simp only [beq_iff_eq]
    exact fun h => hNe h.symm
  unfold writeReturnFrameToTcb
  cases h : st.getTcb? tid with
  | none => rfl
  | some tcb =>
    exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne
        st.objects tid.toObjId oid _ hNe' hObjInv

/-- WS-RA RA.B.1 frame lemma: the scheduler is untouched. -/
theorem writeReturnFrameToTcb_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) :
    (writeReturnFrameToTcb st tid frame).scheduler = st.scheduler := by
  unfold writeReturnFrameToTcb
  cases h : st.getTcb? tid with
  | none => rfl
  | some tcb => rfl

/-- WS-RA RA.B.1 frame lemma: the machine is untouched — the staging
writes the TCB's saved context only, never the machine mirror. -/
theorem writeReturnFrameToTcb_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) :
    (writeReturnFrameToTcb st tid frame).machine = st.machine := by
  unfold writeReturnFrameToTcb
  cases h : st.getTcb? tid with
  | none => rfl
  | some tcb => rfl

/-- WS-SM SM9.C.8 frame lemma: the declassification audit trail is untouched.

Needed because a *dispatch arm* that stages a return frame after a
declassifying transition must be shown not to grow the trail — the transition's
own trail statement covers the transition only, and an arm that appended in its
post-processing would falsify the arm-level property while leaving the
transition's theorem true.  The staging writes one TCB, so the trail rides the
`with` reconstruction definitionally. -/
theorem writeReturnFrameToTcb_declassificationAuditLog_eq
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) :
    (writeReturnFrameToTcb st tid frame).declassificationAuditLog =
      st.declassificationAuditLog := by
  unfold writeReturnFrameToTcb
  cases h : st.getTcb? tid with
  | none => rfl
  | some tcb => rfl

/-- WS-RA RA.B.1: staging a frame for a target that is not a TCB is the
identity — the totality witness, mirroring
`writeFfiRegistersToTcb_id_when_not_tcb`. -/
theorem writeReturnFrameToTcb_id_when_not_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame)
    (hNot : st.getTcb? tid = none) :
    writeReturnFrameToTcb st tid frame = st := by
  unfold writeReturnFrameToTcb
  rw [hNot]

/-- WS-RA RA.B.6: stage the message a completed receive-shaped syscall
delivered into the **caller's own** `pendingMessage` — the arm-level
staging for the non-blocking consume paths (`.receive` / `.replyRecv`).

Guarded on the caller's post-state being `.ready`: a caller that blocked
has no fresh delivery (its `pendingMessage` may hold a stale message from
an earlier exchange), stages nothing here, and its frame is owed by the
unblocking transition (RA.B.5b) with delivery at the SM10.1 context
restore.  A `.ready` caller with no `pendingMessage` (a zero-length
delivery is still `some` with an empty register array) stages nothing —
the boundary's shape-driven read then sees whatever the arm staged, so
receive arms pair this with the shape theorem rather than relying on
incidental register content.

`installedCaps` (PR #866 round-2 review) is the count of capabilities the
delivering transfer **actually installed** — the arm's transfer-summary
`installedCount`, or `0` on a path that runs no unwrap.  It is never the
delivered message's own `caps.size`, which records what the sender
*requested*. -/
def stageDeliveredMessage (st : SystemState) (tid : SeLe4n.ThreadId)
    (installedCaps : Nat) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      if tcb.ipcState = .ready then
        match tcb.pendingMessage with
        | some msg =>
            writeReturnFrameToTcb st tid (returnFrameOfMessage msg installedCaps)
        | none => st
      else st
  | none => st

/-- RA.B.5b frame lemma: delivery staging never touches the scheduler —
every arm is either `writeReturnFrameToTcb` (whose `_scheduler_eq` this
lifts) or the identity. -/
theorem stageDeliveredMessage_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (installedCaps : Nat) :
    (stageDeliveredMessage st tid installedCaps).scheduler = st.scheduler := by
  unfold stageDeliveredMessage
  cases st.getTcb? tid with
  | none => rfl
  | some tcb =>
      by_cases hReady : tcb.ipcState = .ready
      · simp only [hReady, if_pos]
        cases tcb.pendingMessage with
        | none => rfl
        | some msg => exact writeReturnFrameToTcb_scheduler_eq st tid _
      · simp [hReady]

/-- RA.B.5b frame lemma: delivery staging never touches the machine — the
staging writes the TCB's saved context only, never the machine mirror. -/
theorem stageDeliveredMessage_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (installedCaps : Nat) :
    (stageDeliveredMessage st tid installedCaps).machine = st.machine := by
  unfold stageDeliveredMessage
  cases st.getTcb? tid with
  | none => rfl
  | some tcb =>
      by_cases hReady : tcb.ipcState = .ready
      · simp only [hReady, if_pos]
        cases tcb.pendingMessage with
        | none => rfl
        | some msg => exact writeReturnFrameToTcb_machine_eq st tid _
      · simp [hReady]

/-- WS-SM SM9.C.8 frame lemma: delivery staging never touches the
declassification audit trail (the lift of
`writeReturnFrameToTcb_declassificationAuditLog_eq`). -/
theorem stageDeliveredMessage_declassificationAuditLog_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (installedCaps : Nat) :
    (stageDeliveredMessage st tid installedCaps).declassificationAuditLog =
      st.declassificationAuditLog := by
  unfold stageDeliveredMessage
  cases st.getTcb? tid with
  | none => rfl
  | some tcb =>
      by_cases hReady : tcb.ipcState = .ready
      · simp only [hReady, if_pos]
        cases tcb.pendingMessage with
        | none => rfl
        | some msg => exact writeReturnFrameToTcb_declassificationAuditLog_eq st tid _
      · simp [hReady]

/-- A blocked caller stages nothing — `stageDeliveredMessage` is the
identity whenever the caller's post-state is not `.ready`. -/
theorem stageDeliveredMessage_id_when_blocked
    (st : SystemState) (tid : SeLe4n.ThreadId) (installedCaps : Nat) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    (hBlocked : tcb.ipcState ≠ .ready) :
    stageDeliveredMessage st tid installedCaps = st := by
  unfold stageDeliveredMessage
  rw [hTcb]
  simp [hBlocked]

/-- A queried-word frame — `.serviceQuery`'s shape (and SM9.A's audit
reads): the word in `x0`, success `x1`, no message registers. -/
def returnFrameOfWord (w : UInt64) : SyscallReturnFrame :=
  { x0 := w }

-- ============================================================================
-- §4d  Staging for a woken counterparty (RA.B.5b)
-- ============================================================================
--
-- The blocked-waiter half of §3.5: when an unblocking syscall wakes a
-- counterparty that was blocked in ITS OWN syscall, the woken thread's
-- return frame must be staged now — its own boundary crossing ended in
-- `.blocks` with no frame written, and the SM10.1 context restore delivers
-- whatever its `registerContext` holds.  Every wake in the tree delivers
-- through one of two shapes, and each gets a guarded Option-lifted stager
-- so the dispatch arms compose them in one call:
--
-- * a **payload wake** — the wake wrote `.ready` + `pendingMessage := msg`
--   (`storeTcbIpcStateAndMessage` / `storeTcbReceiveComplete`): the frame
--   is `returnFrameOfMessage msg`, which is `stageDeliveredMessage` —
--   `stageWokenDelivery` lifts it over the arm's pre-resolved counterparty;
-- * a **completion wake** — a plain sender whose send finished at a
--   rendezvous was woken `.ready` with its `pendingMessage` *consumed*
--   (`none`): its syscall returns `Unit`, so the frame is the zero frame —
--   `stageWokenSendCompletion`, whose guard (`.ready` AND no pending
--   delivery) keeps it inert on a consumed `Call` sender (which lands
--   `.blockedOnReply` and is owed its frame by the reply path) and on a
--   payload wake (owed `returnFrameOfMessage` instead).

/-- WS-RA RA.B.5b: stage the delivered message of an optionally-woken
counterparty — `stageDeliveredMessage` lifted over the dispatch arm's
pre-resolved wake target (`none` when no counterparty was blocked).  The
inner `.ready` + `pendingMessage` guards make this the identity whenever
the wake did not actually happen (the transition errored short of the
wake, the counterparty vanished, or it is still blocked).
`installedCaps` per `stageDeliveredMessage` (PR #866 round-2): the
delivering transfer's `installedCount`, `0` on unwrap-free paths. -/
def stageWokenDelivery (st : SystemState) (woken? : Option SeLe4n.ThreadId)
    (installedCaps : Nat) : SystemState :=
  match woken? with
  | some tid => stageDeliveredMessage st tid installedCaps
  | none => st

@[simp] theorem stageWokenDelivery_none (st : SystemState)
    (installedCaps : Nat) :
    stageWokenDelivery st none installedCaps = st := rfl

@[simp] theorem stageWokenDelivery_some (st : SystemState)
    (tid : SeLe4n.ThreadId) (installedCaps : Nat) :
    stageWokenDelivery st (some tid) installedCaps
      = stageDeliveredMessage st tid installedCaps := rfl

/-- WS-RA RA.B.5b: stage the **unit success frame** for a woken plain
sender whose send completed at a rendezvous.  Guarded on the
counterparty's post-state being `.ready` with **no** pending delivery: a
consumed `Call` sender lands `.blockedOnReply` (frame owed by the reply
path), and a `.ready` thread WITH a pending delivery is a payload wake
owed `returnFrameOfMessage` by `stageWokenDelivery` instead — staging
zero there would clobber a real value. -/
def stageWokenSendCompletion (st : SystemState)
    (woken? : Option SeLe4n.ThreadId) : SystemState :=
  match woken? with
  | none => st
  | some tid =>
      match st.getTcb? tid with
      | some tcb =>
          if tcb.ipcState = .ready ∧ tcb.pendingMessage = none then
            writeReturnFrameToTcb st tid .zero
          else st
      | none => st

@[simp] theorem stageWokenSendCompletion_none (st : SystemState) :
    stageWokenSendCompletion st none = st := rfl

/-- The completion stager is inert on a counterparty the rendezvous did
not complete — a consumed `Call` sender (`.blockedOnReply`), a still-queued
sender, or any non-`.ready` post-state. -/
theorem stageWokenSendCompletion_id_when_not_ready
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    (hNotReady : tcb.ipcState ≠ .ready) :
    stageWokenSendCompletion st (some tid) = st := by
  simp only [stageWokenSendCompletion]
  rw [hTcb]
  simp [hNotReady]

/-- The completion stager is inert on a payload wake — a `.ready`
counterparty still holding a pending delivery is owed
`returnFrameOfMessage`, never the zero frame. -/
theorem stageWokenSendCompletion_id_when_pending
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) (msg : IpcMessage)
    (hTcb : st.getTcb? tid = some tcb)
    (hPending : tcb.pendingMessage = some msg) :
    stageWokenSendCompletion st (some tid) = st := by
  simp only [stageWokenSendCompletion]
  rw [hTcb]
  simp [hPending]

/-- The completion stager's positive arm: a genuinely completed sender
(`.ready`, delivery consumed) gets exactly the zero frame staged. -/
theorem stageWokenSendCompletion_stages_zero
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hConsumed : tcb.pendingMessage = none) :
    stageWokenSendCompletion st (some tid)
      = writeReturnFrameToTcb st tid .zero := by
  simp only [stageWokenSendCompletion]
  rw [hTcb]
  simp [hReady, hConsumed]

/-- RA.B.5b frame lemma: neither stager touches the scheduler. -/
theorem stageWokenDelivery_scheduler_eq (st : SystemState)
    (woken? : Option SeLe4n.ThreadId) (installedCaps : Nat) :
    (stageWokenDelivery st woken? installedCaps).scheduler = st.scheduler := by
  cases woken? with
  | none => rfl
  | some tid => exact stageDeliveredMessage_scheduler_eq st tid installedCaps

/-- RA.B.5b frame lemma: neither stager touches the machine. -/
theorem stageWokenDelivery_machine_eq (st : SystemState)
    (woken? : Option SeLe4n.ThreadId) (installedCaps : Nat) :
    (stageWokenDelivery st woken? installedCaps).machine = st.machine := by
  cases woken? with
  | none => rfl
  | some tid => exact stageDeliveredMessage_machine_eq st tid installedCaps

/-- WS-SM SM9.C.8 frame lemma: the delivery stager never touches the
declassification audit trail. -/
theorem stageWokenDelivery_declassificationAuditLog_eq (st : SystemState)
    (woken? : Option SeLe4n.ThreadId) (installedCaps : Nat) :
    (stageWokenDelivery st woken? installedCaps).declassificationAuditLog =
      st.declassificationAuditLog := by
  cases woken? with
  | none => rfl
  | some tid => exact stageDeliveredMessage_declassificationAuditLog_eq st tid installedCaps

/-- RA.B.5b frame lemma: the completion stager never touches the
scheduler. -/
theorem stageWokenSendCompletion_scheduler_eq (st : SystemState)
    (woken? : Option SeLe4n.ThreadId) :
    (stageWokenSendCompletion st woken?).scheduler = st.scheduler := by
  cases woken? with
  | none => rfl
  | some tid =>
      simp only [stageWokenSendCompletion]
      cases st.getTcb? tid with
      | none => rfl
      | some tcb =>
          by_cases hGuard : tcb.ipcState = .ready ∧ tcb.pendingMessage = none
          · simp only [hGuard]
            exact writeReturnFrameToTcb_scheduler_eq st tid _
          · simp [hGuard]

/-- RA.B.5b frame lemma: the completion stager never touches the
machine. -/
theorem stageWokenSendCompletion_machine_eq (st : SystemState)
    (woken? : Option SeLe4n.ThreadId) :
    (stageWokenSendCompletion st woken?).machine = st.machine := by
  cases woken? with
  | none => rfl
  | some tid =>
      simp only [stageWokenSendCompletion]
      cases st.getTcb? tid with
      | none => rfl
      | some tcb =>
          by_cases hGuard : tcb.ipcState = .ready ∧ tcb.pendingMessage = none
          · simp only [hGuard]
            exact writeReturnFrameToTcb_machine_eq st tid _
          · simp [hGuard]

/-- **WS-RA RA.B.5b — the plan-named theorem (§3.5, §8).**  A payload wake
leaves the woken waiter's frame staged: whenever a wake delivered `msg`
into a counterparty (post-state `.ready` with `pendingMessage = some msg`
— the `storeTcbIpcStateAndMessage`/`storeTcbReceiveComplete` shape every
wake in the tree produces), the staging step writes exactly
`returnFrameOfMessage msg` into its saved register context, and the
boundary read recovers it bit for bit.  Delivery is the SM10.1 context
restore's; what this pins is that the frame is *there* to deliver. -/
theorem blockedReturn_staged_in_waiter_frame
    (st : SystemState) (w : SeLe4n.ThreadId) (tcb : TCB) (msg : IpcMessage)
    (installedCaps : Nat)
    (hTcb : st.getTcb? w = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : st.objects.invExt) :
    readReturnFrame (stageWokenDelivery st (some w) installedCaps) w
      = returnFrameOfMessage msg installedCaps := by
  show readReturnFrame (stageDeliveredMessage st w installedCaps) w
    = returnFrameOfMessage msg installedCaps
  unfold stageDeliveredMessage
  rw [hTcb]
  simp only [hReady, hMsg]
  exact readReturnFrame_writeReturnFrame st w
    (returnFrameOfMessage msg installedCaps) tcb hTcb hObjInv

/-- WS-RA RA.B.5b — the completion dual: a woken plain sender's staged
frame is the zero frame (unit success), recovered by the boundary read. -/
theorem blockedUnitReturn_staged_in_sender_frame
    (st : SystemState) (s : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? s = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hConsumed : tcb.pendingMessage = none)
    (hObjInv : st.objects.invExt) :
    readReturnFrame (stageWokenSendCompletion st (some s)) s
      = SyscallReturnFrame.zero := by
  rw [stageWokenSendCompletion_stages_zero st s tcb hTcb hReady hConsumed]
  exact readReturnFrame_writeReturnFrame st s .zero tcb hTcb hObjInv

-- ============================================================================
-- §5  Error carriage on the x1 label (RA.A.5, RA.A.6)
-- ============================================================================

/-- The offset error label (plan §3.1): discriminant `d` rides as label
`d + 1`, and label `0` means success.  The offset is load-bearing —
discriminant `0` is `.invalidCapability`, and a label carrying it directly
would alias the first error with success. -/
def errorLabel (e : KernelError) : Nat :=
  e.toDiscriminant + 1

/-- Decode a label back to its error: `0` is success (`none`), `n + 1` is
discriminant `n`, unknown discriminants fail closed. -/
def ofErrorLabel? : Nat → Option KernelError
  | 0     => none
  | n + 1 => KernelError.ofDiscriminant? n

/-- §3.1's non-aliasing: no error's label is the success label. -/
theorem errorLabel_never_zero (e : KernelError) : errorLabel e ≠ 0 :=
  Nat.succ_ne_zero _

/-- The success label decodes as success. -/
theorem ofErrorLabel?_zero : ofErrorLabel? 0 = none := rfl

/-- RA.A.5 — every error survives the label round trip. -/
theorem errorLabel_roundtrip (e : KernelError) :
    ofErrorLabel? (errorLabel e) = some e :=
  KernelError.ofDiscriminant?_toDiscriminant e

/-- The decode side over the whole in-range domain: label `0` is success,
labels `1..57` hit their errors and re-encode to themselves, label `58`
(the first out-of-range value) is rejected — so label `0` decodes as
success and *only* label `0` does, on the entire inhabited label space. -/
theorem errorLabel_zero_iff_success :
    ofErrorLabel? 0 = none ∧
      (∀ n, n < 57 →
        ((ofErrorLabel? (n + 1)).map errorLabel) = some (n + 1)) ∧
      ofErrorLabel? 58 = none := by
  refine ⟨rfl, ?_, rfl⟩
  decide

/-- RA.A.6 — all 57 offset labels (1..57) fit the 20-bit `MessageInfo`
label field, so the error carriage never needs a wider register. -/
theorem kernelErrorFitsLabel (e : KernelError) :
    errorLabel e ≤ MessageInfo.maxLabel := by
  have h := KernelError.toDiscriminant_lt e
  unfold errorLabel MessageInfo.maxLabel
  omega

/-- The load-bearing negative for RA.A.6: an over-wide `x1` word is not
silently truncated — `MessageInfo.decode` fail-closes on any word whose
label bits exceed `maxLabel` (bits ≥ 29 set), so a corrupted status
register decodes as an explicit failure rather than a wrong error. -/
theorem overWideLabel_rejected :
    MessageInfo.decode ((MessageInfo.maxLabel + 1) <<< 9) = none := by
  decide

/-- The error frame the boundary returns on a failed syscall: `x0 = 0`,
the offset label in `x1`, no message registers.  Computed at the boundary,
**never staged into the TCB** — which is what keeps the error path
state-preserving (RA.B.4). -/
def errorFrame (e : KernelError) : SyscallReturnFrame :=
  { x1 := (MessageInfo.encode
      { length := 0, extraCaps := 0, label := errorLabel e }).toUInt64 }

/-- An error frame's `x1` decodes back to the `MessageInfo` that names the
error — the encode side is inside the decoder's fail-closed bounds.  Every
`errorLabel` is a concrete literal per variant, so the whole statement is
decided by evaluation, 55 cases at a time. -/
theorem errorFrame_x1_decodes (e : KernelError) :
    MessageInfo.decode (errorFrame e).x1.toNat =
      some { length := 0, extraCaps := 0, label := errorLabel e } := by
  cases e <;> decide

-- ============================================================================
-- §6  SyscallOutcome — returns or blocks (RA.A.4, plan §3.5)
-- ============================================================================

/-- What a syscall execution hands the FFI boundary: a frame to write back,
or the fact that the caller blocked and the frame will be staged by the
unblocking transition (delivered at the SM10.1 context restore).  Outcome
is decided from the caller's **post-state** — whether `.notificationWait`
blocks depends on `pendingBadge`, `.receive` on the sender queue, `.send`
on a waiting receiver — never from the syscall id alone. -/
inductive SyscallOutcome where
  | returns (frame : SyscallReturnFrame)
  | blocks
  deriving Repr, DecidableEq

namespace SyscallOutcome

/-- The outcome tag the `lean_syscall_dispatch_cross_core` export returns
(the frame itself crosses through the per-core mailbox — plan §3.3):
`0` = a frame was written, `1` = the caller blocked and no frame exists. -/
def tagWord : SyscallOutcome → UInt64
  | .returns _ => 0
  | .blocks    => 1

/-- The two tags are distinct — a blocked outcome cannot be mistaken for a
frame delivery at the boundary. -/
theorem tagWord_blocks_ne_returns (f : SyscallReturnFrame) :
    tagWord .blocks ≠ tagWord (.returns f) := by
  simp [tagWord]

/-- The mailbox frame for an outcome: a blocked caller's mailbox stays
zeroed (no return value exists for it — RA.C.9; its real frame is staged
by the unblocking arm and delivered by the SM10.1 context restore).
Until that seam flips, the hardware trap layer substitutes a fail-closed
poison frame for the premature resume (`blocked_resume_sentinel_regs` in
`svc_dispatch.rs`) — an interim HAL artifact, deliberately NOT part of
this model: the model stages real frames only. -/
def mailboxFrame : SyscallOutcome → SyscallReturnFrame
  | .returns f => f
  | .blocks    => .zero

end SyscallOutcome

/-- Does the caller's post-state IPC state mean the syscall **blocked**?
Everything except `.ready` is an IPC-blocked state; a descheduled but
IPC-`.ready` caller (a self-`.tcbSuspend`) still counts as returning, since
the unit frame is exactly what it should observe when later resumed
(plan §3.5).

**Exhaustive match, no wildcard** — the §3.4 discipline `ReturnShape`
established, applied here for the same reason: a wildcard would silently
classify a future `ThreadIpcState` constructor as "blocks", and a
returning caller misclassified as blocked gets NO staged frame — its
computed result is silently discarded.  (The trap layer poisons the
misclassified caller's frame with the fail-closed blocked-resume
sentinel, so the hardware failure mode is an unmistakable
`UnknownKernelError`, not the false success the caller's own spilled
`x0`/`x1` would decode as — but a fail-closed wrong answer is still a
wrong answer.)  A new constructor must decide its arm at elaboration. -/
def ipcStateBlocksReturn : ThreadIpcState → Bool
  | .ready                   => false
  | .blockedOnSend _         => true
  | .blockedOnReceive _      => true
  | .blockedOnNotification _ => true
  | .blockedOnReply _ _      => true
  | .blockedOnCall _         => true

@[simp] theorem ipcStateBlocksReturn_ready :
    ipcStateBlocksReturn .ready = false := rfl

/-- §3.3's shape-driven boundary read: a `.unit` syscall's frame is
**constructed**, never read from the staged registers — reading them back
would return the caller's own staged arguments, which is the §1.2 defect.
Value shapes read what the arm staged (`dispatchArm_matches_returnShape`
is what makes that read safe). -/
def frameForShape (shape : ReturnShape) (staged : SyscallReturnFrame) :
    SyscallReturnFrame :=
  match shape with
  | .unit => .zero
  | _     => staged

/-- The unit shape ignores the staged registers entirely — however corrupt
or stale they are, a `Unit`-returning syscall reports `x0 = 0` and a
success `x1`. -/
theorem frameForShape_unit (staged : SyscallReturnFrame) :
    frameForShape .unit staged = .zero := rfl

/-- Value shapes pass the staged frame through unchanged. -/
theorem frameForShape_value (shape : ReturnShape) (staged : SyscallReturnFrame)
    (h : shape ≠ .unit) : frameForShape shape staged = staged := by
  cases shape <;> simp_all [frameForShape]

-- ============================================================================
-- §6b  WS-RR RR4.16 — the fault-restart writeback
-- ============================================================================
--
-- A fault reply restarts the faulted thread, and on two of the four fault
-- kinds it installs registers the handler supplied (seL4's
-- `copyMRsFaultReply` over `fault_messages[MessageID_Syscall]` /
-- `[MessageID_Exception]`).  That is the *same* act as a syscall return
-- writeback — a frame of words staged into a thread's saved register
-- context — so it goes through the same mechanism rather than a second one:
-- `stageRestartFrame` is defined *as* `stageReturnFrame` plus the three
-- registers a restart reaches that a syscall return does not (`x6`/`x7`,
-- `lr`), and `pc`/`sp`.

/-- WS-RR RR4.16: the register state a fault reply restarts a thread with.

The union of seL4's two fault-reply register lists on AArch64:
`fault_messages[MessageID_Syscall] = {x0..x7, FaultIP, SP_EL0, x30, SPSR_EL1}`
and `[MessageID_Exception] = {FaultIP, SP_EL0, SPSR_EL1}`, minus `SPSR_EL1` —
the model's `RegisterFile` carries no PSTATE, and refusing the override is
the fail-closed direction (see `Model.FaultContext.spsr`). -/
structure FaultRestartFrame where
  /-- The instruction to restart at — seL4's `FaultIP`, installed as the
      thread's saved `pc`. -/
  pc : UInt64 := 0
  /-- The user stack pointer to restart with (`SP_EL0`). -/
  sp : UInt64 := 0
  /-- The link register to restart with (`x30`). -/
  lr : UInt64 := 0
  x0 : UInt64 := 0
  x1 : UInt64 := 0
  x2 : UInt64 := 0
  x3 : UInt64 := 0
  x4 : UInt64 := 0
  x5 : UInt64 := 0
  x6 : UInt64 := 0
  x7 : UInt64 := 0
  deriving Repr, DecidableEq, Inhabited

namespace FaultRestartFrame

/-- WS-RR RR4.16: the `x0`-`x5` sub-frame, so the restart writeback can hand
it to the syscall-return stager rather than repeating its six writes. -/
def returnWindow (f : FaultRestartFrame) : SyscallReturnFrame :=
  { x0 := f.x0, x1 := f.x1, x2 := f.x2, x3 := f.x3, x4 := f.x4, x5 := f.x5 }

end FaultRestartFrame

/-- WS-RR RR4.16: stage a fault-restart frame into a register file.

**Defined through `stageReturnFrame`**, not beside it: the `x0`-`x5` window
is written by the syscall-return stager and this adds only what a restart
reaches beyond it (`x6`, `x7`, `x30`, `pc`, `sp`).  One mechanism, so a
change to how a frame lands in a register file cannot apply to syscall
returns and miss fault restarts. -/
def _root_.SeLe4n.RegisterFile.stageRestartFrame
    (rf : SeLe4n.RegisterFile) (f : FaultRestartFrame) : SeLe4n.RegisterFile :=
  let rf := rf.stageReturnFrame f.returnWindow
  let rf := SeLe4n.writeReg rf ⟨6⟩ ⟨f.x6.toNat⟩
  let rf := SeLe4n.writeReg rf ⟨7⟩ ⟨f.x7.toNat⟩
  let rf := SeLe4n.writeReg rf ⟨30⟩ ⟨f.lr.toNat⟩
  { rf with pc := ⟨f.pc.toNat⟩, sp := ⟨f.sp.toNat⟩ }

/-- WS-RR RR4.16: the restart PC lands in the register file's `pc` — the
word that decides where the thread resumes, and therefore the whole point of
a restart (`faultRestart_moves_pc` lifts this to the state). -/
@[simp] theorem _root_.SeLe4n.RegisterFile.stageRestartFrame_pc
    (rf : SeLe4n.RegisterFile) (f : FaultRestartFrame) :
    (rf.stageRestartFrame f).pc = ⟨f.pc.toNat⟩ := rfl

@[simp] theorem _root_.SeLe4n.RegisterFile.stageRestartFrame_sp
    (rf : SeLe4n.RegisterFile) (f : FaultRestartFrame) :
    (rf.stageRestartFrame f).sp = ⟨f.sp.toNat⟩ := rfl

/-- WS-RR RR4.16: the eight-register argument window and the link register
read back as the frame — the property a handler emulating a trapped syscall
relies on when it replies with the emulation's results. -/
theorem _root_.SeLe4n.RegisterFile.stageRestartFrame_reads_back
    (rf : SeLe4n.RegisterFile) (f : FaultRestartFrame) :
    (rf.stageRestartFrame f).gpr ⟨0⟩ = ⟨f.x0.toNat⟩ ∧
    (rf.stageRestartFrame f).gpr ⟨1⟩ = ⟨f.x1.toNat⟩ ∧
    (rf.stageRestartFrame f).gpr ⟨2⟩ = ⟨f.x2.toNat⟩ ∧
    (rf.stageRestartFrame f).gpr ⟨3⟩ = ⟨f.x3.toNat⟩ ∧
    (rf.stageRestartFrame f).gpr ⟨4⟩ = ⟨f.x4.toNat⟩ ∧
    (rf.stageRestartFrame f).gpr ⟨5⟩ = ⟨f.x5.toNat⟩ ∧
    (rf.stageRestartFrame f).gpr ⟨6⟩ = ⟨f.x6.toNat⟩ ∧
    (rf.stageRestartFrame f).gpr ⟨7⟩ = ⟨f.x7.toNat⟩ ∧
    (rf.stageRestartFrame f).gpr ⟨30⟩ = ⟨f.lr.toNat⟩ := by
  unfold SeLe4n.RegisterFile.stageRestartFrame SeLe4n.RegisterFile.stageReturnFrame
    SeLe4n.writeReg FaultRestartFrame.returnWindow
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- WS-RR RR4.16: registers outside the restart window survive — the
callee-saved range `x8`-`x29` is the faulted thread's own, and a handler that
did not ask to change it does not. -/
theorem _root_.SeLe4n.RegisterFile.stageRestartFrame_gpr_untouched
    (rf : SeLe4n.RegisterFile) (f : FaultRestartFrame) (r : SeLe4n.RegName)
    (hLow : 7 < r.val) (hHigh : r.val ≠ 30) :
    (rf.stageRestartFrame f).gpr r = rf.gpr r := by
  unfold SeLe4n.RegisterFile.stageRestartFrame SeLe4n.RegisterFile.stageReturnFrame
    SeLe4n.writeReg FaultRestartFrame.returnWindow
  simp only
  have h0 : r.val ≠ 0 := by omega
  have h1 : r.val ≠ 1 := by omega
  have h2 : r.val ≠ 2 := by omega
  have h3 : r.val ≠ 3 := by omega
  have h4 : r.val ≠ 4 := by omega
  have h5 : r.val ≠ 5 := by omega
  have h6 : r.val ≠ 6 := by omega
  have h7 : r.val ≠ 7 := by omega
  simp [h0, h1, h2, h3, h4, h5, h6, h7, hHigh]

/-- WS-RR RR4.16: stage a restart frame into a TCB's saved register context —
the single record update the restart path goes through, mirroring
`TCB.withReturnFrame`.  `registerContext` moves; every other TCB field is
definitionally unchanged. -/
def _root_.SeLe4n.Model.TCB.withRestartFrame (tcb : TCB) (f : FaultRestartFrame) : TCB :=
  { tcb with registerContext := tcb.registerContext.stageRestartFrame f }

@[simp] theorem _root_.SeLe4n.Model.TCB.withRestartFrame_ipcState
    (tcb : TCB) (f : FaultRestartFrame) :
    (tcb.withRestartFrame f).ipcState = tcb.ipcState := rfl

@[simp] theorem _root_.SeLe4n.Model.TCB.withRestartFrame_threadState
    (tcb : TCB) (f : FaultRestartFrame) :
    (tcb.withRestartFrame f).threadState = tcb.threadState := rfl

@[simp] theorem _root_.SeLe4n.Model.TCB.withRestartFrame_tid
    (tcb : TCB) (f : FaultRestartFrame) :
    (tcb.withRestartFrame f).tid = tcb.tid := rfl

@[simp] theorem _root_.SeLe4n.Model.TCB.withRestartFrame_pendingMessage
    (tcb : TCB) (f : FaultRestartFrame) :
    (tcb.withRestartFrame f).pendingMessage = tcb.pendingMessage := rfl

@[simp] theorem _root_.SeLe4n.Model.TCB.withRestartFrame_pendingFault
    (tcb : TCB) (f : FaultRestartFrame) :
    (tcb.withRestartFrame f).pendingFault = tcb.pendingFault := rfl

@[simp] theorem _root_.SeLe4n.Model.TCB.withRestartFrame_registerContext
    (tcb : TCB) (f : FaultRestartFrame) :
    (tcb.withRestartFrame f).registerContext
      = tcb.registerContext.stageRestartFrame f := rfl

/-- WS-RR RR4.16: stage a restart frame into a thread's saved register
context — the state-level writeback, mirroring `writeReturnFrameToTcb` down
to its totality posture (a non-TCB target returns the state unchanged). -/
def writeRestartFrameToTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : FaultRestartFrame) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      { st with objects := st.objects.insert tid.toObjId (.tcb (tcb.withRestartFrame frame)) }
  | none => st

/-- WS-RR RR4.16 (frame): the restart writeback never touches the scheduler —
restarting a thread installs registers; making it runnable again is the
separate act the delivery's counterpart performs. -/
@[simp] theorem writeRestartFrameToTcb_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame) :
    (writeRestartFrameToTcb st tid frame).scheduler = st.scheduler := by
  unfold writeRestartFrameToTcb; cases st.getTcb? tid <;> rfl

/-- WS-RR RR4.16 (frame): nor the machine mirror — same posture as
`writeReturnFrameToTcb`, and for the same reason (the SM10.1 context restore
owns that mirror). -/
@[simp] theorem writeRestartFrameToTcb_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame) :
    (writeRestartFrameToTcb st tid frame).machine = st.machine := by
  unfold writeRestartFrameToTcb; cases st.getTcb? tid <;> rfl

/-- WS-RR RR4.16 (frame): nor the declassification audit trail. -/
@[simp] theorem writeRestartFrameToTcb_declassificationAuditLog_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame) :
    (writeRestartFrameToTcb st tid frame).declassificationAuditLog
      = st.declassificationAuditLog := by
  unfold writeRestartFrameToTcb; cases st.getTcb? tid <;> rfl

/-- WS-RR RR4.16 (frame): every object but the restarted thread's is
untouched — the restart is a single-TCB write. -/
theorem writeRestartFrameToTcb_objects_ne
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hObjInv : st.objects.invExt) :
    (writeRestartFrameToTcb st tid frame).objects[oid]? = st.objects[oid]? := by
  have hNe' : ¬(tid.toObjId == oid) = true := by
    simp only [beq_iff_eq]
    exact fun h => hNe h.symm
  unfold writeRestartFrameToTcb
  cases h : st.getTcb? tid with
  | none => rfl
  | some tcb =>
    exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne
        st.objects tid.toObjId oid _ hNe' hObjInv

/-- WS-RR RR4.16: the restarted thread's saved `pc` is the frame's — the
statement RR4.19's progress argument consumes, since "the thread does not
re-execute the faulting instruction" is exactly "its saved `pc` is what the
handler chose". -/
theorem writeRestartFrameToTcb_pc
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt) :
    (writeRestartFrameToTcb st tid frame).getTcb? tid
      = some (tcb.withRestartFrame frame) ∧
    (tcb.withRestartFrame frame).registerContext.pc = ⟨frame.pc.toNat⟩ := by
  refine ⟨?_, rfl⟩
  unfold writeRestartFrameToTcb
  rw [hTcb]
  simp only
  unfold SystemState.getTcb?
  rw [RHTable_getElem?_eq_get?,
      SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId
        (KernelObject.tcb (tcb.withRestartFrame frame)) hObjInv]

-- ============================================================================
-- §7  The ABI version pin (RA.A.7, plan §3.6)
-- ============================================================================

/-- WS-RA RA.A.8 — **the retired bit-63 protocol's hazard, kept on the
record.**  Under the pre-WS-RA convention the success encoder masked bit 63
(`encodeOk v = v &&& 0x7FFFFFFFFFFFFFFF`) to keep success words disjoint
from the error flag, so two *distinct* valid badges (`Badge.valid` admits
everything below `2^64`) collided.  The functions are deleted with the
flip; the statement survives over the mask literal itself, so the protocol
cannot quietly return with its hazard forgotten. -/
theorem bit63Encoding_not_injective_on_badges :
    ∃ a b : UInt64, a ≠ b ∧
      (a &&& 0x7FFFFFFFFFFFFFFF) = (b &&& 0x7FFFFFFFFFFFFFFF) := by
  exact ⟨0x42, 0x8000000000000042, by decide, by decide⟩

/-- The syscall return-ABI version this module defines.

* Version **1** — the retired bit-63 protocol: one status word in `x0`,
  bit 63 the error flag, values masked to 63 bits.
* Version **2** — the seL4 frame convention this module models: `x0` the
  full-width value, `x1` a `MessageInfo` whose offset label carries the
  error, `x2`-`x5` message registers.

Mirrored as `SYSCALL_ABI_VERSION` in `rust/sele4n-types` at the flip, with
each side's conformance suite pinning its own constant to the same literal —
so a half-bumped tree fails its own suite rather than mis-decoding at
runtime (plan §3.6). -/
def syscallAbiVersion : Nat := 2

/-- The Lean half of the version pin (RA.A.7).  The Rust conformance test
asserts the identical literal; a bump that forgets one side fails there. -/
theorem syscallAbiVersion_pinned : syscallAbiVersion = 2 := rfl

end SeLe4n.Kernel.Architecture
