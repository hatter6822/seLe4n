-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State

/-! # Per-Syscall Argument Decode Layer (WS-K-B)

This module implements the second layer of the two-layer syscall argument
decode architecture:

1. **Layer 1** (`RegisterDecode.lean`): Converts raw register file values into
   a flat `SyscallDecodeResult` containing `capAddr`, `msgInfo`, `syscallId`,
   and `msgRegs : Array RegValue`.

2. **Layer 2** (this module): Converts the `msgRegs` array within a
   `SyscallDecodeResult` into per-syscall typed argument structures. Each
   syscall family gets a dedicated structure and total decode function.

**Dependencies:** Only `Model.State` (for types). Does not import any kernel
subsystem module, maintaining the same dependency discipline as
`RegisterDecode.lean`.

**Key properties:**
- All decode functions are total with explicit `Except KernelError` returns.
- Shared `requireMsgReg` provides bounds-checked array indexing.
- Determinism theorems: each decode is a pure function of its input.
- Error-exclusivity theorems: decode fails iff register count insufficient.
-/

namespace SeLe4n.Kernel.Architecture.SyscallArgDecode

open SeLe4n
open SeLe4n.Model

-- ============================================================================
-- Shared infrastructure
-- ============================================================================

/-- Bounds-checked message register access. Returns `invalidMessageInfo` if
    the index exceeds the array size. All per-syscall decode functions
    delegate to this, avoiding duplicated bounds logic. -/
@[inline] def requireMsgReg (regs : Array RegValue) (idx : Nat)
    : Except KernelError RegValue :=
  if h : idx < regs.size then .ok regs[idx]
  else .error .invalidMessageInfo

/-- Error exclusivity: `requireMsgReg` fails iff the index is out of bounds. -/
theorem requireMsgReg_error_iff (regs : Array RegValue) (idx : Nat) :
    requireMsgReg regs idx = .error .invalidMessageInfo ↔ ¬(idx < regs.size) := by
  unfold requireMsgReg
  constructor
  · intro h; split at h <;> simp_all
  · intro h; simp at h; simp [h]

/-- Success exclusivity: `requireMsgReg` succeeds iff the index is in bounds. -/
theorem requireMsgReg_ok_iff (regs : Array RegValue) (idx : Nat) :
    (∃ v, requireMsgReg regs idx = .ok v) ↔ idx < regs.size := by
  unfold requireMsgReg
  constructor
  · intro ⟨v, hv⟩; split at hv <;> simp_all
  · intro h; exact ⟨regs[idx], by simp [h]⟩

/-- **The argument words an invocation's decode reads** (seL4's
`seL4_TruncatedMessage` bound): a message whose length is below it is refused
`.truncatedMessage` before any argument is read (`requireMessageLength`), as
seL4's `decode*Invocation` refuses `length < n` once the capability's kind has
chosen the decode.  The figure is the model's own word count: its ABI carries
every argument as a word, where seL4 passes a capability argument as an extra
capability and an index-and-depth pair.  The seL4 counterparts, and their
checks:

* `cspaceCopy` 4 (`decodeCNodeInvocation`, Copy `length < 5`: the
  destination index, the source root's address, the source index and the
  word of the depths and the rights mask, `CNodeOpWord`), `cspaceMove` 4
  (Move `length < 4`: the same, the word the depths alone), `cspaceMint` 5
  (Mint `length < 6`: a copy's four and the badge);
  `cspaceDelete` `cspaceRevoke` 1 (`length < 2`);
* `untypedRetype` 4 (`decodeUntypedInvocation`, `length < 6`);
* `vspaceMap` 4 (`decodeARMFrameInvocation`, Map `length < 3`),
  `vspaceUnmap` `vspaceUnifyInstruction` 2 (Unify `length < 2`);
* `pageTableMap` 2 (`decodeARMPageTableInvocation`, `length < 2`);
* `tcbSetPriority` `tcbSetMCPriority` `tcbSetIPCBuffer` `tcbSetAffinity`
  1 (`decodeSetPriority` / `decodeSetMCPriority` / `decodeSetIPCBuffer`,
  `length < 1`), `tcbSetSpace` 2 (MCS `decodeSetSpace`, `length < 2`),
  `tcbSetFaultHandler` 1 (the fault endpoint word);
* `schedContextConfigure` 5 (`decodeSchedControl_ConfigureFlags`,
  `length < 5`);
* `irqControlGet` 3 (`Arch_decodeIRQControlInvocation`, IssueIRQHandler
  `length < 3`);
* `schedContextBind` `tcbBindNotification` `irqHandlerSetNotification`
  1: seL4's `decodeSchedContext_Bind`, `decodeBindNotification` and
  `IRQSetIRQHandler` check only for an extra capability, which this ABI
  passes as a word;
* `serviceRegister` 5, `mintReplyCap` 2, `auditRead` 3, `auditDrain` 1:
  model calls with no seL4 counterpart, held to their decodes' word counts as
  every invocation is.

Each figure is the number of words its decode reads, and the decode reads
exactly words `0, …, n - 1` after checking `n`: `#assert_decoder_arities`, in
`SeLe4n.Testing.DecoderArityCheck` (built by Tier 1, outside the kernel's
import closure), reads every listed decode's body and the dispatch arm that
calls it, and fails the build otherwise.

Every other syscall reads no argument word, or is an IPC or a signal, for
which seL4 checks no length (`notificationSignal` included). -/
def truncationMinimum : SyscallId → Nat
  | .untypedRetype | .vspaceMap => 4
  | .cspaceCopy | .cspaceMove => 4
  | .irqControlGet | .auditRead => 3
  | .mintReplyCap | .vspaceUnmap | .vspaceUnifyInstruction
  | .tcbSetSpace | .pageTableMap => 2
  | .cspaceDelete | .cspaceRevoke | .schedContextBind | .tcbBindNotification
  | .tcbSetPriority | .tcbSetMCPriority | .tcbSetIPCBuffer | .tcbSetAffinity
  | .tcbSetFaultHandler | .irqHandlerSetNotification | .auditDrain => 1
  | .schedContextConfigure | .serviceRegister | .cspaceMint => 5
  | _ => 0

/-- **The truncation check** (`truncationMinimum`): a message shorter than
`n` words is refused `.truncatedMessage`, read off the message-info length
before any argument word. -/
@[inline] def requireMessageLength (decoded : SyscallDecodeResult) (n : Nat) :
    Except KernelError Unit :=
  if decoded.msgInfo.length < n then .error .truncatedMessage else .ok ()

theorem requireMessageLength_of_le {decoded : SyscallDecodeResult} {n : Nat}
    (h : n ≤ decoded.msgInfo.length) : requireMessageLength decoded n = .ok () := by
  unfold requireMessageLength; simp only [Nat.not_lt.mpr h, ↓reduceIte]

theorem requireMessageLength_of_lt {decoded : SyscallDecodeResult} {n : Nat}
    (h : decoded.msgInfo.length < n) :
    requireMessageLength decoded n = .error .truncatedMessage := by
  unfold requireMessageLength; simp only [h, ↓reduceIte]

/-- No invocation reads more than five argument words, so a message past the
layout's four message registers is never truncated. -/
theorem truncationMinimum_le_five (sid : SyscallId) : truncationMinimum sid ≤ 5 := by
  cases sid <;> decide

-- ============================================================================
-- CSpace argument structures
-- ============================================================================

/-! ### The CNode operation word

seL4's `seL4_CNode_Copy`, `_Mint` and `_Move` each name two slots by an index
and a depth: the destination's in the invoked CNode, the source's in a source
root CNode.  seLe4n passes the four words those need in the four argument
registers: the destination index, the source root (an address in the caller's
CSpace), the source index, and one word that packs the two depths and, for a
copy or a mint, the rights mask.  Packing is what keeps the copy and the move
to the four inline registers, so they make no IPC-buffer read; seL4 itself
packs its `seL4_CapRights` into a word.  A mint's badge (seL4's `capData`) is
its fifth word, overflow slot 0 of the caller's IPC buffer.

The layout has one owner, the field readers below, and the decoders read the
word only through them.  Bits `[0, 8)` are the destination depth, `[8, 16)` the
source depth, and `[16, 21)` a copy's or a mint's rights mask.  A move that
sets a bit at or above 16, or a copy or a mint one at or above 21, is refused
`.invalidArgument`.  The Lean suite renders the layout by decoding each bit
alone through the copy's and the move's decodes, and the Rust ABI crate renders
its own decoders' layout the same way, against the same fixture
(`tests/fixtures/abi_layout.expected`). -/

namespace CNodeOpWord

/-- The destination depth: bits `[0, 8)`. -/
@[inline] def destDepth (w : Nat) : Nat := w % 256

/-- The source depth: bits `[8, 16)`. -/
@[inline] def srcDepth (w : Nat) : Nat := w / 256 % 256

/-- A copy's or a mint's rights mask: bits `[16, 21)`. -/
@[inline] def rights (w : Nat) : Nat := w / 65536 % 32

/-- The words a move admits: the two depths, no other bit. -/
@[inline] def addressingFits (w : Nat) : Bool := w < 65536

/-- The words a copy or a mint admits: the two depths and the rights mask, no
other bit. -/
@[inline] def rightsFits (w : Nat) : Bool := w < 2097152

/-- The word whose fields are the given depths and rights, each cut to its
width: the encoder the round trips read back. -/
@[inline] def pack (destDepth srcDepth rights : Nat) : Nat :=
  destDepth % 256 + srcDepth % 256 * 256 + rights % 32 * 65536

theorem destDepth_pack (d s r : Nat) : CNodeOpWord.destDepth (pack d s r) = d % 256 := by
  unfold CNodeOpWord.destDepth pack; omega

theorem srcDepth_pack (d s r : Nat) : CNodeOpWord.srcDepth (pack d s r) = s % 256 := by
  unfold CNodeOpWord.srcDepth pack; omega

theorem rights_pack (d s r : Nat) : CNodeOpWord.rights (pack d s r) = r % 32 := by
  unfold CNodeOpWord.rights pack; omega

theorem rightsFits_pack (d s r : Nat) : rightsFits (pack d s r) = true := by
  unfold rightsFits pack; simp only [decide_eq_true_eq]; omega

theorem addressingFits_pack (d s : Nat) : addressingFits (pack d s 0) = true := by
  unfold addressingFits pack; simp only [decide_eq_true_eq]; omega

end CNodeOpWord

/-- **The two slots of a CNode Copy, Mint or Move**, as seL4 names them: the
destination by an index and a depth in the invoked CNode, the source by an
index and a depth in the source root, a CNode capability's address in the
caller's CSpace (seL4's `srcRoot`).
    Register mapping: x2=destIndex, x3=srcRoot, x4=srcIndex, x5=the depths
    (`CNodeOpWord`). -/
structure CNodeOpArgs where
  destIndex : CPtr
  srcRoot   : CPtr
  srcIndex  : CPtr
  destDepth : Nat
  srcDepth  : Nat
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `cspaceCopy`: the two slots and the
rights mask, seL4's `seL4_CNode_Copy` `rights` (the copy's rights are the
source's masked by it, `maskCapRights`).
    Register mapping: x2=destIndex, x3=srcRoot, x4=srcIndex, x5=the depths and
    the mask (`CNodeOpWord`). -/
structure CSpaceCopyArgs extends CNodeOpArgs where
  rights : AccessRightSet
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `cspaceMove`: the two slots.  seL4's
`seL4_CNode_Move` takes no rights. -/
abbrev CSpaceMoveArgs := CNodeOpArgs

/-- Per-syscall argument structure for `cspaceMint`: a copy's operands and the
badge, seL4's `seL4_CNode_Mint` `badge` (its `capData`, `updateCapData`).
    Register mapping: as `CSpaceCopyArgs`, then overflow slot 0 = the badge. -/
structure CSpaceMintArgs extends CSpaceCopyArgs where
  badge : Badge
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `mintReplyCap`: two slots of the invoked
CNode, the reply object's capability and the empty slot the reply capability
goes to.  Register mapping: x2=srcSlot, x3=dstSlot. -/
structure MintReplyCapArgs where
  srcSlot : Slot
  dstSlot : Slot
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `cspaceDelete`.
    Register mapping: x2=targetSlot. -/
structure CSpaceDeleteArgs where
  targetSlot : Slot
  deriving Repr, DecidableEq

-- ============================================================================
-- Lifecycle and VSpace argument structures
-- ============================================================================

/-- **WS-BP BP7.1 (`v0.36.5`)**: per-syscall argument structure for
`untypedRetype` — seL4's `seL4_Untyped_Retype`, invoked on an untyped
capability.  Register mapping: x2=newType tag in bits `[0, 8)` and the object's
size in bits `[8, 64)` as a power of two (seL4's `size_bits`), x3=childId (the
object id the carved object takes), x4=destination CNode capability address,
x5=destination slot.  `newType` is typed at the decode boundary; the arm
carves every kind (WS-ZA ZA5.4 part 14), each at the size `carveRequestOf?`
decodes: a fixed-size kind with `sizeBits = 0`, a child untyped, CNode or
scheduling context at the size `sizeBits` names.

The size shares MR0 with the tag because every register a syscall can read is
already taken — the four argument registers x2–x5 — and seL4's own
`seL4_Untyped_Retype` carries `size_bits` beside `type`.  A frame's MR0 is its
tag alone, exactly as before this field existed. -/
structure UntypedRetypeArgs where
  newType  : KernelObjectType
  sizeBits : Nat
  childId  : ObjId
  dstCNode : CPtr
  dstSlot  : Slot
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `vspaceMap`.
    Register mapping: x2=asid, x3=vaddr, x4=frame capability address, x5=perms word.
    T6-C/M-ARCH-1: `perms` is typed as `PagePermissions` instead of raw `Nat`.
    Validation occurs at decode time via `PagePermissions.ofNat?`, rejecting
    values outside the valid 5-bit range (0–31).

    **WS-BP BP7.1: MR2 names a frame capability, not a physical address.**  It
    was `paddr : PAddr`, a raw number the arm mapped after checking only that it
    was in range and page-aligned — so any holder of a writable VSpace
    capability could map *any* physical memory, the kernel's own image and
    every other domain's pages included.  seL4's `seL4_ARM_Page_Map` is invoked
    on a frame capability: the address comes from the object the capability
    names, and holding the capability is the authority over that memory.  This
    is that: `frame` is resolved through the caller's own CSpace
    (`resolveVSpaceMapFrame`) and the mapping installs the resolved frame's
    `base`. -/
structure VSpaceMapArgs where
  asid  : ASID
  vaddr : VAddr
  frame : CPtr
  perms : PagePermissions
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `vspaceUnmap`.
    Register mapping: x2=asid, x3=vaddr. -/
structure VSpaceUnmapArgs where
  asid  : ASID
  vaddr : VAddr
  deriving Repr, DecidableEq

/-- **WS-SM SM7.D**: arguments of `.vspaceUnifyInstruction` — an address space
and a virtual page, exactly the operand shape `.vspaceUnmap` takes.  Aliased
rather than duplicated so the two share one decoder and one set of decode
theorems; the distinct name keeps the *semantics* legible at the dispatch
site. -/
abbrev VSpaceUnifyInstructionArgs := VSpaceUnmapArgs

-- ============================================================================
-- CSpace decode functions
-- ============================================================================

/-- The two slots of a CNode operation from its four words: the three
addresses and the depth word, which must set no bit past the two depths
(`.invalidArgument`, `CNodeOpWord.addressingFits`). -/
@[inline] def cnodeOpArgsOfWords (destIndex srcRoot srcIndex : CPtr) (depths : Nat) :
    Except KernelError CNodeOpArgs :=
  if CNodeOpWord.addressingFits depths then
    .ok { destIndex, srcRoot, srcIndex
          destDepth := CNodeOpWord.destDepth depths
          srcDepth := CNodeOpWord.srcDepth depths }
  else .error .invalidArgument

/-- A copy's operands from its four words: the three addresses and the word of
the depths and the rights mask, which must set no bit past the mask
(`.invalidArgument`, `CNodeOpWord.rightsFits`). -/
@[inline] def cnodeCopyArgsOfWords (destIndex srcRoot srcIndex : CPtr) (w : Nat) :
    Except KernelError CSpaceCopyArgs :=
  if CNodeOpWord.rightsFits w then
    .ok { destIndex, srcRoot, srcIndex
          destDepth := CNodeOpWord.destDepth w
          srcDepth := CNodeOpWord.srcDepth w
          rights := AccessRightSet.ofNat (CNodeOpWord.rights w) }
  else .error .invalidArgument

/-- Decode CSpace copy arguments from message registers.
    Requires 4 message registers (destIndex, srcRoot, srcIndex, the depths and
    the rights mask). -/
def decodeCSpaceCopyArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceCopyArgs := do
  requireMessageLength decoded (truncationMinimum .cspaceCopy)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  cnodeCopyArgsOfWords (CPtr.ofNat r0.val) (CPtr.ofNat r1.val) (CPtr.ofNat r2.val) r3.val

/-- A mint's operands: a copy's four words, then the badge word (seL4's
`capData`, masked to the badge's width as a badge register is). -/
@[inline] def cnodeMintArgsOfWords (destIndex srcRoot srcIndex : CPtr) (w badge : Nat) :
    Except KernelError CSpaceMintArgs :=
  match cnodeCopyArgsOfWords destIndex srcRoot srcIndex w with
  | .error e => .error e
  | .ok c => .ok { c with badge := Badge.ofNatMasked badge }

/-- A decoded mint's badge is its badge word, masked to the badge width. -/
theorem cnodeMintArgsOfWords_badge {destIndex srcRoot srcIndex : CPtr} {w badge : Nat}
    {args : CSpaceMintArgs}
    (h : cnodeMintArgsOfWords destIndex srcRoot srcIndex w badge = .ok args) :
    args.badge = Badge.ofNatMasked badge := by
  unfold cnodeMintArgsOfWords at h
  split at h
  · cases h
  · cases h; rfl

/-- Decode CSpace mint arguments from message registers.
    Requires 5 message registers: a copy's four and the badge, the fifth read
    from overflow slot 0 of the caller's IPC buffer. -/
def decodeCSpaceMintArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceMintArgs := do
  requireMessageLength decoded (truncationMinimum .cspaceMint)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  let r4 ← requireMsgReg decoded.msgRegs 4
  cnodeMintArgsOfWords (CPtr.ofNat r0.val) (CPtr.ofNat r1.val) (CPtr.ofNat r2.val) r3.val r4.val

/-- Decode CSpace move arguments from message registers.
    Requires 4 message registers (destIndex, srcRoot, srcIndex, depths). -/
def decodeCSpaceMoveArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceMoveArgs := do
  requireMessageLength decoded (truncationMinimum .cspaceMove)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  cnodeOpArgsOfWords (CPtr.ofNat r0.val) (CPtr.ofNat r1.val) (CPtr.ofNat r2.val) r3.val

/-- Decode reply-capability mint arguments from message registers.
    Requires 2 message registers (srcSlot, dstSlot). -/
def decodeMintReplyCapArgs (decoded : SyscallDecodeResult)
    : Except KernelError MintReplyCapArgs := do
  requireMessageLength decoded (truncationMinimum .mintReplyCap)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  pure { srcSlot := Slot.ofNat r0.val, dstSlot := Slot.ofNat r1.val }

/-- Decode CSpace delete arguments from message registers.
    Requires 1 message register (targetSlot). -/
def decodeCSpaceDeleteArgs (decoded : SyscallDecodeResult)
    : Except KernelError CSpaceDeleteArgs := do
  requireMessageLength decoded (truncationMinimum .cspaceDelete)
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { targetSlot := Slot.ofNat r0.val }

-- ============================================================================
-- Lifecycle and VSpace decode functions
-- ============================================================================

/-- **WS-BP BP7.1**: decode untyped-retype arguments from message registers.
Requires 4 message registers; an unrecognised type tag is `.invalidTypeTag`. -/
def decodeUntypedRetypeArgs (decoded : SyscallDecodeResult)
    : Except KernelError UntypedRetypeArgs := do
  requireMessageLength decoded (truncationMinimum .untypedRetype)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  match KernelObjectType.ofNat? (r0.val % 256) with
  | some objType =>
    pure { newType  := objType
           sizeBits := r0.val / 256
           childId  := ObjId.ofNat r1.val
           dstCNode := CPtr.ofNat r2.val
           dstSlot  := Slot.ofNat r3.val }
  | none => .error .invalidTypeTag

/-- Decode VSpace map arguments from message registers.
    Requires 4 message registers (asid, vaddr, frame capability address,
    perms word).
    T6-C/M-ARCH-1: Validates the permissions word at decode time via
    `PagePermissions.ofNat?`. Returns `invalidArgument` for values ≥ 32
    (undefined permission bits set — U5-E/U-M07: decode error, not policy).
    U2-B/U-H06: Validates VAddr lies within ARM64 48-bit canonical range.
    Returns `addressOutOfBounds` for VAddr ≥ 2^48. -/
def decodeVSpaceMapArgs (decoded : SyscallDecodeResult) (maxASID : Nat)
    : Except KernelError VSpaceMapArgs := do
  requireMessageLength decoded (truncationMinimum .vspaceMap)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  -- U2-G/U-H08: Validate ASID within platform-configured range
  -- AH3-C (L-14): Parameterized — callers pass `st.machine.maxASID`
  let asid := ASID.ofNat r0.val
  if !asid.isValidForConfig maxASID then .error .asidNotBound
  else
  -- U2-B/U-H06: Validate VAddr lies within ARM64 48-bit canonical address range
  let vaddr := VAddr.ofNat r1.val
  if !vaddr.isCanonical then .error .addressOutOfBounds
  else
    match PagePermissions.ofNat? r3.val with
    | some perms =>
      pure { asid  := asid
             vaddr := vaddr
             frame := CPtr.ofNat r2.val
             perms := perms }
    -- U5-E/U-M07: Invalid permission bits are a decode error, not a policy violation.
    -- Prior to U5-E this incorrectly returned `.policyDenied`.
    -- X5-E/M-11: Use `invalidSyscallArgument` for syscall-specific decode context.
    | none => .error .invalidSyscallArgument

-- **WS-BP BP7.1: `decodeVSpaceMapArgsChecked` and its two theorems
-- (`decodeVSpaceMapArgsChecked_paddr_bounded`,
-- `decodeVSpaceMapArgsChecked_eq_of_bounded`) are DELETED.**  AK3-E's
-- decode-time physical-address bound had a subject only while MR2 carried a
-- physical address; it carries a frame capability address now, so the address
-- the arm maps is the resolved frame's own `base`, and the downstream
-- `vspaceMapPageCheckedWithFlushFromState` bound — which AK3-E already named as
-- the production check — is the one that applies to it.  The arm calls
-- `decodeVSpaceMapArgs` directly.

/-- Decode VSpace unmap arguments from message registers.
    Requires 2 message registers (asid, vaddr). -/
def decodeVSpaceUnmapArgs (decoded : SyscallDecodeResult) (maxASID : Nat)
    : Except KernelError VSpaceUnmapArgs := do
  requireMessageLength decoded (truncationMinimum .vspaceUnmap)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  -- U2-G/U-H08: Validate ASID within platform-configured range
  -- AH3-C (L-14): Parameterized — callers pass `st.machine.maxASID`
  let asid := ASID.ofNat r0.val
  if !asid.isValidForConfig maxASID then .error .asidNotBound
  else
  -- AE4-B (U-26/ARCH-03): Validate VAddr canonical for consistency with
  -- decodeVSpaceMapArgs. Non-canonical addresses fault on ARM64 hardware;
  -- rejecting at decode provides defense-in-depth.
  let vaddr := VAddr.ofNat r1.val
  if !vaddr.isCanonical then .error .addressOutOfBounds
  else
  pure { asid  := asid
         vaddr := vaddr }

/-- **WS-SM SM7.D**: decode `.vspaceUnifyInstruction` arguments.

Shares `decodeVSpaceUnmapArgs`'s parse and validation — the operand shape is
identical (an ASID validated against the platform's `maxASID`, plus a canonical
virtual address) — so it inherits every decode theorem rather than duplicating
them.  The alias exists so the dispatch arm and its delegation theorem name the
operation they are actually performing. -/
@[inline] def decodeVSpaceUnifyInstructionArgs (decoded : SyscallDecodeResult)
    (maxASID : Nat) : Except KernelError VSpaceUnifyInstructionArgs :=
  decodeVSpaceUnmapArgs decoded maxASID

/-- **WS-SM SM7.D**: the unify decoder is definitionally the unmap decoder. -/
theorem decodeVSpaceUnifyInstructionArgs_eq (decoded : SyscallDecodeResult)
    (maxASID : Nat) :
    decodeVSpaceUnifyInstructionArgs decoded maxASID =
      decodeVSpaceUnmapArgs decoded maxASID := rfl

-- ============================================================================
-- V4-F/M-HW-5: MemoryKind cross-check for VSpace permissions
-- ============================================================================

/-- V4-F/M-HW-5: Post-decode validation that cross-checks VSpace permissions
    against the target physical address's `MemoryKind`. Device regions must not
    receive execute permission (execute-from-device is undefined on ARM64).

    This validation occurs after the frame is resolved, because the address it
    checks is the frame's (`FrameObject.base`, WS-BP BP7.1) and the memory map is
    not available at the register-decode layer. -/
def validateVSpaceMapPermsForMemoryKind
    (paddr : PAddr) (perms : PagePermissions) (memoryMap : List MemoryRegion) :
    Except KernelError PagePermissions :=
  let regionKind := memoryMap.find? (fun r => r.contains paddr)
    |>.map (fun r => r.kind)
  match regionKind with
  | some MemoryKind.device =>
    -- Device regions must not have execute permission
    if perms.execute then .error .policyDenied
    else .ok perms
  | _ => .ok perms

/-- WS-ZA ZA5.4: does the first region of `memoryMap` containing `paddr` hold
device memory?  A first-order loop. -/
def firstRegionIsDevice (paddr : PAddr) : List MemoryRegion → Bool
  | [] => false
  | r :: rs =>
    if r.contains paddr then (match r.kind with | .device => true | _ => false)
    else firstRegionIsDevice paddr rs

/-- WS-ZA ZA5.4: the memory-kind check as it runs — the region found by a
first-order loop, no predicate closure or region `Option`, and inlined so the
caller's match on the result cancels (`validateVSpaceMapPermsForMemoryKind_eq_direct`). -/
@[inline] def validateVSpaceMapPermsForMemoryKindDirect
    (paddr : PAddr) (perms : PagePermissions) (memoryMap : List MemoryRegion) :
    Except KernelError PagePermissions :=
  if firstRegionIsDevice paddr memoryMap && perms.execute then .error .policyDenied
  else .ok perms

@[csimp] theorem validateVSpaceMapPermsForMemoryKind_eq_direct :
    @validateVSpaceMapPermsForMemoryKind = @validateVSpaceMapPermsForMemoryKindDirect := by
  funext paddr perms memoryMap
  unfold validateVSpaceMapPermsForMemoryKind validateVSpaceMapPermsForMemoryKindDirect
  induction memoryMap with
  | nil => simp [firstRegionIsDevice]
  | cons r rs ih =>
    by_cases h : r.contains paddr = true
    · simp only [List.find?_cons, h, Option.map_some, firstRegionIsDevice, ↓reduceIte]
      cases r.kind <;> cases perms.execute <;> rfl
    · simp only [List.find?_cons, h, firstRegionIsDevice, Bool.false_eq_true, ↓reduceIte]
      exact ih

/-- V4-F: Device regions with execute permission are rejected. -/
theorem validateVSpaceMapPermsForMemoryKind_device_noexec
    (paddr : PAddr) (perms : PagePermissions) (memoryMap : List MemoryRegion)
    (hFind : memoryMap.find? (fun r => r.contains paddr) = some region)
    (hDevice : region.kind = .device)
    (hExec : perms.execute = true) :
    ∃ e, validateVSpaceMapPermsForMemoryKind paddr perms memoryMap = .error e := by
  simp [validateVSpaceMapPermsForMemoryKind, hFind, hDevice, hExec]

/-- **WS-BP BP7.1**: a successful validation returns the permissions it was
    given — it refuses, it never rewrites. -/
theorem validateVSpaceMapPermsForMemoryKind_ok_eq
    (paddr : PAddr) (perms perms' : PagePermissions) (memoryMap : List MemoryRegion)
    (h : validateVSpaceMapPermsForMemoryKind paddr perms memoryMap = .ok perms') :
    perms' = perms := by
  unfold validateVSpaceMapPermsForMemoryKind at h
  simp only at h
  cases hK : (memoryMap.find? (fun r => r.contains paddr)).map (fun r => r.kind) with
  | none => rw [hK] at h; exact (Except.ok.inj h).symm
  | some k =>
    rw [hK] at h
    cases k <;> simp at h
    all_goals first
      | exact h.symm
      | (split at h
         · cases h
         · exact (Except.ok.inj h).symm)

-- ============================================================================
-- Encode functions (inverse of decode, for round-trip proofs)
-- ============================================================================

/-- Encode CSpace mint arguments into message registers.
    Inverse of `decodeCSpaceMintArgs`. -/
@[inline] def encodeCSpaceMintArgs (args : CSpaceMintArgs) : Array RegValue :=
  #[⟨args.destIndex.toNat⟩, ⟨args.srcRoot.toNat⟩, ⟨args.srcIndex.toNat⟩,
    ⟨CNodeOpWord.pack args.destDepth args.srcDepth args.rights.bits⟩, ⟨args.badge.toNat⟩]

/-- Encode CSpace copy arguments into message registers.
    Inverse of `decodeCSpaceCopyArgs` for depths below 256 and a valid mask. -/
@[inline] def encodeCSpaceCopyArgs (args : CSpaceCopyArgs) : Array RegValue :=
  #[⟨args.destIndex.toNat⟩, ⟨args.srcRoot.toNat⟩, ⟨args.srcIndex.toNat⟩,
    ⟨CNodeOpWord.pack args.destDepth args.srcDepth args.rights.bits⟩]

/-- Encode CSpace move arguments into message registers.
    Inverse of `decodeCSpaceMoveArgs` for depths below 256. -/
@[inline] def encodeCSpaceMoveArgs (args : CSpaceMoveArgs) : Array RegValue :=
  #[⟨args.destIndex.toNat⟩, ⟨args.srcRoot.toNat⟩, ⟨args.srcIndex.toNat⟩,
    ⟨CNodeOpWord.pack args.destDepth args.srcDepth 0⟩]

/-- Encode reply-capability mint arguments into message registers.
    Inverse of `decodeMintReplyCapArgs`. -/
@[inline] def encodeMintReplyCapArgs (args : MintReplyCapArgs) : Array RegValue :=
  #[⟨args.srcSlot.toNat⟩, ⟨args.dstSlot.toNat⟩]

/-- Encode CSpace delete arguments into message registers.
    Inverse of `decodeCSpaceDeleteArgs`. -/
@[inline] def encodeCSpaceDeleteArgs (args : CSpaceDeleteArgs) : Array RegValue :=
  #[⟨args.targetSlot.toNat⟩]

/-- **WS-BP BP7.1**: encode untyped-retype arguments into message registers.
    Inverse of `decodeUntypedRetypeArgs`. -/
@[inline] def encodeUntypedRetypeArgs (args : UntypedRetypeArgs) : Array RegValue :=
  #[⟨args.newType.toNat + args.sizeBits * 256⟩, ⟨args.childId.toNat⟩,
    ⟨args.dstCNode.toNat⟩, ⟨args.dstSlot.toNat⟩]

/-- Encode VSpace map arguments into message registers.
    Inverse of `decodeVSpaceMapArgs`. T6-C: encodes PagePermissions via toNat. -/
@[inline] def encodeVSpaceMapArgs (args : VSpaceMapArgs) : Array RegValue :=
  #[⟨args.asid.toNat⟩, ⟨args.vaddr.toNat⟩, ⟨args.frame.toNat⟩, ⟨args.perms.toNat⟩]

/-- Encode VSpace unmap arguments into message registers.
    Inverse of `decodeVSpaceUnmapArgs`. -/
@[inline] def encodeVSpaceUnmapArgs (args : VSpaceUnmapArgs) : Array RegValue :=
  #[⟨args.asid.toNat⟩, ⟨args.vaddr.toNat⟩]

-- ============================================================================
-- Error-exclusivity theorems
-- ============================================================================

/-- Helper: unfold requireMsgReg in a goal and simplify dite. -/
private theorem requireMsgReg_unfold_ok (regs : Array RegValue) (idx : Nat) (h : idx < regs.size) :
    requireMsgReg regs idx = .ok regs[idx] := by simp [requireMsgReg, dif_pos h]

private theorem requireMsgReg_unfold_err (regs : Array RegValue) (idx : Nat) (h : ¬(idx < regs.size)) :
    requireMsgReg regs idx = .error .invalidMessageInfo := by simp [requireMsgReg, dif_neg h]

/-- A CNode operation's four words refuse exactly when the message is short of
them or the depth word sets a bit past the two depths. -/
private theorem cnodeOpWords_error_iff (regs : Array RegValue) :
    (∃ e, (do
        let r0 ← requireMsgReg regs 0
        let r1 ← requireMsgReg regs 1
        let r2 ← requireMsgReg regs 2
        let r3 ← requireMsgReg regs 3
        cnodeOpArgsOfWords (CPtr.ofNat r0.val) (CPtr.ofNat r1.val) (CPtr.ofNat r2.val) r3.val :
          Except KernelError CNodeOpArgs) = .error e) ↔
      regs.size < 4 ∨ ∃ h : 3 < regs.size, CNodeOpWord.addressingFits regs[3].val = false := by
  unfold requireMsgReg cnodeOpArgsOfWords
  by_cases h3 : 3 < regs.size
  · simp only [dif_pos (show 0 < regs.size by omega), dif_pos (show 1 < regs.size by omega),
      dif_pos (show 2 < regs.size by omega), dif_pos h3, bind, Except.bind]
    cases hF : CNodeOpWord.addressingFits regs[3].val <;> simp [h3, hF] <;> omega
  · by_cases h0 : 0 < regs.size
    · by_cases h1 : 1 < regs.size
      · by_cases h2 : 2 < regs.size
        · simp [h0, h1, h2, h3, bind, Except.bind]; omega
        · simp [h0, h1, h2, bind, Except.bind]; omega
      · simp [h0, h1, bind, Except.bind]; omega
    · simp [h0, bind, Except.bind]; omega

/-- A copy's four words refuse exactly when the message is short of them or
the word of the depths and the mask sets a bit past the mask. -/
private theorem cnodeCopyWords_error_iff (regs : Array RegValue) :
    (∃ e, (do
        let r0 ← requireMsgReg regs 0
        let r1 ← requireMsgReg regs 1
        let r2 ← requireMsgReg regs 2
        let r3 ← requireMsgReg regs 3
        cnodeCopyArgsOfWords (CPtr.ofNat r0.val) (CPtr.ofNat r1.val) (CPtr.ofNat r2.val) r3.val :
          Except KernelError CSpaceCopyArgs) = .error e) ↔
      regs.size < 4 ∨ ∃ h : 3 < regs.size, CNodeOpWord.rightsFits regs[3].val = false := by
  unfold requireMsgReg cnodeCopyArgsOfWords
  by_cases h3 : 3 < regs.size
  · simp only [dif_pos (show 0 < regs.size by omega), dif_pos (show 1 < regs.size by omega),
      dif_pos (show 2 < regs.size by omega), dif_pos h3, bind, Except.bind]
    cases hF : CNodeOpWord.rightsFits regs[3].val <;> simp [h3, hF] <;> omega
  · by_cases h0 : 0 < regs.size
    · by_cases h1 : 1 < regs.size
      · by_cases h2 : 2 < regs.size
        · simp [h0, h1, h2, h3, bind, Except.bind]; omega
        · simp [h0, h1, h2, bind, Except.bind]; omega
      · simp [h0, h1, bind, Except.bind]; omega
    · simp [h0, bind, Except.bind]; omega

/-- CSpace copy decode fails iff fewer than 4 message registers, or a word of
the depths and the mask with a bit set past the mask. -/
theorem decodeCSpaceCopyArgs_error_iff (d : SyscallDecodeResult) (hLen : truncationMinimum .cspaceCopy ≤ d.msgInfo.length) :
    (∃ e, decodeCSpaceCopyArgs d = .error e) ↔
      d.msgRegs.size < 4 ∨ ∃ h : 3 < d.msgRegs.size,
        CNodeOpWord.rightsFits d.msgRegs[3].val = false := by
  have hL := requireMessageLength_of_le hLen
  unfold decodeCSpaceCopyArgs
  simp only [hL, bind, Except.bind]
  exact cnodeCopyWords_error_iff d.msgRegs

/-- CSpace mint decode fails iff fewer than 5 message registers, or a word of
the depths and the mask with a bit set past the mask. -/
theorem decodeCSpaceMintArgs_error_iff (d : SyscallDecodeResult) (hLen : truncationMinimum .cspaceMint ≤ d.msgInfo.length) :
    (∃ e, decodeCSpaceMintArgs d = .error e) ↔
      d.msgRegs.size < 5 ∨ ∃ h : 3 < d.msgRegs.size,
        CNodeOpWord.rightsFits d.msgRegs[3].val = false := by
  have hL := requireMessageLength_of_le hLen
  unfold decodeCSpaceMintArgs cnodeMintArgsOfWords cnodeCopyArgsOfWords requireMsgReg
  simp only [hL, bind, Except.bind]
  by_cases h4 : 4 < d.msgRegs.size
  · simp only [dif_pos (show 0 < d.msgRegs.size by omega), dif_pos (show 1 < d.msgRegs.size by omega),
      dif_pos (show 2 < d.msgRegs.size by omega), dif_pos (show 3 < d.msgRegs.size by omega),
      dif_pos h4]
    cases hF : CNodeOpWord.rightsFits d.msgRegs[3].val <;> simp [hF] <;> omega
  · constructor
    · intro _; exact .inl (by omega)
    · intro _
      by_cases h0 : 0 < d.msgRegs.size
      · by_cases h1 : 1 < d.msgRegs.size
        · by_cases h2 : 2 < d.msgRegs.size
          · by_cases h3 : 3 < d.msgRegs.size
            · simp [h0, h1, h2, h3, h4]
            · simp [h0, h1, h2, h3]
          · simp [h0, h1, h2]
        · simp [h0, h1]
      · simp [h0]

/-- CSpace move decode fails iff fewer than 4 message registers, or a depth
word with a bit set past the two depths. -/
theorem decodeCSpaceMoveArgs_error_iff (d : SyscallDecodeResult) (hLen : truncationMinimum .cspaceMove ≤ d.msgInfo.length) :
    (∃ e, decodeCSpaceMoveArgs d = .error e) ↔
      d.msgRegs.size < 4 ∨ ∃ h : 3 < d.msgRegs.size,
        CNodeOpWord.addressingFits d.msgRegs[3].val = false := by
  have hL := requireMessageLength_of_le hLen
  unfold decodeCSpaceMoveArgs
  simp only [hL, bind, Except.bind]
  exact cnodeOpWords_error_iff d.msgRegs

/-- CSpace delete decode fails iff fewer than 1 message register. -/
theorem decodeCSpaceDeleteArgs_error_iff (d : SyscallDecodeResult) (hLen : truncationMinimum .cspaceDelete ≤ d.msgInfo.length) :
    (∃ e, decodeCSpaceDeleteArgs d = .error e) ↔ d.msgRegs.size < 1 := by
  have hL := requireMessageLength_of_le hLen
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 1
    · exact hlt
    · exfalso
      simp only [decodeCSpaceDeleteArgs, hL, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeCSpaceDeleteArgs, hL, bind, Except.bind]
    rw [requireMsgReg_unfold_err _ _ (by omega)]

/-- **WS-BP BP7.1**: untyped-retype decode fails if fewer than 4 message registers. -/
theorem decodeUntypedRetypeArgs_error_of_insufficient_regs (d : SyscallDecodeResult) (hLen : truncationMinimum .untypedRetype ≤ d.msgInfo.length)
    (h : d.msgRegs.size < 4) :
    ∃ e, decodeUntypedRetypeArgs d = .error e := by
  have hL := requireMessageLength_of_le hLen
  refine ⟨.invalidMessageInfo, ?_⟩
  simp only [decodeUntypedRetypeArgs, hL, bind, Except.bind]
  by_cases h0 : 0 < d.msgRegs.size
  · rw [requireMsgReg_unfold_ok _ _ h0]; simp
    by_cases h1 : 1 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h1]; simp
      by_cases h2 : 2 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h2]; simp
        rw [requireMsgReg_unfold_err _ _ (by omega)]
      · rw [requireMsgReg_unfold_err _ _ h2]
    · rw [requireMsgReg_unfold_err _ _ h1]
  · rw [requireMsgReg_unfold_err _ _ h0]

/-- T6-C/D: VSpace map decode fails if fewer than 4 message registers. -/
theorem decodeVSpaceMapArgs_error_of_insufficient_regs (d : SyscallDecodeResult) (maxASID : Nat) (hLen : truncationMinimum .vspaceMap ≤ d.msgInfo.length)
    (h : d.msgRegs.size < 4) :
    ∃ e, decodeVSpaceMapArgs d maxASID = .error e := by
  have hL := requireMessageLength_of_le hLen
  refine ⟨.invalidMessageInfo, ?_⟩
  simp only [decodeVSpaceMapArgs, hL, bind, Except.bind]
  by_cases h0 : 0 < d.msgRegs.size
  · rw [requireMsgReg_unfold_ok _ _ h0]; simp
    by_cases h1 : 1 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h1]; simp
      by_cases h2 : 2 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h2]; simp
        rw [requireMsgReg_unfold_err _ _ (by omega)]
      · rw [requireMsgReg_unfold_err _ _ h2]
    · rw [requireMsgReg_unfold_err _ _ h1]
  · rw [requireMsgReg_unfold_err _ _ h0]

/-- U2-B: VSpace map decode fails if VAddr is non-canonical (≥ 2^48). -/
theorem decodeVSpaceMapArgs_error_of_noncanonical_vaddr (d : SyscallDecodeResult) (maxASID : Nat) (hLen : truncationMinimum .vspaceMap ≤ d.msgInfo.length)
    (hSize : 4 ≤ d.msgRegs.size)
    (hVAddr : (VAddr.ofNat d.msgRegs[1].val).isCanonical = false) :
    ∃ e, decodeVSpaceMapArgs d maxASID = .error e := by
  have hL := requireMessageLength_of_le hLen
  simp only [decodeVSpaceMapArgs, hL, bind, Except.bind,
    requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
    dif_pos (show 1 < d.msgRegs.size by omega),
    dif_pos (show 2 < d.msgRegs.size by omega),
    dif_pos (show 3 < d.msgRegs.size by omega)]
  split
  · -- ASID invalid → error (asidNotBound)
    exact ⟨.asidNotBound, rfl⟩
  · -- ASID valid → VAddr check fails
    exact ⟨.addressOutOfBounds, by simp [hVAddr]⟩

/-- T6-D/M-ARCH-1: VSpace map decode fails if the permissions word is invalid (≥ 32). -/
theorem decodeVSpaceMapArgs_error_of_invalid_perms (d : SyscallDecodeResult) (maxASID : Nat) (hLen : truncationMinimum .vspaceMap ≤ d.msgInfo.length)
    (hSize : 4 ≤ d.msgRegs.size)
    (hPerms : PagePermissions.ofNat? d.msgRegs[3].val = none) :
    ∃ e, decodeVSpaceMapArgs d maxASID = .error e := by
  have hL := requireMessageLength_of_le hLen
  simp only [decodeVSpaceMapArgs, hL, bind, Except.bind,
    requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
    dif_pos (show 1 < d.msgRegs.size by omega),
    dif_pos (show 2 < d.msgRegs.size by omega),
    dif_pos (show 3 < d.msgRegs.size by omega)]
  split
  · -- ASID invalid → error
    exact ⟨.asidNotBound, rfl⟩
  · -- ASID valid → check VAddr
    split
    · -- VAddr not canonical → error
      exact ⟨.addressOutOfBounds, rfl⟩
    · -- VAddr canonical → perms check fails
      exact ⟨.invalidSyscallArgument, by simp [hPerms]⟩

/-- VSpace map decode fails iff fewer than 4 message registers,
    ASID is invalid, VAddr is non-canonical, or the permissions word is invalid.
    Four failure modes:
    1. `msgRegs.size < 4` → `requireMsgReg` returns error
    2. ASID (msgRegs[0]) ≥ maxASID → asidNotBound
    3. VAddr (msgRegs[1]) ≥ 2^48 → addressOutOfBounds
    4. `msgRegs.size ≥ 4`, ASID valid, VAddr canonical, but `PagePermissions.ofNat?` returns none → invalidSyscallArgument (X5-E) -/
theorem decodeVSpaceMapArgs_error_iff (d : SyscallDecodeResult) (maxASID : Nat) (hLen : truncationMinimum .vspaceMap ≤ d.msgInfo.length) :
    (∃ e, decodeVSpaceMapArgs d maxASID = .error e) ↔
    (d.msgRegs.size < 4 ∨
     (∃ (h : 3 < d.msgRegs.size), (ASID.ofNat (d.msgRegs[0]'(by omega)).val).isValidForConfig maxASID = false) ∨
     (∃ (h : 3 < d.msgRegs.size), (VAddr.ofNat (d.msgRegs[1]'(by omega)).val).isCanonical = false) ∨
     (∃ (h : 3 < d.msgRegs.size), PagePermissions.ofNat? (d.msgRegs[3]'h).val = none)) := by
  have hL := requireMessageLength_of_le hLen
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 4
    · exact .inl hlt
    · have h3 : 3 < d.msgRegs.size := by omega
      simp only [decodeVSpaceMapArgs, hL, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        dif_pos (show 2 < d.msgRegs.size by omega),
        dif_pos (show 3 < d.msgRegs.size by omega)] at he
      split at he
      · -- ASID invalid
        rename_i hAsidInvalid
        right; left
        exact ⟨h3, by
          simp only [Bool.not_eq_true'] at hAsidInvalid
          cases hc : (ASID.ofNat d.msgRegs[0].val).isValidForConfig maxASID
          · rfl
          · rw [hc] at hAsidInvalid; simp at hAsidInvalid⟩
      · -- ASID valid → check VAddr
        split at he
        · -- VAddr not canonical
          rename_i hNotCanon
          right; right; left
          exact ⟨h3, by
            simp only [Bool.not_eq_true'] at hNotCanon
            cases hc : (VAddr.ofNat d.msgRegs[1].val).isCanonical
            · rfl
            · rw [hc] at hNotCanon; simp at hNotCanon⟩
        · -- VAddr canonical → check perms
          right; right; right
          exact ⟨h3, by
            split at he
            · -- some perms case: decode succeeded → contradicts error assumption
              nomatch he
            · -- none case: perms invalid
              assumption⟩
  · intro h
    match h with
    | .inl hLt => exact decodeVSpaceMapArgs_error_of_insufficient_regs d maxASID hLen hLt
    | .inr (.inl ⟨h3, hAsid⟩) =>
      exact ⟨.asidNotBound, by
        simp only [decodeVSpaceMapArgs, hL, bind, Except.bind,
          requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
          dif_pos (show 1 < d.msgRegs.size by omega),
          dif_pos (show 2 < d.msgRegs.size by omega),
          dif_pos (show 3 < d.msgRegs.size by omega)]
        have : (!(ASID.ofNat d.msgRegs[0].val).isValidForConfig maxASID) = true := by
          rw [hAsid]; rfl
        simp [this]⟩
    | .inr (.inr (.inl ⟨h3, hVAddr⟩)) =>
      exact decodeVSpaceMapArgs_error_of_noncanonical_vaddr d maxASID hLen (by omega) hVAddr
    | .inr (.inr (.inr ⟨h3, hPerms⟩)) =>
      exact decodeVSpaceMapArgs_error_of_invalid_perms d maxASID hLen (by omega) hPerms

/-- AE4-B: VSpace unmap decode fails iff fewer than 2 message registers,
    ASID invalid, or VAddr non-canonical. -/
theorem decodeVSpaceUnmapArgs_error_iff (d : SyscallDecodeResult) (maxASID : Nat) (hLen : truncationMinimum .vspaceUnmap ≤ d.msgInfo.length) :
    (∃ e, decodeVSpaceUnmapArgs d maxASID = .error e) ↔
    (d.msgRegs.size < 2 ∨
     (∃ (h : 1 < d.msgRegs.size), (ASID.ofNat (d.msgRegs[0]'(by omega)).val).isValidForConfig maxASID = false) ∨
     (∃ (h : 1 < d.msgRegs.size),
       (ASID.ofNat (d.msgRegs[0]'(by omega)).val).isValidForConfig maxASID = true ∧
       (VAddr.ofNat (d.msgRegs[1]'(by omega)).val).isCanonical = false)) := by
  have hL := requireMessageLength_of_le hLen
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 2
    · exact .inl hlt
    · have h1 : 1 < d.msgRegs.size := by omega
      simp only [decodeVSpaceUnmapArgs, hL, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega)] at he
      -- Branch on ASID validity
      by_cases hAsid : (ASID.ofNat d.msgRegs[0].val).isValidForConfig maxASID = true
      · -- ASID valid
        have hAsidBool : (!(ASID.ofNat d.msgRegs[0].val).isValidForConfig maxASID) = false := by
          rw [hAsid]; rfl
        simp only [hAsidBool, Bool.false_eq_true, ↓reduceIte] at he
        -- Branch on VAddr canonicity
        by_cases hVAddr : (VAddr.ofNat d.msgRegs[1].val).isCanonical = true
        · -- VAddr canonical → pure succeeds → contradiction
          have hVBool : (!(VAddr.ofNat d.msgRegs[1].val).isCanonical) = false := by
            rw [hVAddr]; rfl
          simp only [hVBool, Bool.false_eq_true, ↓reduceIte] at he
          nomatch he
        · -- VAddr non-canonical
          right; right
          refine ⟨h1, hAsid, ?_⟩
          cases hc : (VAddr.ofNat d.msgRegs[1].val).isCanonical
          · rfl
          · exact absurd hc hVAddr
      · -- ASID invalid
        right; left
        exact ⟨h1, by
          cases hc : (ASID.ofNat d.msgRegs[0].val).isValidForConfig maxASID
          · rfl
          · exact absurd hc hAsid⟩
  · intro h
    match h with
    | .inl hLt =>
      refine ⟨.invalidMessageInfo, ?_⟩
      simp only [decodeVSpaceUnmapArgs, hL, bind, Except.bind]
      by_cases h0 : 0 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h0]; simp
        rw [requireMsgReg_unfold_err _ _ (by omega)]
      · rw [requireMsgReg_unfold_err _ _ h0]
    | .inr (.inl ⟨h1, hAsid⟩) =>
      exact ⟨.asidNotBound, by
        simp only [decodeVSpaceUnmapArgs, hL, bind, Except.bind,
          requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
          dif_pos (show 1 < d.msgRegs.size by omega)]
        have : (!(ASID.ofNat d.msgRegs[0].val).isValidForConfig maxASID) = true := by
          rw [hAsid]; rfl
        simp [this]⟩
    | .inr (.inr ⟨h1, hAsidOk, hVAddr⟩) =>
      exact ⟨.addressOutOfBounds, by
        simp only [decodeVSpaceUnmapArgs, hL, bind, Except.bind,
          requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
          dif_pos (show 1 < d.msgRegs.size by omega)]
        have hAsidTrue : (!(ASID.ofNat d.msgRegs[0].val).isValidForConfig maxASID) = false := by
          rw [hAsidOk]; rfl
        have hVAddrFalse : (!(VAddr.ofNat d.msgRegs[1].val).isCanonical) = true := by
          rw [hVAddr]; rfl
        simp [hAsidTrue, hVAddrFalse]⟩

-- ============================================================================
-- Round-trip proofs: encode then decode recovers the original
-- ============================================================================

/-- Helper: a `SyscallDecodeResult` stub with given message registers.
    Used exclusively for round-trip proof statements. -/
private def stubDecoded (regs : Array RegValue) : SyscallDecodeResult :=
  { capAddr := CPtr.ofNat 0
    msgInfo := { length := regs.size, extraCaps := 0, label := 0 }
    syscallId := .send
    msgRegs := regs }

/-- A copy's operands read back from their packed word, when both depths fit
their eight bits and the mask is a valid rights set. -/
private theorem cnodeCopyArgsOfWords_pack (di sr si : CPtr) (dd sd : Nat) (r : AccessRightSet)
    (hDest : dd < 256) (hSrc : sd < 256) (hRights : r.valid) :
    cnodeCopyArgsOfWords (CPtr.ofNat di.toNat) (CPtr.ofNat sr.toNat) (CPtr.ofNat si.toNat)
      (CNodeOpWord.pack dd sd r.bits) = .ok ⟨⟨di, sr, si, dd, sd⟩, r⟩ := by
  have hFits := CNodeOpWord.rightsFits_pack dd sd r.bits
  have hLt : r.bits < 32 := AccessRightSet.isWord5_of_valid r hRights
  simp only [cnodeCopyArgsOfWords, hFits, ↓reduceIte, CNodeOpWord.destDepth_pack,
    CNodeOpWord.srcDepth_pack, CNodeOpWord.rights_pack, Nat.mod_eq_of_lt hDest,
    Nat.mod_eq_of_lt hSrc, Nat.mod_eq_of_lt hLt, CPtr.ofNat_toNat,
    AccessRightSet.ofNat_idempotent r hRights]

/-- A mint's operands are its copy's and the badge. -/
private theorem cnodeMintArgsOfWords_of_copy {a b c : CPtr} {w bd : Nat} {x : CSpaceCopyArgs}
    (h : cnodeCopyArgsOfWords a b c w = .ok x) :
    cnodeMintArgsOfWords a b c w bd = .ok { x with badge := Badge.ofNatMasked bd } := by
  unfold cnodeMintArgsOfWords; rw [h]

/-- Round-trip: encoding then decoding CSpaceCopyArgs recovers the original
when both depths fit their eight bits and the mask is a valid rights set
(`AccessRightSet.ofNat` keeps five bits). -/
theorem decodeCSpaceCopyArgs_roundtrip (args : CSpaceCopyArgs)
    (hDest : args.destDepth < 256) (hSrc : args.srcDepth < 256) (hRights : args.rights.valid) :
    decodeCSpaceCopyArgs (stubDecoded (encodeCSpaceCopyArgs args)) = .ok args := by
  rcases args with ⟨⟨di, sr, si, dd, sd⟩, r⟩
  simp only at hDest hSrc hRights
  have hFits := CNodeOpWord.rightsFits_pack dd sd r.bits
  have hLt : r.bits < 32 := AccessRightSet.isWord5_of_valid r hRights
  -- The word is generalised so the kernel never evaluates the fit check.
  have hStep : ∀ w, decodeCSpaceCopyArgs (stubDecoded #[⟨di.toNat⟩, ⟨sr.toNat⟩, ⟨si.toNat⟩, ⟨w⟩]) =
      cnodeCopyArgsOfWords (CPtr.ofNat di.toNat) (CPtr.ofNat sr.toNat) (CPtr.ofNat si.toNat) w :=
    fun _ => rfl
  rw [show encodeCSpaceCopyArgs ⟨⟨di, sr, si, dd, sd⟩, r⟩ =
      #[⟨di.toNat⟩, ⟨sr.toNat⟩, ⟨si.toNat⟩, ⟨CNodeOpWord.pack dd sd r.bits⟩] from rfl, hStep]
  simp only [cnodeCopyArgsOfWords, hFits, ↓reduceIte, CNodeOpWord.destDepth_pack,
    CNodeOpWord.srcDepth_pack, CNodeOpWord.rights_pack, Nat.mod_eq_of_lt hDest,
    Nat.mod_eq_of_lt hSrc, Nat.mod_eq_of_lt hLt, CPtr.ofNat_toNat,
    AccessRightSet.ofNat_idempotent r hRights]

/-- Round-trip: encoding then decoding CSpaceMintArgs recovers the original
    when the copy's operands round-trip and the badge is word-bounded.
    R6-B: `ofNatMasked` decode requires the badge to fit in one machine word
    for lossless roundtrip. -/
theorem decodeCSpaceMintArgs_roundtrip (args : CSpaceMintArgs)
    (hDest : args.destDepth < 256) (hSrc : args.srcDepth < 256) (hRights : args.rights.valid)
    (hBadge : args.badge.valid) :
    decodeCSpaceMintArgs (stubDecoded (encodeCSpaceMintArgs args)) = .ok args := by
  -- AN2-A: `Badge.mk` is private cross-module, so the badge is not
  -- destructured; `ofNatMasked_toNat` recovers it.
  rcases args with ⟨⟨⟨di, sr, si, dd, sd⟩, r⟩, b⟩
  simp only at hDest hSrc hRights hBadge
  have hFits := CNodeOpWord.rightsFits_pack dd sd r.bits
  have hLt : r.bits < 32 := AccessRightSet.isWord5_of_valid r hRights
  have hBadgeId : Badge.ofNatMasked b.toNat = b := Badge.ofNatMasked_toNat b hBadge
  -- The word is generalised so the kernel never evaluates the fit check.
  have hStep : ∀ w, decodeCSpaceMintArgs
      (stubDecoded #[⟨di.toNat⟩, ⟨sr.toNat⟩, ⟨si.toNat⟩, ⟨w⟩, ⟨b.toNat⟩]) =
      cnodeMintArgsOfWords (CPtr.ofNat di.toNat) (CPtr.ofNat sr.toNat) (CPtr.ofNat si.toNat)
        w b.toNat :=
    fun _ => rfl
  simp only [encodeCSpaceMintArgs]
  rw [hStep, cnodeMintArgsOfWords_of_copy
    (cnodeCopyArgsOfWords_pack di sr si dd sd r hDest hSrc hRights), hBadgeId]

/-- Round-trip: encoding then decoding CSpaceMoveArgs recovers the original
when both depths fit their eight bits. -/
theorem decodeCSpaceMoveArgs_roundtrip (args : CSpaceMoveArgs)
    (hDest : args.destDepth < 256) (hSrc : args.srcDepth < 256) :
    decodeCSpaceMoveArgs (stubDecoded (encodeCSpaceMoveArgs args)) = .ok args := by
  rcases args with ⟨di, sr, si, dd, sd⟩
  simp only at hDest hSrc
  have hFits := CNodeOpWord.addressingFits_pack dd sd
  show cnodeOpArgsOfWords (CPtr.ofNat di.toNat) (CPtr.ofNat sr.toNat) (CPtr.ofNat si.toNat)
    (CNodeOpWord.pack dd sd 0) = _
  simp only [cnodeOpArgsOfWords, hFits, ↓reduceIte, CNodeOpWord.destDepth_pack,
    CNodeOpWord.srcDepth_pack, Nat.mod_eq_of_lt hDest, Nat.mod_eq_of_lt hSrc,
    CPtr.ofNat_toNat]

/-- Round-trip: encoding then decoding MintReplyCapArgs recovers the original. -/
theorem decodeMintReplyCapArgs_roundtrip (args : MintReplyCapArgs) :
    decodeMintReplyCapArgs (stubDecoded (encodeMintReplyCapArgs args)) = .ok args := by
  rcases args with ⟨s, d⟩; rfl

/-- Round-trip: encoding then decoding CSpaceDeleteArgs recovers the original. -/
theorem decodeCSpaceDeleteArgs_roundtrip (args : CSpaceDeleteArgs) :
    decodeCSpaceDeleteArgs (stubDecoded (encodeCSpaceDeleteArgs args)) = .ok args := by
  rcases args with ⟨t⟩; rfl

/-- **WS-BP BP7.1**: round-trip for UntypedRetypeArgs — the type tag's `ofNat?`
and `toNat` are inverses per variant, every tag is below `256` so the size in
the word's upper bits reads back whole, and the three identifier registers carry
their values verbatim. -/
theorem decodeUntypedRetypeArgs_roundtrip (args : UntypedRetypeArgs) :
    decodeUntypedRetypeArgs (stubDecoded (encodeUntypedRetypeArgs args)) = .ok args := by
  rcases args with ⟨t, b, c, d, sl⟩
  have hLt : t.toNat < 256 := by cases t <;> decide
  have hDiv : (t.toNat + b * 256) / 256 = b := by omega
  have hTag' : KernelObjectType.ofNat? (t.toNat % 256) = some t := by
    rw [Nat.mod_eq_of_lt hLt]; cases t <;> rfl
  simp [requireMessageLength, truncationMinimum, hTag', decodeUntypedRetypeArgs, encodeUntypedRetypeArgs, stubDecoded,
    requireMsgReg, hDiv, bind, Except.bind, pure, Except.pure]
  exact ⟨rfl, rfl⟩

/-- T6-C: Round-trip requires that the permissions encode to a valid range.
    `PagePermissions.toNat` always produces values < 32 (5-bit bitfield). -/
private theorem pagePermissions_toNat_lt_32 (p : PagePermissions) :
    p.toNat < 32 := by
  rcases p with ⟨r, w, e, u, c⟩
  cases r <;> cases w <;> cases e <;> cases u <;> cases c <;> decide

private theorem pagePermissions_ofNat?_toNat (p : PagePermissions)
    (hWx : p.wxCompliant = true) :
    PagePermissions.ofNat? p.toNat = some (PagePermissions.ofNat p.toNat) := by
  have hLt := pagePermissions_toNat_lt_32 p
  have hWxRt : (PagePermissions.ofNat p.toNat).wxCompliant = true := by
    rw [PagePermissions.ofNat_toNat_roundtrip]; exact hWx
  simp [PagePermissions.ofNat?, hLt, hWxRt]

/-- U2-B/U2-G/V4-K: Round-trip requires VAddr is canonical (within 48-bit range),
    ASID is valid for the platform-configured maxASID, and permissions are W^X compliant.
    V4-K: W^X compliance is now enforced at decode time by `ofNat?`. -/
theorem decodeVSpaceMapArgs_roundtrip (args : VSpaceMapArgs) (maxASID : Nat)
    (hAsid : args.asid.isValidForConfig maxASID = true)
    (hVAddr : args.vaddr.isCanonical = true)
    (hWx : args.perms.wxCompliant = true) :
    decodeVSpaceMapArgs (stubDecoded (encodeVSpaceMapArgs args)) maxASID = .ok args := by
  rcases args with ⟨a, v, p, perms⟩
  show decodeVSpaceMapArgs (stubDecoded (encodeVSpaceMapArgs ⟨a, v, p, perms⟩)) maxASID = .ok ⟨a, v, p, perms⟩
  -- U2-G: The ASID validity check needs to pass; derive that from hAsid
  have hAsidValid : (ASID.ofNat a.toNat).isValidForConfig maxASID = true := by
    simp only [ASID.ofNat, ASID.toNat]; exact hAsid
  have hAsidNotFalse : (!(ASID.ofNat a.toNat).isValidForConfig maxASID) = false := by
    rw [hAsidValid]; rfl
  -- U2-B: The VAddr canonical check needs to pass; derive that from hVAddr
  have hCanon : (VAddr.ofNat v.toNat).isCanonical = true := by
    simp only [VAddr.ofNat, VAddr.toNat]; exact hVAddr
  have hNotCanonFalse : (!(VAddr.ofNat v.toNat).isCanonical) = false := by
    rw [hCanon]; rfl
  rcases perms with ⟨r, w, e, u, c⟩
  have hA : a.isValidForConfig maxASID = true := hAsid
  have hV : v.isCanonical = true := hVAddr
  -- V4-K: W^X cases (write=true, execute=true) are excluded by hWx
  cases r <;> cases w <;> cases e <;> cases u <;> cases c <;>
    simp_all [requireMessageLength, truncationMinimum, decodeVSpaceMapArgs, encodeVSpaceMapArgs, stubDecoded,
      bind, Except.bind, requireMsgReg, PagePermissions.wxCompliant,
      PagePermissions.toNat, PagePermissions.ofNat?, PagePermissions.ofNat,
      ASID.ofNat_toNat, VAddr.ofNat_toNat, CPtr.ofNat_toNat, pure, Except.pure]

/-- Round-trip: encoding then decoding VSpaceUnmapArgs recovers the original.
    U2-G: Requires ASID is valid for the platform-configured maxASID.
    AE4-B: Requires VAddr is canonical. -/
theorem decodeVSpaceUnmapArgs_roundtrip (args : VSpaceUnmapArgs) (maxASID : Nat)
    (hAsid : args.asid.isValidForConfig maxASID = true)
    (hVAddr : args.vaddr.isCanonical = true) :
    decodeVSpaceUnmapArgs (stubDecoded (encodeVSpaceUnmapArgs args)) maxASID = .ok args := by
  rcases args with ⟨a, v⟩
  simp [requireMessageLength, truncationMinimum, decodeVSpaceUnmapArgs, encodeVSpaceUnmapArgs, stubDecoded,
    bind, Except.bind, requireMsgReg, ASID.ofNat_toNat, VAddr.ofNat_toNat,
    pure, Except.pure, hAsid, hVAddr]

-- ============================================================================
-- WS-Q1-D: Service argument structures
-- ============================================================================

/-- Per-syscall argument structure for `serviceRegister`.
    Register mapping: x2=interfaceId, x3=methodCount, x4=maxMessageSize,
    x5=maxResponseSize, x6=requiresGrant (0 or 1). -/
structure ServiceRegisterArgs where
  interfaceId    : InterfaceId
  methodCount    : Nat
  maxMessageSize : Nat
  maxResponseSize : Nat
  requiresGrant  : Bool
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `serviceRevoke`.
    No message registers: the revoke removes the registration the invoked
    endpoint records (`revokeServiceByRecordedRegistration`), so the endpoint comes
    from the capability target and the caller names no service. -/
structure ServiceRevokeArgs where
  deriving Repr, DecidableEq

/-- Per-syscall argument structure for `serviceQuery`.
    No additional message registers required — the endpoint object ID comes
    from the capability target, not from message registers. -/
structure ServiceQueryArgs where
  deriving Repr, DecidableEq

-- ============================================================================
-- WS-Q1-D: Service decode functions
-- ============================================================================

/-- AK4-B (R-ABI-H02 / HIGH): Maximum method count for a service registration,
    matching `MAX_METHOD_COUNT = 1024` in `rust/sele4n-abi/src/args/service.rs`. -/
def serviceMaxMethodCount : Nat := 1024

/-- AK4-B (R-ABI-H02 / HIGH): Maximum IPC message size in bytes for service
    registration, matching `MAX_SERVICE_MESSAGE_SIZE = 960` (= 120 registers ×
    8 bytes). Applies to both `maxMessageSize` and `maxResponseSize`. -/
def serviceMaxMessageSize : Nat := 120 * 8

/-- Decode service register arguments from message registers.
    Requires 5 message registers (interfaceId, methodCount, maxMessageSize,
    maxResponseSize, requiresGrant).

    AK4-B (R-ABI-H02 / HIGH): Tightened validation to match Rust-side
    `sele4n-abi/src/args/service.rs:decode`:
    - `r4` (`requiresGrant`) must be `0` or `1`; any other value fails closed.
    - `r1` (`methodCount`) must be ≤ `serviceMaxMethodCount` (1024).
    - `r2` (`maxMessageSize`) must be ≤ `serviceMaxMessageSize` (960).
    - `r3` (`maxResponseSize`) must be ≤ `serviceMaxMessageSize` (960).
    Kernel is the authoritative validator — the tightening prevents any
    Rust-validated-but-Lean-accepted divergence. -/
def decodeServiceRegisterArgs (decoded : SyscallDecodeResult)
    : Except KernelError ServiceRegisterArgs := do
  requireMessageLength decoded (truncationMinimum .serviceRegister)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  let r4 ← requireMsgReg decoded.msgRegs 4
  -- AK4-B: bounds validation (matches Rust ABI constants).
  if r1.val > serviceMaxMethodCount then .error .invalidArgument
  else if r2.val > serviceMaxMessageSize then .error .invalidArgument
  else if r3.val > serviceMaxMessageSize then .error .invalidArgument
  else if r4.val ≥ 2 then .error .invalidMessageInfo
  else
    pure { interfaceId    := InterfaceId.ofNat r0.val
           methodCount    := r1.val
           maxMessageSize := r2.val
           maxResponseSize := r3.val
           requiresGrant  := r4.val == 1 }

-- ============================================================================
-- WS-Q1-D: Service encode functions
-- ============================================================================

/-- Encode service register arguments into message registers.
    Inverse of `decodeServiceRegisterArgs`. -/
@[inline] def encodeServiceRegisterArgs (args : ServiceRegisterArgs) : Array RegValue :=
  #[⟨args.interfaceId.toNat⟩, ⟨args.methodCount⟩, ⟨args.maxMessageSize⟩,
    ⟨args.maxResponseSize⟩, ⟨if args.requiresGrant then 1 else 0⟩]

-- ============================================================================
-- WS-Q1-D: Service error-exclusivity theorems
-- ============================================================================

/-- AK4-B: Service register decode fails when msgRegs are insufficient OR
    when any argument exceeds its validated bound. This supersedes the legacy
    `size < 5`-only iff. -/
theorem decodeServiceRegisterArgs_error_of_insufficient_regs
    (d : SyscallDecodeResult) (hLen : truncationMinimum .serviceRegister ≤ d.msgInfo.length) (h : d.msgRegs.size < 5) :
    ∃ e, decodeServiceRegisterArgs d = .error e := by
  have hL := requireMessageLength_of_le hLen
  refine ⟨.invalidMessageInfo, ?_⟩
  simp only [decodeServiceRegisterArgs, hL, bind, Except.bind]
  by_cases h0 : 0 < d.msgRegs.size
  · rw [requireMsgReg_unfold_ok _ _ h0]; simp
    by_cases h1 : 1 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h1]; simp
      by_cases h2 : 2 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h2]; simp
        by_cases h3 : 3 < d.msgRegs.size
        · rw [requireMsgReg_unfold_ok _ _ h3]; simp
          rw [requireMsgReg_unfold_err _ _ (by omega)]
        · rw [requireMsgReg_unfold_err _ _ h3]
      · rw [requireMsgReg_unfold_err _ _ h2]
    · rw [requireMsgReg_unfold_err _ _ h1]
  · rw [requireMsgReg_unfold_err _ _ h0]

/-- AK4-B: Out-of-range `methodCount` fails closed. -/
theorem decodeServiceRegisterArgs_error_of_methodCount_too_large
    (d : SyscallDecodeResult) (hLen : truncationMinimum .serviceRegister ≤ d.msgInfo.length) (hSize : 5 ≤ d.msgRegs.size)
    (hMc : d.msgRegs[1].val > serviceMaxMethodCount) :
    decodeServiceRegisterArgs d = .error .invalidArgument := by
  have hL := requireMessageLength_of_le hLen
  simp only [decodeServiceRegisterArgs, hL, bind, Except.bind,
    requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
    dif_pos (show 1 < d.msgRegs.size by omega),
    dif_pos (show 2 < d.msgRegs.size by omega),
    dif_pos (show 3 < d.msgRegs.size by omega),
    dif_pos (show 4 < d.msgRegs.size by omega)]
  simp [hMc]

/-- AK4-B: Out-of-range `requiresGrant` fails closed. -/
theorem decodeServiceRegisterArgs_error_of_invalid_grant
    (d : SyscallDecodeResult) (hLen : truncationMinimum .serviceRegister ≤ d.msgInfo.length) (hSize : 5 ≤ d.msgRegs.size)
    (hMc : d.msgRegs[1].val ≤ serviceMaxMethodCount)
    (hMms : d.msgRegs[2].val ≤ serviceMaxMessageSize)
    (hMrs : d.msgRegs[3].val ≤ serviceMaxMessageSize)
    (hGrant : d.msgRegs[4].val ≥ 2) :
    decodeServiceRegisterArgs d = .error .invalidMessageInfo := by
  have hL := requireMessageLength_of_le hLen
  simp only [decodeServiceRegisterArgs, hL, bind, Except.bind,
    requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
    dif_pos (show 1 < d.msgRegs.size by omega),
    dif_pos (show 2 < d.msgRegs.size by omega),
    dif_pos (show 3 < d.msgRegs.size by omega),
    dif_pos (show 4 < d.msgRegs.size by omega)]
  have hMcFalse : ¬ d.msgRegs[1].val > serviceMaxMethodCount := Nat.not_lt.mpr hMc
  have hMmsFalse : ¬ d.msgRegs[2].val > serviceMaxMessageSize := Nat.not_lt.mpr hMms
  have hMrsFalse : ¬ d.msgRegs[3].val > serviceMaxMessageSize := Nat.not_lt.mpr hMrs
  simp [hMcFalse, hMmsFalse, hMrsFalse, hGrant]

-- ============================================================================
-- WS-Q1-D: Service round-trip theorems
-- ============================================================================

/-- Round-trip: encoding then decoding ServiceRegisterArgs recovers the original.
    AK4-B (R-ABI-H02): Requires bounds preconditions matching the validated
    range — the tightened decoder rejects values outside these bounds. -/
theorem decodeServiceRegisterArgs_roundtrip (args : ServiceRegisterArgs)
    (hMc : args.methodCount ≤ serviceMaxMethodCount)
    (hMms : args.maxMessageSize ≤ serviceMaxMessageSize)
    (hMrs : args.maxResponseSize ≤ serviceMaxMessageSize) :
    decodeServiceRegisterArgs (stubDecoded (encodeServiceRegisterArgs args)) = .ok args := by
  rcases args with ⟨iid, mc, mms, mrs, rg⟩
  have hMcFalse : ¬ serviceMaxMethodCount < mc := Nat.not_lt.mpr hMc
  have hMmsFalse : ¬ serviceMaxMessageSize < mms := Nat.not_lt.mpr hMms
  have hMrsFalse : ¬ serviceMaxMessageSize < mrs := Nat.not_lt.mpr hMrs
  simp only [requireMessageLength, truncationMinimum, decodeServiceRegisterArgs, encodeServiceRegisterArgs, stubDecoded,
        requireMsgReg, bind, Except.bind, pure, Except.pure,
        InterfaceId.ofNat, InterfaceId.toNat]
  cases rg <;>
    simp [hMcFalse, hMmsFalse, hMrsFalse]

-- ============================================================================
-- V2-I: Notification and ReplyRecv argument structures
-- ============================================================================

/-- V2-A/V2-I: Per-syscall argument structure for `notificationWait`.
    No message registers needed — the notification object is resolved from the
    capability target. The waiter thread ID comes from the current thread. -/
structure NotificationWaitArgs where
  deriving Repr, DecidableEq

/-- V2-C/V2-I: Per-syscall argument structure for `replyRecv`.
    Register mapping: `msgRegs[0]` = the server-supplied reply capability pointer.
    WS-SM SM6.D (faithful seL4-MCS): `ReplyRecv` replies to the *previous* caller
    via the reply *object* the cap names (`reply.caller`) — not a raw thread id —
    and re-links that same reply object to the *next* caller on the receive leg.
    The endpoint is resolved from the capability target. Message body comes
    from the standard message registers (same as send). -/
structure ReplyRecvArgs where
  replyCPtr : SeLe4n.CPtr
  deriving Repr, DecidableEq

/-- V2-I: Decode notification wait arguments. No message registers needed. -/
def decodeNotificationWaitArgs (_decoded : SyscallDecodeResult)
    : Except KernelError NotificationWaitArgs :=
  pure {}

/-- V2-I: Decode replyRecv arguments from message registers.
    Requires 1 message register (the server-supplied reply capability pointer). -/
def decodeReplyRecvArgs (decoded : SyscallDecodeResult)
    : Except KernelError ReplyRecvArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { replyCPtr := SeLe4n.CPtr.ofNat r0.val }

-- ============================================================================

-- WS-SM SM6.D: MCS `Recv` ABI (faithful server-supplied reply objects)
-- ============================================================================

/-- WS-SM SM6.D: argument structure for the MCS `Recv` syscall — `msgRegs[0]` =
    the reply capability pointer (the server-supplied Reply object cap slot the
    kernel links to a rendezvousing Call-caller). -/
structure RecvArgs where
  replyCPtr : SeLe4n.CPtr
  deriving Repr, DecidableEq

/-- WS-SM SM6.D: decode MCS `Recv` arguments (1 register: the reply capability
    pointer the server supplies, resolved through the server's CSpace — like
    `tcbBindNotification` — so the link authority flows from *holding* a reply
    capability, never from naming a raw `ReplyId`). -/
def decodeRecvArgs (decoded : SyscallDecodeResult) : Except KernelError RecvArgs := do
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { replyCPtr := SeLe4n.CPtr.ofNat r0.val }

/-- WS-SM SM6.D: encode MCS `Recv` arguments into message registers.  Inverse of
    `decodeRecvArgs`. -/
@[inline] def encodeRecvArgs (args : RecvArgs) : Array RegValue :=
  #[⟨args.replyCPtr.toNat⟩]

/-- WS-SM SM6.D: `Recv` decode fails iff fewer than 1 message register. -/
theorem decodeRecvArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeRecvArgs d = .error e) ↔ d.msgRegs.size < 1 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 1
    · exact hlt
    · exfalso
      simp only [decodeRecvArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeRecvArgs, bind, Except.bind]
    rw [requireMsgReg_unfold_err _ _ (by omega)]

/-- WS-SM SM6.D: round-trip — encoding then decoding `RecvArgs` recovers the
    original. -/
theorem decodeRecvArgs_roundtrip (args : RecvArgs) :
    decodeRecvArgs (stubDecoded (encodeRecvArgs args)) = .ok args := by
  simp [decodeRecvArgs, encodeRecvArgs, stubDecoded, requireMsgReg,
        Bind.bind, Except.bind, Pure.pure, Except.pure, SeLe4n.CPtr.ofNat_toNat]

-- ============================================================================
-- Z5-A/B/C: SchedContext argument structures
-- ============================================================================

/-- Z5-A: Per-syscall argument structure for `schedContextConfigure`.

WS-ZA ZA6.4: the configure is invoked on a **scheduling-control** capability and
names the context it configures by a capability, as seL4-MCS's
`seL4_SchedControl_ConfigureFlags` takes the context as an extra capability.
Register mapping: msgRegs[0]=scCPtr (the context capability's address in the
caller's CSpace), msgRegs[1]=budget, msgRegs[2]=period, msgRegs[3]=schedParams
(the priority in bits 0–7 and the domain from bit 8, `priority` / `domain`),
msgRegs[4]=deadline.  Priority and domain share a word so the configure keeps
five words, one of them the IPC buffer's first overflow word. -/
structure SchedContextConfigureArgs where
  scCPtr      : SeLe4n.CPtr
  budget      : Nat
  period      : Nat
  schedParams : Nat
  deadline    : Nat
  deriving Repr, DecidableEq

/-- The configured priority: bits 0–7 of the parameter word. -/
@[inline] def SchedContextConfigureArgs.priority (a : SchedContextConfigureArgs) : Nat :=
  a.schedParams % 256

/-- The configured domain: the parameter word from bit 8. -/
@[inline] def SchedContextConfigureArgs.domain (a : SchedContextConfigureArgs) : Nat :=
  a.schedParams / 256

/-- Z5-B: Per-syscall argument structure for `schedContextBind`.
    Register mapping: msgRegs[0]=tcbCPtr — the **capability address**, in the
    caller's own CSpace, of the TCB to bind to this SchedContext.

    **`v0.35.204`**: this was `threadId : Nat`, a raw thread id the arm bound
    directly, so a holder of an ordinary SchedContext capability could bind that
    context to any thread it could name and rewrite that thread's base priority
    through the bind's Z5-G3 propagation.  seL4-MCS's `seL4_SchedContext_Bind`
    takes the TCB as a capability, and `.tcbBindNotification` already resolved
    its extra operand that way (`TcbBindNotificationArgs.notificationCPtr`); the
    bind now does too, through `Kernel.resolveSchedContextBindThread`. -/
structure SchedContextBindArgs where
  tcbCPtr : SeLe4n.CPtr
  deriving Repr, DecidableEq

/-- Z5-C: Per-syscall argument structure for `schedContextUnbind`.
    No additional arguments — the SchedContext comes from the capability target. -/
structure SchedContextUnbindArgs where
  deriving Repr, DecidableEq

-- ============================================================================
-- Z5-A/B/C: SchedContext decode functions
-- ============================================================================

/-- Z5-A: Decode schedContextConfigure arguments from message registers.
    Requires 5 message registers (context capability, budget, period, the
    priority-and-domain word, deadline). -/
def decodeSchedContextConfigureArgs (decoded : SyscallDecodeResult)
    : Except KernelError SchedContextConfigureArgs := do
  requireMessageLength decoded (truncationMinimum .schedContextConfigure)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  let r3 ← requireMsgReg decoded.msgRegs 3
  let r4 ← requireMsgReg decoded.msgRegs 4
  pure { scCPtr := SeLe4n.CPtr.ofNat r0.val, budget := r1.val, period := r2.val,
         schedParams := r3.val, deadline := r4.val }

/-- AK3-J (A-M07 / MEDIUM): Validation wrapper that rejects configurations
    violating core CBS/scheduler invariants before reaching the scheduler
    subsystem. Mirror of AK3-E's decode-time-bound pattern (the retired
    `decodeVSpaceMapArgsChecked`; WS-BP BP7.1 tombstone in this file).

    Checks:
    - schedParams < 4096 (WS-ZA ZA6.4: the priority is bits 0–7 and the
                        domain bits 8–11 of one word, and a word with any bit at
                        or above 12 set is refused — so the domain fits in
                        `numDomains` and the priority, its low byte, fits in
                        `Priority`, and no stray bit is silently dropped)
    - budget > 0       (non-degenerate CBS server; also closes SC-H01 part)
    - period > 0       (CBS replenishment math requires positive period)

    Rejects violations with `.invalidArgument`. The underlying
    `decodeSchedContextConfigureArgs` remains unchanged so existing error
    theorems and round-trip proofs are preserved. -/
def decodeSchedContextConfigureArgsChecked (decoded : SyscallDecodeResult)
    : Except KernelError SchedContextConfigureArgs := do
  let args ← decodeSchedContextConfigureArgs decoded
  if args.schedParams ≥ 4096 then .error .invalidArgument
  else if args.budget = 0 then .error .invalidArgument
  else if args.period = 0 then .error .invalidArgument
  else pure args

/-- AK3-J: A successful checked configure decode satisfies all CBS invariants. -/
theorem decodeSchedContextConfigureArgsChecked_invariants
    (d : SyscallDecodeResult) (args : SchedContextConfigureArgs)
    (hOk : decodeSchedContextConfigureArgsChecked d = .ok args) :
    args.schedParams < 4096 ∧ args.priority ≤ 255 ∧ args.domain < 16 ∧
      args.budget > 0 ∧ args.period > 0 := by
  unfold decodeSchedContextConfigureArgsChecked at hOk
  simp only [bind, Except.bind] at hOk
  cases hInner : decodeSchedContextConfigureArgs d with
  | error e => rw [hInner] at hOk; simp at hOk
  | ok a =>
    rw [hInner] at hOk; simp only at hOk
    split at hOk
    · simp at hOk
    · split at hOk
      · simp at hOk
      · split at hOk
        · simp at hOk
        · rename_i hD hB hPer
          simp only [pure, Except.pure, Except.ok.injEq] at hOk
          subst hOk
          have hW := Nat.not_le.mp hD
          refine ⟨hW, ?_, ?_, ?_, ?_⟩
          · unfold SchedContextConfigureArgs.priority; omega
          · unfold SchedContextConfigureArgs.domain; omega
          · omega
          · omega

/-- Z5-B: Decode schedContextBind arguments from message registers.
    Requires 1 message register (`tcbCPtr`, the TCB capability's address in
    the caller's CSpace — `v0.35.204`; a raw thread id until then). -/
def decodeSchedContextBindArgs (decoded : SyscallDecodeResult)
    : Except KernelError SchedContextBindArgs := do
  requireMessageLength decoded (truncationMinimum .schedContextBind)
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { tcbCPtr := SeLe4n.CPtr.ofNat r0.val }

/-- Z5-C: Decode schedContextUnbind arguments. No message registers needed. -/
def decodeSchedContextUnbindArgs (_decoded : SyscallDecodeResult)
    : Except KernelError SchedContextUnbindArgs :=
  pure {}

/-- WS-SM SM6.B: arguments for `tcbBindNotification` — `msgRegs[0]` is the
    **capability address** (CPtr) of the notification to bind to the
    capability-target TCB.  Resolved through the caller's CSpace (review #1):
    binding requires the caller to *hold* a notification capability, not merely
    name a raw `ObjId`. -/
structure TcbBindNotificationArgs where
  notificationCPtr : SeLe4n.CPtr
  deriving Repr, DecidableEq

/-- WS-SM SM6.B: arguments for `tcbUnbindNotification` (none — the bound
    notification is recovered from the TCB). -/
structure TcbUnbindNotificationArgs where
  deriving Repr, DecidableEq

/-- WS-SM SM6.B: decode `tcbBindNotification` arguments (1 register: the
    notification capability address). -/
def decodeTcbBindNotificationArgs (decoded : SyscallDecodeResult)
    : Except KernelError TcbBindNotificationArgs := do
  requireMessageLength decoded (truncationMinimum .tcbBindNotification)
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { notificationCPtr := SeLe4n.CPtr.ofNat r0.val }

/-- WS-ZA ZA6.32: arguments for `irqControlGet` (seL4's
    `seL4_IRQControl_Get`): `msgRegs[0]` the interrupt line, `msgRegs[1]` the
    capability address of the CNode the handler capability is issued into, and
    `msgRegs[2]` the slot in it. -/
structure IrqControlGetArgs where
  line     : Nat
  dstCNode : CPtr
  dstSlot  : Slot
  deriving Repr, DecidableEq

/-- WS-ZA ZA6.32: decode `irqControlGet` arguments (3 registers). -/
def decodeIrqControlGetArgs (decoded : SyscallDecodeResult)
    : Except KernelError IrqControlGetArgs := do
  requireMessageLength decoded (truncationMinimum .irqControlGet)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  pure { line := r0.val, dstCNode := CPtr.ofNat r1.val, dstSlot := Slot.ofNat r2.val }

/-- WS-ZA ZA6.32: arguments for `irqHandlerSetNotification` (seL4's
    `seL4_IRQHandler_SetNotification`): `msgRegs[0]` the capability address of
    the notification the line is to signal. -/
structure IrqHandlerSetNotificationArgs where
  notificationCPtr : SeLe4n.CPtr
  deriving Repr, DecidableEq

/-- WS-ZA ZA6.32: decode `irqHandlerSetNotification` arguments (1 register). -/
def decodeIrqHandlerSetNotificationArgs (decoded : SyscallDecodeResult)
    : Except KernelError IrqHandlerSetNotificationArgs := do
  requireMessageLength decoded (truncationMinimum .irqHandlerSetNotification)
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { notificationCPtr := SeLe4n.CPtr.ofNat r0.val }

-- ============================================================================
-- Z5-A/B/C: SchedContext encode functions
-- ============================================================================

/-- Z5-A: Encode schedContextConfigure arguments into message registers. -/
@[inline] def encodeSchedContextConfigureArgs (args : SchedContextConfigureArgs) : Array RegValue :=
  #[⟨args.scCPtr.toNat⟩, ⟨args.budget⟩, ⟨args.period⟩, ⟨args.schedParams⟩, ⟨args.deadline⟩]

/-- Z5-B: Encode schedContextBind arguments into message registers. -/
@[inline] def encodeSchedContextBindArgs (args : SchedContextBindArgs) : Array RegValue :=
  #[⟨args.tcbCPtr.toNat⟩]

/-- Z5-C: Encode schedContextUnbind arguments (empty — no message registers). -/
@[inline] def encodeSchedContextUnbindArgs (_args : SchedContextUnbindArgs) : Array RegValue :=
  #[]

-- ============================================================================
-- Z5-A/B/C: SchedContext round-trip proofs
-- ============================================================================

/-- Z5-A: SchedContextConfigureArgs decode round-trip. -/
theorem decodeSchedContextConfigureArgs_roundtrip (args : SchedContextConfigureArgs) :
    decodeSchedContextConfigureArgs (stubDecoded (encodeSchedContextConfigureArgs args)) = .ok args := by
  simp [requireMessageLength, truncationMinimum, decodeSchedContextConfigureArgs, encodeSchedContextConfigureArgs, stubDecoded, requireMsgReg,
        Bind.bind, Except.bind, Pure.pure, Except.pure, SeLe4n.CPtr.ofNat_toNat]

/-- Z5-B: SchedContextBindArgs decode round-trip. -/
theorem decodeSchedContextBindArgs_roundtrip (args : SchedContextBindArgs) :
    decodeSchedContextBindArgs (stubDecoded (encodeSchedContextBindArgs args)) = .ok args := by
  simp [requireMessageLength, truncationMinimum, decodeSchedContextBindArgs, encodeSchedContextBindArgs, stubDecoded, requireMsgReg,
        Bind.bind, Except.bind, Pure.pure, Except.pure, SeLe4n.CPtr.ofNat_toNat]

/-- Z5-C: SchedContextUnbindArgs decode round-trip (trivial). -/
theorem decodeSchedContextUnbindArgs_roundtrip (args : SchedContextUnbindArgs) :
    decodeSchedContextUnbindArgs (stubDecoded (encodeSchedContextUnbindArgs args)) = .ok args := by
  rcases args; rfl

/-- V2-I: Encode notification wait arguments (empty — no message registers). -/
@[inline] def encodeNotificationWaitArgs (_args : NotificationWaitArgs) : Array RegValue :=
  #[]

/-- V2-I: Encode replyRecv arguments into message registers. -/
@[inline] def encodeReplyRecvArgs (args : ReplyRecvArgs) : Array RegValue :=
  #[⟨args.replyCPtr.toNat⟩]

/-- V2-I: NotificationWaitArgs decode round-trip (trivial — no MR decode). -/
theorem decodeNotificationWaitArgs_roundtrip (args : NotificationWaitArgs) :
    decodeNotificationWaitArgs (stubDecoded (encodeNotificationWaitArgs args)) = .ok args := by
  rcases args; rfl

/-- V2-I: ReplyRecvArgs decode round-trip. -/
theorem decodeReplyRecvArgs_roundtrip (args : ReplyRecvArgs) :
    decodeReplyRecvArgs (stubDecoded (encodeReplyRecvArgs args)) = .ok args := by
  simp [decodeReplyRecvArgs, encodeReplyRecvArgs, stubDecoded, requireMsgReg,
        Bind.bind, Except.bind, Pure.pure, Except.pure, SeLe4n.CPtr.ofNat_toNat]

/-- Composed round-trip: every argument structure listed satisfies the
    encode-decode round-trip property. R6-B: CSpaceMintArgs requires badge
    validity for lossless roundtrip through `ofNatMasked` (a signal has no
    argument structure: its badge is the capability's, `Capability.signalBadge`,
    and it reads no message register). Y1-D:
    CSpaceMintArgs additionally requires rights validity for lossless roundtrip
    through `AccessRightSet.ofNat`. Parallel to `decode_components_roundtrip`
    in `RegisterDecode.lean`. -/
theorem decode_layer2_roundtrip_all (maxASID : Nat) :
    (∀ args : CSpaceMintArgs, args.destDepth < 256 → args.srcDepth < 256 →
      args.rights.valid → args.badge.valid →
      decodeCSpaceMintArgs (stubDecoded (encodeCSpaceMintArgs args)) = .ok args) ∧
    (∀ args : CSpaceCopyArgs, args.destDepth < 256 → args.srcDepth < 256 →
      args.rights.valid →
      decodeCSpaceCopyArgs (stubDecoded (encodeCSpaceCopyArgs args)) = .ok args) ∧
    (∀ args : CSpaceMoveArgs, args.destDepth < 256 → args.srcDepth < 256 →
      decodeCSpaceMoveArgs (stubDecoded (encodeCSpaceMoveArgs args)) = .ok args) ∧
    (∀ args, decodeCSpaceDeleteArgs (stubDecoded (encodeCSpaceDeleteArgs args)) = .ok args) ∧
    (∀ args, decodeUntypedRetypeArgs (stubDecoded (encodeUntypedRetypeArgs args)) = .ok args) ∧
    (∀ args, args.asid.isValidForConfig maxASID = true → args.vaddr.isCanonical = true →
      args.perms.wxCompliant = true →
      decodeVSpaceMapArgs (stubDecoded (encodeVSpaceMapArgs args)) maxASID = .ok args) ∧
    (∀ args, args.asid.isValidForConfig maxASID = true → args.vaddr.isCanonical = true →
      decodeVSpaceUnmapArgs (stubDecoded (encodeVSpaceUnmapArgs args)) maxASID = .ok args) ∧
    (∀ args,
      args.methodCount ≤ serviceMaxMethodCount →
      args.maxMessageSize ≤ serviceMaxMessageSize →
      args.maxResponseSize ≤ serviceMaxMessageSize →
      decodeServiceRegisterArgs (stubDecoded (encodeServiceRegisterArgs args)) = .ok args) ∧
    (∀ args, decodeNotificationWaitArgs (stubDecoded (encodeNotificationWaitArgs args)) = .ok args) ∧
    (∀ args, decodeReplyRecvArgs (stubDecoded (encodeReplyRecvArgs args)) = .ok args) ∧
    (∀ args, decodeRecvArgs (stubDecoded (encodeRecvArgs args)) = .ok args) ∧
    (∀ args, decodeSchedContextConfigureArgs (stubDecoded (encodeSchedContextConfigureArgs args)) = .ok args) ∧
    (∀ args, decodeSchedContextBindArgs (stubDecoded (encodeSchedContextBindArgs args)) = .ok args) ∧
    (∀ args, decodeSchedContextUnbindArgs (stubDecoded (encodeSchedContextUnbindArgs args)) = .ok args) :=
  ⟨decodeCSpaceMintArgs_roundtrip,
   decodeCSpaceCopyArgs_roundtrip,
   decodeCSpaceMoveArgs_roundtrip,
   decodeCSpaceDeleteArgs_roundtrip,
   decodeUntypedRetypeArgs_roundtrip,
   fun args hA hV hWx => decodeVSpaceMapArgs_roundtrip args maxASID hA hV hWx,
   fun args hA hV => decodeVSpaceUnmapArgs_roundtrip args maxASID hA hV,
   fun args hMc hMms hMrs => decodeServiceRegisterArgs_roundtrip args hMc hMms hMrs,
   decodeNotificationWaitArgs_roundtrip,
   decodeReplyRecvArgs_roundtrip,
   decodeRecvArgs_roundtrip,
   decodeSchedContextConfigureArgs_roundtrip,
   decodeSchedContextBindArgs_roundtrip,
   decodeSchedContextUnbindArgs_roundtrip⟩

/-- V2-I: ReplyRecvArgs error exclusivity. -/
theorem decodeReplyRecvArgs_error_iff (d : SyscallDecodeResult) :
    (∃ e, decodeReplyRecvArgs d = .error e) ↔ d.msgRegs.size < 1 := by
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 1
    · exact hlt
    · exfalso
      simp only [decodeReplyRecvArgs, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeReplyRecvArgs, bind, Except.bind]
    rw [requireMsgReg_unfold_err _ _ (by omega)]

-- ============================================================================
-- Z8-B: SchedContext error-exclusivity theorems
-- ============================================================================

/-- Z8-B: SchedContextConfigureArgs decode fails iff fewer than 5 message registers. -/
theorem decodeSchedContextConfigureArgs_error_iff (d : SyscallDecodeResult) (hLen : truncationMinimum .schedContextConfigure ≤ d.msgInfo.length) :
    (∃ e, decodeSchedContextConfigureArgs d = .error e) ↔ d.msgRegs.size < 5 := by
  have hL := requireMessageLength_of_le hLen
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 5
    · exact hlt
    · exfalso
      simp only [decodeSchedContextConfigureArgs, hL, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        dif_pos (show 1 < d.msgRegs.size by omega),
        dif_pos (show 2 < d.msgRegs.size by omega),
        dif_pos (show 3 < d.msgRegs.size by omega),
        dif_pos (show 4 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeSchedContextConfigureArgs, hL, bind, Except.bind]
    by_cases h0 : 0 < d.msgRegs.size
    · rw [requireMsgReg_unfold_ok _ _ h0]; simp
      by_cases h1 : 1 < d.msgRegs.size
      · rw [requireMsgReg_unfold_ok _ _ h1]; simp
        by_cases h2 : 2 < d.msgRegs.size
        · rw [requireMsgReg_unfold_ok _ _ h2]; simp
          by_cases h3 : 3 < d.msgRegs.size
          · rw [requireMsgReg_unfold_ok _ _ h3]; simp
            rw [requireMsgReg_unfold_err _ _ (by omega)]
          · rw [requireMsgReg_unfold_err _ _ h3]
        · rw [requireMsgReg_unfold_err _ _ h2]
      · rw [requireMsgReg_unfold_err _ _ h1]
    · rw [requireMsgReg_unfold_err _ _ h0]

/-- Z8-B: SchedContextBindArgs decode fails iff fewer than 1 message register. -/
theorem decodeSchedContextBindArgs_error_iff (d : SyscallDecodeResult) (hLen : truncationMinimum .schedContextBind ≤ d.msgInfo.length) :
    (∃ e, decodeSchedContextBindArgs d = .error e) ↔ d.msgRegs.size < 1 := by
  have hL := requireMessageLength_of_le hLen
  constructor
  · intro ⟨e, he⟩
    by_cases hlt : d.msgRegs.size < 1
    · exact hlt
    · exfalso
      simp only [decodeSchedContextBindArgs, hL, bind, Except.bind,
        requireMsgReg, dif_pos (show 0 < d.msgRegs.size by omega),
        pure, Except.pure] at he
      nomatch he
  · intro h
    refine ⟨.invalidMessageInfo, ?_⟩
    simp only [decodeSchedContextBindArgs, hL, bind, Except.bind]
    rw [requireMsgReg_unfold_err _ _ (by omega)]

/-- Z8-B: SchedContextUnbindArgs decode never fails (no message registers required). -/
theorem decodeSchedContextUnbindArgs_error_iff (d : SyscallDecodeResult) :
    ¬(∃ e, decodeSchedContextUnbindArgs d = .error e) := by
  intro ⟨e, he⟩
  simp only [decodeSchedContextUnbindArgs, pure, Except.pure] at he
  nomatch he

-- ============================================================================
-- X4-F/M-8: Platform-specific regCount validation
-- ============================================================================

/-- X4-F/M-8: ARM64 register count correctness.
    Confirms that the default `regCount := 32` used by `decodeSyscallArgs`
    matches the architectural GPR count defined in `Machine.lean`.
    ARM64 AAPCS64: x0–x30 (31 general-purpose) + xzr (zero register) = 32 indices.
    Register index 31 (xzr) is the last valid index; index 32 is correctly
    rejected by `validateRegBound`.

    If targeting a non-ARM64 platform with a different register file width,
    `regCount` must be updated to match `RegName.arm64GPRCount` (or its
    platform-specific equivalent) and this theorem must be re-proven. -/
theorem arm64_regCount_valid :
    32 = RegName.arm64GPRCount := rfl

/-- X4-F/M-8: The `MachineConfig.registerCount` default value equals the
    ARM64 GPR count, ensuring configuration-level consistency.
    Any `MachineConfig` using the default `registerCount` field is aligned
    with the ARM64 architecture. -/
theorem machineConfig_registerCount_default_eq_arm64GPRCount :
    ({ registerWidth := 64, virtualAddressWidth := 48,
       physicalAddressWidth := 40, pageSize := 4096,
       maxASID := 65536, memoryMap := [] } : MachineConfig).registerCount
    = RegName.arm64GPRCount := rfl

-- ============================================================================
-- D1-B: Thread suspend/resume argument structures
-- ============================================================================

/-- D1-B: Per-syscall argument structure for `tcbSuspend`.
    No additional arguments — the target thread comes from the capability target.
    The capability must target a TCB object. -/
structure SuspendArgs where
  deriving Repr, DecidableEq

/-- D1-B: Per-syscall argument structure for `tcbResume`.
    No additional arguments — the target thread comes from the capability target.
    The capability must target a TCB object. -/
structure ResumeArgs where
  deriving Repr, DecidableEq

/-- D1-B: Decode suspend arguments. No message registers needed. -/
def decodeSuspendArgs (_decoded : SyscallDecodeResult)
    : Except KernelError SuspendArgs :=
  pure {}

/-- D1-B: Decode resume arguments. No message registers needed. -/
def decodeResumeArgs (_decoded : SyscallDecodeResult)
    : Except KernelError ResumeArgs :=
  pure {}

/-- D1-B: Encode suspend arguments (empty — no message registers). -/
@[inline] def encodeSuspendArgs (_args : SuspendArgs) : Array RegValue := #[]

/-- D1-B: Encode resume arguments (empty — no message registers). -/
@[inline] def encodeResumeArgs (_args : ResumeArgs) : Array RegValue := #[]

/-- D1-B: SuspendArgs decode round-trip (trivial). -/
theorem decodeSuspendArgs_roundtrip (args : SuspendArgs) :
    decodeSuspendArgs (stubDecoded (encodeSuspendArgs args)) = .ok args := by
  rcases args; rfl

/-- D1-B: ResumeArgs decode round-trip (trivial). -/
theorem decodeResumeArgs_roundtrip (args : ResumeArgs) :
    decodeResumeArgs (stubDecoded (encodeResumeArgs args)) = .ok args := by
  rcases args; rfl

-- ============================================================================
-- D2-C: Priority management argument structures
-- ============================================================================

/-- D2-C: Per-syscall argument structure for `tcbSetPriority`.
    Register mapping: x2=newPriority. The target thread comes from the
    capability target. -/
structure SetPriorityArgs where
  newPriority : Nat
  deriving Repr, DecidableEq

/-- D2-C: Per-syscall argument structure for `tcbSetMCPriority`.
    Register mapping: x2=newMCP. The target thread comes from the
    capability target. -/
structure SetMCPriorityArgs where
  newMCP : Nat
  deriving Repr, DecidableEq

-- ============================================================================
-- D2-C: Priority management decode functions
-- ============================================================================

/-- D2-C: Decode setPriority arguments from message registers.
    Requires 1 message register (newPriority). Validates that the priority
    value is within the valid range (≤ 0xFF). -/
def decodeSetPriorityArgs (decoded : SyscallDecodeResult)
    : Except KernelError SetPriorityArgs := do
  requireMessageLength decoded (truncationMinimum .tcbSetPriority)
  let r0 ← requireMsgReg decoded.msgRegs 0
  if r0.val > 0xFF then .error .invalidArgument
  else pure { newPriority := r0.val }

/-- D2-C: Decode setMCPriority arguments from message registers.
    Requires 1 message register (newMCP). Validates that the MCP
    value is within the valid range (≤ 0xFF). -/
def decodeSetMCPriorityArgs (decoded : SyscallDecodeResult)
    : Except KernelError SetMCPriorityArgs := do
  requireMessageLength decoded (truncationMinimum .tcbSetMCPriority)
  let r0 ← requireMsgReg decoded.msgRegs 0
  if r0.val > 0xFF then .error .invalidArgument
  else pure { newMCP := r0.val }

-- ============================================================================
-- D2-C: Priority management encode functions
-- ============================================================================

/-- D2-C: Encode setPriority arguments into message registers. -/
@[inline] def encodeSetPriorityArgs (args : SetPriorityArgs) : Array RegValue :=
  #[⟨args.newPriority⟩]

/-- D2-C: Encode setMCPriority arguments into message registers. -/
@[inline] def encodeSetMCPriorityArgs (args : SetMCPriorityArgs) : Array RegValue :=
  #[⟨args.newMCP⟩]

-- ============================================================================
-- D2-C: Priority management round-trip theorems
-- ============================================================================

/-- D2-C: SetPriorityArgs decode round-trip for in-range values. -/
theorem decodeSetPriorityArgs_roundtrip (args : SetPriorityArgs) (h : args.newPriority ≤ 0xFF) :
    decodeSetPriorityArgs (stubDecoded (encodeSetPriorityArgs args)) = .ok args := by
  simp [requireMessageLength, truncationMinimum, decodeSetPriorityArgs, encodeSetPriorityArgs, stubDecoded, requireMsgReg, Bind.bind,
        Except.bind, Pure.pure, Except.pure, show ¬(args.newPriority > 0xFF) from Nat.not_lt.mpr h]

/-- D2-C: SetMCPriorityArgs decode round-trip for in-range values. -/
theorem decodeSetMCPriorityArgs_roundtrip (args : SetMCPriorityArgs) (h : args.newMCP ≤ 0xFF) :
    decodeSetMCPriorityArgs (stubDecoded (encodeSetMCPriorityArgs args)) = .ok args := by
  simp [requireMessageLength, truncationMinimum, decodeSetMCPriorityArgs, encodeSetMCPriorityArgs, stubDecoded, requireMsgReg, Bind.bind,
        Except.bind, Pure.pure, Except.pure, show ¬(args.newMCP > 0xFF) from Nat.not_lt.mpr h]

-- ============================================================================
-- D3-B: IPC buffer configuration decode
-- ============================================================================

/-- D3-B: Per-syscall argument structure for `tcbSetIPCBuffer`.
    Register mapping: x2=bufferAddr. The target thread comes from the
    capability target. The buffer address must be 512-byte aligned
    (matching seL4's `seL4_IPCBufferSizeBits = 9`). -/
structure SetIPCBufferArgs where
  bufferAddr : SeLe4n.VAddr
  deriving Repr, DecidableEq

/-- D3-B: Decode setIPCBuffer arguments from message registers.
    Requires 1 message register (bufferAddr). Validates alignment:
    `bufferAddr.toNat % ipcBufferAlignment = 0`. -/
def decodeSetIPCBufferArgs (decoded : SyscallDecodeResult)
    : Except KernelError SetIPCBufferArgs := do
  requireMessageLength decoded (truncationMinimum .tcbSetIPCBuffer)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let addr := SeLe4n.VAddr.ofNat r0.val
  if addr.toNat % SeLe4n.ipcBufferAlignment != 0 then .error .alignmentError
  else pure { bufferAddr := addr }

/-- D3-B: Encode setIPCBuffer arguments into message registers. -/
@[inline] def encodeSetIPCBufferArgs (args : SetIPCBufferArgs) : Array RegValue :=
  #[⟨args.bufferAddr.toNat⟩]

-- ============================================================================
-- D3-B: IPC buffer configuration round-trip theorem
-- ============================================================================

/-- D3-B: SetIPCBufferArgs decode round-trip for aligned addresses. -/
theorem decodeSetIPCBufferArgs_roundtrip (args : SetIPCBufferArgs)
    (hAligned : args.bufferAddr.toNat % SeLe4n.ipcBufferAlignment = 0) :
    decodeSetIPCBufferArgs (stubDecoded (encodeSetIPCBufferArgs args)) = .ok args := by
  simp only [requireMessageLength, truncationMinimum, decodeSetIPCBufferArgs, encodeSetIPCBufferArgs, stubDecoded, requireMsgReg,
        Bind.bind, Except.bind, Pure.pure, Except.pure,
        SeLe4n.VAddr.ofNat, SeLe4n.VAddr.toNat] at *
  simp [hAligned]

-- ============================================================================
-- WS-SM SM5.H.4: CPU-affinity configuration decode (`tcbSetAffinity`)
-- ============================================================================

/-- WS-SM SM5.H.4: per-syscall argument structure for `tcbSetAffinity`.
    Register mapping: x2 = the raw affinity word.  Values `0 .. numCores-1` bind the
    target thread to that core; the marker `numCores` unbinds it (homed on the boot core).
    The target thread comes from the capability target.  The raw value is range-validated
    downstream by `decodeAffinity` (which produces the typed `Option CoreId`). -/
structure SetAffinityArgs where
  affinityRaw : Nat
  deriving Repr, DecidableEq

/-- WS-SM SM5.H.4: decode `tcbSetAffinity` arguments from message registers.
    Requires 1 message register (the raw affinity word).  The semantic range check
    (`< numCores`, or the unbind marker) is `decodeAffinity`'s responsibility, so the
    decode itself only extracts the raw word. -/
def decodeSetAffinityArgs (decoded : SyscallDecodeResult)
    : Except KernelError SetAffinityArgs := do
  requireMessageLength decoded (truncationMinimum .tcbSetAffinity)
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { affinityRaw := r0.val }

/-- WS-SM SM5.H.4: encode `tcbSetAffinity` arguments into message registers. -/
@[inline] def encodeSetAffinityArgs (args : SetAffinityArgs) : Array RegValue :=
  #[⟨args.affinityRaw⟩]

/-- WS-SM SM5.H.4: SetAffinityArgs decode round-trip. -/
theorem decodeSetAffinityArgs_roundtrip (args : SetAffinityArgs) :
    decodeSetAffinityArgs (stubDecoded (encodeSetAffinityArgs args)) = .ok args := by
  simp [requireMessageLength, truncationMinimum, decodeSetAffinityArgs, encodeSetAffinityArgs, stubDecoded, requireMsgReg, Bind.bind,
        Except.bind, Pure.pure, Except.pure]

-- ============================================================================
-- Review round (PR #887): fault-handler configuration decode (`tcbSetFaultHandler`)
-- ============================================================================

/-- Per-syscall argument structure for `tcbSetFaultHandler`.
    Register mapping: x2 = the fault-handler CPtr, interpreted in the **target
    thread's** CSpace (seL4's `fault_ep`).  The target thread comes from the
    capability target; the CPtr is validated downstream by
    `setThreadFaultHandlerOp` (it must resolve to an endpoint capability
    carrying send and grant-or-grant-reply). -/
structure SetFaultHandlerArgs where
  handlerCPtr : SeLe4n.CPtr
  deriving Repr, DecidableEq

/-- Decode `tcbSetFaultHandler` arguments from message registers.  Requires 1
    message register (the CPtr word). -/
def decodeSetFaultHandlerArgs (decoded : SyscallDecodeResult)
    : Except KernelError SetFaultHandlerArgs := do
  requireMessageLength decoded (truncationMinimum .tcbSetFaultHandler)
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { handlerCPtr := SeLe4n.CPtr.ofNat r0.val }

/-- Encode `tcbSetFaultHandler` arguments into message registers. -/
@[inline] def encodeSetFaultHandlerArgs (args : SetFaultHandlerArgs) : Array RegValue :=
  #[⟨args.handlerCPtr.toNat⟩]

/-- SetFaultHandlerArgs decode round-trip. -/
theorem decodeSetFaultHandlerArgs_roundtrip (args : SetFaultHandlerArgs) :
    decodeSetFaultHandlerArgs (stubDecoded (encodeSetFaultHandlerArgs args)) = .ok args := by
  simp [requireMessageLength, truncationMinimum, decodeSetFaultHandlerArgs, encodeSetFaultHandlerArgs, stubDecoded, requireMsgReg,
        Bind.bind, Except.bind, Pure.pure, Except.pure, SeLe4n.CPtr.ofNat_toNat]

-- ============================================================================
-- WS-SM SM9.A.10: audit-trail read and drain arguments
-- ============================================================================

/-- WS-SM SM9.A.10: `auditRead` arguments.
    Register mapping: x2=opcode, x3=index, x4=chunk.

    The sub-operation and the field it selects share the **opcode** rather than
    taking a register each: `AuditReadOp.field` needs three coordinates (index,
    field, chunk) and a fourth operand register would buy nothing, since the
    field space is four values and the opcode space is free.  The semantic range
    check is `decodeAuditReadOp`'s responsibility (fail-closed on an unknown
    opcode), so the decode itself only extracts the three raw words. -/
structure AuditReadArgs where
  opcode : Nat
  index : Nat
  chunk : Nat
  deriving Repr, DecidableEq

/-- WS-SM SM9.A.10: decode `auditRead` arguments from message registers.
    Requires 3 message registers. -/
def decodeAuditReadArgs (decoded : SyscallDecodeResult)
    : Except KernelError AuditReadArgs := do
  requireMessageLength decoded (truncationMinimum .auditRead)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  let r2 ← requireMsgReg decoded.msgRegs 2
  pure { opcode := r0.val, index := r1.val, chunk := r2.val }

/-- WS-SM SM9.A.10: encode `auditRead` arguments into message registers. -/
@[inline] def encodeAuditReadArgs (args : AuditReadArgs) : Array RegValue :=
  #[⟨args.opcode⟩, ⟨args.index⟩, ⟨args.chunk⟩]

/-- WS-SM SM9.A.10: AuditReadArgs decode round-trip. -/
theorem decodeAuditReadArgs_roundtrip (args : AuditReadArgs) :
    decodeAuditReadArgs (stubDecoded (encodeAuditReadArgs args)) = .ok args := by
  simp [decodeAuditReadArgs, encodeAuditReadArgs, stubDecoded, requireMsgReg, requireMessageLength,
        truncationMinimum, Bind.bind, Except.bind, Pure.pure, Except.pure]

/-- WS-SM SM9.A.10: `auditDrain` arguments.
    Register mapping: x2=count (entries to remove).

    A `count` at or above the trail's length clears it, which is the call a
    monitor recovering from the capacity cliff makes. -/
structure AuditDrainArgs where
  count : Nat
  deriving Repr, DecidableEq

/-- WS-SM SM9.A.10: decode `auditDrain` arguments from message registers.
    Requires 1 message register. -/
def decodeAuditDrainArgs (decoded : SyscallDecodeResult)
    : Except KernelError AuditDrainArgs := do
  requireMessageLength decoded (truncationMinimum .auditDrain)
  let r0 ← requireMsgReg decoded.msgRegs 0
  pure { count := r0.val }

/-- WS-SM SM9.A.10: encode `auditDrain` arguments into message registers. -/
@[inline] def encodeAuditDrainArgs (args : AuditDrainArgs) : Array RegValue :=
  #[⟨args.count⟩]

/-- WS-SM SM9.A.10: AuditDrainArgs decode round-trip. -/
theorem decodeAuditDrainArgs_roundtrip (args : AuditDrainArgs) :
    decodeAuditDrainArgs (stubDecoded (encodeAuditDrainArgs args)) = .ok args := by
  simp [decodeAuditDrainArgs, encodeAuditDrainArgs, stubDecoded, requireMsgReg, requireMessageLength,
        truncationMinimum, Bind.bind, Except.bind, Pure.pure, Except.pure]


-- ============================================================================
-- WS-BP BP7.1 (`v0.36.11`): thread-space configuration decode (`tcbSetSpace`)
-- ============================================================================

/-- WS-BP BP7.1 (`v0.36.11`): per-syscall argument structure for `tcbSetSpace`
    — seL4's `TCB_SetSpace`.  Register mapping: x2 = the address, in the
    caller's CSpace, of a capability to the new **CSpace root** (a CNode); x3 =
    the address of a capability to the new **VSpace root**.  The target thread
    comes from the invoked capability. -/
structure SetSpaceArgs where
  cspaceRoot : SeLe4n.CPtr
  vspaceRoot : SeLe4n.CPtr
  deriving Repr, DecidableEq

/-- WS-BP BP7.1: decode `tcbSetSpace` arguments.  Requires 2 message registers. -/
def decodeSetSpaceArgs (decoded : SyscallDecodeResult)
    : Except KernelError SetSpaceArgs := do
  requireMessageLength decoded (truncationMinimum .tcbSetSpace)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  pure { cspaceRoot := SeLe4n.CPtr.ofNat r0.val, vspaceRoot := SeLe4n.CPtr.ofNat r1.val }

/-- WS-BP BP7.1: encode `tcbSetSpace` arguments into message registers. -/
@[inline] def encodeSetSpaceArgs (args : SetSpaceArgs) : Array RegValue :=
  #[⟨args.cspaceRoot.toNat⟩, ⟨args.vspaceRoot.toNat⟩]

/-- WS-BP BP7.1: SetSpaceArgs decode round-trip. -/
theorem decodeSetSpaceArgs_roundtrip (args : SetSpaceArgs) :
    decodeSetSpaceArgs (stubDecoded (encodeSetSpaceArgs args)) = .ok args := by
  simp [requireMessageLength, truncationMinimum, decodeSetSpaceArgs, encodeSetSpaceArgs, stubDecoded, requireMsgReg, Bind.bind,
        Except.bind, Pure.pure, Except.pure, SeLe4n.CPtr.ofNat_toNat]

-- ============================================================================
-- WS-BP BP7.1 (`v0.36.12`): page-table install decode (`pageTableMap`)
-- ============================================================================

/-- WS-BP BP7.1 (`v0.36.12`): per-syscall argument structure for `pageTableMap`
    — seL4's `seL4_ARM_PageTable_Map`.  Register mapping: x2 = the address, in
    the caller's CSpace, of a capability to the **address space** the table is
    installed in (a VSpace root); x3 = a virtual address whose walk the table
    serves.  The table comes from the invoked capability. -/
structure PageTableMapArgs where
  vspaceRoot : SeLe4n.CPtr
  vaddr : SeLe4n.VAddr
  deriving Repr, DecidableEq

/-- WS-BP BP7.1: decode `pageTableMap` arguments.  Requires 2 message registers. -/
def decodePageTableMapArgs (decoded : SyscallDecodeResult)
    : Except KernelError PageTableMapArgs := do
  requireMessageLength decoded (truncationMinimum .pageTableMap)
  let r0 ← requireMsgReg decoded.msgRegs 0
  let r1 ← requireMsgReg decoded.msgRegs 1
  pure { vspaceRoot := SeLe4n.CPtr.ofNat r0.val, vaddr := SeLe4n.VAddr.ofNat r1.val }

/-- WS-BP BP7.1: encode `pageTableMap` arguments into message registers. -/
@[inline] def encodePageTableMapArgs (args : PageTableMapArgs) : Array RegValue :=
  #[⟨args.vspaceRoot.toNat⟩, ⟨args.vaddr.toNat⟩]

/-- WS-BP BP7.1: PageTableMapArgs decode round-trip. -/
theorem decodePageTableMapArgs_roundtrip (args : PageTableMapArgs) :
    decodePageTableMapArgs (stubDecoded (encodePageTableMapArgs args)) = .ok args := by
  simp [requireMessageLength, truncationMinimum, decodePageTableMapArgs, encodePageTableMapArgs, stubDecoded, requireMsgReg, Bind.bind,
        Except.bind, Pure.pure, Except.pure, SeLe4n.CPtr.ofNat_toNat,
        SeLe4n.VAddr.ofNat, SeLe4n.VAddr.toNat]

-- ============================================================================
-- WS-ZA ZA5.1: the decoders over the caller's register file
-- ============================================================================

/-- A reader of message register `i`'s word.  The register-routed arms read the
caller's register file itself (`msgRegOfFile`): no message-register array is
built, and a word `≥ 2^63` — a capability address — is never a number. -/
abbrev MsgRegReader := Nat → Except KernelError UInt64

/-- Message register `i`'s word read straight from a register file through a
layout, refusing an index past the layout's registers as `requireMsgReg` does. -/
@[inline] def msgRegOfFile (layout : SyscallRegisterLayout) (regs : RegisterFile) :
    MsgRegReader :=
  fun i => if h : i < layout.msgRegs.size then .ok (readRegWord regs layout.msgRegs[i])
    else .error .invalidMessageInfo

/-- A decode whose message registers are the layout's, read from the file, reads
each as the number of the file's word. -/
theorem requireMsgReg_map_readReg (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (i : Nat) :
    requireMsgReg (layout.msgRegs.map (readReg regs)) i =
      (msgRegOfFile layout regs i).map (fun w => (⟨w.toNat⟩ : RegValue)) := by
  unfold requireMsgReg msgRegOfFile
  by_cases hi : i < layout.msgRegs.size
  · simp only [Array.size_map, hi, ↓reduceDIte, Array.getElem_map, readReg_eq_word,
      Except.map]
  · simp only [Array.size_map, hi, ↓reduceDIte, Except.map]

/-- Two message-register arrays read alike below index `k`: each decoder below
reads no register at or past its own bound, so a decode whose registers run on
into overflow words decodes as one holding only the registers below it. -/
def MsgRegsAgreeBelow (a b : Array RegValue) (k : Nat) : Prop :=
  ∀ i, i < k → requireMsgReg a i = requireMsgReg b i

theorem MsgRegsAgreeBelow.of_eq {a b : Array RegValue} (h : a = b) (k : Nat) :
    MsgRegsAgreeBelow a b k := fun _ _ => by rw [h]

/-- An array and the same array with words appended read alike below its size. -/
theorem MsgRegsAgreeBelow.append (a extra : Array RegValue) :
    MsgRegsAgreeBelow (a ++ extra) a a.size := by
  intro i hi
  unfold requireMsgReg
  have hi' : i < (a ++ extra).size := by simp only [Array.size_append]; omega
  simp only [hi, hi', ↓reduceDIte, Array.getElem_append_left hi]

/-- An array and the same array with one word and then more appended read
alike, below one past its size, as the array with that one word appended. -/
theorem MsgRegsAgreeBelow.append_cons (a : Array RegValue) (x : RegValue)
    (rest : List RegValue) :
    MsgRegsAgreeBelow (a ++ (x :: rest).toArray) (a ++ #[x]) (a.size + 1) := by
  intro i hi
  unfold requireMsgReg
  have h1 : i < (a ++ (x :: rest).toArray).size := by
    simp only [Array.size_append, List.size_toArray, List.length_cons]; omega
  have h2 : i < (a ++ #[x]).size := by
    simp only [Array.size_append, List.size_toArray, List.length_singleton]; omega
  rw [dif_pos h1, dif_pos h2]
  by_cases hl : i < a.size
  · rw [Array.getElem_append_left hl, Array.getElem_append_left hl]
  · have hi' : i = a.size := by omega
    subst hi'
    simp [Array.getElem_append_right]

/-! Each decoder below is its `SyscallDecodeResult` form read from the register
file: equal to it whenever the decode's message registers are the layout's, read
from the file (the `_eq_by` theorems).  Capability addresses are built from the
word (`CPtr.ofWord`), every other field from its number, as the decode does. -/

@[inline] def decodeCSpaceCopyArgsBy (get : MsgRegReader)
    : Except KernelError CSpaceCopyArgs := do
  let r0 ← get 0
  let r1 ← get 1
  let r2 ← get 2
  let r3 ← get 3
  cnodeCopyArgsOfWords (CPtr.ofWord r0) (CPtr.ofWord r1) (CPtr.ofWord r2) r3.toNat

theorem decodeCSpaceCopyArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .cspaceCopy ≤ decoded.msgInfo.length) :
    decodeCSpaceCopyArgs decoded = decodeCSpaceCopyArgsBy (msgRegOfFile layout regs) := by
  unfold decodeCSpaceCopyArgs decodeCSpaceCopyArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat]

@[inline] def decodeCSpaceMoveArgsBy (get : MsgRegReader)
    : Except KernelError CSpaceMoveArgs := do
  let r0 ← get 0
  let r1 ← get 1
  let r2 ← get 2
  let r3 ← get 3
  cnodeOpArgsOfWords (CPtr.ofWord r0) (CPtr.ofWord r1) (CPtr.ofWord r2) r3.toNat

theorem decodeCSpaceMoveArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .cspaceMove ≤ decoded.msgInfo.length) :
    decodeCSpaceMoveArgs decoded = decodeCSpaceMoveArgsBy (msgRegOfFile layout regs) := by
  unfold decodeCSpaceMoveArgs decodeCSpaceMoveArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat]

@[inline] def decodeMintReplyCapArgsBy (get : MsgRegReader)
    : Except KernelError MintReplyCapArgs := do
  let r0 ← get 0
  let r1 ← get 1
  pure { srcSlot := Slot.ofNat r0.toNat, dstSlot := Slot.ofNat r1.toNat }

theorem decodeMintReplyCapArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .mintReplyCap ≤ decoded.msgInfo.length) :
    decodeMintReplyCapArgs decoded = decodeMintReplyCapArgsBy (msgRegOfFile layout regs) := by
  unfold decodeMintReplyCapArgs decodeMintReplyCapArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map]

@[inline] def decodeCSpaceDeleteArgsBy (get : MsgRegReader)
    : Except KernelError CSpaceDeleteArgs := do
  let r0 ← get 0
  pure { targetSlot := Slot.ofNat r0.toNat }

theorem decodeCSpaceDeleteArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .cspaceDelete ≤ decoded.msgInfo.length) :
    decodeCSpaceDeleteArgs decoded = decodeCSpaceDeleteArgsBy (msgRegOfFile layout regs) := by
  unfold decodeCSpaceDeleteArgs decodeCSpaceDeleteArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeUntypedRetypeArgsBy (get : MsgRegReader)
    : Except KernelError UntypedRetypeArgs := do
  let r0 ← get 0
  let r1 ← get 1
  let r2 ← get 2
  let r3 ← get 3
  match KernelObjectType.ofNat? (r0.toNat % 256) with
  | some objType =>
    pure { newType  := objType
           sizeBits := r0.toNat / 256
           childId  := ObjId.ofNat r1.toNat
           dstCNode := CPtr.ofWord r2
           dstSlot  := Slot.ofNat r3.toNat }
  | none => .error .invalidTypeTag

theorem decodeUntypedRetypeArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .untypedRetype ≤ decoded.msgInfo.length) :
    decodeUntypedRetypeArgs decoded = decodeUntypedRetypeArgsBy (msgRegOfFile layout regs) := by
  unfold decodeUntypedRetypeArgs decodeUntypedRetypeArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeVSpaceMapArgsBy (get : MsgRegReader) (maxASID : Nat)
    : Except KernelError VSpaceMapArgs := do
  let r0 ← get 0
  let r1 ← get 1
  let r2 ← get 2
  let r3 ← get 3
  let asid := ASID.ofNat r0.toNat
  if !asid.isValidForConfig maxASID then .error .asidNotBound
  else
  let vaddr := VAddr.ofNat r1.toNat
  if !vaddr.isCanonical then .error .addressOutOfBounds
  else
    match PagePermissions.ofNat? r3.toNat with
    | some perms =>
      pure { asid  := asid
             vaddr := vaddr
             frame := CPtr.ofWord r2
             perms := perms }
    | none => .error .invalidSyscallArgument

theorem decodeVSpaceMapArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult) (maxASID : Nat)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .vspaceMap ≤ decoded.msgInfo.length) :
    decodeVSpaceMapArgs decoded maxASID = decodeVSpaceMapArgsBy (msgRegOfFile layout regs) maxASID := by
  unfold decodeVSpaceMapArgs decodeVSpaceMapArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeVSpaceUnmapArgsBy (get : MsgRegReader) (maxASID : Nat)
    : Except KernelError VSpaceUnmapArgs := do
  let r0 ← get 0
  let r1 ← get 1
  let asid := ASID.ofNat r0.toNat
  if !asid.isValidForConfig maxASID then .error .asidNotBound
  else
  let vaddr := VAddr.ofNat r1.toNat
  if !vaddr.isCanonical then .error .addressOutOfBounds
  else
  pure { asid  := asid
         vaddr := vaddr }

theorem decodeVSpaceUnmapArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult) (maxASID : Nat)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .vspaceUnmap ≤ decoded.msgInfo.length) :
    decodeVSpaceUnmapArgs decoded maxASID = decodeVSpaceUnmapArgsBy (msgRegOfFile layout regs) maxASID := by
  unfold decodeVSpaceUnmapArgs decodeVSpaceUnmapArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeSchedContextBindArgsBy (get : MsgRegReader)
    : Except KernelError SchedContextBindArgs := do
  let r0 ← get 0
  pure { tcbCPtr := SeLe4n.CPtr.ofWord r0 }

theorem decodeSchedContextBindArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .schedContextBind ≤ decoded.msgInfo.length) :
    decodeSchedContextBindArgs decoded = decodeSchedContextBindArgsBy (msgRegOfFile layout regs) := by
  unfold decodeSchedContextBindArgs decodeSchedContextBindArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

/-- WS-ZA ZA5.2: message register `i`'s word for a call whose one overflow word
`w` follows the layout's registers: the file's registers, then `w`, refusing any
later index as `requireMsgReg` does past a decode's registers. -/
@[inline] def msgRegOfFileThen (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (w : UInt64) : MsgRegReader :=
  fun i => if h : i < layout.msgRegs.size then .ok (readRegWord regs layout.msgRegs[i])
    else if i = layout.msgRegs.size then .ok w
    else .error .invalidMessageInfo

/-- A decode whose message registers are the layout's, read from the file, then
one overflow word, reads each as the number of its word. -/
theorem requireMsgReg_map_readReg_push (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (w : UInt64) (i : Nat) :
    requireMsgReg (layout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]) i =
      (msgRegOfFileThen layout regs w i).map (fun w => (⟨w.toNat⟩ : RegValue)) := by
  unfold requireMsgReg msgRegOfFileThen
  by_cases hi : i < layout.msgRegs.size
  · have hi' : i < (layout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]).size := by
      simp only [Array.size_append, Array.size_map, List.size_toArray, List.length_singleton]
      omega
    simp only [hi, hi', ↓reduceDIte, Except.map]
    rw [Array.getElem_append_left (by simpa using hi)]
    simp only [Array.getElem_map, readReg_eq_word]
  · by_cases hEq : i = layout.msgRegs.size
    · subst hEq
      simp [Except.map, Array.getElem_push]
    · have hi' : ¬ i < (layout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]).size := by
        simp only [Array.size_append, Array.size_map, List.size_toArray, List.length_singleton]
        omega
      simp only [hi, hi', hEq, ↓reduceDIte, ↓reduceIte, Except.map]

/-- WS-ZA ZA6.4: the parameter word sets a bit above the domain's (bit 12 or
higher, which includes every out-of-range domain) exactly when it is at least
`16 * 256`: the check read on the machine word, so a word of any value is
compared without a heap number. -/
theorem schedParams_ge_iff (w : UInt64) : 4096 ≤ w.toNat ↔ 4096 ≤ w := by
  rw [UInt64.le_iff_toNat_le]
  simp only [UInt64.toNat_ofNat]

/-- WS-ZA ZA5.2: `decodeSchedContextConfigureArgsChecked` over a reader, each
check in the decode's order.  WS-ZA ZA6.4: the context capability's address is
read as its word (`CPtr.ofWord`), as the bind reads its thread's. -/
@[inline] def decodeSchedContextConfigureArgsCheckedBy (get : MsgRegReader)
    : Except KernelError SchedContextConfigureArgs := do
  let r0 ← get 0
  let r1 ← get 1
  let r2 ← get 2
  let r3 ← get 3
  let r4 ← get 4
  if 4096 ≤ r3 then .error .invalidArgument
  else if r1.toNat = 0 then .error .invalidArgument
  else if r2.toNat = 0 then .error .invalidArgument
  else pure { scCPtr := SeLe4n.CPtr.ofWord r0, budget := r1.toNat, period := r2.toNat,
              schedParams := r3.toNat, deadline := r4.toNat }

theorem decodeSchedContextConfigureArgsChecked_eq_by (layout : SyscallRegisterLayout)
    (regs : RegisterFile) (w : UInt64) (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs
      (layout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]) 5)
    (hLen : truncationMinimum .schedContextConfigure ≤ decoded.msgInfo.length) :
    decodeSchedContextConfigureArgsChecked decoded =
      decodeSchedContextConfigureArgsCheckedBy (msgRegOfFileThen layout regs w) := by
  unfold decodeSchedContextConfigureArgsChecked decodeSchedContextConfigureArgs
    decodeSchedContextConfigureArgsCheckedBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg_push]
  generalize msgRegOfFileThen layout regs w = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;> cases g 4 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      schedParams_ge_iff, SeLe4n.CPtr.ofWord_eq_ofNat]

/-- `decodeCSpaceMintArgs` over a reader: a copy's four words, then the badge,
the fifth word (overflow slot 0 of the caller's IPC buffer, at the entry). -/
@[inline] def decodeCSpaceMintArgsBy (get : MsgRegReader)
    : Except KernelError CSpaceMintArgs := do
  let r0 ← get 0
  let r1 ← get 1
  let r2 ← get 2
  let r3 ← get 3
  let r4 ← get 4
  match cnodeCopyArgsOfWords (CPtr.ofWord r0) (CPtr.ofWord r1) (CPtr.ofWord r2) r3.toNat with
  | .error e => .error e
  | .ok c => .ok { c with badge := Badge.ofWord r4 }

theorem decodeCSpaceMintArgs_eq_by (layout : SyscallRegisterLayout)
    (regs : RegisterFile) (w : UInt64) (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs
      (layout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]) 5)
    (hLen : truncationMinimum .cspaceMint ≤ decoded.msgInfo.length) :
    decodeCSpaceMintArgs decoded =
      decodeCSpaceMintArgsBy (msgRegOfFileThen layout regs w) := by
  unfold decodeCSpaceMintArgs decodeCSpaceMintArgsBy cnodeMintArgsOfWords
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg_push]
  generalize msgRegOfFileThen layout regs w = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;> cases g 4 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

/-- WS-ZA ZA5.5: `decodeServiceRegisterArgs` over a reader, each check in the
decode's order. -/
@[inline] def decodeServiceRegisterArgsBy (get : MsgRegReader)
    : Except KernelError ServiceRegisterArgs := do
  let r0 ← get 0
  let r1 ← get 1
  let r2 ← get 2
  let r3 ← get 3
  let r4 ← get 4
  if r1.toNat > serviceMaxMethodCount then .error .invalidArgument
  else if r2.toNat > serviceMaxMessageSize then .error .invalidArgument
  else if r3.toNat > serviceMaxMessageSize then .error .invalidArgument
  else if r4.toNat ≥ 2 then .error .invalidMessageInfo
  else
    pure { interfaceId    := InterfaceId.ofNat r0.toNat
           methodCount    := r1.toNat
           maxMessageSize := r2.toNat
           maxResponseSize := r3.toNat
           requiresGrant  := r4.toNat == 1 }

theorem decodeServiceRegisterArgs_eq_by (layout : SyscallRegisterLayout)
    (regs : RegisterFile) (w : UInt64) (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs
      (layout.msgRegs.map (readReg regs) ++ #[(⟨w.toNat⟩ : RegValue)]) 5)
    (hLen : truncationMinimum .serviceRegister ≤ decoded.msgInfo.length) :
    decodeServiceRegisterArgs decoded =
      decodeServiceRegisterArgsBy (msgRegOfFileThen layout regs w) := by
  unfold decodeServiceRegisterArgs decodeServiceRegisterArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg_push]
  generalize msgRegOfFileThen layout regs w = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;> cases g 4 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map]

@[inline] def decodeTcbBindNotificationArgsBy (get : MsgRegReader)
    : Except KernelError TcbBindNotificationArgs := do
  let r0 ← get 0
  pure { notificationCPtr := SeLe4n.CPtr.ofWord r0 }

theorem decodeTcbBindNotificationArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .tcbBindNotification ≤ decoded.msgInfo.length) :
    decodeTcbBindNotificationArgs decoded = decodeTcbBindNotificationArgsBy (msgRegOfFile layout regs) := by
  unfold decodeTcbBindNotificationArgs decodeTcbBindNotificationArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeIrqControlGetArgsBy (get : MsgRegReader)
    : Except KernelError IrqControlGetArgs := do
  let r0 ← get 0
  let r1 ← get 1
  let r2 ← get 2
  pure { line := r0.toNat, dstCNode := CPtr.ofWord r1, dstSlot := Slot.ofNat r2.toNat }

theorem decodeIrqControlGetArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .irqControlGet ≤ decoded.msgInfo.length) :
    decodeIrqControlGetArgs decoded = decodeIrqControlGetArgsBy (msgRegOfFile layout regs) := by
  unfold decodeIrqControlGetArgs decodeIrqControlGetArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeIrqHandlerSetNotificationArgsBy (get : MsgRegReader)
    : Except KernelError IrqHandlerSetNotificationArgs := do
  let r0 ← get 0
  pure { notificationCPtr := SeLe4n.CPtr.ofWord r0 }

theorem decodeIrqHandlerSetNotificationArgs_eq_by (layout : SyscallRegisterLayout)
    (regs : RegisterFile) (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .irqHandlerSetNotification ≤ decoded.msgInfo.length) :
    decodeIrqHandlerSetNotificationArgs decoded =
      decodeIrqHandlerSetNotificationArgsBy (msgRegOfFile layout regs) := by
  unfold decodeIrqHandlerSetNotificationArgs decodeIrqHandlerSetNotificationArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeSetPriorityArgsBy (get : MsgRegReader)
    : Except KernelError SetPriorityArgs := do
  let r0 ← get 0
  if r0.toNat > 0xFF then .error .invalidArgument
  else pure { newPriority := r0.toNat }

theorem decodeSetPriorityArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .tcbSetPriority ≤ decoded.msgInfo.length) :
    decodeSetPriorityArgs decoded = decodeSetPriorityArgsBy (msgRegOfFile layout regs) := by
  unfold decodeSetPriorityArgs decodeSetPriorityArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeSetMCPriorityArgsBy (get : MsgRegReader)
    : Except KernelError SetMCPriorityArgs := do
  let r0 ← get 0
  if r0.toNat > 0xFF then .error .invalidArgument
  else pure { newMCP := r0.toNat }

theorem decodeSetMCPriorityArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .tcbSetMCPriority ≤ decoded.msgInfo.length) :
    decodeSetMCPriorityArgs decoded = decodeSetMCPriorityArgsBy (msgRegOfFile layout regs) := by
  unfold decodeSetMCPriorityArgs decodeSetMCPriorityArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeSetIPCBufferArgsBy (get : MsgRegReader)
    : Except KernelError SetIPCBufferArgs := do
  let r0 ← get 0
  let addr := SeLe4n.VAddr.ofNat r0.toNat
  if addr.toNat % SeLe4n.ipcBufferAlignment != 0 then .error .alignmentError
  else pure { bufferAddr := addr }

theorem decodeSetIPCBufferArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .tcbSetIPCBuffer ≤ decoded.msgInfo.length) :
    decodeSetIPCBufferArgs decoded = decodeSetIPCBufferArgsBy (msgRegOfFile layout regs) := by
  unfold decodeSetIPCBufferArgs decodeSetIPCBufferArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeSetAffinityArgsBy (get : MsgRegReader)
    : Except KernelError SetAffinityArgs := do
  let r0 ← get 0
  pure { affinityRaw := r0.toNat }

theorem decodeSetAffinityArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .tcbSetAffinity ≤ decoded.msgInfo.length) :
    decodeSetAffinityArgs decoded = decodeSetAffinityArgsBy (msgRegOfFile layout regs) := by
  unfold decodeSetAffinityArgs decodeSetAffinityArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeSetFaultHandlerArgsBy (get : MsgRegReader)
    : Except KernelError SetFaultHandlerArgs := do
  let r0 ← get 0
  pure { handlerCPtr := SeLe4n.CPtr.ofWord r0 }

theorem decodeSetFaultHandlerArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .tcbSetFaultHandler ≤ decoded.msgInfo.length) :
    decodeSetFaultHandlerArgs decoded = decodeSetFaultHandlerArgsBy (msgRegOfFile layout regs) := by
  unfold decodeSetFaultHandlerArgs decodeSetFaultHandlerArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodeSetSpaceArgsBy (get : MsgRegReader)
    : Except KernelError SetSpaceArgs := do
  let r0 ← get 0
  let r1 ← get 1
  pure { cspaceRoot := SeLe4n.CPtr.ofWord r0, vspaceRoot := SeLe4n.CPtr.ofWord r1 }

theorem decodeSetSpaceArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .tcbSetSpace ≤ decoded.msgInfo.length) :
    decodeSetSpaceArgs decoded = decodeSetSpaceArgsBy (msgRegOfFile layout regs) := by
  unfold decodeSetSpaceArgs decodeSetSpaceArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

@[inline] def decodePageTableMapArgsBy (get : MsgRegReader)
    : Except KernelError PageTableMapArgs := do
  let r0 ← get 0
  let r1 ← get 1
  pure { vspaceRoot := SeLe4n.CPtr.ofWord r0, vaddr := SeLe4n.VAddr.ofNat r1.toNat }

theorem decodePageTableMapArgs_eq_by (layout : SyscallRegisterLayout) (regs : RegisterFile)
    (decoded : SyscallDecodeResult)
    (h : MsgRegsAgreeBelow decoded.msgRegs (layout.msgRegs.map (readReg regs)) 4)
    (hLen : truncationMinimum .pageTableMap ≤ decoded.msgInfo.length) :
    decodePageTableMapArgs decoded = decodePageTableMapArgsBy (msgRegOfFile layout regs) := by
  unfold decodePageTableMapArgs decodePageTableMapArgsBy
  rw [requireMessageLength_of_le hLen]
  unfold MsgRegsAgreeBelow at h
  simp (disch := decide) only [h]
  simp only [requireMsgReg_map_readReg]
  generalize msgRegOfFile layout regs = g
  cases g 0 <;> cases g 1 <;> cases g 2 <;> cases g 3 <;>
    simp [Except.map, bind, Except.bind, pure, Except.pure, Functor.map,
      SeLe4n.CPtr.ofWord_eq_ofNat, SeLe4n.Badge.ofWord_eq_ofNatMasked]

end SeLe4n.Kernel.Architecture.SyscallArgDecode
