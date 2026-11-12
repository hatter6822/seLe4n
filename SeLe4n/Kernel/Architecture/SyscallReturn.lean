-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.State
import SeLe4n.Kernel.Architecture.HardwareTables
import SeLe4n.Kernel.Architecture.IpcBufferRead

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
* `x2`-`x5` — message registers (the inline window).  Since WS-BP BP7.8 the
  registers past the fourth are written into the receiver's IPC buffer
  (`overflowDeliveryWrites`), and the frame's length counts the inline window
  plus the words actually written (`returnFrame_message_window`).

Nothing in this module is live until the WS-RA flip: the FFI boundary keeps
the bit-63 `encodeOk` / `encodeError` protocol until `Platform/FFI.lean` and
the Rust mirror move together (plan §5, the migration window).

Plan: WS-RA RA.A.1-RA.A.8.
-/

namespace SeLe4n.Model.KernelError

/-- The canonical numeric discriminant of each `KernelError` — the table
that previously lived only in `Platform.FFI.KernelError.toUInt32` (which
becomes this function's `UInt32` instance, so the table exists exactly once).
Discriminant `37` is retired (`retiredDiscriminants`) and no variant has it.  Mirrors `rust/sele4n-types/src/error.rs` exactly;
`tests/SyscallDispatchSuite.lean` round-trips the pairing. -/
@[inline] def toDiscriminant : KernelError → Nat
  | .invalidCapability _           => 0
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
  | .untypedRegionExhausted _      => 20
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
  -- 37: retired (`retiredDiscriminants`).
  | .revocationRequired            => 38
  | .invalidArgument _             => 39
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
  -- WS-RR RR7.14: a blocking IPC forcibly cancelled.
  | .ipcCancelled                  => 57
  -- seL4's `seL4_TruncatedMessage`: a message shorter than its decode reads.
  | .truncatedMessage              => 58
  | .rangeError _ _                => 59
  | .failedLookup _ _              => 60

/-- The inverse the tree never had: `Platform.FFI.KernelError.toUInt32` is
one-directional, and the Rust side decodes with its own
`KernelError::from_u32`.  WS-RA's error-label carriage needs the Lean-side
round trip (RA.A.5).  Fail-closed: out-of-range discriminants map to
`none`, exactly as `from_u32` yields its `UnknownKernelError` sentinel. -/
def ofDiscriminant? : Nat → Option KernelError
  | 0  => some (.invalidCapability 0)
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
  | 20 => some (.untypedRegionExhausted 0)
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
  -- 37: retired (`retiredDiscriminants`), decodes to `none`.
  | 38 => some .revocationRequired
  | 39 => some (.invalidArgument 0)
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
  | 57 => some .ipcCancelled
  | 58 => some .truncatedMessage
  | 59 => some (.rangeError 0 0)
  | 60 => some (.failedLookup false .invalidRoot)
  | _  => none

/-- The discriminant map is a section of its inverse over codes: every
`KernelError` survives the numeric round trip with its payload cleared
(`erasePayload`) — the discriminant names the code, and the payload rides in
the message registers (`Architecture.errorFrame`).  With `toDiscriminant_lt`
this pins the map as a bijection from codes onto the discriminants below
`kernelErrorEncodingBound` that are not retired. -/
theorem ofDiscriminant?_toDiscriminant (e : KernelError) :
    ofDiscriminant? (toDiscriminant e) = some e.erasePayload := by
  cases e <;> rfl

/-- Clearing the payload keeps the code. -/
@[simp] theorem toDiscriminant_erasePayload (e : KernelError) :
    toDiscriminant e.erasePayload = toDiscriminant e := by
  cases e <;> rfl

/-- Two errors share a discriminant exactly when they share a code. -/
theorem toDiscriminant_eq_iff (e₁ e₂ : KernelError) :
    toDiscriminant e₁ = toDiscriminant e₂ ↔ e₁.erasePayload = e₂.erasePayload := by
  constructor
  · intro h
    have h₁ := ofDiscriminant?_toDiscriminant e₁
    rw [h, ofDiscriminant?_toDiscriminant e₂] at h₁
    exact (Option.some.inj h₁).symm
  · intro h
    rw [← toDiscriminant_erasePayload e₁, h, toDiscriminant_erasePayload]

/-- **One past the largest `KernelError` discriminant**, named once so no
caller has to write the literal: every value below it is a variant's or a
retired one (`retiredDiscriminants`).

Lean gives an `inductive` no constructor list to measure, so the figure is a
literal — but it is a literal with a *machine-checked meaning*: `_lt` below
bounds every discriminant by it (`decide` over every constructor, so a new
variant fails there), and `_tight` bounds it from the other side, so this is
the **least** strict upper bound and cannot drift up either.  Before it existed
the number was written out at nine sites across Lean, the suites and three Rust
crates, and WS-RR RR7.14 found one of them stated as prose in a trace line that
kept saying `57` while the check beside it had moved to `58`. -/
def kernelErrorEncodingBound : Nat := 61

/-- **Retired discriminants**, reserved and never reassigned: `37`, the
`allocationMisaligned` the carve returned before it rounded the free index up
to the object's boundary (WS-ZA ZA5.4 part 14).  No variant has one, and
`ofDiscriminant?` decodes one to `none`. -/
def retiredDiscriminants : List Nat := [37]

/-- Every discriminant is inside the table. -/
theorem toDiscriminant_lt (e : KernelError) : toDiscriminant e < kernelErrorEncodingBound := by
  cases e <;> simp [toDiscriminant, kernelErrorEncodingBound]

/-- …and the bound is **tight**: the last in-range value is inhabited, so
`kernelErrorEncodingBound` is the least strict upper bound rather than merely one.
Without this half the constant could be raised silently and every consumer
would still pass while covering a range with a hole at the top. -/
theorem kernelErrorEncodingBound_tight :
    (ofDiscriminant? (kernelErrorEncodingBound - 1)).isSome
      ∧ ofDiscriminant? kernelErrorEncodingBound = none := by
  constructor
  · rfl
  · rfl

/-- The other direction of the round trip, over the whole in-range domain:
below `kernelErrorEncodingBound` every discriminant that is not retired hits
and maps back to itself; `kernelErrorEncodingBound` itself (the first
out-of-range value) is rejected. -/
theorem toDiscriminant_ofDiscriminant? :
    (∀ n, n < kernelErrorEncodingBound → retiredDiscriminants.contains n = false →
        ((ofDiscriminant? n).map toDiscriminant) = some n) ∧
      ofDiscriminant? kernelErrorEncodingBound = none := by
  constructor
  · decide
  · rfl

/-- Every number decodes to an error exactly when it is below
`kernelErrorEncodingBound` and not retired. -/
theorem ofDiscriminant?_isSome_iff (n : Nat) :
    (ofDiscriminant? n).isSome =
      (decide (n < kernelErrorEncodingBound) && !retiredDiscriminants.contains n) := by
  match n with
  | 0  | 1  | 2  | 3  | 4  | 5  | 6  | 7  | 8  | 9
  | 10 | 11 | 12 | 13 | 14 | 15 | 16 | 17 | 18 | 19
  | 20 | 21 | 22 | 23 | 24 | 25 | 26 | 27 | 28 | 29
  | 30 | 31 | 32 | 33 | 34 | 35 | 36 | 37 | 38 | 39
  | 40 | 41 | 42 | 43 | 44 | 45 | 46 | 47 | 48 | 49
  | 50 | 51 | 52 | 53 | 54 | 55 | 56 | 57 | 58 | 59
  | 60 => rfl
  | n + 61 => simp [ofDiscriminant?, kernelErrorEncodingBound, retiredDiscriminants]

/-- The retired `allocationMisaligned` discriminant names no error. -/
theorem ofDiscriminant?_retired : ofDiscriminant? 37 = none := rfl

/-! ### The error payload, in seL4's message-register order

`setMRs_syscall_error` (`src/object/tcb.c`) writes an error's payload into the
caller's message registers, and `setMRs_lookup_failure` (`src/api/faults.c`)
writes a lookup fault after `wasSource`. -/

/-- The payload's words: `invalidCapability` and `invalidArgument` one (the
capability's or the argument's number), `rangeError` two (min, max),
`untypedRegionExhausted` one (the memory left), `failedLookup` one (`wasSource`)
and its lookup fault's (`LookupFault.wordCount`); every other code none. -/
@[inline] def payloadLength : KernelError → Nat
  | .invalidCapability _ => 1
  | .invalidArgument _ => 1
  | .rangeError _ _ => 2
  | .failedLookup _ f => 1 + f.wordCount
  | .untypedRegionExhausted _ => 1
  | _ => 0

/-- Payload word `i` (message register `i`), `0` past the payload. -/
@[inline] def payloadWord (e : KernelError) (i : Nat) : UInt64 :=
  match e, i with
  | .invalidCapability n, 0 => n
  | .invalidArgument n, 0 => n
  | .rangeError lo _, 0 => lo
  | .rangeError _ hi, 1 => hi
  | .failedLookup wasSource _, 0 => if wasSource then 1 else 0
  | .failedLookup _ f, i + 1 => f.word i
  | .untypedRegionExhausted m, 0 => m
  | _, _ => 0

/-- At most five words: a guard mismatch's, the one payload past the four
inline message registers. -/
theorem payloadLength_le (e : KernelError) : e.payloadLength ≤ 5 := by
  cases e with
  | failedLookup _ f => cases f <;> simp [payloadLength, LookupFault.wordCount]
  | _ => simp [payloadLength]

/-- **The message's length, as seL4's `setMR` chain returns it**: the payload's
words, except that a fifth word counts only when it was written to the caller's
IPC buffer (`setMR` past `n_msgRegisters` with no buffer answers
`n_msgRegisters`). -/
@[inline] def messageLength (e : KernelError) (overflowWritten : Bool) : Nat :=
  if e.payloadLength ≤ 4 ∨ overflowWritten = true then e.payloadLength else 4

theorem messageLength_le (e : KernelError) (w : Bool) : e.messageLength w ≤ 5 := by
  unfold messageLength
  have := payloadLength_le e
  split <;> omega

/-- The length is the payload's whenever the payload fits the four inline
message registers. -/
theorem messageLength_of_le_four (e : KernelError) (w : Bool) (h : e.payloadLength ≤ 4) :
    e.messageLength w = e.payloadLength := by
  unfold messageLength; rw [if_pos (Or.inl h)]

/-! ### The error, from its words

A refusal handed on as scalars (`SystemState.pushEntryReport`) is its
discriminant and its five payload words; these rebuild it. -/

/-- A lookup fault from its words in `setMRs_lookup_failure`'s order: the type
word, then the fields. -/
def _root_.SeLe4n.Model.LookupFault.ofWords (t a b c : UInt64) : LookupFault :=
  if t = 2 then .missingCapability a
  else if t = 3 then .depthMismatch a b
  else if t = 4 then .guardMismatch a b c
  else .invalidRoot

/-- `e`'s code with the payload the words name. -/
def withPayloadWords : KernelError → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → KernelError
  | .invalidCapability _, w0, _, _, _, _ => .invalidCapability w0
  | .invalidArgument _, w0, _, _, _, _ => .invalidArgument w0
  | .rangeError _ _, w0, w1, _, _, _ => .rangeError w0 w1
  | .failedLookup _ _, w0, w1, w2, w3, w4 =>
      .failedLookup (w0 != 0) (LookupFault.ofWords w1 w2 w3 w4)
  | .untypedRegionExhausted _, w0, _, _, _, _ => .untypedRegionExhausted w0
  | e, _, _, _, _, _ => e

/-- `withPayloadWords` as it runs: a payload of zeros is the closed constant,
so rebuilding a refusal that carries no data builds nothing. -/
def withPayloadWordsFast : KernelError → UInt64 → UInt64 → UInt64 → UInt64 → UInt64 → KernelError
  | .invalidCapability _, w0, _, _, _, _ =>
      if w0 = 0 then .invalidCapability 0 else .invalidCapability w0
  | .invalidArgument _, w0, _, _, _, _ =>
      if w0 = 0 then .invalidArgument 0 else .invalidArgument w0
  | .rangeError _ _, w0, w1, _, _, _ => .rangeError w0 w1
  | .failedLookup _ _, w0, w1, w2, w3, w4 =>
      .failedLookup (w0 != 0) (LookupFault.ofWords w1 w2 w3 w4)
  | .untypedRegionExhausted _, w0, _, _, _, _ =>
      if w0 = 0 then .untypedRegionExhausted 0 else .untypedRegionExhausted w0
  | e, _, _, _, _, _ => e

@[csimp] theorem withPayloadWords_eq_fast : @withPayloadWords = @withPayloadWordsFast := by
  funext e w0 w1 w2 w3 w4
  cases e <;> simp only [withPayloadWords, withPayloadWordsFast] <;> split <;> simp_all

/-- The error whose discriminant is `d` and whose payload words are `w0`–`w4`
(`illegalState` for a discriminant that names none). -/
@[inline] def ofPayloadWords (d : Nat) (w0 w1 w2 w3 w4 : UInt64) : KernelError :=
  match ofDiscriminant? d with
  | some e => e.withPayloadWords w0 w1 w2 w3 w4
  | none => .illegalState

/-- **An error is its discriminant and its payload words.** -/
theorem ofPayloadWords_payloadWord (e : KernelError) :
    ofPayloadWords e.toDiscriminant (e.payloadWord 0) (e.payloadWord 1) (e.payloadWord 2)
      (e.payloadWord 3) (e.payloadWord 4) = e := by
  unfold ofPayloadWords
  rw [ofDiscriminant?_toDiscriminant]
  cases e with
  | failedLookup w f =>
    cases w <;> cases f <;>
      simp [erasePayload, withPayloadWords, payloadWord, LookupFault.ofWords, LookupFault.word,
        LookupFault.typeWord]
  | _ => rfl

/-- Whether `e` is the error with discriminant `d` and payload words `w0`–`w4`,
decided on the words. -/
@[inline] def matchesWords (e : KernelError) (d : Nat) (w0 w1 w2 w3 w4 : UInt64) : Bool :=
  e.toDiscriminant == d && e.payloadWord 0 == w0 && e.payloadWord 1 == w1 &&
    e.payloadWord 2 == w2 && e.payloadWord 3 == w3 && e.payloadWord 4 == w4

theorem matchesWords_iff (e ke : KernelError) :
    e.matchesWords ke.toDiscriminant (ke.payloadWord 0) (ke.payloadWord 1) (ke.payloadWord 2)
      (ke.payloadWord 3) (ke.payloadWord 4) = true ↔ e = ke := by
  constructor
  · intro h
    simp only [matchesWords, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩ := h
    rw [← ofPayloadWords_payloadWord e, ← ofPayloadWords_payloadWord ke, h0, h1, h2, h3, h4, h5]
  · rintro rfl
    simp [matchesWords]

/-- The payload's length from the words: the code, and for a lookup failure its
type word (word 1). -/
@[inline] def payloadLengthOfWords (d : Nat) (w1 : UInt64) : Nat :=
  if d = 0 ∨ d = 39 ∨ d = 20 then 1
  else if d = 59 then 2
  else if d = 60 then
    (if w1 = 2 then 3 else if w1 = 3 then 4 else if w1 = 4 then 5 else 2)
  else 0

theorem payloadLengthOfWords_eq (e : KernelError) :
    payloadLengthOfWords e.toDiscriminant (e.payloadWord 1) = e.payloadLength := by
  cases e with
  | failedLookup w f =>
    cases f <;> simp [payloadLengthOfWords, toDiscriminant, payloadWord, payloadLength,
      LookupFault.word, LookupFault.typeWord, LookupFault.wordCount]
  | _ => simp [payloadLengthOfWords, toDiscriminant, payloadLength]


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
  -- **WS-RR RR8.16 (`v0.35.190`)**: revocation returns nothing.  seL4's
  -- `seL4_CNode_Revoke` returns only an error code, and the count of
  -- destroyed derivations is deliberately not a return value: it is a
  -- measure of *other* CSpaces' contents, which the invoker may hold no
  -- authority over, so returning it would make the CDT's shape readable
  -- from a slot the caller merely owns.
  | .cspaceRevoke          => .unit
  -- **WS-BP BP7.1 (`v0.36.5`)**: a carve returns nothing — seL4's
  -- `seL4_Untyped_Retype` returns only an error code; what it produced is the
  -- capability it installed at the slot the caller named.
  | .untypedRetype         => .unit
  -- **WS-BP BP7.1 (`v0.36.6`)**: a reset returns nothing — what it produced is
  -- the untyped's memory, which the next carve hands out.
  | .untypedReset          => .unit
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
  | .tcbSetFaultHandler    => .unit
  | .tcbSetSpace           => .unit
  | .pageTableMap          => .unit
  | .pageTableUnmap        => .unit
  | .yield                 => .unit
  -- WS-ZA ZA6.9: the Consumed invocation returns the consumed time `setConsumed`
  -- wrote into the caller's first message register, with its message info in
  -- `x1`: the frame passes the staged registers through.
  | .schedContextConsumed  => .message
  -- WS-ZA ZA6.29: the yieldTo invocation returns the consumed time the same way:
  -- written now by `setConsumed`, or at the caller's activation on the linked
  -- branch (`activateThreadOnCore`).
  | .schedContextYieldTo   => .message
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
  -- WS-ZA ZA6.32: an acknowledge returns nothing — seL4's `seL4_IRQHandler_Ack`
  -- returns only an error code.
  | .irqHandlerAck         => .unit
  | .irqControlGet         => .unit
  | .irqHandlerSetNotification => .unit
  | .irqHandlerClear       => .unit

/-- Totality anchor (RA.A.2).  The *mechanism* is the definition itself —
an exhaustive match with no wildcard, so elaboration rejects a tree where a
new `SyscallId` variant lacks a shape.  The theorem is the named surface
anchor for that fact. -/
theorem syscallReturnShape_total (sid : SyscallId) :
    ∃ shape, syscallReturnShape sid = shape :=
  ⟨_, rfl⟩

/-- The value-returning surface, pinned by enumeration over the ABI's own
`SyscallId.all` (plan §1.3): nine syscalls return a value — the five WS-RA
classified, WS-SM SM9.A's two audit reads, WS-ZA ZA6.9's Consumed invocation
and WS-ZA ZA6.29's yieldTo invocation. -/
theorem syscallReturnShape_value_returning :
    SyscallId.all.filter (fun sid => syscallReturnShape sid != .unit) =
      [.receive, .call, .serviceQuery, .notificationWait, .replyRecv,
       .auditRead, .auditDrain, .schedContextConsumed, .schedContextYieldTo] := by
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

/-- **WS-RR RR4 (audit round) — ABI version 3: kernel status rides in the top
of the label range.**

Version 2 carried a `KernelError` discriminant `d` as label `d + 1`, with `0`
success.  That was sound while every delivered message had label `0`, which
was true of the whole tree until RR4: a fault message is delivered under its
`seL4_Fault_tag` (`1`, `2`, `3`, `6` — `Architecture.faultLabel`), and a
handler's `seL4_Recv` returns that label in `x1`.  Under the offset scheme a
`vmFault` (tag 6) decoded in userspace as `KernelError` discriminant 5, and
`capFault` (tag 1) as `.invalidCapability` — every fault a handler received
read as a failed receive, so no fault handler could be written against
`sele4n-abi`.

The fix keeps one syscall-agnostic decoder and separates the two by
**range**: the top `errorLabelRangeSize` labels of the 52-bit field are
kernel status, everything below is a delivered message's own label.  Success
is still `0`; error `d` is `errorLabelBase + d`; and a delivered label is
always below `errorLabelBase` (`returnMessageInfo` clamps there, and every
kernel-emitted label — the fault tags — sits far below it,
`faultLabel_lt_errorLabelBase`).  The blocked-resume sentinel `maxLabel` is
the top of the range, naming discriminant `255`, which no `KernelError` has
— so it still decodes as `UnknownKernelError`, and now for the *stated*
reason rather than by happening to exceed the enumeration. -/
def errorLabelRangeSize : Nat := 256

/-- The first kernel-status label: `2^52 − 256`.  Labels at or above it are
kernel status; labels below it are a delivered message's own. -/
def errorLabelBase : Nat := MessageInfo.maxLabel + 1 - errorLabelRangeSize

/-- The base, as a literal — pinned so a change to `maxLabel` or the range
size cannot move it silently past the Rust mirror
(`sele4n_types::ERROR_LABEL_BASE`). -/
theorem errorLabelBase_eq : errorLabelBase = 0xFFFFFFFFFFF00 := by decide

/-- The `MessageInfo` a delivered message returns in `x1`.  `IpcMessage`
carries no `MessageInfo` (it is discarded at decode time), so the return
word is synthesized — here, once, for every delivery site: `length` is the
inline window actually delivered in `x2`-`x5`, `extraCaps` and
`capsUnwrapped` what the capability transfer reports (`capInfo`), and
`label` the message's own, clamped below the status labels.

**`capInfo` is the transfer's report, seL4's `transferCaps` answer**
(`CapTransferSummary.capInfo`): the low two bits are the number of extra
capabilities the transfer processed before it stopped (each unwrapped to its
badge or installed in the receive slot), the next three which of them were
unwrapped.  It is never read off the sender's request: a transfer that stops
at its first capability reports none, and a count read off the request would
tell the receiver its receive slot holds fresh authority when it does not.
The parameter is deliberately **not defaulted**: a site that cannot name the
transfer's report has no business synthesizing a message frame.  Arms whose
path runs no transfer (the reply delivery, badge-only notification wakes)
pass `0`.

**`overflow` is the count of message registers past the fourth the delivery
actually wrote into the receiver's IPC buffer** (WS-BP BP7.8,
`overflowDeliveryWrites`), and the length reports exactly what arrived: the
inline window plus those words, never more than the message holds.  Like
`capInfo` it is not defaulted — a delivery that wrote none says `0`, and a
receiver whose buffer resolves nowhere reads a length of at most four, which is
seL4's own answer for a receiver with no IPC buffer (`copyMRs` copies the
registers alone). -/
@[inline] def returnMessageInfo (msg : IpcMessage) (capInfo overflow : Nat) : MessageInfo :=
  { length    := min (min msg.registers.size (4 + overflow)) maxMessageRegisters
    extraCaps := capInfo % 4
    label     := min msg.label (errorLabelBase - 1)
    capsUnwrapped := capInfo / 4 % 8 }

/-- The window bound, stated: the returned length never exceeds the four inline
message registers plus the overflow words the delivery wrote. -/
theorem returnFrame_message_window (msg : IpcMessage) (capInfo overflow : Nat) :
    (returnMessageInfo msg capInfo overflow).length ≤ 4 + overflow :=
  Nat.le_trans (Nat.min_le_left _ _) (Nat.min_le_right _ _)

/-- The synthesized word is well-formed for seL4's encoding:
length ≤ 120, extraCaps ≤ 3, label ≤ 2^52 − 1, capsUnwrapped ≤ 7. -/
theorem returnMessageInfo_wellFormed (msg : IpcMessage) (capInfo overflow : Nat) :
    (returnMessageInfo msg capInfo overflow).wellFormed := by
  refine ⟨Nat.min_le_right _ _, ?_, ?_, ?_⟩
  · show capInfo % 4 ≤ Model.maxExtraCaps
    unfold Model.maxExtraCaps; omega
  · exact Nat.le_trans (Nat.min_le_right _ _) (by rw [errorLabelBase_eq]; decide)
  · show capInfo / 4 % 8 ≤ MessageInfo.maxCapsUnwrapped
    unfold MessageInfo.maxCapsUnwrapped; omega

/-- **A delivered message never carries a status label** (ABI v3): the
synthesized label is below `errorLabelBase`, so a receiver's decoder cannot
read a delivery as a kernel error whatever the message's label was. -/
theorem returnMessageInfo_label_lt_errorLabelBase (msg : IpcMessage) (capInfo overflow : Nat) :
    (returnMessageInfo msg capInfo overflow).label < errorLabelBase := by
  unfold returnMessageInfo
  have : errorLabelBase - 1 < errorLabelBase := by rw [errorLabelBase_eq]; decide
  exact Nat.lt_of_le_of_lt (Nat.min_le_right _ _) this

/-- WS-RR RR4.4: the delivered label is the message's own whenever it is
below the status range — the clamp above is the fail-closed guard for an
out-of-range label, never a rewrite of a real one.  Every kernel-emitted label
satisfies the hypothesis (`Architecture.faultLabel_lt_errorLabelBase` for a
fault message; a user send carries label `0`), so on every live path this
reads as the identity. -/
@[simp] theorem returnMessageInfo_label_of_lt (msg : IpcMessage) (capInfo overflow : Nat)
    (h : msg.label < errorLabelBase) :
    (returnMessageInfo msg capInfo overflow).label = msg.label :=
  Nat.min_eq_left (Nat.le_sub_one_of_lt h)

/-- WS-RR RR4.4: a message carrying no label (the default, and every message
built before RR4) delivers the `0` label the pre-RR4 synthesis hard-coded —
the backward-compatibility bridge. -/
@[simp] theorem returnMessageInfo_label_zero (msg : IpcMessage) (capInfo overflow : Nat)
    (h : msg.label = 0) : (returnMessageInfo msg capInfo overflow).label = 0 := by
  simp [returnMessageInfo, h]

/-- The honesty bound (PR #866 round-2): the returned `extraCaps` never
exceeds the transfer's report — in particular, a path that transferred
nothing reports zero, however many capabilities the sender asked to
transfer. -/
theorem returnMessageInfo_extraCaps_le_capInfo
    (msg : IpcMessage) (capInfo overflow : Nat) :
    (returnMessageInfo msg capInfo overflow).extraCaps ≤ capInfo :=
  Nat.mod_le _ _

@[simp] theorem returnMessageInfo_extraCaps_zero (msg : IpcMessage) (overflow : Nat) :
    (returnMessageInfo msg 0 overflow).extraCaps = 0 := rfl

/-- A delivered `IpcMessage` as a return frame — badge to `x0`, synthesized
`MessageInfo` to `x1`, the inline register window to `x2`-`x5` (RA.A.3).
The **single** place a message becomes a frame, used by every RA.B.5b
staging site, so the synthesis cannot drift between sites.
`capInfo` per `returnMessageInfo`: this delivery's transfer report,
`0` for paths that run none. -/
@[inline] def returnFrameOfMessage (msg : IpcMessage) (capInfo overflow : Nat) :
    SyscallReturnFrame :=
  { x0 := (msg.badge.map Badge.word).getD 0
    x1 := (returnMessageInfo msg capInfo overflow).encode.toUInt64
    x2 := ((msg.registers[0]?.map RegValue.val).getD 0).toUInt64
    x3 := ((msg.registers[1]?.map RegValue.val).getD 0).toUInt64
    x4 := ((msg.registers[2]?.map RegValue.val).getD 0).toUInt64
    x5 := ((msg.registers[3]?.map RegValue.val).getD 0).toUInt64 }

/-- A badge-only frame — `.notificationWait`'s shape: the badge in `x0`,
success `MessageInfo` (all-zero word) in `x1`, no message registers. -/
@[inline] def returnFrameOfBadge (b : Badge) : SyscallReturnFrame :=
  { x0 := b.word }

-- ============================================================================
-- §4b  Staging a frame into a register context (RA.B.1's pure core)
-- ============================================================================

/-- Stage a return frame into a register file: `x0`-`x5` overwritten with
the frame, every other register (including `x7`, `pc`, `sp`) untouched.
The dual of the argument spill's register writes. -/
@[inline] def _root_.SeLe4n.RegisterFile.stageReturnFrame
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) : SeLe4n.RegisterFile :=
  { rf with x0 := f.x0, x1 := f.x1, x2 := f.x2, x3 := f.x3, x4 := f.x4, x5 := f.x5 }

/-- Staging touches `x0`-`x5` only — `pc` and `sp` survive. -/
@[simp] theorem _root_.SeLe4n.RegisterFile.stageReturnFrame_pc
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) :
    (rf.stageReturnFrame f).pc = rf.pc := rfl

@[simp] theorem _root_.SeLe4n.RegisterFile.stageReturnFrame_sp
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) :
    (rf.stageReturnFrame f).sp = rf.sp := rfl

/-- Word `i` of a staged file: the frame's `x0`-`x5`, the file underneath
everywhere else. -/
theorem _root_.SeLe4n.RegisterFile.stageReturnFrame_word
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) (i : Nat) :
    (rf.stageReturnFrame f).word i =
      if i = 0 then f.x0 else if i = 1 then f.x1 else if i = 2 then f.x2
      else if i = 3 then f.x3 else if i = 4 then f.x4 else if i = 5 then f.x5
      else rf.word i := by
  by_cases hi : i < SeLe4n.Kernel.Architecture.trapFrameWordCount
  · match i, hi with
    | 0, _ => rfl
    | 1, _ => rfl
    | 2, _ => rfl
    | 3, _ => rfl
    | 4, _ => rfl
    | 5, _ => rfl
    | 6, _ => rfl
    | 7, _ => rfl
    | 8, _ => rfl
    | 9, _ => rfl
    | 10, _ => rfl
    | 11, _ => rfl
    | 12, _ => rfl
    | 13, _ => rfl
    | 14, _ => rfl
    | 15, _ => rfl
    | 16, _ => rfl
    | 17, _ => rfl
    | 18, _ => rfl
    | 19, _ => rfl
    | 20, _ => rfl
    | 21, _ => rfl
    | 22, _ => rfl
    | 23, _ => rfl
    | 24, _ => rfl
    | 25, _ => rfl
    | 26, _ => rfl
    | 27, _ => rfl
    | 28, _ => rfl
    | 29, _ => rfl
    | 30, _ => rfl
    | 31, _ => rfl
    | 32, _ => rfl
    | 33, _ => rfl
    | 34, _ => rfl
    | n + 35, h => exact absurd h (by unfold SeLe4n.Kernel.Architecture.trapFrameWordCount; omega)
  · have h5 : 5 < i := by unfold SeLe4n.Kernel.Architecture.trapFrameWordCount at hi; omega
    simp only [show i ≠ 0 by omega, show i ≠ 1 by omega, show i ≠ 2 by omega,
      show i ≠ 3 by omega, show i ≠ 4 by omega, show i ≠ 5 by omega, if_false]
    rw [SeLe4n.RegisterFile.word_of_ge _ i hi, SeLe4n.RegisterFile.word_of_ge _ i hi]

/-- Registers outside the frame window are untouched — in particular `x7`
(the staged syscall number) and the callee-saved range. -/
theorem _root_.SeLe4n.RegisterFile.stageReturnFrame_gpr_high
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) (r : SeLe4n.RegName)
    (h : 5 < r.val) : (rf.stageReturnFrame f).gpr r = rf.gpr r := by
  unfold SeLe4n.RegisterFile.gpr
  split
  · rw [SeLe4n.RegisterFile.stageReturnFrame_word]
    simp only [show r.val ≠ 0 by omega, show r.val ≠ 1 by omega, show r.val ≠ 2 by omega,
      show r.val ≠ 3 by omega, show r.val ≠ 4 by omega, show r.val ≠ 5 by omega, if_false]
  · rfl

/-- The staged registers read back as the frame, register for register —
the pure core of RA.B.2's `readReturnFrame_writeReturnFrame` round trip. -/
theorem _root_.SeLe4n.RegisterFile.stageReturnFrame_reads_back
    (rf : SeLe4n.RegisterFile) (f : SyscallReturnFrame) :
    (rf.stageReturnFrame f).gpr ⟨0⟩ = ⟨f.x0.toNat⟩ ∧
    (rf.stageReturnFrame f).gpr ⟨1⟩ = ⟨f.x1.toNat⟩ ∧
    (rf.stageReturnFrame f).gpr ⟨2⟩ = ⟨f.x2.toNat⟩ ∧
    (rf.stageReturnFrame f).gpr ⟨3⟩ = ⟨f.x3.toNat⟩ ∧
    (rf.stageReturnFrame f).gpr ⟨4⟩ = ⟨f.x4.toNat⟩ ∧
    (rf.stageReturnFrame f).gpr ⟨5⟩ = ⟨f.x5.toNat⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩

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

/-- **WS-ZA ZA4.7**: stage a delivered message's frame and drop the message —
seL4 keeps a delivered message only in the receiver's registers and IPC buffer,
never in a ready TCB.  `withReturnFrame` then `pendingMessage := none`. -/
@[inline] def _root_.SeLe4n.Model.TCB.withDeliveredFrame (tcb : TCB) (f : SyscallReturnFrame) : TCB :=
  { tcb with registerContext := tcb.registerContext.stageReturnFrame f, pendingMessage := none }

@[simp] theorem _root_.SeLe4n.Model.TCB.withDeliveredFrame_ipcState
    (tcb : TCB) (f : SyscallReturnFrame) :
    (tcb.withDeliveredFrame f).ipcState = tcb.ipcState := rfl

@[simp] theorem _root_.SeLe4n.Model.TCB.withDeliveredFrame_pendingMessage
    (tcb : TCB) (f : SyscallReturnFrame) :
    (tcb.withDeliveredFrame f).pendingMessage = none := rfl

@[simp] theorem _root_.SeLe4n.Model.TCB.withDeliveredFrame_registerContext
    (tcb : TCB) (f : SyscallReturnFrame) :
    (tcb.withDeliveredFrame f).registerContext
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
`regsOnCore`** — keeping the write out of `machine` is part of what makes the
RA.B.10 projection preservation hold for every observer.  Since WS-BP BP7.3 the
bank and the current thread's context are one value at every trap entry
(`Architecture.saveTrapFrameOnCore`); what reconciles a frame staged for the
*current* thread with the bank is `Architecture.stageCallerReturn` (WS-BP BP7.4),
which writes both.

Total: a non-TCB target returns the state unchanged, mirroring
`writeFfiRegistersToTcb`'s posture (the caller surfaces the error).

The write is the typed in-place rewrite `SystemState.updateTcb` (`v0.35.69`):
the witnessed lookup around `rewriteObject`, whose bookkeeping-neutrality is a
theorem, so the staging cannot register, unregister or re-kind anything — and
the identity where the thread resolves to no TCB, which is the totality
posture stated above (`writeReturnFrameToTcb_id_when_not_tcb`). -/
def writeReturnFrameToTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) : SystemState :=
  st.updateTcb tid (·.withReturnFrame frame)

/-- **WS-ZA ZA4.7**: the delivery write — `writeReturnFrameToTcb` that also
drops the delivered message (`TCB.withDeliveredFrame`), one `updateTcb`. -/
def writeDeliveredFrameToTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) : SystemState :=
  st.updateTcb tid (·.withDeliveredFrame frame)

theorem writeDeliveredFrameToTcb_id_when_not_tcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) (hNot : st.getTcb? tid = none) :
    writeDeliveredFrameToTcb st tid frame = st :=
  SystemState.updateTcb_eq_self_of_none hNot _

theorem writeDeliveredFrameToTcb_objects_ne (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hObjInv : st.objects.invExt) :
    (writeDeliveredFrameToTcb st tid frame).objects[oid]? = st.objects[oid]? :=
  SystemState.updateTcb_objects_ne st tid _ oid (fun h => hNe h.symm) hObjInv

theorem writeDeliveredFrameToTcb_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) :
    (writeDeliveredFrameToTcb st tid frame).scheduler = st.scheduler :=
  SystemState.updateTcb_scheduler st tid _

theorem writeDeliveredFrameToTcb_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) :
    (writeDeliveredFrameToTcb st tid frame).machine = st.machine :=
  SystemState.updateTcb_machine st tid _

theorem writeDeliveredFrameToTcb_declassificationAuditLog_eq (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : SyscallReturnFrame) :
    (writeDeliveredFrameToTcb st tid frame).declassificationAuditLog =
      st.declassificationAuditLog := by
  unfold writeDeliveredFrameToTcb
  rw [SystemState.updateTcb_eq_objects_update]

theorem writeDeliveredFrameToTcb_kindPreservingWrite (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : SyscallReturnFrame) (hObjInv : st.objects.invExt) :
    SeLe4n.Model.kindPreservingWrite st (writeDeliveredFrameToTcb st tid frame) :=
  SystemState.updateTcb_kindPreservingWrite st tid _ hObjInv

theorem writeDeliveredFrameToTcb_cdt_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) :
    (writeDeliveredFrameToTcb st tid frame).cdt = st.cdt :=
  SystemState.updateTcb_cdt st tid _

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
  have hRead : (writeReturnFrameToTcb st tid frame).getTcb? tid
      = some (tcb.withReturnFrame frame) := by
    unfold writeReturnFrameToTcb
    rw [SystemState.updateTcb_getTcb?_self st tid _ hObjInv, hTcb]
    rfl
  unfold readReturnFrame
  rw [hRead]
  simp only
  have hReads := (tcb.registerContext).stageReturnFrame_reads_back frame
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hReads
  simp only [SeLe4n.Model.TCB.withReturnFrame_registerContext, h0, h1, h2, h3, h4, h5]
  cases frame
  simp [UInt64.ofNat_toNat]

/-- **WS-ZA ZA4.7**: the delivery write reads back the same frame. -/
theorem readReturnFrame_writeDeliveredFrame
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hObjInv : st.objects.invExt) :
    readReturnFrame (writeDeliveredFrameToTcb st tid frame) tid = frame := by
  have hRead : (writeDeliveredFrameToTcb st tid frame).getTcb? tid
      = some (tcb.withDeliveredFrame frame) := by
    unfold writeDeliveredFrameToTcb
    rw [SystemState.updateTcb_getTcb?_self st tid _ hObjInv, hTcb]
    rfl
  unfold readReturnFrame
  rw [hRead]
  simp only
  have hReads := (tcb.registerContext).stageReturnFrame_reads_back frame
  obtain ⟨h0, h1, h2, h3, h4, h5⟩ := hReads
  simp only [SeLe4n.Model.TCB.withDeliveredFrame_registerContext, h0, h1, h2, h3, h4, h5]
  cases frame
  simp [UInt64.ofNat_toNat]

/-- **WS-ZA ZA4.7**: and leaves the thread holding no message. -/
theorem writeDeliveredFrameToTcb_getTcb?_self
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : SyscallReturnFrame)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) (hObjInv : st.objects.invExt) :
    (writeDeliveredFrameToTcb st tid frame).getTcb? tid
      = some (tcb.withDeliveredFrame frame) := by
  unfold writeDeliveredFrameToTcb
  rw [SystemState.updateTcb_getTcb?_self st tid _ hObjInv, hTcb]
  rfl

/-- WS-RA RA.B.1 frame lemma: objects off the target are untouched. -/
theorem writeReturnFrameToTcb_objects_ne
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hObjInv : st.objects.invExt) :
    (writeReturnFrameToTcb st tid frame).objects[oid]? = st.objects[oid]? := by
  unfold writeReturnFrameToTcb
  exact SystemState.updateTcb_objects_ne st tid _ oid (fun h => hNe h.symm) hObjInv

/-- WS-RA RA.B.1 frame lemma: the scheduler is untouched. -/
theorem writeReturnFrameToTcb_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) :
    (writeReturnFrameToTcb st tid frame).scheduler = st.scheduler := by
  unfold writeReturnFrameToTcb
  exact SystemState.updateTcb_scheduler st tid _

/-- WS-RA RA.B.1 frame lemma: the machine is untouched — the staging
writes the TCB's saved context only, never the machine mirror. -/
theorem writeReturnFrameToTcb_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) :
    (writeReturnFrameToTcb st tid frame).machine = st.machine := by
  unfold writeReturnFrameToTcb
  exact SystemState.updateTcb_machine st tid _

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
  rw [SystemState.updateTcb_eq_objects_update]

/-- WS-RA RA.B.1: staging a frame for a target that is not a TCB is the
identity — the totality witness, mirroring
`writeFfiRegistersToTcb_id_when_not_tcb`. -/
theorem writeReturnFrameToTcb_id_when_not_tcb
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame)
    (hNot : st.getTcb? tid = none) :
    writeReturnFrameToTcb st tid frame = st := by
  unfold writeReturnFrameToTcb
  exact SystemState.updateTcb_eq_self_of_none hNot _

/-- **WS-BP BP7.8: the message registers past the fourth, written into the
receiver's IPC buffer.**  Register `4 + i` goes to overflow slot `i`, at the
address the shared resolver answers for a **writable** mapping
(`IpcBufferRead.ipcBufferSlotPAddr?` with `needWrite := true`), and the list
stops at the first slot it refuses — so what arrives is always a prefix, and
the frame's length (`returnMessageInfo`'s `overflow`) is that prefix's length.
seL4 answers a receiver with no usable buffer the same way: `copyMRs` copies the
registers alone and `setMessageInfo` reports what was copied.

Each word is a `PhysicalWrite.storeUserWord`, recorded on the ledger the syscall
seam drains (`Architecture.recordPhysicalWrites`) rather than written into the
model's `machine.memory`: the model holds no thread's memory — the entry reads a
sender's words from RAM when it needs them (`IpcBufferRead.syncUserWords`) — so
the store is owed to RAM, exactly as a descriptor store is. -/
def overflowDeliveryWrites (st : SystemState) (tcb : TCB) :
    List SeLe4n.RegValue → Nat → List PhysicalWrite
  | [], _ => []
  | w :: rest, idx =>
      match IpcBufferRead.ipcBufferSlotPAddr? st tcb idx true with
      | some pa => .storeUserWord pa w.val.toUInt64 :: overflowDeliveryWrites st tcb rest (idx + 1)
      | none => []

/-- The overflow words a delivery of `msg` to `tcb` writes. -/
def messageOverflowWrites (st : SystemState) (tcb : TCB) (msg : IpcMessage) :
    List PhysicalWrite :=
  overflowDeliveryWrites st tcb (msg.registers.toList.drop 4) 0

/-- **WS-ZA ZA4.7**: the compiled `messageOverflowWrites` — a message of at most
four words writes nothing, answered without listing its words. -/
@[inline] def messageOverflowWritesImpl (st : SystemState) (tcb : TCB) (msg : IpcMessage) :
    List PhysicalWrite :=
  if msg.registers.size ≤ 4 then [] else overflowDeliveryWrites st tcb (msg.registers.toList.drop 4) 0

@[csimp] theorem messageOverflowWrites_eq_impl : @messageOverflowWrites = @messageOverflowWritesImpl := by
  funext st tcb msg
  unfold messageOverflowWrites messageOverflowWritesImpl
  split
  · next h =>
    rw [List.drop_eq_nil_of_le (by simpa using h)]
    rfl
  · rfl

/-- Every word a delivery writes is a user-word store. -/
theorem overflowDeliveryWrites_storeUserWord (st : SystemState) (tcb : TCB) :
    ∀ (ws : List SeLe4n.RegValue) (idx : Nat) (w : PhysicalWrite),
      w ∈ overflowDeliveryWrites st tcb ws idx → ∃ pa v, w = .storeUserWord pa v
  | [], _, _, h => by simp [overflowDeliveryWrites] at h
  | x :: rest, idx, w, h => by
      unfold overflowDeliveryWrites at h
      split at h
      · rename_i pa _
        rcases List.mem_cons.mp h with h | h
        · exact ⟨pa, _, h⟩
        · exact overflowDeliveryWrites_storeUserWord st tcb rest (idx + 1) w h
      · simp at h

/-- A delivery writes no more words than the message carries past the fourth. -/
theorem overflowDeliveryWrites_length_le (st : SystemState) (tcb : TCB) :
    ∀ (ws : List SeLe4n.RegValue) (idx : Nat),
      (overflowDeliveryWrites st tcb ws idx).length ≤ ws.length
  | [], _ => by simp [overflowDeliveryWrites]
  | x :: rest, idx => by
      unfold overflowDeliveryWrites
      split
      · simp only [List.length_cons]
        exact Nat.succ_le_succ (overflowDeliveryWrites_length_le st tcb rest (idx + 1))
      · simp

/-- WS-RA RA.B.6: stage the message a completed receive-shaped syscall
delivered into the **caller's own** `pendingMessage` — the arm-level
staging for the non-blocking consume paths (`.receive` / `.replyRecv`).

Guarded on the caller's post-state being `.ready`: a caller that blocked
has no fresh delivery (its `pendingMessage` may hold a stale message from
an earlier exchange), stages nothing here, and its frame is owed by the
unblocking transition (RA.B.5b) with delivery at the context restore
(WS-BP BP7.6).  A `.ready` caller with no `pendingMessage` (a zero-length
delivery is still `some` with an empty register array) stages nothing —
the boundary's shape-driven read then sees whatever the arm staged, so
receive arms pair this with the shape theorem rather than relying on
incidental register content.

`capInfo` (PR #866 round-2 review) is the delivering transfer's report — the
arm's transfer-summary `capInfo`, or `0` on a path that runs no transfer: the
number of capabilities seL4's `transferCaps` **processed** (installed or
unwrapped), plus four times the mask of those it unwrapped.  It is never the
number of addresses the sender's frame names, which records what the sender
*requested*.

**WS-BP BP7.8**: the registers past the fourth are written into the
receiver's IPC buffer (`messageOverflowWrites`), recorded on the physical-write
ledger, and the frame's length counts them. -/
def stageDeliveredMessage (st : SystemState) (tid : SeLe4n.ThreadId)
    (capInfo : Nat) : SystemState :=
  match st.getTcb? tid with
  | some tcb =>
      if tcb.ipcState = .ready then
        match tcb.pendingMessage with
        | some msg =>
            recordPhysicalWrites
              (writeDeliveredFrameToTcb st tid (returnFrameOfMessage msg capInfo
                (messageOverflowWrites st tcb msg).length))
              (messageOverflowWrites st tcb msg)
        | none => st
      else st
  | none => st

/-- **WS-RR RR8.16** (`v0.35.200`): staging a return frame is a
`kindPreservingWrite` and writes neither derivation table — it is `updateTcb`,
so both are that primitive's own facts rather than a re-derivation here. -/
theorem writeReturnFrameToTcb_kindPreservingWrite (st : SystemState)
    (tid : SeLe4n.ThreadId) (frame : SyscallReturnFrame) (hObjInv : st.objects.invExt) :
    SeLe4n.Model.kindPreservingWrite st (writeReturnFrameToTcb st tid frame) :=
  SystemState.updateTcb_kindPreservingWrite st tid _ hObjInv

theorem writeReturnFrameToTcb_cdt_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : SyscallReturnFrame) :
    (writeReturnFrameToTcb st tid frame).cdt = st.cdt :=
  SystemState.updateTcb_cdt st tid _

/-- RA.B.5b frame lemma: delivery staging never touches the scheduler —
every arm is either `writeReturnFrameToTcb` (whose `_scheduler_eq` this
lifts) or the identity. -/
theorem stageDeliveredMessage_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (capInfo : Nat) :
    (stageDeliveredMessage st tid capInfo).scheduler = st.scheduler := by
  unfold stageDeliveredMessage
  cases st.getTcb? tid with
  | none => rfl
  | some tcb =>
      by_cases hReady : tcb.ipcState = .ready
      · simp only [hReady, if_pos]
        cases tcb.pendingMessage with
        | none => rfl
        | some msg => exact writeDeliveredFrameToTcb_scheduler_eq st tid _
      · simp [hReady]

/-- RA.B.5b frame lemma: delivery staging never touches the machine — the
staging writes the TCB's saved context only, never the machine mirror. -/
theorem stageDeliveredMessage_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (capInfo : Nat) :
    (stageDeliveredMessage st tid capInfo).machine = st.machine := by
  unfold stageDeliveredMessage
  cases st.getTcb? tid with
  | none => rfl
  | some tcb =>
      by_cases hReady : tcb.ipcState = .ready
      · simp only [hReady, if_pos]
        cases tcb.pendingMessage with
        | none => rfl
        | some msg => exact writeDeliveredFrameToTcb_machine_eq st tid _
      · simp [hReady]

/-- WS-SM SM9.C.8 frame lemma: delivery staging never touches the
declassification audit trail (the lift of
`writeReturnFrameToTcb_declassificationAuditLog_eq`). -/
theorem stageDeliveredMessage_declassificationAuditLog_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (capInfo : Nat) :
    (stageDeliveredMessage st tid capInfo).declassificationAuditLog =
      st.declassificationAuditLog := by
  unfold stageDeliveredMessage
  cases st.getTcb? tid with
  | none => rfl
  | some tcb =>
      by_cases hReady : tcb.ipcState = .ready
      · simp only [hReady, if_pos]
        cases tcb.pendingMessage with
        | none => rfl
        | some msg => exact writeDeliveredFrameToTcb_declassificationAuditLog_eq st tid _
      · simp [hReady]

/-- A blocked caller stages nothing — `stageDeliveredMessage` is the
identity whenever the caller's post-state is not `.ready`. -/
theorem stageDeliveredMessage_id_when_blocked
    (st : SystemState) (tid : SeLe4n.ThreadId) (capInfo : Nat) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb)
    (hBlocked : tcb.ipcState ≠ .ready) :
    stageDeliveredMessage st tid capInfo = st := by
  unfold stageDeliveredMessage
  rw [hTcb]
  simp [hBlocked]

/-- A queried-word frame — `.serviceQuery`'s shape (and SM9.A's audit
reads): the word in `x0`, success `x1`, no message registers. -/
def returnFrameOfWord (w : UInt64) : SyscallReturnFrame :=
  { x0 := w }

/-- WS-ZA ZA4: a return frame's six words written into `x0`-`x5`
(`stageReturnFrame` of the frame they make).  A call, so the file arrives as
an owned argument and an exclusive one is written in place. -/
def stageReturnWords (rf : SeLe4n.RegisterFile) (w0 w1 w2 w3 w4 w5 : UInt64) :
    SeLe4n.RegisterFile :=
  { rf with x0 := w0, x1 := w1, x2 := w2, x3 := w3, x4 := w4, x5 := w5 }

/-- WS-ZA ZA4: `TCB.withReturnFrame` from the frame's six words.  A call, so
the TCB arrives owned and its context is handed on with one reference. -/
def _root_.SeLe4n.Model.TCB.withReturnWords (t : TCB) (w0 w1 w2 w3 w4 w5 : UInt64) : TCB :=
  { t with registerContext := stageReturnWords t.registerContext w0 w1 w2 w3 w4 w5 }

/-- **WS-ZA ZA5.5**: a queried word's frame staged as its six words — the word
in `x0`, the rest zero — so a writer builds no frame record. -/
theorem writeReturnFrameToTcb_ofWord_eq_words (st : SystemState) (tid : SeLe4n.ThreadId)
    (w : UInt64) :
    writeReturnFrameToTcb st tid (returnFrameOfWord w) =
      st.updateTcb tid (SeLe4n.Model.TCB.withReturnWords · w 0 0 0 0 0) := rfl

-- ============================================================================
-- §4d  Staging for a woken counterparty (RA.B.5b)
-- ============================================================================
--
-- The blocked-waiter half of §3.5: when an unblocking syscall wakes a
-- counterparty that was blocked in ITS OWN syscall, the woken thread's
-- return frame must be staged now — its own boundary crossing ended in
-- `.blocks` with no frame written, and the context restore (WS-BP BP7.6) delivers
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
`capInfo` per `stageDeliveredMessage` (PR #866 round-2): the
delivering transfer's `capInfo`, `0` on transfer-free paths. -/
@[inline] def stageWokenDelivery (st : SystemState) (woken? : Option SeLe4n.ThreadId)
    (capInfo : Nat) : SystemState :=
  match woken? with
  | some tid => stageDeliveredMessage st tid capInfo
  | none => st

@[simp] theorem stageWokenDelivery_none (st : SystemState)
    (capInfo : Nat) :
    stageWokenDelivery st none capInfo = st := rfl

@[simp] theorem stageWokenDelivery_some (st : SystemState)
    (tid : SeLe4n.ThreadId) (capInfo : Nat) :
    stageWokenDelivery st (some tid) capInfo
      = stageDeliveredMessage st tid capInfo := rfl

/-- WS-RA RA.B.5b: stage the **unit success frame** for a woken plain
sender whose send completed at a rendezvous.  Guarded on the
counterparty's post-state being `.ready` with **no** pending delivery: a
consumed `Call` sender lands `.blockedOnReply` (frame owed by the reply
path), and a `.ready` thread WITH a pending delivery is a payload wake
owed `returnFrameOfMessage` by `stageWokenDelivery` instead — staging
zero there would clobber a real value.

`@[inline]` so a caller that names the woken thread (`some s`) builds no
`Option` cell: the match folds at the call site (WS-ZA ZA4.7). -/
@[inline] def stageWokenSendCompletion (st : SystemState)
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
    (woken? : Option SeLe4n.ThreadId) (capInfo : Nat) :
    (stageWokenDelivery st woken? capInfo).scheduler = st.scheduler := by
  cases woken? with
  | none => rfl
  | some tid => exact stageDeliveredMessage_scheduler_eq st tid capInfo

/-- **WS-RR RR8.16** (`v0.35.200`): delivery staging is a `kindPreservingWrite`
— every arm is either the identity or one return-frame write. -/
theorem stageDeliveredMessage_kindPreservingWrite (st : SystemState)
    (tid : SeLe4n.ThreadId) (capInfo : Nat) (hObjInv : st.objects.invExt) :
    SeLe4n.Model.kindPreservingWrite st (stageDeliveredMessage st tid capInfo) := by
  unfold stageDeliveredMessage
  cases st.getTcb? tid with
  | none => exact SeLe4n.Model.kindPreservingWrite.refl st
  | some tcb =>
      by_cases hReady : tcb.ipcState = .ready
      · simp only [hReady, if_pos]
        cases tcb.pendingMessage with
        | none => exact SeLe4n.Model.kindPreservingWrite.refl st
        | some msg =>
          exact SeLe4n.Model.kindPreservingWrite.trans
            (writeDeliveredFrameToTcb_kindPreservingWrite st tid _ hObjInv) (.of_objects_eq rfl)
      · simp only [hReady, if_false]
        exact SeLe4n.Model.kindPreservingWrite.refl st

/-- **WS-RR RR8.16** (`v0.35.200`): ...and writes neither derivation table. -/
theorem stageDeliveredMessage_cdt_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (capInfo : Nat) :
    (stageDeliveredMessage st tid capInfo).cdt = st.cdt := by
  unfold stageDeliveredMessage
  cases st.getTcb? tid with
  | none => all_goals rfl
  | some tcb =>
      by_cases hReady : tcb.ipcState = .ready
      · simp only [hReady, if_pos]
        cases tcb.pendingMessage with
        | none => all_goals rfl
        | some msg => exact writeDeliveredFrameToTcb_cdt_eq st tid _
      · simp only [hReady, if_false]
        all_goals rfl

/-- **WS-RR RR8.16** (`v0.35.200`): and the woken-delivery stager inherits both. -/
theorem stageWokenDelivery_kindPreservingWrite (st : SystemState)
    (woken? : Option SeLe4n.ThreadId) (capInfo : Nat) (hObjInv : st.objects.invExt) :
    SeLe4n.Model.kindPreservingWrite st (stageWokenDelivery st woken? capInfo) := by
  cases woken? with
  | none => exact SeLe4n.Model.kindPreservingWrite.refl st
  | some tid => exact stageDeliveredMessage_kindPreservingWrite st tid capInfo hObjInv

theorem stageWokenDelivery_cdt_eq (st : SystemState)
    (woken? : Option SeLe4n.ThreadId) (capInfo : Nat) :
    (stageWokenDelivery st woken? capInfo).cdt = st.cdt := by
  cases woken? with
  | none => all_goals rfl
  | some tid => exact stageDeliveredMessage_cdt_eq st tid capInfo

/-- RA.B.5b frame lemma: neither stager touches the machine. -/
theorem stageWokenDelivery_machine_eq (st : SystemState)
    (woken? : Option SeLe4n.ThreadId) (capInfo : Nat) :
    (stageWokenDelivery st woken? capInfo).machine = st.machine := by
  cases woken? with
  | none => rfl
  | some tid => exact stageDeliveredMessage_machine_eq st tid capInfo

/-- WS-SM SM9.C.8 frame lemma: the delivery stager never touches the
declassification audit trail. -/
theorem stageWokenDelivery_declassificationAuditLog_eq (st : SystemState)
    (woken? : Option SeLe4n.ThreadId) (capInfo : Nat) :
    (stageWokenDelivery st woken? capInfo).declassificationAuditLog =
      st.declassificationAuditLog := by
  cases woken? with
  | none => rfl
  | some tid => exact stageDeliveredMessage_declassificationAuditLog_eq st tid capInfo

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
`returnFrameOfMessage msg` into its saved register context — its length
counting the overflow words written into the waiter's IPC buffer (WS-BP BP7.8)
— and the boundary read recovers it bit for bit.  Delivery is the context restore
(WS-BP BP7.6)'s; what this pins is that the frame is *there* to deliver. -/
theorem blockedReturn_staged_in_waiter_frame
    (st : SystemState) (w : SeLe4n.ThreadId) (tcb : TCB) (msg : IpcMessage)
    (capInfo : Nat)
    (hTcb : st.getTcb? w = some tcb)
    (hReady : tcb.ipcState = .ready)
    (hMsg : tcb.pendingMessage = some msg)
    (hObjInv : st.objects.invExt) :
    readReturnFrame (stageWokenDelivery st (some w) capInfo) w
      = returnFrameOfMessage msg capInfo (messageOverflowWrites st tcb msg).length := by
  show readReturnFrame (stageDeliveredMessage st w capInfo) w
    = returnFrameOfMessage msg capInfo (messageOverflowWrites st tcb msg).length
  unfold stageDeliveredMessage
  rw [hTcb]
  simp only [hReady, hMsg]
  exact readReturnFrame_writeDeliveredFrame st w
    (returnFrameOfMessage msg capInfo (messageOverflowWrites st tcb msg).length)
    tcb hTcb hObjInv

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

/-- The status label of an error: discriminant `d` rides as
`errorLabelBase + d`.  Never `0` (the base is positive) and never below the
base, so no error can be read as a delivered message. -/
@[inline] def errorLabel (e : KernelError) : Nat :=
  errorLabelBase + e.toDiscriminant

/-- Decode a label back to its error: below the base is not an error
(`none` — success, or a delivered message's label), at or above it is
discriminant `label - errorLabelBase`, unknown discriminants failing closed. -/
def ofErrorLabel? (label : Nat) : Option KernelError :=
  if errorLabelBase ≤ label then KernelError.ofDiscriminant? (label - errorLabelBase)
  else none

/-- §3.1's non-aliasing: no error's label is the success label. -/
theorem errorLabel_never_zero (e : KernelError) : errorLabel e ≠ 0 := by
  unfold errorLabel; rw [errorLabelBase_eq]; omega

/-- Every error's label is in the status range. -/
theorem errorLabelBase_le_errorLabel (e : KernelError) : errorLabelBase ≤ errorLabel e :=
  Nat.le_add_right _ _

/-- The success label decodes as success. -/
theorem ofErrorLabel?_zero : ofErrorLabel? 0 = none := by
  unfold ofErrorLabel?; rw [errorLabelBase_eq]; decide

/-- **A delivered message's label is never read as an error** — the property
the fault handler's receive needs, and the one the offset scheme lacked.
Every label below the base, the four fault tags included, decodes as
"no kernel error". -/
theorem ofErrorLabel?_none_of_lt_base (label : Nat) (h : label < errorLabelBase) :
    ofErrorLabel? label = none := by
  unfold ofErrorLabel?
  rw [if_neg (Nat.not_le.mpr h)]

/-- RA.A.5 — every error's code survives the label round trip; the payload
rides in the message registers (`errorFrame_payload_roundtrip`). -/
theorem errorLabel_roundtrip (e : KernelError) :
    ofErrorLabel? (errorLabel e) = some e.erasePayload := by
  unfold ofErrorLabel? errorLabel
  rw [if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
  exact KernelError.ofDiscriminant?_toDiscriminant e

/-- The decode side over the whole status range: the base plus
each discriminant below `kernelErrorEncodingBound` that is not retired hits
an error and re-encodes to itself, the base plus `kernelErrorEncodingBound`
(the first discriminant past the table) is rejected, and the label just *below* the base
is not an error at all — so the range boundary is pinned from both sides on
the inhabited label space. -/
theorem errorLabel_zero_iff_success :
    ofErrorLabel? 0 = none ∧
      (∀ n, n < KernelError.kernelErrorEncodingBound →
        KernelError.retiredDiscriminants.contains n = false →
        ((ofErrorLabel? (errorLabelBase + n)).map errorLabel) = some (errorLabelBase + n)) ∧
      ofErrorLabel? (errorLabelBase + KernelError.kernelErrorEncodingBound) = none ∧
      ofErrorLabel? (errorLabelBase - 1) = none := by
  refine ⟨ofErrorLabel?_zero, ?_, ?_, ?_⟩
  · intro n hn hNr
    have hRt := KernelError.toDiscriminant_ofDiscriminant?.1 n hn hNr
    unfold ofErrorLabel? errorLabel
    rw [if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    cases hE : KernelError.ofDiscriminant? n with
    | none => rw [hE] at hRt; exact absurd hRt (by simp)
    | some e =>
        rw [hE] at hRt
        simp only [Option.map_some, Option.some.injEq] at hRt ⊢
        rw [hRt]
  · unfold ofErrorLabel?
    rw [if_pos (Nat.le_add_right _ _), Nat.add_sub_cancel_left]
    exact KernelError.toDiscriminant_ofDiscriminant?.2
  · apply ofErrorLabel?_none_of_lt_base
    rw [errorLabelBase_eq]; decide

/-- RA.A.6 — every status label fits the 52-bit `MessageInfo` label field:
the range is sized so `errorLabelBase + 255 = maxLabel`, and every
discriminant is below `KernelError.kernelErrorEncodingBound`. -/
theorem kernelErrorFitsLabel (e : KernelError) :
    errorLabel e ≤ MessageInfo.maxLabel := by
  have h := KernelError.toDiscriminant_lt e
  rw [show KernelError.kernelErrorEncodingBound = 61 from rfl] at h
  unfold errorLabel
  rw [errorLabelBase_eq, show MessageInfo.maxLabel = 0xFFFFFFFFFFFFF by decide]
  omega

/-- The status range is exactly the top of the field: the sentinel
`maxLabel` is its last member. -/
theorem errorLabelBase_add_range_eq_maxLabel :
    errorLabelBase + errorLabelRangeSize = MessageInfo.maxLabel + 1 := by
  rw [errorLabelBase_eq]; decide

/-- The load-bearing negative for RA.A.6: an over-wide `x1` word is not
silently truncated — `MessageInfo.decode` fail-closes on any word whose
label bits exceed `maxLabel` (bits ≥ 64 set), so a corrupted status
register decodes as an explicit failure rather than a wrong error. -/
theorem overWideLabel_rejected :
    MessageInfo.decode ((MessageInfo.maxLabel + 1) <<< 12) = none := by
  decide

/-- **An error's `x1` word**: its status label in bits 12-63 and every other
field `0`, shifted as a machine word.  The label is in the top of the 52-bit
range, so the shifted value is past `2^63` and a `Nat` encoding of it would be a
heap number; the word is `MessageInfo.encode`'s (`errorLabelWord_eq_encode`). -/
@[inline] def errorLabelWord (e : KernelError) : UInt64 := (errorLabel e).toUInt64 <<< 12

theorem errorLabelWord_eq_encode (e : KernelError) :
    errorLabelWord e =
      (MessageInfo.encode { length := 0, extraCaps := 0, label := errorLabel e }).toUInt64 := by
  have hLt := KernelError.toDiscriminant_lt e
  unfold errorLabelWord errorLabel
  generalize e.toDiscriminant = d at hLt ⊢
  rw [show KernelError.kernelErrorEncodingBound = 61 from rfl] at hLt
  revert d
  decide

/-- **An error's `x1` word with its message length**: the status label in bits
12-63 and the length (at most five words) in bits 0-6, as seL4's
`replyFromKernel_error` writes `seL4_MessageInfo_new(error, 0, 0, len)`. -/
@[inline] def errorInfoWord (e : KernelError) (len : Nat) : UInt64 :=
  errorLabelWord e ||| len.toUInt64

/-- The error frame the boundary returns on a failed syscall: `x0 = 0`, the
status label and the message length in `x1`, and the payload's first four words
in `x2`-`x5` (seL4's `msgRegisters`, MR0-MR3).  A fifth word goes to the
caller's IPC buffer (`recordErrorOverflow`), and `overflowWritten` says whether
it went, so the length is the one seL4's `setMR` chain returns
(`KernelError.messageLength`).  Computed at the boundary, **never staged into
the TCB** — the error path writes no thread's registers (RA.B.4). -/
def errorFrame (e : KernelError) (overflowWritten : Bool) : SyscallReturnFrame :=
  { x1 := errorInfoWord e (e.messageLength overflowWritten),
    x2 := e.payloadWord 0, x3 := e.payloadWord 1,
    x4 := e.payloadWord 2, x5 := e.payloadWord 3 }

/-- The `x1` word of every discriminant and every length an error message can
have decodes to that discriminant's label and that length.  Decided over the
table. -/
private theorem errorInfoWord_decodes_discriminants :
    ∀ d, d < KernelError.kernelErrorEncodingBound → ∀ len, len ≤ 5 →
      MessageInfo.decode
          (((errorLabelBase + d).toUInt64 <<< 12) ||| len.toUInt64).toNat =
        some { length := len, extraCaps := 0, label := errorLabelBase + d } := by
  decide

/-- An error frame's `x1` decodes back to the `MessageInfo` that names the
error's code and its message's length — the encode side is inside the
decoder's fail-closed bounds. -/
theorem errorFrame_x1_decodes (e : KernelError) (w : Bool) :
    MessageInfo.decode (errorFrame e w).x1.toNat =
      some { length := e.messageLength w, extraCaps := 0, label := errorLabel e } :=
  errorInfoWord_decodes_discriminants _ (KernelError.toDiscriminant_lt e) _
    (KernelError.messageLength_le e w)

/-- **The payload round trip**: the frame's message registers, and the fifth
word where the payload has one, are the payload's words in seL4's order —
`setMRs_syscall_error`'s, read back word for word. -/
theorem errorFrame_payload_roundtrip (e : KernelError) (w : Bool) :
    (errorFrame e w).x2 = e.payloadWord 0 ∧ (errorFrame e w).x3 = e.payloadWord 1 ∧
      (errorFrame e w).x4 = e.payloadWord 2 ∧ (errorFrame e w).x5 = e.payloadWord 3 ∧
      (errorFrame e w).x0 = 0 :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **Where an error's fifth payload word goes** (seL4's `setMR` past
`n_msgRegisters`): message register 4, overflow slot 0 of the caller's IPC
buffer, at the address the shared resolver answers for a writable mapping
(`IpcBufferRead.ipcBufferSlotPAddr?`, the one a delivery writes through, as
seL4's `replyFromKernel_error` takes `lookupIPCBuffer(true, thread)`).  `none`
when the payload fits the four inline registers, or the buffer does not
resolve: then the word is not written and the length stops at four
(`KernelError.messageLength`). -/
@[inline] def errorOverflowPAddr? (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : KernelError) : Option SeLe4n.PAddr :=
  if e.payloadLength ≤ 4 then none
  else
    match st.getTcb? tid with
    | some tcb => IpcBufferRead.ipcBufferSlotPAddr? st tcb 0 true
    | none => none

/-- **Write an error's fifth payload word** into the caller's IPC buffer,
`msg[4]`, as a user-word store owed to RAM (`PhysicalWrite.storeUserWord`, the
store a delivery's overflow words take, drained by the syscall seam).  Nothing
when the payload fits the inline registers or the buffer does not resolve. -/
def recordErrorOverflow (st : SystemState) (tid : SeLe4n.ThreadId) (e : KernelError) :
    SystemState :=
  match errorOverflowPAddr? st tid e with
  | some pa => st.recordPhysicalWrite (.storeUserWord pa (e.payloadWord 4))
  | none => st

/-- The frame of an error returned to `tid`: its length counts the fifth word
exactly when `recordErrorOverflow` writes it. -/
@[inline] def errorFrameFor (st : SystemState) (tid : SeLe4n.ThreadId) (e : KernelError) :
    SyscallReturnFrame :=
  errorFrame e (errorOverflowPAddr? st tid e).isSome

/-- An error whose payload fits the inline registers writes nothing. -/
theorem recordErrorOverflow_of_le_four (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : KernelError) (h : e.payloadLength ≤ 4) : recordErrorOverflow st tid e = st := by
  unfold recordErrorOverflow errorOverflowPAddr?
  rw [if_pos h]

/-- …and its frame is the one with no buffer to consult. -/
theorem errorFrameFor_of_le_four (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : KernelError) (h : e.payloadLength ≤ 4) : errorFrameFor st tid e = errorFrame e false := by
  unfold errorFrameFor errorOverflowPAddr?
  rw [if_pos h]; rfl

/-- **The error path's write** (RA.B.4, restated): it changes the state only by
the one store of the caller's `msg[4]`, and only for a five-word payload whose
buffer resolves; otherwise it changes nothing. -/
theorem recordErrorOverflow_cases (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : KernelError) :
    (errorOverflowPAddr? st tid e = none ∧ recordErrorOverflow st tid e = st) ∨
      ∃ pa, errorOverflowPAddr? st tid e = some pa ∧ e.payloadLength = 5 ∧
        recordErrorOverflow st tid e = st.recordPhysicalWrite (.storeUserWord pa (e.payloadWord 4)) := by
  unfold recordErrorOverflow
  cases hP : errorOverflowPAddr? st tid e with
  | none => exact Or.inl ⟨rfl, rfl⟩
  | some pa =>
    refine Or.inr ⟨pa, rfl, ?_, rfl⟩
    have h5 := KernelError.payloadLength_le e
    unfold errorOverflowPAddr? at hP
    split at hP
    · cases hP
    · omega

/-- The error path's write touches only the physical-write ledger. -/
theorem recordErrorOverflow_objects (st : SystemState) (tid : SeLe4n.ThreadId) (e : KernelError) :
    (recordErrorOverflow st tid e).objects = st.objects := by
  unfold recordErrorOverflow; split <;> rfl

theorem recordErrorOverflow_scheduler (st : SystemState) (tid : SeLe4n.ThreadId) (e : KernelError) :
    (recordErrorOverflow st tid e).scheduler = st.scheduler := by
  unfold recordErrorOverflow; split <;> rfl

theorem recordErrorOverflow_machine (st : SystemState) (tid : SeLe4n.ThreadId) (e : KernelError) :
    (recordErrorOverflow st tid e).machine = st.machine := by
  unfold recordErrorOverflow; split <;> rfl

theorem recordErrorOverflow_declassificationRefusals (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : KernelError) :
    (recordErrorOverflow st tid e).declassificationRefusals = st.declassificationRefusals := by
  unfold recordErrorOverflow; split <;> rfl

/-- No thread's return frame moves with the fifth word's write. -/
theorem readReturnFrame_recordErrorOverflow (st : SystemState) (tid : SeLe4n.ThreadId)
    (e : KernelError) (t : SeLe4n.ThreadId) :
    readReturnFrame (recordErrorOverflow st tid e) t = readReturnFrame st t := by
  unfold readReturnFrame SystemState.getTcb?
  rw [recordErrorOverflow_objects]

-- ============================================================================
-- §5b  Staging an error frame for a forcibly unblocked thread (WS-RR RR7.14)
-- ============================================================================

/-- **WS-RR RR7.14: the frame a forcibly unblocked thread is owed.**

The unblocking paths — `timeoutThread` and `cancelIpcBlocking` — take a thread
out of a blocking IPC with **no value to deliver**, and until this row they
staged nothing at all.  That is not a neutral omission.  A blocked thread's
boundary crossing ended in `.blocks`, so its `x0`-`x5` still hold whatever the
argument spill left there (or the trap layer's fail-closed sentinel); the context
restore (WS-BP BP7.6) delivers whatever `registerContext` holds, so the thread would
resume reading its own stale request registers as a return value.

The honest frame is an **error** frame, and which error is the design question
the WS-RA plan §3.5 deferred to this row.  The two paths get different answers
because they are different facts:

* a **timeout** is the SchedContext budget expiring under a live operation.  The
  endpoint queue entry was removed but the operation was well-formed, and the
  caller may reasonably reissue it — `.ipcTimeout`, which the enum has carried
  since WS-Z Z6 for exactly this;
* a **cancellation** is the operation being destroyed out from under the thread
  — by `.tcbSuspend` on a blocked victim, by lifecycle cleanup, or by a retype
  of an object it was blocked on.  Reissuing may be meaningless (the endpoint
  may be gone), so it is `.ipcCancelled` (WS-RR RR7.14), added rather than
  folded into `.ipcTimeout` because a userspace library cannot write a correct
  retry against a conflated code.

seL4 answers this differently: it sets the thread `Restart` so the syscall
re-executes.  This kernel has no restart state, so the crossing has to end in an
error the caller can distinguish, which is what these stage. -/
def timeoutFrame : SyscallReturnFrame := errorFrame .ipcTimeout false

/-- **WS-RR RR7.14**: the cancellation twin — see `timeoutFrame`. -/
def cancelledIpcFrame : SyscallReturnFrame := errorFrame .ipcCancelled false

/-- **WS-RR RR7.14**: stage the timeout frame into a thread's saved register
context.  The state-level spelling, for a call site that holds a `SystemState`;
a site already building the TCB record uses `TCB.withReturnFrame timeoutFrame`,
and `stageTimeoutFrame_eq_withReturnFrame` below holds the two together so the
two spellings cannot answer "what frame does a timeout owe" differently. -/
def stageTimeoutFrame (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  writeReturnFrameToTcb st tid timeoutFrame

/-- **WS-RR RR7.14**: the cancellation twin — see `stageTimeoutFrame`. -/
def stageCancelledIpcFrame (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  writeReturnFrameToTcb st tid cancelledIpcFrame

/-- **WS-RR RR7.14**: the state-level stager IS the TCB-level record update at
the target, so a transition that folds the staging into a TCB record it is
already writing commits exactly what the state-level stager would have. -/
theorem stageTimeoutFrame_eq_withReturnFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) :
    stageTimeoutFrame st tid
      = { st with
          objects := st.objects.insert tid.toObjId
              (.tcb (tcb.withReturnFrame timeoutFrame)) } := by
  unfold stageTimeoutFrame writeReturnFrameToTcb
  exact SystemState.updateTcb_eq_of_some hTcb _

/-- **WS-RR RR7.14**: and the cancellation twin. -/
theorem stageCancelledIpcFrame_eq_withReturnFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) :
    stageCancelledIpcFrame st tid
      = { st with
          objects := st.objects.insert tid.toObjId
              (.tcb (tcb.withReturnFrame cancelledIpcFrame)) } := by
  unfold stageCancelledIpcFrame writeReturnFrameToTcb
  exact SystemState.updateTcb_eq_of_some hTcb _

/-- **WS-RR RR7.14**: what a timed-out thread reads back is the timeout error,
not its own stale request registers. -/
theorem readReturnFrame_stageTimeoutFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) (hObjInv : st.objects.invExt) :
    readReturnFrame (stageTimeoutFrame st tid) tid = timeoutFrame :=
  readReturnFrame_writeReturnFrame st tid _ tcb hTcb hObjInv

/-- **WS-RR RR7.14**: and a cancelled one reads the cancellation error. -/
theorem readReturnFrame_stageCancelledIpcFrame (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (hTcb : st.getTcb? tid = some tcb) (hObjInv : st.objects.invExt) :
    readReturnFrame (stageCancelledIpcFrame st tid) tid = cancelledIpcFrame :=
  readReturnFrame_writeReturnFrame st tid _ tcb hTcb hObjInv

/-- **WS-RR RR7.14 (the load-bearing distinction)**: the two frames differ, so a
caller can tell a budget expiry from a destroyed operation.

Folding cancellation into `.ipcTimeout` would have been the cheap answer, and
this is why it is the wrong one: a userspace library retrying on timeout would
also retry a cancellation, against an endpoint that may no longer exist. -/
theorem timeout_and_cancelled_frames_differ : timeoutFrame ≠ cancelledIpcFrame := by
  decide

/-- **WS-RR RR7.14**: and neither is the success frame — a forcibly unblocked
thread never reads back a `0` status label, which is what `x1 = 0` means on
every other return path. -/
theorem unblockFrames_ne_success :
    timeoutFrame ≠ ({} : SyscallReturnFrame) ∧
      cancelledIpcFrame ≠ ({} : SyscallReturnFrame) := by
  refine ⟨?_, ?_⟩ <;> decide

/-- **WS-RR RR7.14**: both frames decode back to the error that names them, so
a userspace caller reading `x1` through `ofErrorLabel?` gets the disposition,
not an opaque word. -/
theorem unblockFrames_decode :
    ofErrorLabel? (MessageInfo.decode timeoutFrame.x1.toNat).get!.label
        = some KernelError.ipcTimeout ∧
      ofErrorLabel? (MessageInfo.decode cancelledIpcFrame.x1.toNat).get!.label
        = some KernelError.ipcCancelled := by
  constructor
  · unfold timeoutFrame
    rw [errorFrame_x1_decodes]
    exact errorLabel_roundtrip _
  · unfold cancelledIpcFrame
    rw [errorFrame_x1_decodes]
    exact errorLabel_roundtrip _

/-- **WS-RR RR7.14**: neither stager touches any object but the thread's own. -/
theorem stageTimeoutFrame_objects_ne (st : SystemState) (tid : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId) (hObjInv : st.objects.invExt) :
    (stageTimeoutFrame st tid).objects[oid]? = st.objects[oid]? :=
  writeReturnFrameToTcb_objects_ne st tid _ oid hNe hObjInv

/-- **WS-RR RR7.14**: and the cancellation twin. -/
theorem stageCancelledIpcFrame_objects_ne (st : SystemState) (tid : SeLe4n.ThreadId)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId) (hObjInv : st.objects.invExt) :
    (stageCancelledIpcFrame st tid).objects[oid]? = st.objects[oid]? :=
  writeReturnFrameToTcb_objects_ne st tid _ oid hNe hObjInv


-- ============================================================================
-- §6  SyscallOutcome — returns or blocks (RA.A.4, plan §3.5)
-- ============================================================================

/-- What a syscall execution hands the FFI boundary: a frame to write back,
or the fact that the caller blocked and the frame will be staged by the
unblocking transition (delivered at the context restore (WS-BP BP7.6)).  Outcome
is decided from the caller's **post-state** — whether `.notificationWait`
blocks depends on `pendingBadge`, `.receive` on the sender queue, `.send`
on a waiting receiver — never from the syscall id alone. -/
inductive SyscallOutcome where
  | returns (frame : SyscallReturnFrame)
  | blocks
  /-- PR #887 review round 5: the caller **took a fault at the seam** — a
  failed capability lookup delivered to its fault handler, or the fail-closed
  suspend when no handler could take it.  Like `.blocks`, no frame exists for
  it; unlike `.blocks`, the caller is not waiting on an IPC partner but on a
  fault reply that restarts it *at* the `SVC` (`svcFaultIP`), so the interim
  trap layer must not `eret` it past the `SVC` behind a sentinel frame.  Since
  WS-BP BP7.6 `.faulted` and `.blocks` alike resume the successor the context
  restore staged; the halt (`halt_after_delivered_syscall_fault`) is reached
  only on a core with no restore staged. -/
  | faulted
  deriving Repr, DecidableEq

namespace SyscallOutcome

/-- The outcome tag the `lean_syscall_dispatch_cross_core` export returns
(the frame itself crosses through the per-core mailbox — plan §3.3):
`0` = a frame was written, `1` = the caller blocked and no frame exists,
`2` = the caller faulted at the seam (PR #887 review round 5) — no frame,
and, where the context restore staged no successor, the trap layer halts
rather than resumes it. -/
def tagWord : SyscallOutcome → UInt64
  | .returns _ => 0
  | .blocks    => 1
  | .faulted   => 2

/-- The tags are distinct — a blocked outcome cannot be mistaken for a
frame delivery at the boundary. -/
theorem tagWord_blocks_ne_returns (f : SyscallReturnFrame) :
    tagWord .blocks ≠ tagWord (.returns f) := by
  simp [tagWord]

/-- …nor a faulted one for a frame delivery… -/
theorem tagWord_faulted_ne_returns (f : SyscallReturnFrame) :
    tagWord .faulted ≠ tagWord (.returns f) := by
  simp [tagWord]

/-- …nor a faulted one for a block: the trap layer's `Blocked` arm resumes
the caller behind a sentinel and its `Faulted` arm halts wherever the context
restore (WS-BP BP7.6) staged no successor, and the two must never be confused at the boundary. -/
theorem tagWord_faulted_ne_blocks : tagWord .faulted ≠ tagWord .blocks := by
  simp [tagWord]

/-- The mailbox frame for an outcome: a blocked caller's mailbox stays
zeroed (no return value exists for it — RA.C.9; its real frame is staged
by the unblocking arm and delivered by the context restore (WS-BP BP7.6)).
Until that seam flips, the hardware trap layer substitutes a fail-closed
poison frame for the premature resume (`blocked_resume_sentinel_regs` in
`svc_dispatch.rs`) — an interim HAL artifact, deliberately NOT part of
this model: the model stages real frames only. -/
def mailboxFrame : SyscallOutcome → SyscallReturnFrame
  | .returns f => f
  | .blocks    => .zero
  | .faulted   => .zero

/-- WS-ZA ZA4: **what the boundary reads of an outcome**: its tag and its
mailbox frame's six words.  The live entry carries these words across the
commit instead of the outcome, so a value-returning syscall builds neither the
outcome nor its frame. -/
@[inline] def words (o : SyscallOutcome) :
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 :=
  (o.tagWord, o.mailboxFrame.x0, o.mailboxFrame.x1, o.mailboxFrame.x2, o.mailboxFrame.x3,
   o.mailboxFrame.x4, o.mailboxFrame.x5)

/-- **The outcome the boundary's words name**: tag `0` the frame of the six
words, `1` a blocked caller, any other tag a faulted one. -/
@[inline] def ofWords :
    UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 × UInt64 → SyscallOutcome
  | (tag, w0, w1, w2, w3, w4, w5) =>
    if tag = 0 then .returns { x0 := w0, x1 := w1, x2 := w2, x3 := w3, x4 := w4, x5 := w5 }
    else if tag = 1 then .blocks
    else .faulted

/-- An outcome's words name it: the boundary loses nothing of an outcome. -/
theorem ofWords_words (o : SyscallOutcome) : ofWords o.words = o := by
  cases o <;> rfl

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

/-- `ipcStateBlocksReturn` read straight off a TCB's two IPC-state codes:
only `.ready` has both codes zero, so the caller blocked exactly when either
code is nonzero.  The compiled return paths ask this, so the state itself is
never built to be matched on (WS-ZA ZA4.7). -/
@[inline] def tcbBlocksReturn (tcb : TCB) : Bool :=
  tcb.ipcObjectCode != 0 || tcb.ipcStateCode != 0

theorem tcbBlocksReturn_eq (tcb : TCB) :
    tcbBlocksReturn tcb = ipcStateBlocksReturn tcb.ipcState := by
  unfold tcbBlocksReturn TCB.ipcState
  generalize tcb.ipcObjectCode = o
  generalize tcb.ipcStateCode = c
  rcases c with _ | _ | _ | _ | c <;> rcases o with _ | o <;> rfl

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
@[inline] def returnWindow (f : FaultRestartFrame) : SyscallReturnFrame :=
  { x0 := f.x0, x1 := f.x1, x2 := f.x2, x3 := f.x3, x4 := f.x4, x5 := f.x5 }

end FaultRestartFrame

/-- WS-RR RR4.16: stage a fault-restart frame into a register file.

**Defined through `stageReturnFrame`**, not beside it: the `x0`-`x5` window
is written by the syscall-return stager and this adds only what a restart
reaches beyond it (`x6`, `x7`, `x30`, `pc`, `sp`).  One mechanism, so a
change to how a frame lands in a register file cannot apply to syscall
returns and miss fault restarts. -/
@[inline] def _root_.SeLe4n.RegisterFile.stageRestartFrame
    (rf : SeLe4n.RegisterFile) (f : FaultRestartFrame) : SeLe4n.RegisterFile :=
  { rf.stageReturnFrame f.returnWindow with
    x6 := f.x6, x7 := f.x7, x30 := f.lr, pc := f.pc, sp := f.sp }

/-- WS-RR RR4.16: the restart PC lands in the register file's `pc` — the
word that decides where the thread resumes, and therefore the whole point of
a restart (`faultRestart_moves_pc` lifts this to the state). -/
@[simp] theorem _root_.SeLe4n.RegisterFile.stageRestartFrame_pc
    (rf : SeLe4n.RegisterFile) (f : FaultRestartFrame) :
    (rf.stageRestartFrame f).pc = f.pc := rfl

@[simp] theorem _root_.SeLe4n.RegisterFile.stageRestartFrame_sp
    (rf : SeLe4n.RegisterFile) (f : FaultRestartFrame) :
    (rf.stageRestartFrame f).sp = f.sp := rfl

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
    (rf.stageRestartFrame f).gpr ⟨30⟩ = ⟨f.lr.toNat⟩ :=
  ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- WS-RR RR4.16: registers outside the restart window survive — the
callee-saved range `x8`-`x29` is the faulted thread's own, and a handler that
did not ask to change it does not. -/
theorem _root_.SeLe4n.RegisterFile.stageRestartFrame_gpr_untouched
    (rf : SeLe4n.RegisterFile) (f : FaultRestartFrame) (r : SeLe4n.RegName)
    (hLow : 7 < r.val) (hHigh : r.val ≠ 30) :
    (rf.stageRestartFrame f).gpr r = rf.gpr r := by
  have hw : ∀ i, 7 < i → i < 31 → i ≠ 30 →
      (rf.stageRestartFrame f).word i = (rf.stageReturnFrame f.returnWindow).word i := by
    intro i h7 hLt31 hNe30
    match i, h7, hLt31, hNe30 with
    | 0, h7, _, hNe30 => exact absurd h7 (by decide)
    | 1, h7, _, hNe30 => exact absurd h7 (by decide)
    | 2, h7, _, hNe30 => exact absurd h7 (by decide)
    | 3, h7, _, hNe30 => exact absurd h7 (by decide)
    | 4, h7, _, hNe30 => exact absurd h7 (by decide)
    | 5, h7, _, hNe30 => exact absurd h7 (by decide)
    | 6, h7, _, hNe30 => exact absurd h7 (by decide)
    | 7, h7, _, hNe30 => exact absurd h7 (by decide)
    | 8, h7, _, hNe30 => rfl
    | 9, h7, _, hNe30 => rfl
    | 10, h7, _, hNe30 => rfl
    | 11, h7, _, hNe30 => rfl
    | 12, h7, _, hNe30 => rfl
    | 13, h7, _, hNe30 => rfl
    | 14, h7, _, hNe30 => rfl
    | 15, h7, _, hNe30 => rfl
    | 16, h7, _, hNe30 => rfl
    | 17, h7, _, hNe30 => rfl
    | 18, h7, _, hNe30 => rfl
    | 19, h7, _, hNe30 => rfl
    | 20, h7, _, hNe30 => rfl
    | 21, h7, _, hNe30 => rfl
    | 22, h7, _, hNe30 => rfl
    | 23, h7, _, hNe30 => rfl
    | 24, h7, _, hNe30 => rfl
    | 25, h7, _, hNe30 => rfl
    | 26, h7, _, hNe30 => rfl
    | 27, h7, _, hNe30 => rfl
    | 28, h7, _, hNe30 => rfl
    | 29, h7, _, hNe30 => rfl
    | 30, h7, _, hNe30 => exact absurd rfl hNe30
    | n + 31, _, h, _ => exact absurd h (by omega)
  unfold SeLe4n.RegisterFile.gpr
  split
  · rename_i hr
    rw [hw r.val hLow hr hHigh, SeLe4n.RegisterFile.stageReturnFrame_word]
    simp only [show r.val ≠ 0 by omega, show r.val ≠ 1 by omega, show r.val ≠ 2 by omega,
      show r.val ≠ 3 by omega, show r.val ≠ 4 by omega, show r.val ≠ 5 by omega, if_false]
  · rfl

/-- WS-RR RR4.16: stage a restart frame into a TCB's saved register context —
the single record update the restart path goes through, mirroring
`TCB.withReturnFrame`.  `registerContext` moves; every other TCB field is
definitionally unchanged. -/
@[inline] def _root_.SeLe4n.Model.TCB.withRestartFrame (tcb : TCB) (f : FaultRestartFrame) : TCB :=
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
to its totality posture (a non-TCB target returns the state unchanged) and,
since `v0.35.69`, to its primitive: the typed in-place rewrite
`SystemState.updateTcb`. -/
def writeRestartFrameToTcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : FaultRestartFrame) : SystemState :=
  st.updateTcb tid (·.withRestartFrame frame)

/-- WS-RR RR4.16 (frame): the restart writeback never touches the scheduler —
restarting a thread installs registers; making it runnable again is the
separate act the delivery's counterpart performs. -/
@[simp] theorem writeRestartFrameToTcb_scheduler_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame) :
    (writeRestartFrameToTcb st tid frame).scheduler = st.scheduler := by
  unfold writeRestartFrameToTcb; exact SystemState.updateTcb_scheduler st tid _

/-- WS-RR RR4.16 (frame): nor the machine mirror — same posture as
`writeReturnFrameToTcb`, and for the same reason (the context restore (WS-BP BP7.6)
owns that mirror). -/
@[simp] theorem writeRestartFrameToTcb_machine_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame) :
    (writeRestartFrameToTcb st tid frame).machine = st.machine := by
  unfold writeRestartFrameToTcb; exact SystemState.updateTcb_machine st tid _

/-- WS-RR RR4.16 (frame): nor the declassification audit trail. -/
@[simp] theorem writeRestartFrameToTcb_declassificationAuditLog_eq
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame) :
    (writeRestartFrameToTcb st tid frame).declassificationAuditLog
      = st.declassificationAuditLog := by
  unfold writeRestartFrameToTcb; rw [SystemState.updateTcb_eq_objects_update]

/-- WS-RR RR4.16 (frame): every object but the restarted thread's is
untouched — the restart is a single-TCB write. -/
theorem writeRestartFrameToTcb_objects_ne
    (st : SystemState) (tid : SeLe4n.ThreadId) (frame : FaultRestartFrame)
    (oid : SeLe4n.ObjId) (hNe : oid ≠ tid.toObjId)
    (hObjInv : st.objects.invExt) :
    (writeRestartFrameToTcb st tid frame).objects[oid]? = st.objects[oid]? := by
  unfold writeRestartFrameToTcb
  exact SystemState.updateTcb_objects_ne st tid _ oid (fun h => hNe h.symm) hObjInv

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
    (tcb.withRestartFrame frame).registerContext.pc = frame.pc := by
  refine ⟨?_, rfl⟩
  unfold writeRestartFrameToTcb
  rw [SystemState.updateTcb_getTcb?_self st tid _ hObjInv, hTcb]
  rfl

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
* Version **2** — the seL4 frame convention: `x0` the full-width value,
  `x1` a `MessageInfo` whose label carried the error **offset by one**
  (`d + 1`), `x2`-`x5` message registers.  Retired at WS-RR RR4 because a
  delivered fault message's `seL4_Fault_tag` label decoded as a kernel error.
* Version **3** — the same frame, with kernel status in the **top** of the
  20-bit label range (`errorLabelBase + d`, see `errorLabel`) and every
  delivered message's label below it.  A v2 decoder reads a v3 error frame as
  `UnknownKernelError` and a v3 fault delivery as a spurious error, which is
  why this is a version bump and not a patch.
* Version **4** — seL4's `seL4_MessageInfo_t` layout: `capsUnwrapped` in
  bits 9-11 and the label from bit 12, and the IPC buffer is seL4's
  `seL4_IPCBuffer`: a `tag` word first, so message register `i` is word
  `1 + i`, then `userData`, the `caps_or_badges` words and the receive path
  (`receiveCNode`, `receiveIndex`, `receiveDepth`), 128 words.  The label is
  seL4's 52 bits (bits 12-63), so the kernel-status range is the top of that
  field, and a send names its extra capabilities in its buffer's
  `caps_or_badges` words (seL4's `lookupExtraCaps`), not in message
  registers.  A v3 decoder reads every v4 label shifted by three bits and
  every overflow word five words early, so this is a version bump.
* **5** — an error frame carries seL4's error payload
  (`setMRs_syscall_error`): `x1`'s length is the payload's word count as
  seL4's `setMR` chain returns it, `x2`-`x5` the payload's first four words
  (MR0-MR3), and a guard mismatch's fifth word goes to the caller's IPC buffer
  `msg[4]` (`recordErrorOverflow`).  A v4 decoder reads a payload-carrying
  error's length as `0`, so this is a version bump.

Mirrored as `SYSCALL_ABI_VERSION` in `rust/sele4n-types` at each flip, with
each side's conformance suite pinning its own constant to the same literal —
so a half-bumped tree fails its own suite rather than mis-decoding at
runtime (plan §3.6). -/
def syscallAbiVersion : Nat := 5

/-- The Lean half of the version pin (RA.A.7).  The Rust conformance test
asserts the identical literal; a bump that forgets one side fails there. -/
theorem syscallAbiVersion_pinned : syscallAbiVersion = 5 := rfl

end SeLe4n.Kernel.Architecture
