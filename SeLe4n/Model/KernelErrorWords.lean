-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Model.KernelError

/-!
# A kernel error as words

Each `KernelError`'s canonical discriminant (the label the syscall return
convention carries, `Kernel/Architecture/SyscallReturn.lean`) and its payload
words (seL4's `setMRs_syscall_error` and `setMRs_lookup_failure`), and the
error rebuilt from them.  Below the system state, so the declassification
refusal ledger (`InformationFlow/RefusalRecord.lean`) can hold a refusal's
error as these words and build no error on the entry path.
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
  -- 35: retired (`retiredDiscriminants`).
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
  -- 35: retired (`retiredDiscriminants`), decodes to `none`.
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

/-- **Retired discriminants**, reserved and never reassigned: `35`, the
`invalidCapPtr` a capability-pointer register past `2^64` was refused with
before a register became a 64-bit word (WS-SX SX1.3), and `37`, the
`allocationMisaligned` the carve returned before it rounded the free index up
to the object's boundary (WS-ZA ZA5.4 part 14).  No variant has one, and
`ofDiscriminant?` decodes one to `none`. -/
def retiredDiscriminants : List Nat := [35, 37]

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

/-- The retired `invalidCapPtr` discriminant names no error. -/
theorem ofDiscriminant?_retired_capPtr : ofDiscriminant? 35 = none := rfl

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
