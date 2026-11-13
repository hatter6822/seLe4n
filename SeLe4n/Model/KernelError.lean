-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

/-!
# WS-SM SM9.B.1: `KernelError`, extracted below `Model/State`

`KernelError` lived in `Model/State.lean`, immediately above `SystemState`.
SM9.B mounts the **refusal ledger** as a `SystemState` field whose records name
the error that refused the syscall, and the plan's §6 mount checklist requires
the payload of a mounted field to sit in a **leaf** module — otherwise
`Model/State.lean` would have to import the module that names the error, which
is `Model/State.lean` itself.

This is the same extraction SM7.A performed for `Architecture.TlbInvalidation`,
SM7.D for `Architecture.CacheInvalidation` and SM8.C.8 for
`InformationFlow.AuditRecord`: the *operand* type moves to a pure module below
the state, and the state re-exports nothing because the namespace and every
name are unchanged (`SeLe4n.Model.KernelError`).  `Model/State.lean` imports
this module, so every existing reference resolves exactly as before.

The alternative — storing the refusal's reason as a bare discriminant `Nat` —
was rejected for the reason the plan gives for the ledger's counters: a `Nat`
constrained only by its producer leaves every other way of building the
structure unconstrained, so an arbitrary ledger literal could carry a "reason"
that is no kernel error at all.  Typing the field is the structural
enforcement.

Deliberately **import-free**: nothing here depends on any other module, which
is what makes it placeable below every consumer.
-/

namespace SeLe4n.Model

/-- **seL4's `lookup_fault`** (`include/object/structures_64.bf`): why a
capability-address resolution stopped.  A `seL4_FailedLookup` error and (from
WS-SX SX2) a capability fault carry one, and `setMRs_lookup_failure`
(`src/api/faults.c`) writes it as its type plus one, then its fields in this
order.

- `invalidRoot`: the root capability is not a CNode capability.
- `missingCapability bitsLeft`: the slot the address names holds no capability
  of the kind the operation needs, with `bitsLeft` bits of the address
  unresolved.
- `depthMismatch bitsLeft bitsFound`: the walk stopped with `bitsLeft` bits
  left, at a level that resolves `bitsFound` (`0` where it stopped at a slot
  that names no CNode).
- `guardMismatch bitsLeft guardFound bitsFound`: the address's guard bits do
  not match the CNode capability's guard `guardFound`, `bitsFound` bits wide,
  with `bitsLeft` bits left. -/
inductive LookupFault where
  | invalidRoot
  | missingCapability (bitsLeft : UInt64)
  | depthMismatch (bitsLeft bitsFound : UInt64)
  | guardMismatch (bitsLeft guardFound bitsFound : UInt64)
  deriving Repr, DecidableEq

namespace LookupFault

/-- seL4's lookup-failure type word, `lufType + 1`: `seL4_InvalidRoot` (1),
`seL4_MissingCapability` (2), `seL4_DepthMismatch` (3), `seL4_GuardMismatch` (4). -/
@[inline] def typeWord : LookupFault → UInt64
  | .invalidRoot => 1
  | .missingCapability _ => 2
  | .depthMismatch _ _ => 3
  | .guardMismatch _ _ _ => 4

/-- The words `setMRs_lookup_failure` writes: the type word and the fields. -/
@[inline] def wordCount : LookupFault → Nat
  | .invalidRoot => 1
  | .missingCapability _ => 2
  | .depthMismatch _ _ => 3
  | .guardMismatch _ _ _ => 4

/-- Word `i` of the fault, in `setMRs_lookup_failure`'s order: the type word,
then `bitsLeft`, then `bitsFound` (a depth mismatch) or `guardFound` and
`bitsFound` (a guard mismatch); `0` past the last. -/
@[inline] def word (f : LookupFault) (i : Nat) : UInt64 :=
  match f, i with
  | f, 0 => f.typeWord
  | .missingCapability l, 1 => l
  | .depthMismatch l _, 1 => l
  | .depthMismatch _ b, 2 => b
  | .guardMismatch l _ _, 1 => l
  | .guardMismatch _ g _, 2 => g
  | .guardMismatch _ _ b, 3 => b
  | _, _ => 0

/-- **The fault its words name** (WS-SX SX2): the type word picks the
constructor and the next words its fields, as `word` lays them out; a type word
seL4 does not define reads as `invalidRoot`.  A resolver in continuation form
hands its fault on as words, constant type words at each refusal, so the
constructor is fixed where the words are made (`ofWords_word`). -/
@[inline] def ofWords (t w1 w2 w3 : UInt64) : LookupFault :=
  if t = 2 then .missingCapability w1
  else if t = 3 then .depthMismatch w1 w2
  else if t = 4 then .guardMismatch w1 w2 w3
  else .invalidRoot

@[simp] theorem ofWords_word (f : LookupFault) :
    ofWords (f.word 0) (f.word 1) (f.word 2) (f.word 3) = f := by
  cases f <;> rfl

end LookupFault

/-- F-04: Kernel error codes. This inductive has 60 variants.
Five carry seL4's error payload (`setMRs_syscall_error`, `src/object/tcb.c`):
`invalidCapability`, `invalidArgument`, `rangeError`, `failedLookup` and
`untypedRegionExhausted`.  The payload rides in the message registers of the
error frame, never in its label (`Architecture.errorFrame`).  Each payload
field is a machine word (`UInt64`), as seL4's `current_syscall_error` fields
are `word_t`: a payload is exactly the words the caller reads back.
**Coding convention**: Prefer explicit match arms over `| _ =>` catch-all
patterns when matching on `KernelError`. Lean's exhaustiveness checker will
flag missing arms at compile time, but catch-all patterns silently swallow
new variants added in future workstreams, masking potential error-handling
bugs. Use `| _ =>` only for genuinely uniform error handling (e.g., converting
any error to a user-facing string) where variant-specific behavior is not needed.

**AC5-D audit result**: Codebase-wide audit of `| _ =>` patterns confirmed zero
catch-alls on `KernelError` in production code. All `.error _` catch-alls found
are in: (a) test harness code (MainTraceHarness.lean), (b) intentional uniform
error handling in donation/lifecycle wrappers (documented by AC3-A/I-02 atomicity
contract), or (c) seL4-compatible `resolveExtraCaps` silent-drop (documented by
AC3-D/API-01). -/
inductive KernelError where
  /-- seL4's `seL4_InvalidCapability`: `capNumber` names the capability, `0` for
  the invoked one and `i + 1` for argument capability `i`. -/
  | invalidCapability (capNumber : UInt64)
  | objectNotFound
  | illegalState
  | illegalAuthority
  | policyDenied
  | dependencyViolation
  | schedulerInvariantViolation
  | endpointStateMismatch
  | endpointQueueEmpty
  | asidNotBound
  | vspaceRootInvalid
  | mappingConflict
  | translationFault
  | flowDenied
  | declassificationDenied  -- WS-I3/R-08: declassification policy denied downgrade
  | alreadyWaiting
  | cyclicDependency
  | notImplemented
  | targetSlotOccupied   -- WS-E4/H-02: insert into occupied slot
  | replyCapInvalid      -- WS-E4/M-12: reply target not in blockedOnReply state, or replier not authorized (WS-H1/M-02)
  /-- WS-F2: not enough space in the untyped region — seL4's
  `seL4_NotEnoughMemory`, carrying the bytes the untyped has left. -/
  | untypedRegionExhausted (memoryLeft : UInt64)
  | untypedTypeMismatch      -- WS-F2: source object is not an UntypedObject
  | untypedDeviceRestriction -- WS-F2: device untyped cannot back kernel objects
  | untypedAllocSizeTooSmall -- WS-F2: allocSize smaller than minimum for object type
  | childIdSelfOverwrite    -- WS-H2/H-06: childId = untypedId in retypeFromUntyped
  | childIdCollision        -- WS-H2/A-26: childId collides with existing object or untyped child
  | addressOutOfBounds      -- WS-H11/A-05: physical address exceeds machine address width
  | ipcMessageTooLarge      -- WS-H12d/A-09: IPC message registers exceed maxMessageRegisters (120)
  | ipcMessageTooManyCaps   -- WS-H12d/A-09: reserved syscall-ABI code.  Raised
                           -- by no path: a message holds no capabilities, and
                           -- the 2-bit `extraCaps` field cannot exceed
                           -- maxExtraCaps (3)
  | backingObjectMissing    -- WS-H13/A-29: service backing object not in object store
  | invalidRegister         -- WS-J1-B: register index out of architectural bounds
  | invalidSyscallNumber    -- WS-J1-B: syscall number register value not in modeled set
  | invalidMessageInfo      -- WS-J1-B: malformed message-info word (length/caps out of bounds)
  | invalidTypeTag          -- WS-K-D: retype type tag not in modeled object set (0–5)
  | resourceExhausted       -- WS-R2/M-05: fuel exhaustion in streaming BFS revocation
  | invalidCapPtr           -- S4-K: capability pointer exceeds word64 bounds
  | objectStoreCapacityExceeded  -- S4-B: object count exceeds maxObjects capacity
  -- Discriminant 37 is retired (WS-ZA ZA5.4 part 14): it was
  -- `allocationMisaligned`, returned by no carve once the free index is rounded
  -- up to the object's boundary.  It is reserved and never reassigned
  -- (`KernelError.retiredDiscriminants`).
  | revocationRequired    -- U-H03: destroying an object or mapping still in use (unmap, cancel or revoke first)
  /-- U5-E/U-M07: a syscall argument the operation refuses — seL4's
  `seL4_InvalidArgument`, carrying the argument's number (its message word). -/
  | invalidArgument (argNumber : UInt64)
  | mmioUnaligned        -- V4-B/M-HW-1: MMIO access at unaligned address (4-byte for 32-bit, 8-byte for 64-bit)
  | invalidSyscallArgument  -- X5-E/M-11: syscall-specific argument decode failure (distinct from generic invalidArgument)
  | ipcTimeout             -- WS-Z Z6: IPC blocked thread timed out due to SchedContext budget expiry
  | alignmentError         -- D3-B: IPC buffer address not aligned to ipcBufferAlignment (1024 bytes)
  | vmFault                -- AG3-C: virtual memory fault (data abort or instruction abort)
  | userException          -- AG3-C: unclassified synchronous exception from user mode
  | hardwareFault          -- AG3-C: SError (asynchronous external abort / hardware error)
  | notSupported           -- AG3-C: unsupported exception type (e.g., FIQ)
  | invalidIrq             -- AG3-D: interrupt ID not mapped in IRQ handler table
  | invalidObjectType      -- WS-AL AL6 (cascades AK7-F): storeObjectKindChecked
                           -- rejects cross-variant overwrite (e.g., storing a
                           -- SchedContext at an ObjId that already holds a TCB).
  | nullCapability         -- WS-AL AL1b (cascades AK7-I): capability operation
                           -- rejected the `Capability.null` sentinel. Distinct
                           -- from `invalidCapability` (which can mean "slot
                           -- empty" or "cap target is not .object"); this
                           -- specifically signals the seL4_CapNull convention
                           -- (`.object` target with reserved ObjId AND empty
                           -- rights). Produced by the `NonNullCap.ofCap?`
                           -- type-level promotion failure path; the type
                           -- system enforces the discipline at call sites
                           -- that demand `NonNullCap` arguments.
  | partialResolution      -- AN7-E (API-M01): an unresolvable extra-capability
                           -- address, for a deployment that refuses a
                           -- *partial* resolution rather than silently
                           -- dropping the entry as seL4 does.  Every dispatch
                           -- arm drops (`resolveExtraCaps`), so nothing raises
                           -- it; the code stays allocated in the syscall ABI.
                           -- The selection policy is registered debt
                           -- (REGISTERED_DEBT.md table C).
  | missingSchedContext    -- R5.E (DEEP-SCH-04): a bound-budget scheduler
                           -- path lost track of its bound `SchedContext`
                           -- (object not found in `objects` table).  Pre-R5,
                           -- the timer-tick budget branch silently fell back
                           -- to a no-preempt path on this case; under the
                           -- runtime-checked `crossSubsystemInvariant`
                           -- (specifically `schedContextStoreConsistent`) the
                           -- branch is unreachable, but exposing it as a
                           -- distinct discriminant lets observability layers
                           -- surface the invariant violation instead of
                           -- absorbing it.
  | threadOnDifferentCore  -- WS-SM SM5.B.4 (plan §3.2, Theorem 3.2.3): a
                           -- per-core context switch (`switchToThreadOnCore`)
                           -- was asked to dispatch a thread on a core other
                           -- than the core its `cpuAffinity` binds it to.
                           -- Migration of a thread between cores is a
                           -- separate, explicit operation; a context switch
                           -- never implicitly migrates.  Surfacing this as a
                           -- distinct discriminant lets the per-core
                           -- scheduler (SM5.C+) and userspace distinguish a
                           -- genuine wrong-core dispatch from an unrelated
                           -- scheduler fault (`schedulerInvariantViolation`).
  | auditLogCapacityExceeded -- WS-SM SM8.C.8: the declassification audit trail
                           -- is at `maxDeclassificationAuditEntries`, so the
                           -- downgrade was refused rather than performed
                           -- unrecorded.  A distinct discriminant, not
                           -- `resourceExhausted` or `declassificationDenied`,
                           -- because the three mean different things to an
                           -- operator: policy refused the downgrade / the
                           -- kernel ran out of an unrelated resource / the
                           -- kernel could not *audit* the downgrade.  Only the
                           -- last one says "drain the trail"; collapsing it
                           -- into either sibling would hide a system that has
                           -- stopped being able to declassify at all.
  | auditFieldTooLarge     -- WS-SM SM9.A.2: an audit-trail field the reader was
                           -- asked to export needs more than
                           -- `maxAuditFieldChunks` chunks, so the kernel
                           -- **refuses the read** rather than returning a
                           -- truncated value.  The chunk *coordinates* are
                           -- themselves single words, so "any `Nat` can be
                           -- exported" was never true; the honest shape is a
                           -- bounded domain the reconstruction theorem holds
                           -- unconditionally on, plus a fail-closed refusal
                           -- above it.  A distinct discriminant, not
                           -- `invalidArgument`, because the caller's argument
                           -- was well-formed — it is the *value* that does not
                           -- fit, which is a statement about the kernel's
                           -- export width and not about the request.
  | declassificationDeniedAtReceiver
                           -- WS-SM SM9.C.1: a data-carrying declassification
                           -- gates **two** hops — the caller into the
                           -- notification, and the notification onward into the
                           -- resolved receiver — and this is the second one
                           -- refusing.  A distinct discriminant, not
                           -- `declassificationDenied`, because the refusal
                           -- ledger stores exactly this field and a monitor
                           -- reading "denied" with no idea *which*
                           -- authorization failed cannot tell an unauthorized
                           -- caller from an authorized caller aimed at an
                           -- unauthorized sink — the two call for opposite
                           -- responses.  It discloses nothing the caller could
                           -- not already learn: the ordinary checked
                           -- `.notificationSignal` on the same capability
                           -- already answers `.flowDenied` exactly when a bound
                           -- receiver is present and the flow to it is refused.
  | ipcCancelled          -- WS-RR RR7.14: a thread's blocking IPC was forcibly
                           -- cancelled — by `.tcbSuspend` on a blocked victim, by
                           -- lifecycle cleanup, or by a retype of an object it was
                           -- blocked on — so its syscall never completed and never
                           -- will.  Distinct from `.ipcTimeout`, which is the
                           -- SchedContext budget expiring under a *live* operation:
                           -- a timed-out caller may retry the same call, a cancelled
                           -- one has had its endpoint queue entry destroyed.  seL4
                           -- restarts the thread instead; this kernel has no restart
                           -- state, so the boundary crossing has to end in an error
                           -- the caller can distinguish (WS-RA plan §3.5).
  | truncatedMessage      -- seL4's `seL4_TruncatedMessage`: an invocation's
                           -- message holds fewer argument words than its decode
                           -- reads (`truncationMinimum`).  Answered once the
                           -- capability is found and its kind accepted, before
                           -- any argument is read, as seL4's `decode*Invocation`
                           -- answers `length < n`.  The model's own discriminant
                           -- (58), not seL4's numeric code.
  | rangeError (rangeMin rangeMax : UInt64)
                           -- seL4's `seL4_RangeError`: an invocation argument
                           -- outside the range `rangeMin .. rangeMax` its
                           -- operation admits — a CNode operation's depth
                           -- outside `1 .. 64` (seL4's `rangeCheck` in
                           -- `lookupSlotForCNodeOp`), refused before the lookup
                           -- it would bound.  The model's own discriminant (59);
                           -- the bounds are the error's payload.
  | failedLookup (wasSource : Bool) (lookupFault : LookupFault)
                           -- seL4's `seL4_FailedLookup`: a CNode operation's
                           -- address that does not resolve (`lookupSlotForCNodeOp`)
                           -- or names an empty source slot, with whether it was
                           -- the source's and seL4's lookup fault.  The model's
                           -- own discriminant (60).
  deriving Repr

/-- The error's code with its payload cleared: every field `0`, `false` or
`invalidRoot`.  Two errors share a code exactly when their payload-cleared
forms are equal; the error label carries the code alone
(`KernelError.ofDiscriminant?_toDiscriminant`). -/
def KernelError.erasePayload : KernelError → KernelError
  | .invalidCapability _ => .invalidCapability 0
  | .invalidArgument _ => .invalidArgument 0
  | .rangeError _ _ => .rangeError 0 0
  | .failedLookup _ _ => .failedLookup false .invalidRoot
  | .untypedRegionExhausted _ => .untypedRegionExhausted 0
  | e => e

/-- **Equality of errors, decided field by field**: a payload constructor
compares its fields, any other pair its constructor index.  The derived
`DecidableEq` compared two errors of one constructor through a generated
same-constructor matcher whose alternatives are a closure, built on every
such comparison, so a refusal compared against a constant (the refusal
ledger's `declassificationDeniedAtReceiver`) built a cell; this compares
scalars (`eqWords_iff`), and is the instance. -/
@[inline] def KernelError.eqWords : KernelError → KernelError → Bool
  | .invalidCapability n, .invalidCapability m => n == m
  | .invalidArgument n, .invalidArgument m => n == m
  | .rangeError a b, .rangeError c d => a == c && b == d
  | .untypedRegionExhausted n, .untypedRegionExhausted m => n == m
  | .failedLookup w f, .failedLookup v g => w == v && f == g
  | a, b => a.ctorIdx == b.ctorIdx

theorem KernelError.eqWords_iff (a b : KernelError) : a.eqWords b = true ↔ a = b := by
  cases a <;> cases b <;> simp [KernelError.eqWords, KernelError.ctorIdx]

/-- **`DecidableEq KernelError` is `eqWords`**, not derived: the derived
instance compares through a closure it builds on every comparison of two errors
of one constructor. -/
instance : DecidableEq KernelError := fun a b =>
  decidable_of_iff _ (KernelError.eqWords_iff a b)

end SeLe4n.Model
