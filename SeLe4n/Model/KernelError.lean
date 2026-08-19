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

/-- F-04: Kernel error codes. This inductive has 49 variants.
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
  | invalidCapability
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
  | untypedRegionExhausted   -- WS-F2: not enough space in untyped region
  | untypedTypeMismatch      -- WS-F2: source object is not an UntypedObject
  | untypedDeviceRestriction -- WS-F2: device untyped cannot back kernel objects
  | untypedAllocSizeTooSmall -- WS-F2: allocSize smaller than minimum for object type
  | childIdSelfOverwrite    -- WS-H2/H-06: childId = untypedId in retypeFromUntyped
  | childIdCollision        -- WS-H2/A-26: childId collides with existing object or untyped child
  | addressOutOfBounds      -- WS-H11/A-05: physical address exceeds machine address width
  | ipcMessageTooLarge      -- WS-H12d/A-09: IPC message registers exceed maxMessageRegisters (120)
  | ipcMessageTooManyCaps   -- WS-H12d/A-09: IPC message caps exceed maxExtraCaps (3)
  | backingObjectMissing    -- WS-H13/A-29: service backing object not in object store
  | invalidRegister         -- WS-J1-B: register index out of architectural bounds
  | invalidSyscallNumber    -- WS-J1-B: syscall number register value not in modeled set
  | invalidMessageInfo      -- WS-J1-B: malformed message-info word (length/caps out of bounds)
  | invalidTypeTag          -- WS-K-D: retype type tag not in modeled object set (0–5)
  | resourceExhausted       -- WS-R2/M-05: fuel exhaustion in streaming BFS revocation
  | invalidCapPtr           -- S4-K: capability pointer exceeds word64 bounds
  | objectStoreCapacityExceeded  -- S4-B: object count exceeds maxObjects capacity
  | allocationMisaligned  -- S5-G: allocation base not page-aligned for VSpace-bound objects
  | revocationRequired    -- U-H03: delete attempted on slot with CDT children (must revoke first)
  | invalidArgument      -- U5-E/U-M07: syscall argument decode failed (e.g., invalid permission bits)
  | mmioUnaligned        -- V4-B/M-HW-1: MMIO access at unaligned address (4-byte for 32-bit, 8-byte for 64-bit)
  | invalidSyscallArgument  -- X5-E/M-11: syscall-specific argument decode failure (distinct from generic invalidArgument)
  | ipcTimeout             -- WS-Z/Z6: IPC blocked thread timed out due to SchedContext budget expiry
  | alignmentError         -- D3-B: IPC buffer address not aligned to ipcBufferAlignment (512 bytes)
  | vmFault                -- AG3-C: virtual memory fault (data abort or instruction abort)
  | userException          -- AG3-C: unclassified synchronous exception from user mode
  | hardwareFault          -- AG3-C: SError (asynchronous external abort / hardware error)
  | notSupported           -- AG3-C: unsupported exception type (e.g., FIQ)
  | invalidIrq             -- AG3-D: interrupt ID not mapped in IRQ handler table
  | invalidObjectType      -- AL6 (WS-AL / AK7-F.cascade): storeObjectKindChecked
                           -- rejects cross-variant overwrite (e.g., storing a
                           -- SchedContext at an ObjId that already holds a TCB).
  | nullCapability         -- AL1b (WS-AL / AK7-I.cascade): capability operation
                           -- rejected the `Capability.null` sentinel. Distinct
                           -- from `invalidCapability` (which can mean "slot
                           -- empty" or "cap target is not .object"); this
                           -- specifically signals the seL4_CapNull convention
                           -- (`.object` target with reserved ObjId AND empty
                           -- rights). Produced by the `NonNullCap.ofCap?`
                           -- type-level promotion failure path; the type
                           -- system enforces the discipline at call sites
                           -- that demand `NonNullCap` arguments.
  | partialResolution      -- AN7-E (API-M01): `resolveExtraCaps` encountered
                           -- an unresolvable capability address in the extra-
                           -- cap list AND the `sele4n.debug.noisyResolution`
                           -- option was enabled.  By default seL4-compatible
                           -- semantics silently drop the unresolvable entries;
                           -- under the noisy option the kernel surfaces this
                           -- variant so callers can distinguish a *partial*
                           -- resolution from a *complete* success.
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
  deriving Repr, DecidableEq

end SeLe4n.Model
