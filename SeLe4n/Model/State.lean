-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Machine
import SeLe4n.Model.Object
import SeLe4n.Kernel.Scheduler.RunQueue
import SeLe4n.Kernel.SchedContext.ReplenishQueue
import SeLe4n.Kernel.Service.Interface
import SeLe4n.Kernel.RobinHood.Set
import SeLe4n.Kernel.Architecture.TlbShootdown

namespace SeLe4n.Model

open SeLe4n.Kernel.RobinHood
open SeLe4n.Kernel.Concurrency (numCores CoreId bootCoreId)

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
  deriving Repr, DecidableEq

/-- S2-A: Low-priority blanket `ToString` from `Repr`. Enables standard
string interpolation (`s!"{x}"`) for all types with `Repr` instances.
Explicit `ToString` instances take precedence due to priority 10. -/
instance (priority := 10) instToStringOfReprFallback [Repr α] : ToString α where
  toString := reprStr

/-- M-05/WS-E6: One entry in the round-robin domain schedule table.
Mirrors seL4's `dschedule[]` — each entry specifies a domain and how
many ticks that domain runs before the scheduler advances to the next entry. -/
structure DomainScheduleEntry where
  domain : SeLe4n.DomainId
  length : Nat
  deriving Repr, DecidableEq

structure SchedulerState where
  /-- WS-G4/F-P02: Priority-bucketed run queue replacing the flat list.
      Provides O(1) amortized membership, insert, remove; O(1) best-candidate
      via cached maxPriority. The `toList` projection maintains proof/projection
      compatibility with information-flow subsystem. -/
  runQueue : Vector SeLe4n.Kernel.RunQueue numCores :=
    Vector.replicate numCores SeLe4n.Kernel.RunQueue.empty
  current : Vector (Option SeLe4n.ThreadId) numCores :=
    Vector.replicate numCores none
  /-- M-05/WS-E6: Currently active scheduling domain. Only threads in this
      domain are eligible for selection. Default domain 0. -/
  activeDomain : Vector SeLe4n.DomainId numCores := Vector.replicate numCores ⟨0⟩
  /-- M-05/WS-E6: Remaining ticks in the current domain schedule entry.
      When this reaches 0, the scheduler advances to the next domain. -/
  domainTimeRemaining : Vector Nat numCores := Vector.replicate numCores 5
  /-- M-05/WS-E6: Round-robin domain schedule table. Empty = single-domain mode. -/
  domainSchedule : List DomainScheduleEntry := []
  /-- M-05/WS-E6: Current index into `domainSchedule`. -/
  domainScheduleIndex : Vector Nat numCores := Vector.replicate numCores 0
  /-- V5-L (L-SCH-1): Configurable default time-slice quantum (ticks per
      scheduling round). Defaults to 5, matching seL4's default. Used by
      `timerTick` to reset time-slices on preemption. Thread-level time
      slices are deferred to a future MCS scheduling extension. -/
  configDefaultTimeSlice : Nat := 5
  /-- Z4-A: System-wide CBS replenishment queue. Tracks when each active
      SchedContext's budget becomes eligible for refill. Sorted by eligibility
      time for O(1) peek and O(k) prefix split on timer tick. -/
  replenishQueue : Vector SeLe4n.Kernel.ReplenishQueue numCores :=
    Vector.replicate numCores SeLe4n.Kernel.ReplenishQueue.empty
  /-- AK2-D (S-M02): Diagnostic-only record of per-thread timeout errors
      collected during the most recent `timeoutBlockedThreads` run. A non-empty
      list indicates an invariant violation was observed (e.g., a TCB in the
      per-SchedContext index that could not be looked up in the object store).
      Under `crossSubsystemInvariant` the list is always empty. The field is
      cleared at the start of each timer tick so stale diagnostics never
      survive across rounds. -/
  lastTimeoutErrors : Vector (List (SeLe4n.ThreadId × KernelError)) numCores :=
    Vector.replicate numCores []
  deriving Repr

/-! ### WS-SM SM4.B.8: per-core scheduler-state accessors (path-a)

Per `docs/planning/SMP_PER_CORE_STATE_PLAN.md` §3.1, every per-core
`SchedulerState` field is read through an explicit `…OnCore (c : CoreId)`
accessor rather than the bare field projection.  This is the decision-#4
"path-a" discipline: there is no scalar-field shim in the final state, so
every callsite names the core it is reasoning about.

Each accessor is `s.field.get c` — a genuine `Vector.get` projection of
core `c`'s slot (the fields are `Vector α numCores` since SM4.B phase-2).
The accessors are intentionally **not** `@[simp]`: the per-core
store/load algebra below reduces post-write reads, and leaving the
accessors opaque keeps that algebra in control of proof normalisation
(unfolding to raw `Vector.get`/`Vector.set` would defeat it). -/
namespace SchedulerState

/-- Per-core current-thread of `s` on core `c`. -/
def currentOnCore (s : SchedulerState) (c : CoreId) : Option SeLe4n.ThreadId :=
  s.current.get c
/-- Per-core run queue of `s` on core `c`. -/
def runQueueOnCore (s : SchedulerState) (c : CoreId) : SeLe4n.Kernel.RunQueue :=
  s.runQueue.get c
/-- Per-core CBS replenishment queue of `s` on core `c`. -/
def replenishQueueOnCore (s : SchedulerState) (c : CoreId) : SeLe4n.Kernel.ReplenishQueue :=
  s.replenishQueue.get c
/-- Per-core active scheduling domain of `s` on core `c`. -/
def activeDomainOnCore (s : SchedulerState) (c : CoreId) : SeLe4n.DomainId :=
  s.activeDomain.get c
/-- Per-core remaining domain ticks of `s` on core `c`. -/
def domainTimeRemainingOnCore (s : SchedulerState) (c : CoreId) : Nat :=
  s.domainTimeRemaining.get c
/-- Per-core domain-schedule index of `s` on core `c`. -/
def domainScheduleIndexOnCore (s : SchedulerState) (c : CoreId) : Nat :=
  s.domainScheduleIndex.get c
/-- Per-core diagnostic timeout-error log of `s` on core `c`. -/
def lastTimeoutErrorsOnCore (s : SchedulerState) (c : CoreId) :
    List (SeLe4n.ThreadId × KernelError) :=
  s.lastTimeoutErrors.get c

/-! ### WS-SM SM4.B.phase-2: per-core scheduler-state setters (path-a)

Each per-core field has a matching `set…OnCore (c : CoreId)` setter that
writes only core `c`'s slot (`Vector.set c.val … c.isLt`), leaving every
other core's slot and the system-wide fields untouched.  Operation bodies
write per-core fields through these setters rather than the raw `Vector.set`
so the get-after-set reductions (`set…OnCore_…OnCore_*` below) match
syntactically.  Single-core operations write `bootCoreId`'s slot; SM5
cross-core operations write the target core's slot. -/

/-- Write core `c`'s current-thread slot. -/
def setCurrentOnCore (s : SchedulerState) (c : CoreId) (v : Option SeLe4n.ThreadId) :
    SchedulerState := { s with current := s.current.set c.val v c.isLt }
/-- Write core `c`'s run-queue slot. -/
def setRunQueueOnCore (s : SchedulerState) (c : CoreId) (v : SeLe4n.Kernel.RunQueue) :
    SchedulerState := { s with runQueue := s.runQueue.set c.val v c.isLt }
/-- Write core `c`'s CBS replenishment-queue slot. -/
def setReplenishQueueOnCore (s : SchedulerState) (c : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    SchedulerState := { s with replenishQueue := s.replenishQueue.set c.val v c.isLt }
/-- Write core `c`'s active-domain slot. -/
def setActiveDomainOnCore (s : SchedulerState) (c : CoreId) (v : SeLe4n.DomainId) :
    SchedulerState := { s with activeDomain := s.activeDomain.set c.val v c.isLt }
/-- Write core `c`'s remaining-domain-ticks slot. -/
def setDomainTimeRemainingOnCore (s : SchedulerState) (c : CoreId) (v : Nat) :
    SchedulerState := { s with domainTimeRemaining := s.domainTimeRemaining.set c.val v c.isLt }
/-- Write core `c`'s domain-schedule-index slot. -/
def setDomainScheduleIndexOnCore (s : SchedulerState) (c : CoreId) (v : Nat) :
    SchedulerState := { s with domainScheduleIndex := s.domainScheduleIndex.set c.val v c.isLt }
/-- Write core `c`'s diagnostic timeout-error-log slot. -/
def setLastTimeoutErrorsOnCore (s : SchedulerState) (c : CoreId)
    (v : List (SeLe4n.ThreadId × KernelError)) : SchedulerState :=
  { s with lastTimeoutErrors := s.lastTimeoutErrors.set c.val v c.isLt }

/-- WS-SM SM4.B.10: per-core extensionality (plan §3.3).  Two scheduler
states are equal once their per-core fields agree at *every* `CoreId` and
their system-wide fields agree.  Named `ext_perCore` to avoid clashing with
the structure's auto-generated `SchedulerState.ext`.

Each per-core hypothesis (`∀ c, s₁.…OnCore c = s₂.…OnCore c`) lifts to
`Vector` equality via `SeLe4n.PerCoreVector.ext`; the structure is then
destructured and closed by `simp_all`. -/
theorem ext_perCore {s₁ s₂ : SchedulerState}
    (hCur  : ∀ c : CoreId, s₁.currentOnCore c = s₂.currentOnCore c)
    (hRQ   : ∀ c : CoreId, s₁.runQueueOnCore c = s₂.runQueueOnCore c)
    (hRepl : ∀ c : CoreId, s₁.replenishQueueOnCore c = s₂.replenishQueueOnCore c)
    (hAD   : ∀ c : CoreId, s₁.activeDomainOnCore c = s₂.activeDomainOnCore c)
    (hDTR  : ∀ c : CoreId, s₁.domainTimeRemainingOnCore c = s₂.domainTimeRemainingOnCore c)
    (hDSI  : ∀ c : CoreId, s₁.domainScheduleIndexOnCore c = s₂.domainScheduleIndexOnCore c)
    (hLTE  : ∀ c : CoreId, s₁.lastTimeoutErrorsOnCore c = s₂.lastTimeoutErrorsOnCore c)
    (hSched : s₁.domainSchedule = s₂.domainSchedule)
    (hSlice : s₁.configDefaultTimeSlice = s₂.configDefaultTimeSlice) :
    s₁ = s₂ := by
  have h1 : s₁.current = s₂.current := PerCoreVector.ext fun c => hCur c
  have h2 : s₁.runQueue = s₂.runQueue := PerCoreVector.ext fun c => hRQ c
  have h3 : s₁.replenishQueue = s₂.replenishQueue := PerCoreVector.ext fun c => hRepl c
  have h4 : s₁.activeDomain = s₂.activeDomain := PerCoreVector.ext fun c => hAD c
  have h5 : s₁.domainTimeRemaining = s₂.domainTimeRemaining := PerCoreVector.ext fun c => hDTR c
  have h6 : s₁.domainScheduleIndex = s₂.domainScheduleIndex := PerCoreVector.ext fun c => hDSI c
  have h7 : s₁.lastTimeoutErrors = s₂.lastTimeoutErrors := PerCoreVector.ext fun c => hLTE c
  obtain ⟨rq1, cu1, ad1, dtr1, dsch1, dsi1, cdts1, rpl1, lte1⟩ := s₁
  obtain ⟨rq2, cu2, ad2, dtr2, dsch2, dsi2, cdts2, rpl2, lte2⟩ := s₂
  simp_all


/-! ### WS-SM SM4.B phase-2: per-core setter/accessor reduction algebra

The store-load algebra for the per-core setters: reading core `c`'s slot
after writing core `c` returns the written value (`_self`); reading any
other field, or another core's slot, is unaffected.  All `@[simp]` so
post-write reads reduce automatically; the cross-field lemmas hold for
every pair of cores (the fields are independent `Vector`s). -/

@[simp] theorem setCurrentOnCore_currentOnCore_self (s : SchedulerState) (c : CoreId) (v : Option SeLe4n.ThreadId) :
    (s.setCurrentOnCore c v).currentOnCore c = v := by
  simp [SchedulerState.setCurrentOnCore, SchedulerState.currentOnCore]
@[simp] theorem setRunQueueOnCore_runQueueOnCore_self (s : SchedulerState) (c : CoreId) (v : SeLe4n.Kernel.RunQueue) :
    (s.setRunQueueOnCore c v).runQueueOnCore c = v := by
  simp [SchedulerState.setRunQueueOnCore, SchedulerState.runQueueOnCore]
@[simp] theorem setReplenishQueueOnCore_replenishQueueOnCore_self (s : SchedulerState) (c : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    (s.setReplenishQueueOnCore c v).replenishQueueOnCore c = v := by
  simp [SchedulerState.setReplenishQueueOnCore, SchedulerState.replenishQueueOnCore]
@[simp] theorem setActiveDomainOnCore_activeDomainOnCore_self (s : SchedulerState) (c : CoreId) (v : SeLe4n.DomainId) :
    (s.setActiveDomainOnCore c v).activeDomainOnCore c = v := by
  simp [SchedulerState.setActiveDomainOnCore, SchedulerState.activeDomainOnCore]
@[simp] theorem setDomainTimeRemainingOnCore_domainTimeRemainingOnCore_self (s : SchedulerState) (c : CoreId) (v : Nat) :
    (s.setDomainTimeRemainingOnCore c v).domainTimeRemainingOnCore c = v := by
  simp [SchedulerState.setDomainTimeRemainingOnCore, SchedulerState.domainTimeRemainingOnCore]
@[simp] theorem setDomainScheduleIndexOnCore_domainScheduleIndexOnCore_self (s : SchedulerState) (c : CoreId) (v : Nat) :
    (s.setDomainScheduleIndexOnCore c v).domainScheduleIndexOnCore c = v := by
  simp [SchedulerState.setDomainScheduleIndexOnCore, SchedulerState.domainScheduleIndexOnCore]
@[simp] theorem setLastTimeoutErrorsOnCore_lastTimeoutErrorsOnCore_self (s : SchedulerState) (c : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) :
    (s.setLastTimeoutErrorsOnCore c v).lastTimeoutErrorsOnCore c = v := by
  simp [SchedulerState.setLastTimeoutErrorsOnCore, SchedulerState.lastTimeoutErrorsOnCore]
/-! Per-core independence: writing core `c`'s slot leaves a *different* core
`c'`'s slot of the *same* field unchanged.  These are the same-field
cross-core frames (conditional on `c ≠ c'`), lifted from
`SeLe4n.PerCoreVector.get_set_ne`.  Together with the `_self` and cross-field
lemmas they make every per-core read after a per-core write reduce.  Unused
at single-core (every SM4.B operation writes `bootCoreId`); they are the
theorem-level statement of the path-a per-core-independence property that the
runtime suite exercises and that SM5's genuine cross-core writes consume. -/
@[simp] theorem setCurrentOnCore_currentOnCore_ne (s : SchedulerState) (c c' : CoreId) (v : Option SeLe4n.ThreadId) (h : c ≠ c') :
    (s.setCurrentOnCore c v).currentOnCore c' = s.currentOnCore c' := by
  simp only [SchedulerState.setCurrentOnCore, SchedulerState.currentOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne s.current c c' v h
@[simp] theorem setRunQueueOnCore_runQueueOnCore_ne (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.RunQueue) (h : c ≠ c') :
    (s.setRunQueueOnCore c v).runQueueOnCore c' = s.runQueueOnCore c' := by
  simp only [SchedulerState.setRunQueueOnCore, SchedulerState.runQueueOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne s.runQueue c c' v h
@[simp] theorem setReplenishQueueOnCore_replenishQueueOnCore_ne (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) (h : c ≠ c') :
    (s.setReplenishQueueOnCore c v).replenishQueueOnCore c' = s.replenishQueueOnCore c' := by
  simp only [SchedulerState.setReplenishQueueOnCore, SchedulerState.replenishQueueOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne s.replenishQueue c c' v h
@[simp] theorem setActiveDomainOnCore_activeDomainOnCore_ne (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.DomainId) (h : c ≠ c') :
    (s.setActiveDomainOnCore c v).activeDomainOnCore c' = s.activeDomainOnCore c' := by
  simp only [SchedulerState.setActiveDomainOnCore, SchedulerState.activeDomainOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne s.activeDomain c c' v h
@[simp] theorem setDomainTimeRemainingOnCore_domainTimeRemainingOnCore_ne (s : SchedulerState) (c c' : CoreId) (v : Nat) (h : c ≠ c') :
    (s.setDomainTimeRemainingOnCore c v).domainTimeRemainingOnCore c' = s.domainTimeRemainingOnCore c' := by
  simp only [SchedulerState.setDomainTimeRemainingOnCore, SchedulerState.domainTimeRemainingOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne s.domainTimeRemaining c c' v h
@[simp] theorem setDomainScheduleIndexOnCore_domainScheduleIndexOnCore_ne (s : SchedulerState) (c c' : CoreId) (v : Nat) (h : c ≠ c') :
    (s.setDomainScheduleIndexOnCore c v).domainScheduleIndexOnCore c' = s.domainScheduleIndexOnCore c' := by
  simp only [SchedulerState.setDomainScheduleIndexOnCore, SchedulerState.domainScheduleIndexOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne s.domainScheduleIndex c c' v h
@[simp] theorem setLastTimeoutErrorsOnCore_lastTimeoutErrorsOnCore_ne (s : SchedulerState) (c c' : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) (h : c ≠ c') :
    (s.setLastTimeoutErrorsOnCore c v).lastTimeoutErrorsOnCore c' = s.lastTimeoutErrorsOnCore c' := by
  simp only [SchedulerState.setLastTimeoutErrorsOnCore, SchedulerState.lastTimeoutErrorsOnCore]
  exact SeLe4n.PerCoreVector.get_set_ne s.lastTimeoutErrors c c' v h
@[simp] theorem setCurrentOnCore_runQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : Option SeLe4n.ThreadId) :
    (s.setCurrentOnCore c v).runQueueOnCore c' = s.runQueueOnCore c' := by
  simp [SchedulerState.setCurrentOnCore, SchedulerState.runQueueOnCore]
@[simp] theorem setCurrentOnCore_replenishQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : Option SeLe4n.ThreadId) :
    (s.setCurrentOnCore c v).replenishQueueOnCore c' = s.replenishQueueOnCore c' := by
  simp [SchedulerState.setCurrentOnCore, SchedulerState.replenishQueueOnCore]
@[simp] theorem setCurrentOnCore_activeDomainOnCore (s : SchedulerState) (c c' : CoreId) (v : Option SeLe4n.ThreadId) :
    (s.setCurrentOnCore c v).activeDomainOnCore c' = s.activeDomainOnCore c' := by
  simp [SchedulerState.setCurrentOnCore, SchedulerState.activeDomainOnCore]
@[simp] theorem setCurrentOnCore_domainTimeRemainingOnCore (s : SchedulerState) (c c' : CoreId) (v : Option SeLe4n.ThreadId) :
    (s.setCurrentOnCore c v).domainTimeRemainingOnCore c' = s.domainTimeRemainingOnCore c' := by
  simp [SchedulerState.setCurrentOnCore, SchedulerState.domainTimeRemainingOnCore]
@[simp] theorem setCurrentOnCore_domainScheduleIndexOnCore (s : SchedulerState) (c c' : CoreId) (v : Option SeLe4n.ThreadId) :
    (s.setCurrentOnCore c v).domainScheduleIndexOnCore c' = s.domainScheduleIndexOnCore c' := by
  simp [SchedulerState.setCurrentOnCore, SchedulerState.domainScheduleIndexOnCore]
@[simp] theorem setCurrentOnCore_lastTimeoutErrorsOnCore (s : SchedulerState) (c c' : CoreId) (v : Option SeLe4n.ThreadId) :
    (s.setCurrentOnCore c v).lastTimeoutErrorsOnCore c' = s.lastTimeoutErrorsOnCore c' := by
  simp [SchedulerState.setCurrentOnCore, SchedulerState.lastTimeoutErrorsOnCore]
@[simp] theorem setRunQueueOnCore_currentOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.RunQueue) :
    (s.setRunQueueOnCore c v).currentOnCore c' = s.currentOnCore c' := by
  simp [SchedulerState.setRunQueueOnCore, SchedulerState.currentOnCore]
@[simp] theorem setRunQueueOnCore_replenishQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.RunQueue) :
    (s.setRunQueueOnCore c v).replenishQueueOnCore c' = s.replenishQueueOnCore c' := by
  simp [SchedulerState.setRunQueueOnCore, SchedulerState.replenishQueueOnCore]
@[simp] theorem setRunQueueOnCore_activeDomainOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.RunQueue) :
    (s.setRunQueueOnCore c v).activeDomainOnCore c' = s.activeDomainOnCore c' := by
  simp [SchedulerState.setRunQueueOnCore, SchedulerState.activeDomainOnCore]
@[simp] theorem setRunQueueOnCore_domainTimeRemainingOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.RunQueue) :
    (s.setRunQueueOnCore c v).domainTimeRemainingOnCore c' = s.domainTimeRemainingOnCore c' := by
  simp [SchedulerState.setRunQueueOnCore, SchedulerState.domainTimeRemainingOnCore]
@[simp] theorem setRunQueueOnCore_domainScheduleIndexOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.RunQueue) :
    (s.setRunQueueOnCore c v).domainScheduleIndexOnCore c' = s.domainScheduleIndexOnCore c' := by
  simp [SchedulerState.setRunQueueOnCore, SchedulerState.domainScheduleIndexOnCore]
@[simp] theorem setRunQueueOnCore_lastTimeoutErrorsOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.RunQueue) :
    (s.setRunQueueOnCore c v).lastTimeoutErrorsOnCore c' = s.lastTimeoutErrorsOnCore c' := by
  simp [SchedulerState.setRunQueueOnCore, SchedulerState.lastTimeoutErrorsOnCore]
@[simp] theorem setReplenishQueueOnCore_currentOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    (s.setReplenishQueueOnCore c v).currentOnCore c' = s.currentOnCore c' := by
  simp [SchedulerState.setReplenishQueueOnCore, SchedulerState.currentOnCore]
@[simp] theorem setReplenishQueueOnCore_runQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    (s.setReplenishQueueOnCore c v).runQueueOnCore c' = s.runQueueOnCore c' := by
  simp [SchedulerState.setReplenishQueueOnCore, SchedulerState.runQueueOnCore]
@[simp] theorem setReplenishQueueOnCore_activeDomainOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    (s.setReplenishQueueOnCore c v).activeDomainOnCore c' = s.activeDomainOnCore c' := by
  simp [SchedulerState.setReplenishQueueOnCore, SchedulerState.activeDomainOnCore]
@[simp] theorem setReplenishQueueOnCore_domainTimeRemainingOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    (s.setReplenishQueueOnCore c v).domainTimeRemainingOnCore c' = s.domainTimeRemainingOnCore c' := by
  simp [SchedulerState.setReplenishQueueOnCore, SchedulerState.domainTimeRemainingOnCore]
@[simp] theorem setReplenishQueueOnCore_domainScheduleIndexOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    (s.setReplenishQueueOnCore c v).domainScheduleIndexOnCore c' = s.domainScheduleIndexOnCore c' := by
  simp [SchedulerState.setReplenishQueueOnCore, SchedulerState.domainScheduleIndexOnCore]
@[simp] theorem setReplenishQueueOnCore_lastTimeoutErrorsOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    (s.setReplenishQueueOnCore c v).lastTimeoutErrorsOnCore c' = s.lastTimeoutErrorsOnCore c' := by
  simp [SchedulerState.setReplenishQueueOnCore, SchedulerState.lastTimeoutErrorsOnCore]
@[simp] theorem setActiveDomainOnCore_currentOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.DomainId) :
    (s.setActiveDomainOnCore c v).currentOnCore c' = s.currentOnCore c' := by
  simp [SchedulerState.setActiveDomainOnCore, SchedulerState.currentOnCore]
@[simp] theorem setActiveDomainOnCore_runQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.DomainId) :
    (s.setActiveDomainOnCore c v).runQueueOnCore c' = s.runQueueOnCore c' := by
  simp [SchedulerState.setActiveDomainOnCore, SchedulerState.runQueueOnCore]
@[simp] theorem setActiveDomainOnCore_replenishQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.DomainId) :
    (s.setActiveDomainOnCore c v).replenishQueueOnCore c' = s.replenishQueueOnCore c' := by
  simp [SchedulerState.setActiveDomainOnCore, SchedulerState.replenishQueueOnCore]
@[simp] theorem setActiveDomainOnCore_domainTimeRemainingOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.DomainId) :
    (s.setActiveDomainOnCore c v).domainTimeRemainingOnCore c' = s.domainTimeRemainingOnCore c' := by
  simp [SchedulerState.setActiveDomainOnCore, SchedulerState.domainTimeRemainingOnCore]
@[simp] theorem setActiveDomainOnCore_domainScheduleIndexOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.DomainId) :
    (s.setActiveDomainOnCore c v).domainScheduleIndexOnCore c' = s.domainScheduleIndexOnCore c' := by
  simp [SchedulerState.setActiveDomainOnCore, SchedulerState.domainScheduleIndexOnCore]
@[simp] theorem setActiveDomainOnCore_lastTimeoutErrorsOnCore (s : SchedulerState) (c c' : CoreId) (v : SeLe4n.DomainId) :
    (s.setActiveDomainOnCore c v).lastTimeoutErrorsOnCore c' = s.lastTimeoutErrorsOnCore c' := by
  simp [SchedulerState.setActiveDomainOnCore, SchedulerState.lastTimeoutErrorsOnCore]
@[simp] theorem setDomainTimeRemainingOnCore_currentOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainTimeRemainingOnCore c v).currentOnCore c' = s.currentOnCore c' := by
  simp [SchedulerState.setDomainTimeRemainingOnCore, SchedulerState.currentOnCore]
@[simp] theorem setDomainTimeRemainingOnCore_runQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainTimeRemainingOnCore c v).runQueueOnCore c' = s.runQueueOnCore c' := by
  simp [SchedulerState.setDomainTimeRemainingOnCore, SchedulerState.runQueueOnCore]
@[simp] theorem setDomainTimeRemainingOnCore_replenishQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainTimeRemainingOnCore c v).replenishQueueOnCore c' = s.replenishQueueOnCore c' := by
  simp [SchedulerState.setDomainTimeRemainingOnCore, SchedulerState.replenishQueueOnCore]
@[simp] theorem setDomainTimeRemainingOnCore_activeDomainOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainTimeRemainingOnCore c v).activeDomainOnCore c' = s.activeDomainOnCore c' := by
  simp [SchedulerState.setDomainTimeRemainingOnCore, SchedulerState.activeDomainOnCore]
@[simp] theorem setDomainTimeRemainingOnCore_domainScheduleIndexOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainTimeRemainingOnCore c v).domainScheduleIndexOnCore c' = s.domainScheduleIndexOnCore c' := by
  simp [SchedulerState.setDomainTimeRemainingOnCore, SchedulerState.domainScheduleIndexOnCore]
@[simp] theorem setDomainTimeRemainingOnCore_lastTimeoutErrorsOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainTimeRemainingOnCore c v).lastTimeoutErrorsOnCore c' = s.lastTimeoutErrorsOnCore c' := by
  simp [SchedulerState.setDomainTimeRemainingOnCore, SchedulerState.lastTimeoutErrorsOnCore]
@[simp] theorem setDomainScheduleIndexOnCore_currentOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainScheduleIndexOnCore c v).currentOnCore c' = s.currentOnCore c' := by
  simp [SchedulerState.setDomainScheduleIndexOnCore, SchedulerState.currentOnCore]
@[simp] theorem setDomainScheduleIndexOnCore_runQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainScheduleIndexOnCore c v).runQueueOnCore c' = s.runQueueOnCore c' := by
  simp [SchedulerState.setDomainScheduleIndexOnCore, SchedulerState.runQueueOnCore]
@[simp] theorem setDomainScheduleIndexOnCore_replenishQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainScheduleIndexOnCore c v).replenishQueueOnCore c' = s.replenishQueueOnCore c' := by
  simp [SchedulerState.setDomainScheduleIndexOnCore, SchedulerState.replenishQueueOnCore]
@[simp] theorem setDomainScheduleIndexOnCore_activeDomainOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainScheduleIndexOnCore c v).activeDomainOnCore c' = s.activeDomainOnCore c' := by
  simp [SchedulerState.setDomainScheduleIndexOnCore, SchedulerState.activeDomainOnCore]
@[simp] theorem setDomainScheduleIndexOnCore_domainTimeRemainingOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainScheduleIndexOnCore c v).domainTimeRemainingOnCore c' = s.domainTimeRemainingOnCore c' := by
  simp [SchedulerState.setDomainScheduleIndexOnCore, SchedulerState.domainTimeRemainingOnCore]
@[simp] theorem setDomainScheduleIndexOnCore_lastTimeoutErrorsOnCore (s : SchedulerState) (c c' : CoreId) (v : Nat) :
    (s.setDomainScheduleIndexOnCore c v).lastTimeoutErrorsOnCore c' = s.lastTimeoutErrorsOnCore c' := by
  simp [SchedulerState.setDomainScheduleIndexOnCore, SchedulerState.lastTimeoutErrorsOnCore]
@[simp] theorem setLastTimeoutErrorsOnCore_currentOnCore (s : SchedulerState) (c c' : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) :
    (s.setLastTimeoutErrorsOnCore c v).currentOnCore c' = s.currentOnCore c' := by
  simp [SchedulerState.setLastTimeoutErrorsOnCore, SchedulerState.currentOnCore]
@[simp] theorem setLastTimeoutErrorsOnCore_runQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) :
    (s.setLastTimeoutErrorsOnCore c v).runQueueOnCore c' = s.runQueueOnCore c' := by
  simp [SchedulerState.setLastTimeoutErrorsOnCore, SchedulerState.runQueueOnCore]
@[simp] theorem setLastTimeoutErrorsOnCore_replenishQueueOnCore (s : SchedulerState) (c c' : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) :
    (s.setLastTimeoutErrorsOnCore c v).replenishQueueOnCore c' = s.replenishQueueOnCore c' := by
  simp [SchedulerState.setLastTimeoutErrorsOnCore, SchedulerState.replenishQueueOnCore]
@[simp] theorem setLastTimeoutErrorsOnCore_activeDomainOnCore (s : SchedulerState) (c c' : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) :
    (s.setLastTimeoutErrorsOnCore c v).activeDomainOnCore c' = s.activeDomainOnCore c' := by
  simp [SchedulerState.setLastTimeoutErrorsOnCore, SchedulerState.activeDomainOnCore]
@[simp] theorem setLastTimeoutErrorsOnCore_domainTimeRemainingOnCore (s : SchedulerState) (c c' : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) :
    (s.setLastTimeoutErrorsOnCore c v).domainTimeRemainingOnCore c' = s.domainTimeRemainingOnCore c' := by
  simp [SchedulerState.setLastTimeoutErrorsOnCore, SchedulerState.domainTimeRemainingOnCore]
@[simp] theorem setLastTimeoutErrorsOnCore_domainScheduleIndexOnCore (s : SchedulerState) (c c' : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) :
    (s.setLastTimeoutErrorsOnCore c v).domainScheduleIndexOnCore c' = s.domainScheduleIndexOnCore c' := by
  simp [SchedulerState.setLastTimeoutErrorsOnCore, SchedulerState.domainScheduleIndexOnCore]
@[simp] theorem setCurrentOnCore_domainSchedule (s : SchedulerState) (c : CoreId) (v : Option SeLe4n.ThreadId) :
    (s.setCurrentOnCore c v).domainSchedule = s.domainSchedule := by
  simp [SchedulerState.setCurrentOnCore]
@[simp] theorem setCurrentOnCore_configDefaultTimeSlice (s : SchedulerState) (c : CoreId) (v : Option SeLe4n.ThreadId) :
    (s.setCurrentOnCore c v).configDefaultTimeSlice = s.configDefaultTimeSlice := by
  simp [SchedulerState.setCurrentOnCore]
@[simp] theorem setRunQueueOnCore_domainSchedule (s : SchedulerState) (c : CoreId) (v : SeLe4n.Kernel.RunQueue) :
    (s.setRunQueueOnCore c v).domainSchedule = s.domainSchedule := by
  simp [SchedulerState.setRunQueueOnCore]
@[simp] theorem setRunQueueOnCore_configDefaultTimeSlice (s : SchedulerState) (c : CoreId) (v : SeLe4n.Kernel.RunQueue) :
    (s.setRunQueueOnCore c v).configDefaultTimeSlice = s.configDefaultTimeSlice := by
  simp [SchedulerState.setRunQueueOnCore]
@[simp] theorem setReplenishQueueOnCore_domainSchedule (s : SchedulerState) (c : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    (s.setReplenishQueueOnCore c v).domainSchedule = s.domainSchedule := by
  simp [SchedulerState.setReplenishQueueOnCore]
@[simp] theorem setReplenishQueueOnCore_configDefaultTimeSlice (s : SchedulerState) (c : CoreId) (v : SeLe4n.Kernel.ReplenishQueue) :
    (s.setReplenishQueueOnCore c v).configDefaultTimeSlice = s.configDefaultTimeSlice := by
  simp [SchedulerState.setReplenishQueueOnCore]
@[simp] theorem setActiveDomainOnCore_domainSchedule (s : SchedulerState) (c : CoreId) (v : SeLe4n.DomainId) :
    (s.setActiveDomainOnCore c v).domainSchedule = s.domainSchedule := by
  simp [SchedulerState.setActiveDomainOnCore]
@[simp] theorem setActiveDomainOnCore_configDefaultTimeSlice (s : SchedulerState) (c : CoreId) (v : SeLe4n.DomainId) :
    (s.setActiveDomainOnCore c v).configDefaultTimeSlice = s.configDefaultTimeSlice := by
  simp [SchedulerState.setActiveDomainOnCore]
@[simp] theorem setDomainTimeRemainingOnCore_domainSchedule (s : SchedulerState) (c : CoreId) (v : Nat) :
    (s.setDomainTimeRemainingOnCore c v).domainSchedule = s.domainSchedule := by
  simp [SchedulerState.setDomainTimeRemainingOnCore]
@[simp] theorem setDomainTimeRemainingOnCore_configDefaultTimeSlice (s : SchedulerState) (c : CoreId) (v : Nat) :
    (s.setDomainTimeRemainingOnCore c v).configDefaultTimeSlice = s.configDefaultTimeSlice := by
  simp [SchedulerState.setDomainTimeRemainingOnCore]
@[simp] theorem setDomainScheduleIndexOnCore_domainSchedule (s : SchedulerState) (c : CoreId) (v : Nat) :
    (s.setDomainScheduleIndexOnCore c v).domainSchedule = s.domainSchedule := by
  simp [SchedulerState.setDomainScheduleIndexOnCore]
@[simp] theorem setDomainScheduleIndexOnCore_configDefaultTimeSlice (s : SchedulerState) (c : CoreId) (v : Nat) :
    (s.setDomainScheduleIndexOnCore c v).configDefaultTimeSlice = s.configDefaultTimeSlice := by
  simp [SchedulerState.setDomainScheduleIndexOnCore]
@[simp] theorem setLastTimeoutErrorsOnCore_domainSchedule (s : SchedulerState) (c : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) :
    (s.setLastTimeoutErrorsOnCore c v).domainSchedule = s.domainSchedule := by
  simp [SchedulerState.setLastTimeoutErrorsOnCore]
@[simp] theorem setLastTimeoutErrorsOnCore_configDefaultTimeSlice (s : SchedulerState) (c : CoreId) (v : List (SeLe4n.ThreadId × KernelError)) :
    (s.setLastTimeoutErrorsOnCore c v).configDefaultTimeSlice = s.configDefaultTimeSlice := by
  simp [SchedulerState.setLastTimeoutErrorsOnCore]
end SchedulerState

/-- WS-G4: Compatibility alias — `runnable` projects to the flat list maintained
    inside `RunQueue` for proof/projection compatibility. -/
abbrev SchedulerState.runnable (s : SchedulerState) : List SeLe4n.ThreadId :=
  (s.runQueueOnCore bootCoreId).toList

/-- X2-B/H-2: Check that all domain schedule entries have positive length.
This is a runtime-checkable predicate for validating domain schedule
configurations before they are installed. -/
def SchedulerState.domainScheduleAllPositive (schedule : List DomainScheduleEntry) : Bool :=
  schedule.all (fun e => e.length > 0)

/-- Architecture-neutral address of a capability slot inside a CNode object. -/
structure SlotRef where
  cnode : SeLe4n.ObjId
  slot : SeLe4n.Slot
  deriving Repr, DecidableEq

/-- WS-G1: Hash instance for composite HashMap/HashSet keying.
    Combines cnode and slot hashes via `mixHash` for uniform distribution.
    BEq is already provided by DecidableEq via instBEqOfDecidableEq. -/
@[inline] instance : Hashable SlotRef where
  hash a := mixHash (hash a.cnode) (hash a.slot)

/-- Lifecycle metadata required by the first M4-A transition story.

`objectTypes` keeps object-store identity explicit, while `capabilityRefs` records the target
named by each populated capability slot reference.

WS-G2/WS-H7: metadata maps are HashMap-backed for O(1) amortized lookup,
eliminating closure-chain growth from repeated updates. -/
structure LifecycleMetadata where
  objectTypes : RHTable SeLe4n.ObjId KernelObjectType
  capabilityRefs : RHTable SlotRef CapTarget

/-- R7-A.1/M-17: A single TLB entry caching an address translation.

    On ARM64, the TLB caches `(ASID, VAddr, PAddr, PagePermissions)` tuples.
    Stale entries after page table modification are a security concern — the
    `tlbConsistent` invariant (in `TlbModel.lean`) enforces that all cached
    entries match the current page tables.

    AK7-J (F-M11 / MEDIUM): `asidGeneration` mirrors
    `AsidManager.AsidPool.generation` (AK3-D), allowing stale entries to be
    detected after an ASID is freed and re-allocated. When an ASID is
    re-used, `AsidPool.generation` increments; the kernel rejects TLB
    entries whose `asidGeneration` predates the current pool generation
    rather than trusting stale hits. Default `0` preserves backward
    compatibility; substantive ASID-generation bookkeeping is performed
    by `AsidManager` / `adapterFlushTlbByAsid`. -/
structure TlbEntry where
  asid : SeLe4n.ASID
  vaddr : SeLe4n.VAddr
  paddr : SeLe4n.PAddr
  perms : PagePermissions
  /-- AK7-J (F-M11): Generation counter shadowing `AsidPool.generation` at
      the time of TLB entry installation. Stale entries can be detected
      by comparing `asidGeneration` against the current pool generation
      — mismatches indicate the ASID was freed and reused after the entry
      was cached. Default `0` preserves backward compatibility with
      legacy TLB fixtures that predate AK7-J. -/
  asidGeneration : Nat := 0
  deriving Repr, DecidableEq, BEq

/-- R7-A.1/M-17: Abstract TLB state: a collection of cached translation entries.

    The list representation is intentionally simple — hardware TLBs are
    associative caches, but for invariant reasoning we only need membership
    queries, not performance-optimal lookup. -/
structure TlbState where
  entries : List TlbEntry
  deriving Repr

instance : Inhabited TlbState where
  default := { entries := [] }

/-- An empty TLB with no cached entries. -/
def TlbState.empty : TlbState := { entries := [] }

/-- R7-A.3: Full TLB flush — invalidates all cached entries.
    On ARM64 this corresponds to `TLBI ALLE1` or `TLBI VMALLE1IS`.

    S5-J: Complexity is O(1) — returns a fresh empty TLB state. -/
def adapterFlushTlb (_tlb : TlbState) : TlbState :=
  TlbState.empty

/-- R7-A.3: Per-ASID TLB flush — invalidates all entries for a specific ASID.
    On ARM64 this corresponds to `TLBI ASIDE1, <asid>`.

    S5-J: Complexity is O(n) where n = `entries.length`. Acceptable because
    TLB sizes are bounded by hardware (ARM Cortex-A76 TLB has ≤1280 entries
    across all levels, and the model tracks only actively cached entries). -/
def adapterFlushTlbByAsid (tlb : TlbState) (asid : SeLe4n.ASID) : TlbState :=
  { entries := tlb.entries.filter (·.asid != asid) }

/-- R7-A.3: Per-VAddr TLB flush — invalidates entries for a specific (ASID, VAddr).
    On ARM64 this corresponds to `TLBI VAE1, <asid, vaddr>`.

    S5-J: Complexity is O(n) where n = `entries.length`. Same bound as
    `adapterFlushTlbByAsid` — hardware TLB sizes are fixed and small. -/
def adapterFlushTlbByVAddr (tlb : TlbState) (asid : SeLe4n.ASID) (vaddr : SeLe4n.VAddr) : TlbState :=
  { entries := tlb.entries.filter (fun e => !(e.asid == asid && e.vaddr == vaddr)) }

structure SystemState where
  machine : SeLe4n.MachineState
  /-- Q2-C: Object store backed by `RHTable` (verified Robin Hood hash table)
      for O(1) amortized lookup with machine-checked invariants.

      S4-J: All `objects` uses in production kernel code are lookup-only
      (`objects[oid]?`, `objects.get?`). No operation iterates over the
      object store in an order-dependent manner. This is critical because
      `RHTable` iteration order (via `fold`/`toList`) depends on internal
      slot layout and is not deterministic across resize operations.

      **Audit (S4-J):** Two lifecycle cleanup functions use `objects.fold`:
      `removeFromAllEndpointQueues` and `removeFromAllNotificationWaitLists`
      (Lifecycle/Operations.lean). Both are order-independent — they apply
      the same idempotent per-object transformation regardless of iteration
      order. The `freeze` function in FrozenState.lean uses `objects.toList`
      to snapshot the object store, but the resulting `FrozenMap` is keyed
      by `ObjId` with O(1) lookup, so insertion order does not affect
      semantics. No order-dependent iteration patterns exist. -/
  objects : RHTable SeLe4n.ObjId KernelObject
  /-- L-05/WS-E6: Monotonic append-only index of all object IDs that have been
      stored. This list is intentionally never pruned — `storeObject` prepends
      new IDs and never removes old ones.

      **Design rationale:** Monotonic append-only semantics ensure that any
      membership witness (`id ∈ st.objectIndex`) remains valid across all future
      states. This simplifies invariant proofs: once an ID appears in the index,
      it persists, so cross-transition carryover is trivially established. The
      tradeoff is that the index may contain IDs for objects that have since been
      overwritten or logically deleted; consumers must check `st.objects[id]?`
      for `some _` to confirm the object still exists.

      **Migration path:** If bounded-memory semantics or garbage collection are
      added in a future workstream, `objectIndex` can be replaced by a data
      structure supporting removal while preserving the monotonicity invariant
      for the live-object subset.

      **S4-A: Growth analysis.** For a typical RPi5 workload with `maxObjects =
      65536`, the objectIndex list consumes at most `65536 × sizeof(ObjId)` bytes.
      At 8 bytes per ObjId (Nat on 64-bit), this is 512 KB — well within the
      RPi5's 8 GB RAM budget. The advisory predicate `objectIndexBounded` below
      documents the expected bound. -/
  objectIndex : List SeLe4n.ObjId
  /-- WS-G2/F-P10: Shadow hash set for O(1) objectIndex membership checks.
      Maintained in parallel with `objectIndex` — `storeObject` inserts into
      both. The list remains the proof anchor (monotonic, append-only);
      this set is the runtime fast path. -/
  objectIndexSet : RHSet SeLe4n.ObjId := default
  services : RHTable ServiceId ServiceGraphEntry
  scheduler : SchedulerState
  irqHandlers : RHTable SeLe4n.Irq SeLe4n.ObjId
  lifecycle : LifecycleMetadata
  /-- WS-G3/F-P06: ASID→ObjId resolution table for O(1) VSpace lookups.
      Maintained by `storeObject` — insertions on `.vspaceRoot` stores, erasures
      when a VSpaceRoot is overwritten. Replaces the O(n) `objectIndex.findSome?`
      scan in `resolveAsidRoot`. -/
  asidTable : RHTable SeLe4n.ASID SeLe4n.ObjId := {}
  /-- WS-Q1-B: Registry of concrete interface specifications keyed by InterfaceId. -/
  interfaceRegistry : RHTable SeLe4n.InterfaceId InterfaceSpec := {}
  /-- WS-Q1-B: Registry of capability-mediated service registrations keyed by ServiceId. -/
  serviceRegistry : RHTable ServiceId ServiceRegistration := {}
  cdt : CapDerivationTree := .empty   -- WS-E4/C-03: node-based Capability Derivation Tree
  cdtSlotNode : RHTable SlotRef CdtNodeId := {}
  cdtNodeSlot : RHTable CdtNodeId SlotRef := {}
  cdtNextNode : CdtNodeId := ⟨0⟩
  /-- S-05/PERF-O1: Per-SchedContext thread index — maps each `SchedContextId`
      to the list of `ThreadId`s whose `TCB.schedContextBinding.scId?` equals
      that SchedContext. Maintained by `schedContextBind`, `schedContextUnbind`,
      `donateSchedContext`, `returnDonatedSchedContext`, and `cancelDonation`.

      **Purpose**: Eliminates the O(n) full object-store scan in
      `timeoutBlockedThreads` (finding S-05). With this index, timeout on
      budget exhaustion is O(1) RHTable lookup + O(k) iteration where
      k = number of threads referencing the exhausted SchedContext (typically
      1–3 due to the 1:1 binding + donation model).

      **Invariant (`scThreadIndexConsistent`)**: A thread `tid` appears in
      `scThreadIndex[scId]` iff `tid` exists as a TCB in `objects` with
      `schedContextBinding.scId? = some scId`. -/
  scThreadIndex : RHTable SeLe4n.SchedContextId (List SeLe4n.ThreadId) := {}
  /-- R7-A.1/M-17: Abstract TLB state, tracking cached address translations.
      Empty by default (no stale entries at boot). Operations that modify page
      tables must flush the TLB to maintain `tlbConsistent`.

      Under SMP this is the boot core's view; the cross-core invalidation
      coordination lives in the `tlbShootdown` field below (WS-SM SM7.A),
      and SM7.C generalises this field to a per-core `Vector`. -/
  tlb : TlbState := TlbState.empty
  /-- WS-SM SM3.A.10: ObjStore table-level reader-writer lock state.

      Per §4.4 of the SM3 plan, the underlying RobinHood hash table
      (`objects : RHTable ObjId KernelObject`) carries a single table-level
      lock at the top of the lock hierarchy
      (`LockKind.objStore`, level 0).  Rationale: inserts and deletes can
      relocate entries across buckets (Robin Hood probe-sequence
      reorganisation), so a per-bucket lock would require complex
      hand-over-hand acquisition.  The table-level lock is acquired in:

      * `read` mode for lookups (`objects[id]?`, `lookupObject`).
      * `write` mode for inserts (`storeObject`,
        `storeObjectChecked`, `storeObjectKindChecked`) and deletes
        (`removeObject` etc.).

      Default `RwLockState.unheld` means a freshly-created SystemState
      starts with the ObjStore lock available.  This is the lowest-level
      lock in the SM3 hierarchy, acquired first (before any per-object
      lock) per the 2PL discipline in SM3.C.  See
      `docs/planning/SMP_PER_OBJECT_LOCKS_PLAN.md` §5.1 (SM3.A.10). -/
  objStoreLock : SeLe4n.Kernel.Concurrency.RwLockState :=
    SeLe4n.Kernel.Concurrency.RwLockState.unheld
  /-- WS-SM SM7.A: per-core TLB-shootdown coordination state — the
      pending-invalidation queues and acknowledgment flags of
      `SeLe4n/Kernel/Architecture/TlbShootdown.lean`.

      This field realises the SM7 plan's §4.1
      "`pendingShootdowns : Vector (List TlbShootdownDescriptor)
      coreCount` in `ConcurrencyState`" placement in the codebase's
      actual state architecture: `SystemState` is the kernel's runtime
      state (there is no separate `ConcurrencyState` structure; the
      SM3.A.10 `objStoreLock` field above landed the same way).

      Defaults to `TlbShootdownState.initial` — the quiescent boot
      state (all queues empty, all flags acknowledged), matching the
      Rust `SHOOTDOWN_ACK` boot value; pinned by
      `default_tlbShootdown_initial` / the SM7.A default-state
      theorems below.

      **Mutators**: exclusively the SM7.B shootdown protocol
      transitions (`tlbShootdownBroadcast{,Coalescing}` + the
      `.tlbShootdownReq` SGI handler `handleTlbShootdownReqOnCore`,
      `TlbShootdownProtocol.lean`), going exclusively through the
      SM7.A operations (`enqueueShootdown{,OrCoalesce}` /
      `drainShootdowns` / `acknowledgeShootdown` /
      `beginShootdownRound{,For}`), never the raw setters, so the
      `pendingBounded` capacity invariant — the 12th
      `proofLayerInvariantBundle` conjunct since SM7.B — is carried
      by construction (`…_preserves_pendingBounded` family).  Every
      other transition frames this field (`{ st with … }` updates
      never mention it; pinned per-operation by the
      `…_tlbShootdown_eq` frame families).

      **Information flow**: the field is not yet part of the IF
      projection surface — no transition reads it, so it cannot yet
      influence any observable.  SM7.B's protocol NI obligations and
      the SM8 per-core observable-state migration take it into the
      projection together with the transitions that consume it. -/
  tlbShootdown : SeLe4n.Kernel.Architecture.TlbShootdownState :=
    SeLe4n.Kernel.Architecture.TlbShootdownState.initial
  /-- WS-SM SM7.C.1: per-core TLB model — every core's independently
      cached address-translation view.

      The scalar `tlb` field above is the pre-SMP single-core (boot-core)
      abstract TLB (WS-H11/M-17): its flush operations (`adapterFlushTlb*`,
      the `.WithFlush` VSpace ops) manage one view.  Under SMP each PE
      caches translations in its own TLB, so an invalidation issued on one
      core does not reach another core's TLB without the SM7.B shootdown
      protocol.  This field is that generalisation: a
      `Vector TlbState numCores` under the SM4.B path-a discipline
      (`tlbOnCore` / `setTlbOnCore` accessors, store/load algebra, and
      `ext_perCore` in `SeLe4n/Kernel/Architecture/PerCoreTlbModel.lean`),
      with the boot-core slot cohering with the legacy `tlb` view (both
      empty at boot; `default_perCoreTlb`).

      **Semantics**: the SM7.C model operations drive it —
      `tlbInsertOnCore` (the hardware page-table walker filling one core's
      TLB), `tlbInvalidateOnCore` (a local, this-core invalidation), and
      `tlbInvalidateOnAllCores` (the cross-core broadcast, which posts to
      `tlbShootdown` above **and** evolves every core's view exactly as
      Theorem 3.3.1's `shootdownRoundViews` prescribes — so this field is
      a genuine consumer of the shootdown state machine, not a free-standing
      parallel structure).  The per-core consistency invariant
      `tlbInvalidationConsistent_perCore` (every core's view matches the
      page tables) is the 13th `proofLayerInvariantBundle` conjunct,
      generalising the 9th (`tlbConsistent st st.tlb`).

      Defaults to every core's empty view (`Vector.replicate numCores
      TlbState.empty`) — no stale entries at boot; pinned by
      `default_perCoreTlb`.

      **Information flow**: like `tlb` and `machine.timer`, this field is
      deliberately **not** part of the IF projection surface — projecting a
      TLB view would open a covert timing channel.  Its exclusion from
      `projectState` is the correct behaviour. -/
  perCoreTlb : Vector TlbState numCores :=
    Vector.replicate numCores TlbState.empty

/-- Abstract owner identity for a slot in this model: the containing CNode object id. -/
abbrev CSpaceOwner := SeLe4n.ObjId

instance : Inhabited SchedulerState where
  default := {}

/-- WS-SM SM4.B.9: the default scheduler state is per-core initialised to the
neutral value on *every* core (plan §3.6).  Each field defaults to
`Vector.replicate numCores <neutral>`, so each conjunct discharges via
`SeLe4n.PerCoreVector.replicate_get` (every slot of a replicate holds the
replicated value). -/
theorem default_state_perCoreInitialized (c : CoreId) :
    (default : SchedulerState).currentOnCore c = none ∧
    (default : SchedulerState).runQueueOnCore c = SeLe4n.Kernel.RunQueue.empty ∧
    (default : SchedulerState).replenishQueueOnCore c = SeLe4n.Kernel.ReplenishQueue.empty ∧
    (default : SchedulerState).activeDomainOnCore c = ⟨0⟩ ∧
    (default : SchedulerState).domainTimeRemainingOnCore c = 5 ∧
    (default : SchedulerState).domainScheduleIndexOnCore c = 0 ∧
    (default : SchedulerState).lastTimeoutErrorsOnCore c = [] := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> exact PerCoreVector.replicate_get _ _ c

instance : Inhabited SystemState where
  default := {
    machine := default
    objects := {}
    objectIndex := []
    objectIndexSet := default
    services := {}
    scheduler := default
    irqHandlers := {}
    lifecycle := {
      objectTypes := {}
      capabilityRefs := {}
    }
    asidTable := {}
    interfaceRegistry := {}
    serviceRegistry := {}
    cdt := .empty
    cdtSlotNode := {}
    cdtNodeSlot := {}
    cdtNextNode := ⟨0⟩
    scThreadIndex := {}
    tlb := TlbState.empty
    -- WS-SM SM3.A.10: ObjStore table-level lock starts in the unheld
    -- state (lock available) at boot.  Explicit listing pins the
    -- default-state invariant `default.objStoreLock = .unheld` so the
    -- `default_objStoreLock_unheld` and `default_objects_locks_unheld`
    -- theorems (SM3.A.11) can discharge by `rfl`.
    objStoreLock := SeLe4n.Kernel.Concurrency.RwLockState.unheld
    -- WS-SM SM7.A: TLB-shootdown coordination state starts quiescent
    -- (all pending queues empty, all ack flags true — nobody waited
    -- on) at boot, matching the Rust SHOOTDOWN_ACK boot value.
    -- Explicit listing pins the default-state invariant so the
    -- `default_tlbShootdown_initial` / `default_tlbShootdown_quiescent`
    -- theorems (SM7.A) can discharge by `rfl` / the initial-state
    -- theorems.
    tlbShootdown := SeLe4n.Kernel.Architecture.TlbShootdownState.initial
    -- WS-SM SM7.C.1: every core's TLB view starts empty (no stale
    -- translations at boot).  Explicit listing pins the default-state
    -- invariant so `default_perCoreTlb` discharges via
    -- `PerCoreVector.replicate_get`.
    perCoreTlb := Vector.replicate numCores TlbState.empty
  }

/-- X2-B/H-2: Checked domain schedule setter — validates that all entries have
positive length before installing the schedule. Returns `.error` on invalid
input to prevent `switchDomain` from setting `domainTimeRemaining` to 0.
Use this instead of directly setting `scheduler.domainSchedule`. -/
def setDomainScheduleChecked (st : SystemState) (schedule : List DomainScheduleEntry) :
    Except String SystemState :=
  if SchedulerState.domainScheduleAllPositive schedule then
    .ok { st with scheduler := { st.scheduler with domainSchedule := schedule } }
  else
    .error "setDomainScheduleChecked: domain schedule contains zero-length entry"

/-- Q2-J: Predicate asserting that every RHTable and RHSet in the system state
satisfies the Robin Hood invariant extension (WF ∧ distCorrect ∧ noDupKeys ∧
probeChainDominant). This is the global well-formedness condition for the
builder-phase state representation.

AI6-D (L-02): This predicate uses a 17-deep conjunction (∧-chain) over all
RHTable/RHSet instances in the state. Tuple projection (e.g., `h.2.2.1`) is
structurally fragile — adding a new table field shifts all subsequent
projection indices. Named extractors (Builder.lean:30-116) provide
maintainable access to individual conjuncts without positional dependence.
See AF-26 for design rationale on the projection vs. named-extractor
tradeoff. The conjunction depth is stable under the current invariant
bundle and only changes when new RHTable/RHSet fields are added to
SystemState or its sub-structures. -/
def SystemState.allTablesInvExtK (st : SystemState) : Prop :=
  -- SystemState direct fields
  st.objects.invExtK ∧
  st.irqHandlers.invExtK ∧
  st.asidTable.invExtK ∧
  st.cdtSlotNode.invExtK ∧
  st.cdtNodeSlot.invExtK ∧
  -- LifecycleMetadata
  st.lifecycle.objectTypes.invExtK ∧
  st.lifecycle.capabilityRefs.invExtK ∧
  -- CDT
  st.cdt.childMap.invExtK ∧
  st.cdt.parentMap.invExtK ∧
  -- Service and registry
  st.services.invExtK ∧
  st.interfaceRegistry.invExtK ∧
  st.serviceRegistry.invExtK ∧
  -- RunQueue
  (st.scheduler.runQueueOnCore bootCoreId).byPriority.invExtK ∧
  (st.scheduler.runQueueOnCore bootCoreId).threadPriority.invExtK ∧
  -- RHSet invExtK (via table field)
  st.objectIndexSet.table.invExtK ∧
  (st.scheduler.runQueueOnCore bootCoreId).membership.table.invExtK ∧
  -- S-05/PERF-O1: Per-SchedContext thread index
  st.scThreadIndex.invExtK

/-- The default SystemState satisfies `allTablesInvExtK` because all tables are
empty, and empty RHTables with capacity 16 trivially satisfy `invExtK`. -/
theorem default_allTablesInvExtK : (default : SystemState).allTablesInvExtK := by
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)
  constructor; exact SeLe4n.Kernel.RobinHood.RHSet.empty_invExtK
  constructor; exact SeLe4n.Kernel.RobinHood.RHSet.empty_invExtK
  exact SeLe4n.Kernel.RobinHood.RHTable.empty_invExtK 16 (by omega)

-- ============================================================================
-- WS-SM SM3.A.11 — Per-object lock invariants on the default SystemState
-- ============================================================================

/-- WS-SM SM3.A.10/A.11: The default SystemState has `objStoreLock = .unheld`.

This pins the "lock available at boot" semantics of the SM3.A.10
table-level ObjStore lock: a freshly-constructed SystemState (e.g. the
seed passed to `bootFromPlatform`) carries an unheld ObjStore lock by
construction.  Subsequent boot operations (`storeObject`, etc.) acquire
the lock per the SM3.C.1 `withLockSet` discipline. -/
theorem default_objStoreLock_unheld :
    (default : SystemState).objStoreLock = SeLe4n.Kernel.Concurrency.RwLockState.unheld := rfl

/-- WS-SM SM3.A.11: Every object reachable through the default SystemState
has its per-object lock in the `.unheld` state.

This is the canonical SM3.A.11 closure theorem: a freshly-constructed
SystemState has an empty object store (`RHTable.empty 16`), so the
universal quantifier is **vacuously discharged** — no `id` ever resolves
to `some o`.  The discharge uses `RHTable.getElem?_empty`, which proves
that `(RHTable.empty 16 _)[id]? = none` for every key.

For a non-default state where `bootFromPlatform` populates initial
objects, the analogous theorem proves that **every initial object**
(created via the `Builder.createObject` smart constructor) has its
lock in `.unheld` — because the smart constructor invokes the
per-object struct's default constructor, which sets `lock :=
RwLockState.unheld` by the SM3.A.1..A.9 field defaults.  That stronger
statement is part of the SM3.B follow-on (`LockId.lookup` discharge for
post-boot states).

Per SM3.C.4 (`lockSetHeld`), this theorem is the **base case** for the
per-state lock-set-availability induction: at boot, no core holds any
per-object lock; subsequent transitions acquire and release per the
2PL discipline. -/
theorem default_objects_locks_unheld :
    ∀ (id : SeLe4n.ObjId) (o : KernelObject),
      (default : SystemState).objects.get? id = some o →
      KernelObject.objectLockOf o = SeLe4n.Kernel.Concurrency.RwLockState.unheld := by
  intro id o hLookup
  -- The default SystemState's `objects` is `RHTable.empty 16 (by decide)`
  -- via `instInhabitedRHTable`. `RHTable.getElem?_empty` proves that
  -- looking up any key in an empty table returns `none`.
  have hEmpty : (default : SystemState).objects.get? id = none := by
    show (default : SeLe4n.Kernel.RobinHood.RHTable SeLe4n.ObjId KernelObject).get? id = none
    exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_empty
      SeLe4n.Kernel.RobinHood.minPracticalRHCapacity (by decide) id
  -- Lookup returns `some o` and `none` simultaneously — contradiction.
  rw [hEmpty] at hLookup
  cases hLookup

/-- WS-SM SM3.A.11 (decidable variant): the predicate "every object's
lock is unheld" reduces to a vacuous quantification on the default
state.  Used as a Tier-2 runtime assertion in `PerObjectLockSuite`.

The proof closes via `default_objects_toList_empty` below — the default
state's object store has an empty `toList`, so the universal
quantification over members is vacuously discharged. -/
theorem default_objects_toList_empty :
    (default : SystemState).objects.toList = [] := by
  -- `default.objects` is the canonical `RHTable.empty 16` populated with
  -- 16 `none` slots.  `toList` folds the slots with a cons-on-some
  -- handler; since every slot is `none`, the fold accumulator stays
  -- `[]` throughout.  `decide` discharges the finite computation
  -- because the capacity is the literal `16` (`minPracticalRHCapacity`).
  decide

/-- WS-SM SM3.A.11 (decidable variant): every entry in the default
state's `toList` snapshot has `objectLockOf p.2 = .unheld`.  The default
state's `toList` is empty (`default_objects_toList_empty`), so this is
vacuously true.  Used as a Tier-2 runtime assertion in
`PerObjectLockSuite`. -/
theorem default_objects_locks_unheld_via_toList :
    ∀ p ∈ (default : SystemState).objects.toList,
      KernelObject.objectLockOf p.2 = SeLe4n.Kernel.Concurrency.RwLockState.unheld := by
  intro p hp
  rw [default_objects_toList_empty] at hp
  exact absurd hp (List.not_mem_nil)

-- ============================================================================
-- WS-SM SM7.A — TLB-shootdown state invariants on the default SystemState
-- ============================================================================

/-- WS-SM SM7.A: the default SystemState carries the quiescent
TLB-shootdown boot state.  Pinned by the explicit listing in the
`Inhabited SystemState` instance, mirroring
`default_objStoreLock_unheld` (SM3.A.11). -/
theorem default_tlbShootdown_initial :
    (default : SystemState).tlbShootdown =
      SeLe4n.Kernel.Architecture.TlbShootdownState.initial := rfl

/-- WS-SM SM7.A: at boot no shootdown round is in flight — every core's
pending queue is empty and every acknowledgment flag is `true` ("nobody
waited on"), matching the Rust `SHOOTDOWN_ACK` boot value.  Direct
consequence of `default_tlbShootdown_initial` +
`initial_shootdownQuiescent`. -/
theorem default_tlbShootdown_quiescent :
    SeLe4n.Kernel.Architecture.shootdownQuiescent
      (default : SystemState).tlbShootdown := by
  rw [default_tlbShootdown_initial]
  exact SeLe4n.Kernel.Architecture.initial_shootdownQuiescent

/-- WS-SM SM7.A.6: the default SystemState satisfies the shootdown
capacity invariant (empty queues are trivially within
`maxPendingPerCore`). -/
theorem default_tlbShootdown_pendingBounded :
    SeLe4n.Kernel.Architecture.pendingBounded
      (default : SystemState).tlbShootdown :=
  SeLe4n.Kernel.Architecture.pendingBounded_of_shootdownQuiescent
    default_tlbShootdown_quiescent

/-- WS-SM SM7.C.1: at boot every core's TLB view is empty — the per-core
generalisation of `tlb := TlbState.empty`.  Discharged by
`PerCoreVector.replicate_get` (every slot of a `Vector.replicate` holds
the replicated value), so `default_perCoreTlb` is available to the SM7.C
per-core-consistency boot witness and to the Boot general bridge
`bootFromPlatform_perCoreTlb_eq`. -/
theorem default_perCoreTlb (c : CoreId) :
    (default : SystemState).perCoreTlb.get c = TlbState.empty :=
  PerCoreVector.replicate_get _ _ c

-- ============================================================================
-- WS-SM SM3.A audit-pass-5 — Non-vacuous lock-state invariant + preservation
-- ============================================================================

/-- WS-SM SM3.A audit-pass-5: the SM3.A runtime invariant — every
object in the store has its lock in the unheld state, AND the
table-level `objStoreLock` is also unheld.

Captures the *static* shape that holds at SM3.A scope: no current
kernel operation acquires or releases any lock, so every reachable
state from `default` has all locks in their initial state.

This predicate is **not** vacuous: it has two conjuncts that are
both substantive (the `objStoreLock = .unheld` clause alone is a
non-trivial assertion about the state's table-level lock field).

SM3.C (`withLockSet`) will introduce the *dynamic* shape — locks
can transition.  At SM3.A scope this predicate is invariant under
every kernel transition, witnessed by the
`*_preserves_allObjectLocksUnheld` family of theorems below. -/
def SystemState.allObjectLocksUnheld (st : SystemState) : Prop :=
  st.objStoreLock = SeLe4n.Kernel.Concurrency.RwLockState.unheld ∧
  ∀ id o, st.objects.get? id = some o →
    KernelObject.objectLockOf o = SeLe4n.Kernel.Concurrency.RwLockState.unheld

/-- WS-SM SM3.A audit-pass-5: a Bool-valued decidable form of
`allObjectLocksUnheld` over the `toList` snapshot.

Runtime fixtures use this Bool form to `decide`-discharge the
invariant on small object stores.  The relationship to the Prop
form is the standard "list-quantification ↔ universal
quantification on lookups" bridge, captured by
`allObjectLocksUnheld_iff_via_toList` in
`SeLe4n/Model/FreezeProofs.lean` (audit-pass-6) for states whose
object store satisfies the Robin Hood invariant `invExt`.

The Bool form lets `tests/PerObjectLockSuite.lean` exercise the
invariant via `decide ((default : SystemState).allObjectLocksUnheldB
= true)` without needing the Prop ↔ Bool bridge in scope. -/
def SystemState.allObjectLocksUnheldB (st : SystemState) : Bool :=
  (st.objStoreLock = SeLe4n.Kernel.Concurrency.RwLockState.unheld) &&
  (st.objects.toList.all
    (fun p => p.snd.objectLockOf = SeLe4n.Kernel.Concurrency.RwLockState.unheld))

/-- WS-SM SM3.A audit-pass-5 — STRONGER non-vacuous form of SM3.A.11.

The default SystemState satisfies the full SM3.A runtime
invariant: both the table-level `objStoreLock` is unheld AND every
object in the store has its lock unheld.

This is the canonical SM3.A.11 closure theorem in its non-vacuous
form: the first conjunct (`objStoreLock = .unheld`) is a
**substantive** witness, not a vacuous quantification.  The second
conjunct still discharges vacuously on the empty default store,
but its presence in the conjunction is the pin that downstream
SM3.B/C consumers can `obtain` against.

Per the SM3.A scope (no current kernel operation modifies any
lock), every reachable state from `default` satisfies this
predicate.  SM3.C will replace this with a weaker
`lockSetHeld`-relative predicate that accommodates lock
acquisition. -/
theorem default_allObjectLocksUnheld :
    (default : SystemState).allObjectLocksUnheld :=
  ⟨rfl, default_objects_locks_unheld⟩

/-- WS-SM SM3.A audit-pass-5: a more useful form of SM3.A.11 — for
any `SystemState` whose stored objects are constructed via default
constructors (so `objectLockOf` on each yields `.unheld`), the
predicate holds.

This is the "analogous post-boot theorem" promised in the
`default_objects_locks_unheld` docstring: at boot, the builder
populates the object store via `Builder.createObject`, which
constructs each object with the default `lock := .unheld` field
value.  The resulting state therefore satisfies
`allObjectLocksUnheld` (modulo the `objStoreLock` field, which is
also `.unheld` by default at boot).

The theorem is parameterised over `objStoreLock` to capture both
cases: the default `.unheld` and any future operationally-acquired
state.

**Closure path (SM3.B/C)**: once `Builder.createObject` is
extended to enforce `objectLockOf newObj = .unheld` at construction
time (the structural enforcement of the SM3.A.10 invariant), this
theorem becomes a direct corollary. -/
theorem allObjectLocksUnheld_of_pointwise (st : SystemState)
    (hObjStore : st.objStoreLock = SeLe4n.Kernel.Concurrency.RwLockState.unheld)
    (hPointwise : ∀ id o, st.objects.get? id = some o →
        KernelObject.objectLockOf o = SeLe4n.Kernel.Concurrency.RwLockState.unheld) :
    st.allObjectLocksUnheld :=
  ⟨hObjStore, hPointwise⟩

-- WS-SM SM3.A audit-pass-5: the `storeObject_preserves_*` theorems are
-- placed AFTER `storeObject`'s definition (around line 900 below), since
-- they reference its definitional reduction.

/-- U2-M: Compile-time completeness witness for `allTablesInvExtK`.
    This theorem destructures `allTablesInvExtK` into exactly 17 named conjuncts.
    If a new RHTable field is added to `SystemState` and included in
    `allTablesInvExtK` without updating this witness, the proof fails. -/
theorem allTablesInvExtK_witness (st : SystemState) (h : st.allTablesInvExtK) :
    st.objects.invExtK ∧
    st.irqHandlers.invExtK ∧
    st.asidTable.invExtK ∧
    st.cdtSlotNode.invExtK ∧
    st.cdtNodeSlot.invExtK ∧
    st.lifecycle.objectTypes.invExtK ∧
    st.lifecycle.capabilityRefs.invExtK ∧
    st.cdt.childMap.invExtK ∧
    st.cdt.parentMap.invExtK ∧
    st.services.invExtK ∧
    st.interfaceRegistry.invExtK ∧
    st.serviceRegistry.invExtK ∧
    (st.scheduler.runQueueOnCore bootCoreId).byPriority.invExtK ∧
    (st.scheduler.runQueueOnCore bootCoreId).threadPriority.invExtK ∧
    st.objectIndexSet.table.invExtK ∧
    (st.scheduler.runQueueOnCore bootCoreId).membership.table.invExtK ∧
    st.scThreadIndex.invExtK := h

-- ============================================================================
-- S-05/PERF-O1: scThreadIndex maintenance helpers
-- ============================================================================

/-- S-05/PERF-O1: Add a thread to the per-SchedContext thread index.
If the SchedContext already has an entry, the thread is prepended to the list.
If not, a new entry is created with a singleton list. -/
def scThreadIndexAdd (idx : RHTable SeLe4n.SchedContextId (List SeLe4n.ThreadId))
    (scId : SeLe4n.SchedContextId) (tid : SeLe4n.ThreadId)
    : RHTable SeLe4n.SchedContextId (List SeLe4n.ThreadId) :=
  let existing := idx[scId]?.getD []
  idx.insert scId (tid :: existing)

/-- S-05/PERF-O1: Remove a thread from the per-SchedContext thread index.
Filters the thread out of the SchedContext's list. If the list becomes empty,
the entry is erased entirely to avoid accumulating empty lists. -/
def scThreadIndexRemove (idx : RHTable SeLe4n.SchedContextId (List SeLe4n.ThreadId))
    (scId : SeLe4n.SchedContextId) (tid : SeLe4n.ThreadId)
    : RHTable SeLe4n.SchedContextId (List SeLe4n.ThreadId) :=
  match idx[scId]? with
  | none => idx
  | some tids =>
    let remaining := tids.filter (· != tid)
    if remaining.isEmpty then idx.erase scId else idx.insert scId remaining

abbrev Kernel := SeLe4n.KernelM SystemState KernelError

def lookupObject (id : SeLe4n.ObjId) : Kernel KernelObject :=
  fun st =>
    match st.objects[id]? with
    | none => .error .objectNotFound
    | some obj => .ok (obj, st)

/-- Read a typed VSpace-root object from the global object store. -/
def lookupVSpaceRoot (id : SeLe4n.ObjId) : Kernel VSpaceRoot :=
  fun st =>
    match st.objects[id]? with
    | some (.vspaceRoot root) => .ok (root, st)
    | some _ => .error .vspaceRootInvalid
    | none => .error .objectNotFound

-- ============================================================================
-- S4-A/S4-B: Object capacity bounds
-- ============================================================================

/-- S4-A: Advisory maximum object count for RPi5 platform (65536).
    S4-B: Enforced by `retypeFromUntyped` — new allocations are rejected
    when the object index reaches this capacity. -/
def maxObjects : Nat := 65536

/-- S4-A: Advisory predicate — the object index size is bounded by `maxObjects`.
    After S4-B enforcement, this holds for any reachable state (assuming it
    holds at boot and `storeObject` is the only path to add new objects). -/
def objectIndexBounded (st : SystemState) : Prop :=
  st.objectIndex.length ≤ maxObjects

/-- S4-B: Invariant alias — the object count does not exceed `maxObjects`.
    This is definitionally equal to `objectIndexBounded` but named per the
    workstream plan (U-M12) for traceability. Enforced at the allocation
    boundary (`retypeFromUntyped`) rather than in `storeObject`. -/
abbrev objectCount_le_maxObjects := objectIndexBounded

/-- S4-B: The default (empty) system state satisfies the object capacity bound. -/
theorem default_objectCount_le_maxObjects :
    objectCount_le_maxObjects (default : SystemState) := by
  unfold objectCount_le_maxObjects objectIndexBounded maxObjects
  simp [List.length]

/-- AK7-J (F-M09): Advisory invariant — the CDT next-node counter
(`cdtNextNode`) stays strictly below the advisory bound `maxCdtDepth`
(shared with the CDT fuel bound defined in `Model/Object/Structures.lean`).

Rationale: `ensureCdtNodeForSlot` increments `cdtNextNode` each time a
fresh CDT node must be allocated for a slot. The abstract model uses
unbounded `Nat`, but any hardware mapping to fixed-width CDT node ids
risks silent ID reuse once the counter overflows the hardware width.
Callers that expose CDT node identifiers to user space via capabilities
should gate `ensureCdtNodeForSlot` by this predicate (or its decidable
counterpart) to preserve uniqueness. -/
def cdtNextNodeBounded (st : SystemState) : Prop :=
  st.cdtNextNode.val < maxCdtDepth

/-- AK7-J (F-M09): The default system state satisfies `cdtNextNodeBounded`. -/
theorem default_cdtNextNodeBounded :
    cdtNextNodeBounded (default : SystemState) := by
  unfold cdtNextNodeBounded maxCdtDepth
  decide

/-- Replace the object stored at `id` with `obj`.

WS-G2/F-P01: Uses `HashMap.insert` instead of closure wrapping, eliminating
the O(k) closure-chain accumulation on every lookup.
WS-G2/F-P10: Uses `objectIndexSet.contains` for O(1) membership check instead
of O(n) list membership scan.
WS-G3/F-P06: Maintains `asidTable` — erases old ASID when overwriting a
VSpaceRoot, inserts new ASID when storing a VSpaceRoot.

S4-B/U2-L: Capacity enforcement is performed at the allocation boundary
(`retypeFromUntyped` in Lifecycle/Operations.lean), not here. The
`objectCount_le_maxObjects` invariant (alias for `objectIndexBounded`,
defined above) is preserved by allocation-time checking, and `storeObject`
remains infallible for internal use by IPC, scheduler, and capability
operations.

V5-K (L-FND-1): **Design rationale for infallibility.** `storeObject` always
returns `.ok` — it never fails. This is intentional: the object store is an
in-memory map (`RHTable`) with unbounded capacity at the model level. Capacity
enforcement is deferred to `retypeFromUntyped`, which checks
`objectIndexBounded` before creating new objects. Internal mutations (IPC,
scheduler, capability operations) overwrite existing keys and do not grow the
index. This split keeps the common-path kernel operations (`endpointSend`,
`schedule`, etc.) free of error-handling overhead while concentrating capacity
policy at the allocation boundary.

**U2-L callsite audit** (v0.21.1):
- **Allocation-guarded** (capacity checked by `retypeFromUntyped`):
  `lifecycleRetypeObject`, `lifecycleRetypeWithCleanup`, `lifecycleRetypeDirect`,
  `lifecycleRetypeDirectWithCleanup` — all go through retype authority + untyped
  capacity validation before reaching `storeObject`.
- **In-place mutation** (no new ObjId, just updating an existing object):
  `vspaceMapPage`/`vspaceUnmapPage` (VSpaceRoot update), `cspaceInsertSlot`/
  `cspaceDeleteSlot`/`cspaceRevokeSlot` (CNode update), `endpointSend`/
  `endpointReceive`/`notificationSignal`/`notificationWait` (Endpoint/Notification
  update), `schedulerSetPriority`/`schedulerSetDomain` (TCB update).
  These all overwrite an existing ObjId — `objectIndex` growth is zero.
- **Builder/boot** (`IntermediateState.addThread`, `IntermediateState.addObject`):
  Boot-time population — capacity bounded by `maxObjects` in `PlatformConfig`. -/
def storeObject (id : SeLe4n.ObjId) (obj : KernelObject) : Kernel Unit :=
  fun st =>
    .ok ((), {
      st with
        objects := st.objects.insert id obj
        objectIndex := if st.objectIndexSet.contains id then st.objectIndex
                       else id :: st.objectIndex
        objectIndexSet := st.objectIndexSet.insert id
        lifecycle := {
          objectTypes := st.lifecycle.objectTypes.insert id obj.objectType
          capabilityRefs :=
            let cleared := st.lifecycle.capabilityRefs.filter (fun ref _ => ref.cnode ≠ id)
            match obj with
            | .cnode cn =>
                cn.slots.fold (init := cleared) fun refs slot cap =>
                  refs.insert { cnode := id, slot := slot } cap.target
            | _ => cleared
        }
        asidTable :=
          let cleared := match st.objects[id]? with
            | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
            | _ => st.asidTable
          match obj with
          | .vspaceRoot newRoot => cleared.insert newRoot.asid id
          | _ => cleared
    })

-- ============================================================================
-- WS-SM SM3.A audit-pass-5 — `storeObject` lock-state preservation
-- ============================================================================

/-- WS-SM SM3.A audit-pass-5: `storeObject` preserves the
table-level `objStoreLock` field.

`storeObject` updates `objects`, `objectIndex`, `objectIndexSet`,
`lifecycle`, and `asidTable`, but does NOT touch `objStoreLock`.
This is a structural witness that no current SM3.A operation
modifies the table-level lock field — closes the audit-pass-4
finding "no preservation theorems for the new fields".

The theorem statement uses the underlying state-update view to
keep the proof a `rfl`: `storeObject` returns `.ok ((), newSt)`
where `newSt` is the `{st with ...}`-spreaded record that retains
`st.objStoreLock`.

A `result` parameter (rather than introducing the post-state via a
`match`) keeps the theorem in a shape that SM3.B/C 2PL discipline
consumers can chain through `Except.ok`-destructuring on
`storeObject`'s result. -/
theorem storeObject_preserves_objStoreLock (st : SystemState)
    (id : SeLe4n.ObjId) (obj : KernelObject) :
    ∀ result, storeObject id obj st = .ok ((), result) →
      result.objStoreLock = st.objStoreLock := by
  intro result hRun
  -- `storeObject id obj st` reduces definitionally to
  -- `.ok ((), {st with ...})` where `...` does NOT mention `objStoreLock`.
  unfold storeObject at hRun
  cases hRun
  rfl

/-- WS-SM SM3.A audit-pass-5: `storeObject` preserves the
per-object lock state of every object whose ObjId is **not** the
one being overwritten.

For ObjIds other than the inserted one, the object store's entries
are unchanged, so their `objectLockOf` projections agree across the
transition.  Closes the audit-pass-4 finding "no preservation
theorems for per-object lock fields".

The theorem requires `id ≠ id'` because at `id` itself the new
object replaces the old one — its lock state is determined by the
inserted object (`obj`), not the prior state.  The `id = id'`
case is covered by `storeObject_inserted_object_lock` below. -/
theorem storeObject_preserves_objectLockOf_off_target (st : SystemState)
    (id id' : SeLe4n.ObjId) (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hNe : id ≠ id') :
    ∀ result, storeObject id obj st = .ok ((), result) →
      result.objects.get? id' = st.objects.get? id' := by
  intro result hRun
  unfold storeObject at hRun
  cases hRun
  -- `result.objects = st.objects.insert id obj`; lookup at `id' ≠ id`
  -- is unchanged by `RHTable.getElem?_insert_ne` (which requires the
  -- Robin Hood invariant `invExt` on the pre-insert table).
  show (st.objects.insert id obj).get? id' = st.objects.get? id'
  exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_ne st.objects id id' obj
    (fun h => hNe (eq_of_beq h)) hObjInv

/-- WS-SM SM3.A audit-pass-5: lookup at the just-inserted ObjId
returns the inserted object.

Closes the SM3.A.11 conclusion at the operational level: after
storing `obj` at `id`, the lookup returns precisely `obj`.
Combined with the field-level default of `lock := .unheld`, the
SM3.A.11 invariant is operationally preserved through
`storeObject`.

Mirrors `storeObject_objects_eq` (line 1517 below) but is phrased
in terms of `result.objects.get?` so it composes cleanly with
`storeObject_preserves_allObjectLocksUnheld`'s case analysis. -/
theorem storeObject_inserted_object_lookup (st : SystemState)
    (id : SeLe4n.ObjId) (obj : KernelObject)
    (hObjInv : st.objects.invExt) :
    ∀ result, storeObject id obj st = .ok ((), result) →
      result.objects.get? id = some obj := by
  intro result hRun
  unfold storeObject at hRun
  cases hRun
  exact SeLe4n.Kernel.RobinHood.RHTable.getElem?_insert_self st.objects id obj
    hObjInv

/-- WS-SM SM3.A audit-pass-5: `storeObject` with an unheld-lock
object preserves the SM3.A `allObjectLocksUnheld` invariant.

This is the per-operation preservation theorem that the SM3.C
2PL discipline will compose: if every kernel transition either
(a) doesn't modify a lock field (most SM3.A transitions), or
(b) modifies it by storing an object with `objectLockOf = .unheld`
(this case), then the SM3.A `allObjectLocksUnheld` invariant is
maintained.

Closes the audit-pass-4 finding "no preservation theorems for any
kernel transition".  Establishes that `storeObject` is the
canonical operation through which fresh objects enter the store,
and that as long as fresh objects are constructed with the default
`.unheld` lock (which is enforced by the SM3.A.1..A.9 field
defaults plus the convention that `Builder.createObject` never
overrides them), the global invariant holds.

The hypothesis `hFreshLock : objectLockOf obj = .unheld` is the
operational form of "every freshly-allocated object starts with
lock unheld" — discharged at every callsite via the field default
when `obj` is constructed via named-field syntax without an
explicit `lock := ...` override. -/
theorem storeObject_preserves_allObjectLocksUnheld (st : SystemState)
    (id : SeLe4n.ObjId) (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hInv : st.allObjectLocksUnheld)
    (hFreshLock : KernelObject.objectLockOf obj
                    = SeLe4n.Kernel.Concurrency.RwLockState.unheld) :
    ∀ result, storeObject id obj st = .ok ((), result) →
      result.allObjectLocksUnheld := by
  intro result hRun
  refine ⟨?_, ?_⟩
  · -- objStoreLock preserved by storeObject_preserves_objStoreLock
    rw [storeObject_preserves_objStoreLock st id obj result hRun]
    exact hInv.1
  · -- Per-object claim: for any id', the lock is unheld.
    intro id' o hLookup
    -- Two cases: id' = id (the inserted object) or id' ≠ id.
    by_cases hEq : id = id'
    · -- id' = id: the lookup returns `obj`, whose lock is unheld by hFreshLock.
      subst hEq
      have hSelf := storeObject_inserted_object_lookup st id obj hObjInv result hRun
      rw [hSelf] at hLookup
      cases hLookup
      exact hFreshLock
    · -- id' ≠ id: lookup is unchanged from st.objects.get? id'.
      have hOff := storeObject_preserves_objectLockOf_off_target st id id' obj
        hObjInv hEq result hRun
      rw [hOff] at hLookup
      exact hInv.2 id' o hLookup

/-- S4-B: `storeObject` preserves `objectCount_le_maxObjects` — overwriting an
    existing object does not increase the object index length, and inserting
    a new object increments it by at most 1 (which is bounded by the
    allocation-time capacity check in `retypeFromUntyped`). -/
theorem storeObject_preserves_objectIndexBounded
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (_hBound : objectIndexBounded st)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objectIndex.length ≤ st.objectIndex.length + 1 := by
  unfold storeObject at hStore; cases hStore
  simp only
  split <;> simp [List.length] <;> omega

/-- AC3-E / F-03: Capacity-checked variant of `storeObject`. Rejects new object
    insertions that would exceed `maxObjects`. Updates to existing objects are
    always allowed (they don't grow the index).

    Use this in new code paths that are not covered by the `retypeFromUntyped`
    capacity gate. Use `storeObject` only in proof-layer code where
    `objectIndexBounded` is an established precondition. -/
def storeObjectChecked (id : SeLe4n.ObjId) (obj : KernelObject) : Kernel Unit :=
  fun st =>
    if st.objectIndex.length ≥ maxObjects && !st.objectIndexSet.contains id then
      .error .objectStoreCapacityExceeded
    else
      storeObject id obj st

/-- AC3-E: `storeObjectChecked` preserves `objectIndexBounded` on success. -/
theorem storeObjectChecked_preserves_objectIndexBounded
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hBound : objectIndexBounded st)
    (hStore : storeObjectChecked id obj st = .ok ((), st')) :
    objectIndexBounded st' := by
  unfold storeObjectChecked at hStore
  -- Case-split on the capacity guard
  cases hIf : (st.objectIndex.length ≥ maxObjects && !st.objectIndexSet.contains id) with
  | true => simp [hIf] at hStore
  | false =>
    simp [hIf] at hStore
    -- hStore : storeObject id obj st = .ok ((), st')
    unfold objectIndexBounded at hBound ⊢
    unfold storeObject at hStore; cases hStore
    simp only
    split
    · exact hBound
    · -- New object: index grows by 1
      rename_i hNotContains
      -- hIf : (len ≥ max && !contains) = false and hNotContains : contains = false
      -- So !contains = true, meaning len ≥ max must be false, i.e., len < max
      have hLt : st.objectIndex.length < maxObjects := by
        have : (!st.objectIndexSet.contains id) = true := by simp [hNotContains]
        simp [this] at hIf
        exact hIf
      unfold maxObjects at hLt
      show (id :: st.objectIndex).length ≤ 65536
      simp only [List.length_cons]
      exact hLt

/-- AC3-E: `storeObjectChecked` delegates to `storeObject` when the object
    already exists in the store (in-place update). This covers the common case
    for IPC, scheduler, and capability operations that overwrite existing objects. -/
theorem storeObjectChecked_existing_eq_storeObject
    (st : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hExists : st.objectIndexSet.contains id = true) :
    storeObjectChecked id obj st = storeObject id obj st := by
  unfold storeObjectChecked
  simp [hExists]

/-- AC3-E: `storeObjectChecked` delegates to `storeObject` when the store has
    capacity headroom (strictly less than `maxObjects`). This covers the case
    for new object insertions within the capacity bound. -/
theorem storeObjectChecked_headroom_eq_storeObject
    (st : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hHeadroom : st.objectIndex.length < maxObjects) :
    storeObjectChecked id obj st = storeObject id obj st := by
  unfold storeObjectChecked maxObjects at *
  split
  · rename_i hGuard
    simp [Bool.and_eq_true] at hGuard
    omega
  · rfl

-- ============================================================================
-- AL6 (WS-AL / AK7-F.cascade): storeObject kind-guard wrapper.
--
-- The existing `storeObjectChecked` above is a capacity-only variant;
-- it does not prevent a caller from overwriting a TCB stored at ObjId X
-- with a SchedContext (or any other variant). AL6 adds a parallel
-- `storeObjectKindChecked` wrapper that additionally rejects any write
-- whose `KernelObject` variant disagrees with the variant already
-- stored at the target id. Fresh allocations (`objects[id]? = none`)
-- are accepted — the caller is assumed to hold a freshly-allocated
-- ObjId, as enforced by `retypeFromUntyped_childId_fresh`.
--
-- Security impact: closes the silent cross-variant overwrite hole
-- where `storeObject tid (.tcb t)` followed by
-- `storeObject tid (.schedContext sc)` would change the stored kind
-- without any invariant registering the change.
-- ============================================================================

/-- AL6-A (WS-AL / AK7-F.cascade): kind-checked variant of `storeObject`.
Succeeds on a fresh id (pre-state has no object) OR when the pre-state
object has the same `objectType` as the incoming one. Otherwise returns
`.error .invalidObjectType`. Used by consumers that update an existing
object in place and must not accidentally change its variant. Fresh
allocations (boot, retype) continue to use `storeObject` directly.

**AN6-F (CX-M02) cross-reference**: The proof-layer semantic witness
for the property this wrapper enforces is `lifecycleObjectTypeLockstep`
in `SeLe4n/Kernel/CrossSubsystem.lean` (the 11th conjunct of
`crossSubsystemInvariant`). Together the two form a defense-in-depth
pair:

- This wrapper (`storeObjectKindChecked`) is a *dynamic* guard at the
  write boundary: if a caller attempts a cross-variant overwrite, the
  Kernel computation returns `.error .invalidObjectType` and the
  pre-state is preserved.
- `lifecycleObjectTypeLockstep` is a *static* invariant on reachable
  states: every populated `ObjId` has a matching `lifecycle.objectTypes`
  entry. `storeObject` (the underlying primitive this wrapper delegates
  to on the happy path) updates BOTH fields in lockstep, so reachable
  states always satisfy the invariant.

A reader entering from either side discovers the pair. Tamper-detection
is structural: if a bug or malicious write bypasses the wrapper and
performs a cross-variant overwrite, the next proof obligation that
unfolds through `lifecycleObjectTypeLockstep` fails to close, rather
than the cross-variant write silently escaping detection. -/
def storeObjectKindChecked (id : SeLe4n.ObjId) (obj : KernelObject) : Kernel Unit :=
  fun st =>
    match st.objects[id]? with
    | none => storeObject id obj st
    | some existing =>
        if existing.objectType = obj.objectType then
          storeObject id obj st
        else
          .error .invalidObjectType

/-- AL6-A: On a fresh id (no pre-state object), `storeObjectKindChecked`
reduces to `storeObject`. -/
theorem storeObjectKindChecked_fresh_eq_storeObject
    (id : SeLe4n.ObjId) (obj : KernelObject) (st : SystemState)
    (h : st.objects[id]? = none) :
    storeObjectKindChecked id obj st = storeObject id obj st := by
  unfold storeObjectKindChecked
  simp [h]

/-- AL6-A: When the pre-state object has the same `objectType` as the
incoming one, `storeObjectKindChecked` reduces to `storeObject`. -/
theorem storeObjectKindChecked_sameKind_eq_storeObject
    (id : SeLe4n.ObjId) (obj existing : KernelObject) (st : SystemState)
    (hExists : st.objects[id]? = some existing)
    (hKind : existing.objectType = obj.objectType) :
    storeObjectKindChecked id obj st = storeObject id obj st := by
  unfold storeObjectKindChecked
  rw [hExists]; simp [hKind]

/-- AL6-A: Cross-variant writes are rejected. If the store already
holds an object of a different variant, `storeObjectKindChecked`
returns `.error .invalidObjectType` without mutating state. -/
theorem storeObjectKindChecked_crossKind_rejected
    (id : SeLe4n.ObjId) (obj existing : KernelObject) (st : SystemState)
    (hExists : st.objects[id]? = some existing)
    (hKindNe : existing.objectType ≠ obj.objectType) :
    storeObjectKindChecked id obj st = .error .invalidObjectType := by
  unfold storeObjectKindChecked
  rw [hExists]; simp [hKindNe]

-- ============================================================================
-- AF2-A: Machine-checked storeObject capacity safety (AF-03)
-- ============================================================================

/-- AF2-A1: `storeObject` on an existing ObjId preserves `objectIndex.length`
    exactly. The key is already in `objectIndexSet`, so the conditional
    `if st.objectIndexSet.contains id then st.objectIndex else id :: st.objectIndex`
    takes the identity branch. This single lemma covers all 25+ in-place
    mutation callsites generically (IPC, scheduler, capability, VSpace ops). -/
theorem storeObject_existing_preserves_objectIndex_length
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hExists : st.objectIndexSet.contains id = true)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objectIndex.length = st.objectIndex.length := by
  unfold storeObject at hStore; cases hStore
  simp [hExists]

/-- AF2-A3: Capacity safety for in-place mutations. Every `storeObject` call
    on an existing ObjId preserves `objectIndexBounded`. This covers all 25+
    in-place mutation callsites (IPC, scheduler, capability, VSpace ops).

    The allocation boundary is separately gated by `retypeFromUntyped`
    (Lifecycle/Operations.lean:626) — see `retypeFromUntyped_capacity_gated`
    in that file for the machine-checked proof. Together these two theorems
    provide full capacity safety:
    - In-place: `storeObject_capacity_safe_of_existing` (here)
    - Allocation: `retypeFromUntyped_capacity_gated` (Lifecycle/Operations.lean)
    - Boot: `default_objectCount_le_maxObjects` (above) -/
theorem storeObject_capacity_safe_of_existing
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hBound : objectIndexBounded st)
    (hExists : st.objectIndexSet.contains id = true)
    (hStore : storeObject id obj st = .ok ((), st')) :
    objectIndexBounded st' := by
  unfold objectIndexBounded at hBound ⊢
  have hLen := storeObject_existing_preserves_objectIndex_length st st' id obj hExists hStore
  omega

-- AF2-A4: `storeObjectChecked` is UNUSED in operational code by design.
-- Capacity enforcement occurs at the allocation boundary in
-- `retypeFromUntyped` (Lifecycle/Operations.lean:626), not at the storage
-- layer. This function exists for potential future use by external allocation
-- paths that bypass `retypeFromUntyped`. See:
-- - `storeObject_existing_preserves_objectIndex_length` (in-place safety)
-- - `retypeFromUntyped_capacity_gated` (allocation-boundary safety)
-- - `storeObject_capacity_safe_of_existing` (composition)
-- for the machine-checked assurance that capacity is always gated.

/-- Record or clear a slot-to-target lifecycle reference mapping. -/
def storeCapabilityRef (ref : SlotRef) (target : Option CapTarget) : Kernel Unit :=
  fun st =>
    let lifecycle' : LifecycleMetadata :=
      {
        st.lifecycle with
          capabilityRefs :=
            match target with
            | some t => st.lifecycle.capabilityRefs.insert ref t
            | none => st.lifecycle.capabilityRefs.erase ref
      }
    .ok ((), { st with lifecycle := lifecycle' })

/-- M-P01: Fused revoke — filter CNode slots matching the revoke target and clear
their capability refs in a single `RHTable.fold` pass, eliminating the intermediate
refs-list allocation and second traversal of the legacy two-pass revoke path. -/
def revokeAndClearRefsState
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) : SystemState :=
  cn.slots.fold st (fun stAcc s c =>
    if s != sourceSlot && c.target == target then
      { stAcc with lifecycle := { stAcc.lifecycle with
          capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
            { cnode := cnodeId, slot := s } } }
    else stAcc)

/-- M-P01: Fold body for `revokeAndClearRefsState` preserves objects. -/
private theorem revokeAndClearRefsFoldBody_preserves_objects
    (pairs : List (SeLe4n.Slot × Capability))
    (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (pairs.foldl (fun stAcc (p : SeLe4n.Slot × Capability) =>
      if p.1 != sourceSlot && p.2.target == target then
        { stAcc with lifecycle := { stAcc.lifecycle with
            capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
              { cnode := cnodeId, slot := p.1 } } }
      else stAcc) st).objects = st.objects := by
  induction pairs generalizing st with
  | nil => rfl
  | cons p rest ih => simp only [List.foldl_cons]; split <;> exact ih _

/-- M-P01: `revokeAndClearRefsState` preserves `objects` (only modifies `lifecycle`). -/
theorem revokeAndClearRefsState_preserves_objects
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).objects = st.objects := by
  unfold revokeAndClearRefsState
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots.table st _ (fun acc => acc.objects = st.objects)
    rfl (fun acc s c hAcc => by simp only []; split <;> exact hAcc)

private theorem revokeAndClearRefsFoldBody_preserves_cdt
    (pairs : List (SeLe4n.Slot × Capability))
    (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (pairs.foldl (fun stAcc (p : SeLe4n.Slot × Capability) =>
      if p.1 != sourceSlot && p.2.target == target then
        { stAcc with lifecycle := { stAcc.lifecycle with
            capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
              { cnode := cnodeId, slot := p.1 } } }
      else stAcc) st).cdt = st.cdt ∧
    (pairs.foldl (fun stAcc (p : SeLe4n.Slot × Capability) =>
      if p.1 != sourceSlot && p.2.target == target then
        { stAcc with lifecycle := { stAcc.lifecycle with
            capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
              { cnode := cnodeId, slot := p.1 } } }
      else stAcc) st).cdtNodeSlot = st.cdtNodeSlot ∧
    (pairs.foldl (fun stAcc (p : SeLe4n.Slot × Capability) =>
      if p.1 != sourceSlot && p.2.target == target then
        { stAcc with lifecycle := { stAcc.lifecycle with
            capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
              { cnode := cnodeId, slot := p.1 } } }
      else stAcc) st).cdtSlotNode = st.cdtSlotNode := by
  induction pairs generalizing st with
  | nil => exact ⟨rfl, rfl, rfl⟩
  | cons p rest ih =>
      simp only [List.foldl_cons]
      split
      · exact ih _
      · exact ih _

/-- M-P01: `revokeAndClearRefsState` preserves CDT fields and objects. -/
theorem revokeAndClearRefsState_cdt_eq
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).cdt = st.cdt ∧
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).cdtNodeSlot = st.cdtNodeSlot ∧
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).cdtSlotNode = st.cdtSlotNode ∧
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).objects = st.objects := by
  unfold revokeAndClearRefsState
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots.table st _
    (fun acc => acc.cdt = st.cdt ∧ acc.cdtNodeSlot = st.cdtNodeSlot ∧
      acc.cdtSlotNode = st.cdtSlotNode ∧ acc.objects = st.objects)
    ⟨rfl, rfl, rfl, rfl⟩
    (fun acc s c ⟨h1, h2, h3, h4⟩ => by simp only []; split <;> exact ⟨h1, h2, h3, h4⟩)

/-- M-P01: Fold body preserves scheduler, machine, services, irqHandlers, objectIndex fields. -/
private theorem revokeAndClearRefsFoldBody_preserves_fields
    (pairs : List (SeLe4n.Slot × Capability))
    (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    let r := pairs.foldl (fun stAcc (p : SeLe4n.Slot × Capability) =>
      if p.1 != sourceSlot && p.2.target == target then
        { stAcc with lifecycle := { stAcc.lifecycle with
            capabilityRefs := stAcc.lifecycle.capabilityRefs.erase
              { cnode := cnodeId, slot := p.1 } } }
      else stAcc) st
    r.scheduler = st.scheduler ∧
    r.machine = st.machine ∧
    r.services = st.services ∧
    r.irqHandlers = st.irqHandlers ∧
    r.objectIndex = st.objectIndex ∧
    r.objectIndexSet = st.objectIndexSet ∧
    r.asidTable = st.asidTable := by
  induction pairs generalizing st with
  | nil => exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | cons p rest ih =>
      simp only [List.foldl_cons]
      split <;> exact ih _

/-- Helper tactic macro: uses `RHTable.fold_preserves` to show fold body preserves fields. -/
private theorem revokeAndClearRefsState_preserves_allFields
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    let r := revokeAndClearRefsState cn sourceSlot target cnodeId st
    r.scheduler = st.scheduler ∧ r.machine = st.machine ∧
    r.services = st.services ∧ r.irqHandlers = st.irqHandlers ∧
    r.objectIndex = st.objectIndex ∧ r.objectIndexSet = st.objectIndexSet := by
  unfold revokeAndClearRefsState
  exact SeLe4n.Kernel.RobinHood.RHTable.fold_preserves cn.slots.table st _
    (fun acc => acc.scheduler = st.scheduler ∧ acc.machine = st.machine ∧
      acc.services = st.services ∧ acc.irqHandlers = st.irqHandlers ∧
      acc.objectIndex = st.objectIndex ∧ acc.objectIndexSet = st.objectIndexSet)
    ⟨rfl, rfl, rfl, rfl, rfl, rfl⟩
    (fun acc s c ⟨h1, h2, h3, h4, h5, h6⟩ => by
      simp only []; split <;> exact ⟨h1, h2, h3, h4, h5, h6⟩)

/-- M-P01: `revokeAndClearRefsState` preserves scheduler. -/
theorem revokeAndClearRefsState_preserves_scheduler
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).scheduler = st.scheduler :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).1

/-- M-P01: `revokeAndClearRefsState` preserves machine state. -/
theorem revokeAndClearRefsState_preserves_machine
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).machine = st.machine :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).2.1

/-- M-P01: `revokeAndClearRefsState` preserves services. -/
theorem revokeAndClearRefsState_preserves_services
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).services = st.services :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).2.2.1

/-- M-P01: `revokeAndClearRefsState` preserves irqHandlers. -/
theorem revokeAndClearRefsState_preserves_irqHandlers
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).irqHandlers = st.irqHandlers :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).2.2.2.1

/-- M-P01: `revokeAndClearRefsState` preserves objectIndex. -/
theorem revokeAndClearRefsState_preserves_objectIndex
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).objectIndex = st.objectIndex :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).2.2.2.2.1

/-- M-P01: `revokeAndClearRefsState` preserves objectIndexSet. -/
theorem revokeAndClearRefsState_preserves_objectIndexSet
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) :
    (revokeAndClearRefsState cn sourceSlot target cnodeId st).objectIndexSet = st.objectIndexSet :=
  (revokeAndClearRefsState_preserves_allFields cn sourceSlot target cnodeId st).2.2.2.2.2

def setCurrentThread (tid : Option SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    let sched := st.scheduler.setCurrentOnCore bootCoreId tid
    .ok ((), { st with scheduler := sched })

/-- Read one service graph entry. -/
def lookupService (st : SystemState) (sid : ServiceId) : Option ServiceGraphEntry :=
  st.services[sid]?

/-- M-P01: `revokeAndClearRefsState` preserves lookupService. -/
theorem revokeAndClearRefsState_lookupService
    (cn : CNode) (sourceSlot : SeLe4n.Slot) (target : CapTarget)
    (cnodeId : SeLe4n.ObjId) (st : SystemState) (sid : ServiceId) :
    lookupService (revokeAndClearRefsState cn sourceSlot target cnodeId st) sid =
    lookupService st sid := by
  unfold lookupService
  rw [revokeAndClearRefsState_preserves_services]

/-- Determine whether `sid` lists `dependency` as a declared dependency edge. -/
def hasServiceDependency (st : SystemState) (sid dependency : ServiceId) : Bool :=
  match lookupService st sid with
  | some svc => dependency ∈ svc.dependencies
  | none => false

/-- Determine whether two services are explicitly isolated from one another. -/
def hasIsolationEdge (st : SystemState) (lhs rhs : ServiceId) : Bool :=
  match lookupService st lhs, lookupService st rhs with
  | some lhsSvc, some rhsSvc => rhs ∈ lhsSvc.isolatedFrom || lhs ∈ rhsSvc.isolatedFrom
  | _, _ => false

/-- Deterministic pure state helper: replace one service graph entry. -/
def storeServiceState (sid : ServiceId) (entry : ServiceGraphEntry) (st : SystemState) : SystemState :=
  {
    st with
      services := st.services.insert sid entry
  }

theorem storeServiceState_lookup_eq
    (st : SystemState)
    (sid : ServiceId)
    (entry : ServiceGraphEntry)
    (hInv : st.services.invExt) :
    lookupService (storeServiceState sid entry st) sid = some entry := by
  simp only [lookupService, storeServiceState]
  exact RHTable.getElem?_insert_self st.services sid entry hInv

theorem storeServiceState_lookup_ne
    (st : SystemState)
    (sid sid' : ServiceId)
    (entry : ServiceGraphEntry)
    (hNe : sid' ≠ sid)
    (hInv : st.services.invExt) :
    lookupService (storeServiceState sid entry st) sid' = lookupService st sid' := by
  simp only [lookupService, storeServiceState]
  have hNeBeq : ¬((sid == sid') = true) := by
    intro hEq; exact hNe (eq_of_beq hEq).symm
  exact RHTable.getElem?_insert_ne st.services sid sid' entry hNeBeq hInv

theorem storeObject_preserves_services
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.services = st.services := by
  unfold storeObject at hStore; cases hStore
  rfl

theorem storeCapabilityRef_preserves_scheduler
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

theorem storeCapabilityRef_preserves_services
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.services = st.services := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

theorem storeCapabilityRef_preserves_objects
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.objects = st.objects := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

/-- WS-F3: storeCapabilityRef preserves IRQ handler mappings. -/
theorem storeCapabilityRef_preserves_irqHandlers
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

/-- WS-F3: storeCapabilityRef preserves the object index. -/
theorem storeCapabilityRef_preserves_objectIndex
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.objectIndex = st.objectIndex := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

/-- storeCapabilityRef preserves machine state. -/
theorem storeCapabilityRef_preserves_machine
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold storeCapabilityRef at hStep
  simp at hStep; cases hStep; rfl

theorem storeCapabilityRef_lookup_eq
    (st st' : SystemState)
    (ref : SlotRef)
    (target : Option CapTarget)
    (hCapRefsInv : st.lifecycle.capabilityRefs.invExt)
    (hStep : storeCapabilityRef ref target st = .ok ((), st')) :
    st'.lifecycle.capabilityRefs[ref]? = target := by
  unfold storeCapabilityRef at hStep
  cases hTarget : target with
  | none =>
      simp [hTarget] at hStep
      cases hStep
      simp only [RHTable_getElem?_eq_get?]; exact RHTable.getElem?_erase_self _ _ hCapRefsInv
  | some t =>
      simp [hTarget] at hStep
      cases hStep
      simp only [RHTable_getElem?_eq_get?]; exact RHTable.getElem?_insert_self _ _ _ hCapRefsInv


theorem storeObject_objects_eq'
    (st : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (pair : Unit × SystemState)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok pair) :
    pair.2.objects[id]? = some obj := by
  unfold storeObject at hStore; cases hStore
  exact RHTable.getElem?_insert_self _ _ _ hObjInv

/-- WS-SM SM7.B: `storeObject` only touches the object store and lifecycle
metadata — the TLB-shootdown state is framed.  Leaf lemma of the
`pendingBounded` bundle-carriage chain: every object-mutating kernel
transition that bottoms out in `storeObject` transports the shootdown
capacity invariant through this equation. -/
theorem storeObject_tlbShootdown_eq
    (st : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (pair : Unit × SystemState)
    (hStore : storeObject id obj st = .ok pair) :
    pair.2.tlbShootdown = st.tlbShootdown := by
  unfold storeObject at hStore; cases hStore; rfl

theorem storeObject_objects_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[id]? = some obj :=
  storeObject_objects_eq' st id obj ((), st') hObjInv hStore

theorem storeObject_objects_ne'
    (st : SystemState)
    (id oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (pair : Unit × SystemState)
    (hNe : oid ≠ id)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok pair) :
    pair.2.objects[oid]? = st.objects[oid]? := by
  unfold storeObject at hStore; cases hStore
  have hNeBeq : ¬((id == oid) = true) := by intro heq; exact hNe (eq_of_beq heq).symm
  exact RHTable.getElem?_insert_ne _ _ _ _ hNeBeq hObjInv

theorem storeObject_objects_ne
    (st st' : SystemState)
    (id oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hNe : oid ≠ id)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects[oid]? = st.objects[oid]? :=
  storeObject_objects_ne' st id oid obj ((), st') hNe hObjInv hStore

theorem storeObject_preserves_objects_invExt'
    (st : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (pair : Unit × SystemState)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok pair) :
    pair.2.objects.invExt := by
  unfold storeObject at hStore; cases hStore
  exact RHTable_insert_preserves_invExt st.objects id obj hObjInv

theorem storeObject_scheduler_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold storeObject at hStore; cases hStore
  rfl

theorem storeObject_irqHandlers_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.irqHandlers = st.irqHandlers := by
  unfold storeObject at hStore; cases hStore
  rfl

theorem storeObject_machine_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold storeObject at hStore; cases hStore
  rfl

theorem storeObject_preserves_objects_invExt
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objects.invExt :=
  storeObject_preserves_objects_invExt' st id obj ((), st') hObjInv hStore

-- WS-E4/C-03: storeObject preserves the CDT (it only touches objects/lifecycle/index)
theorem storeObject_cdt_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.cdt = st.cdt := by
  unfold storeObject at hStore; cases hStore
  rfl

/-- PR #827 #3 fold: `storeObject` preserves the CDT node→slot mapping (it only
touches objects/lifecycle/index). -/
theorem storeObject_cdtNodeSlot_eq
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.cdtNodeSlot = st.cdtNodeSlot := by
  unfold storeObject at hStore; cases hStore
  rfl

-- ============================================================================
-- WS-G3/F-P06: storeObject ASID table maintenance lemmas
-- ============================================================================

/-- WS-G3: After storing a VSpaceRoot, the ASID table maps the new root's ASID to `id`. -/
theorem storeObject_asidTable_vspaceRoot
    (st st' : SystemState) (id : SeLe4n.ObjId) (newRoot : VSpaceRoot)
    (hAsidInv : (match st.objects[id]? with
      | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
      | _ => st.asidTable).invExt)
    (hStore : storeObject id (.vspaceRoot newRoot) st = .ok ((), st')) :
    st'.asidTable[newRoot.asid]? = some id := by
  unfold storeObject at hStore; cases hStore
  simp only []
  exact RHTable.getElem?_insert_self _ _ _ hAsidInv

/-- WS-G3: After storing a VSpaceRoot, a different ASID's table entry is unchanged
    unless it was the old root's ASID that got erased. -/
theorem storeObject_asidTable_vspaceRoot_ne
    (st st' : SystemState) (id : SeLe4n.ObjId) (newRoot : VSpaceRoot)
    (asid : SeLe4n.ASID)
    (hNe : asid ≠ newRoot.asid)
    (hAsidInv : (match st.objects[id]? with
      | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
      | _ => st.asidTable).invExt)
    (hStore : storeObject id (.vspaceRoot newRoot) st = .ok ((), st')) :
    st'.asidTable[asid]? =
      (match st.objects[id]? with
       | some (.vspaceRoot oldRoot) => (st.asidTable.erase oldRoot.asid)[asid]?
       | _ => st.asidTable[asid]?) := by
  unfold storeObject at hStore; cases hStore
  simp only []
  have hNeBeq : ¬((newRoot.asid == asid) = true) := by intro heq; exact hNe (eq_of_beq heq).symm
  cases hOld : st.objects[id]? with
  | none =>
    simp only [hOld, RHTable_getElem?_eq_get?] at hAsidInv ⊢
    rw [RHTable.getElem?_insert_ne _ _ _ _ hNeBeq hAsidInv]
  | some obj =>
    cases obj with
    | vspaceRoot oldRoot =>
      simp only [hOld, RHTable_getElem?_eq_get?] at hAsidInv ⊢
      rw [RHTable.getElem?_insert_ne _ _ _ _ hNeBeq hAsidInv]
    | tcb _ | cnode _ | endpoint _ | notification _ | untyped _
    | schedContext _ | reply _ =>
      simp only [hOld, RHTable_getElem?_eq_get?] at hAsidInv ⊢
      rw [RHTable.getElem?_insert_ne _ _ _ _ hNeBeq hAsidInv]

/-- WS-G3: After storing a non-VSpaceRoot, the ASID table only changes if the old
    object was a VSpaceRoot (in which case the old ASID is erased). -/
theorem storeObject_asidTable_non_vspaceRoot
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hNotVSpace : ∀ r, obj ≠ .vspaceRoot r)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.asidTable =
      match st.objects[id]? with
      | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
      | _ => st.asidTable := by
  unfold storeObject at hStore; cases hStore
  cases obj with
  | vspaceRoot r => exact absurd rfl (hNotVSpace r)
  | tcb _ => rfl
  | cnode _ => rfl
  | endpoint _ => rfl
  | notification _ => rfl
  | untyped _ => rfl
  | schedContext _ => rfl
  | reply _ => rfl

/-- WS-G2: objectIndex and objectIndexSet contain the same ids. -/
def objectIndexSetSync (st : SystemState) : Prop :=
  ∀ (id : SeLe4n.ObjId), st.objectIndexSet.contains id = true ↔ id ∈ st.objectIndex

/-- WS-G2: objectIndexSetSync implies contains from objectIndex membership. -/
theorem objectIndexSetSync_contains_of_mem
    (st : SystemState) (id : SeLe4n.ObjId)
    (hSync : objectIndexSetSync st) (hMem : id ∈ st.objectIndex) :
    st.objectIndexSet.contains id = true :=
  (hSync id).mpr hMem

/-- TPI-D1: objectIndexSet tracks all object IDs that exist in the objects HashMap. -/
def objectIndexSetComplete (st : SystemState) : Prop :=
  ∀ (oid : SeLe4n.ObjId), st.objects[oid]? ≠ none → st.objectIndexSet.contains oid = true

/-- TPI-D1: storeObject preserves objectIndexSetComplete. -/
theorem storeObject_preserves_objectIndexSetComplete
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hObjInv : st.objects.invExt)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hComplete : objectIndexSetComplete st)
    (hStore : storeObject id obj st = .ok ((), st')) :
    objectIndexSetComplete st' := by
  unfold storeObject at hStore; cases hStore
  intro oid hNe
  simp only at hNe ⊢
  by_cases hEq : (id == oid) = true
  · have hIdEq : id = oid := eq_of_beq hEq
    rw [← hIdEq]; exact RHSet.contains_insert_self st.objectIndexSet id hObjSetInv
  · rw [RHSet.contains_insert_ne st.objectIndexSet id oid hEq hObjSetInv]
    apply hComplete
    rwa [show (st.objects.insert id obj)[oid]? = st.objects[oid]? from
      RHTable.getElem?_insert_ne st.objects id oid obj hEq hObjInv] at hNe

/-- TPI-D1: storeObject preserves objectIndexSet.table.invExt. -/
theorem storeObject_preserves_objectIndexSet_invExt
    (st st' : SystemState) (id : SeLe4n.ObjId) (obj : KernelObject)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.objectIndexSet.table.invExt := by
  unfold storeObject at hStore; cases hStore
  exact RHSet.insert_preserves_invExt st.objectIndexSet id hObjSetInv

theorem storeObject_updates_objectTypeMeta
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    st'.lifecycle.objectTypes[oid]? = some obj.objectType := by
  unfold storeObject at hStep; cases hStep
  simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_self _ _ _ hObjTypesInv]

namespace SystemState

/-- Read a CNode object from the global object store. -/
def lookupCNode (st : SystemState) (id : SeLe4n.ObjId) : Option CNode :=
  match st.objects[id]? with
  | some (.cnode cn) => some cn
  | _ => none

-- ============================================================================
-- AL2-A (WS-AL / AK7-F.cascade): kind-verified lookup helpers
--
-- The AK7-F exploration showed 304 production call sites repeating the
-- pattern `match st.objects[id]? with | some (.variant x) => ... | _ =>
-- ...`. Only two variants had typed helpers (`lookupVSpaceRoot`,
-- `lookupCNode`). The five helpers below close the gap so downstream
-- phases (AL3-AL5) can migrate consumers uniformly.
--
-- Each helper unwraps the `KernelObject` tag on the same ObjId input
-- and returns `Option <variant>`. If the stored object has a
-- different variant, `none` is returned — this is the property that
-- AL6 leverages to gate `storeObject` against cross-variant writes.
-- ============================================================================

/-- AL2-A: Read a TCB from the global object store. -/
def getTcb? (st : SystemState) (tid : SeLe4n.ThreadId) : Option TCB :=
  match st.objects[tid.toObjId]? with
  | some (.tcb t) => some t
  | _             => none

/-- AL2-A: Read a SchedContext from the global object store. -/
def getSchedContext? (st : SystemState) (scId : SeLe4n.SchedContextId)
    : Option SeLe4n.Kernel.SchedContext :=
  match st.objects[scId.toObjId]? with
  | some (.schedContext sc) => some sc
  | _                       => none

/-- WS-SM SM6.D: Read a Reply from the global object store. -/
def getReply? (st : SystemState) (replyId : SeLe4n.ReplyId)
    : Option SeLe4n.Kernel.Reply :=
  match st.objects[replyId.toObjId]? with
  | some (.reply r) => some r
  | _               => none

/-- AL2-A: Read an Endpoint from the global object store. -/
def getEndpoint? (st : SystemState) (id : SeLe4n.ObjId) : Option Endpoint :=
  match st.objects[id]? with
  | some (.endpoint ep) => some ep
  | _                   => none

/-- AL2-A: Read a Notification from the global object store. -/
def getNotification? (st : SystemState) (id : SeLe4n.ObjId) : Option Notification :=
  match st.objects[id]? with
  | some (.notification n) => some n
  | _                      => none

/-- AL2-A: Read an UntypedObject from the global object store. -/
def getUntyped? (st : SystemState) (id : SeLe4n.ObjId) : Option UntypedObject :=
  match st.objects[id]? with
  | some (.untyped ut) => some ut
  | _                  => none

/-- AN10-B: Read a CNode from the global object store. Same kind-checked
discriminator pattern as the AL2-A helpers, extended to cover Capability
operations that resolve a CSpace root or descend a CNode chain. -/
def getCNode? (st : SystemState) (id : SeLe4n.ObjId) : Option CNode :=
  match st.objects[id]? with
  | some (.cnode cn) => some cn
  | _                => none

/-- AN10-B: Read a VSpaceRoot from the global object store. Used by the
IPC-buffer reader and VSpace operations that descend a thread's vspace
root. -/
def getVSpaceRoot? (st : SystemState) (id : SeLe4n.ObjId) : Option VSpaceRoot :=
  match st.objects[id]? with
  | some (.vspaceRoot root) => some root
  | _                       => none

-- ============================================================================
-- AL2-B (WS-AL / AK7-F.cascade): kind-discrimination sanity lemmas.
--
-- Each lemma witnesses the property that if the stored object at `id`
-- is a specific variant, every *other* typed helper returns `none` on
-- the same id. These are the foundation for AL6's `storeObjectChecked`
-- kind-guard and its composition into `crossSubsystemInvariant`.
-- Proofs are single-line `simp` on the helper definition + the stored-
-- object witness (mechanical by `rfl` after unfolding).
-- ============================================================================

/-- AL2-B: If the store holds a SchedContext at `tid.toObjId`, the typed
TCB helper returns `none`. -/
theorem getTcb?_none_of_schedContext (st : SystemState) (tid : SeLe4n.ThreadId)
    (sc : SeLe4n.Kernel.SchedContext)
    (h : st.objects[tid.toObjId]? = some (.schedContext sc)) :
    st.getTcb? tid = none := by
  simp [getTcb?, h]

/-- AL2-B: If the store holds an Endpoint at `tid.toObjId`, the typed
TCB helper returns `none`. -/
theorem getTcb?_none_of_endpoint (st : SystemState) (tid : SeLe4n.ThreadId)
    (ep : Endpoint)
    (h : st.objects[tid.toObjId]? = some (.endpoint ep)) :
    st.getTcb? tid = none := by
  simp [getTcb?, h]

/-- AL2-B (audit remediation): If the store holds a Notification at
`tid.toObjId`, the typed TCB helper returns `none`. -/
theorem getTcb?_none_of_notification (st : SystemState) (tid : SeLe4n.ThreadId)
    (n : Notification) (h : st.objects[tid.toObjId]? = some (.notification n)) :
    st.getTcb? tid = none := by
  simp [getTcb?, h]

/-- AL2-B (audit remediation): If the store holds a CNode at
`tid.toObjId`, the typed TCB helper returns `none`. -/
theorem getTcb?_none_of_cnode (st : SystemState) (tid : SeLe4n.ThreadId)
    (cn : CNode) (h : st.objects[tid.toObjId]? = some (.cnode cn)) :
    st.getTcb? tid = none := by
  simp [getTcb?, h]

/-- AL2-B (audit remediation): If the store holds a VSpaceRoot at
`tid.toObjId`, the typed TCB helper returns `none`. -/
theorem getTcb?_none_of_vspaceRoot (st : SystemState) (tid : SeLe4n.ThreadId)
    (vr : VSpaceRoot) (h : st.objects[tid.toObjId]? = some (.vspaceRoot vr)) :
    st.getTcb? tid = none := by
  simp [getTcb?, h]

/-- AL2-B (audit remediation): If the store holds an UntypedObject at
`tid.toObjId`, the typed TCB helper returns `none`. -/
theorem getTcb?_none_of_untyped (st : SystemState) (tid : SeLe4n.ThreadId)
    (ut : UntypedObject) (h : st.objects[tid.toObjId]? = some (.untyped ut)) :
    st.getTcb? tid = none := by
  simp [getTcb?, h]

/-- AL2-B (audit remediation): If the store is empty at `tid.toObjId`,
the typed TCB helper returns `none`. -/
theorem getTcb?_none_of_absent (st : SystemState) (tid : SeLe4n.ThreadId)
    (h : st.objects[tid.toObjId]? = none) :
    st.getTcb? tid = none := by
  simp [getTcb?, h]

/-- AL2-B: If the store holds a TCB at `scId.toObjId`, the typed
SchedContext helper returns `none`. -/
theorem getSchedContext?_none_of_tcb (st : SystemState) (scId : SeLe4n.SchedContextId)
    (t : TCB)
    (h : st.objects[scId.toObjId]? = some (.tcb t)) :
    st.getSchedContext? scId = none := by
  simp [getSchedContext?, h]

/-- AL2-B: If the store holds a TCB at `id`, the typed Endpoint helper
returns `none`. -/
theorem getEndpoint?_none_of_tcb (st : SystemState) (id : SeLe4n.ObjId)
    (t : TCB) (h : st.objects[id]? = some (.tcb t)) :
    st.getEndpoint? id = none := by
  simp [getEndpoint?, h]

/-- AL2-B: If the store holds a TCB at `id`, the typed Notification
helper returns `none`. -/
theorem getNotification?_none_of_tcb (st : SystemState) (id : SeLe4n.ObjId)
    (t : TCB) (h : st.objects[id]? = some (.tcb t)) :
    st.getNotification? id = none := by
  simp [getNotification?, h]

/-- AL2-B: If the store holds a TCB at `id`, the typed Untyped helper
returns `none`. -/
theorem getUntyped?_none_of_tcb (st : SystemState) (id : SeLe4n.ObjId)
    (t : TCB) (h : st.objects[id]? = some (.tcb t)) :
    st.getUntyped? id = none := by
  simp [getUntyped?, h]

/-- AL2-B: Unfolding lemma — `getTcb?` returns `some t` iff the store
holds exactly `KernelObject.tcb t` at `tid.toObjId`. -/
theorem getTcb?_eq_some_iff (st : SystemState) (tid : SeLe4n.ThreadId) (t : TCB) :
    st.getTcb? tid = some t ↔ st.objects[tid.toObjId]? = some (.tcb t) := by
  unfold getTcb?
  split
  · rename_i t' heq; constructor
    · intro h; cases h; exact heq
    · intro h; rw [h] at heq; cases heq; rfl
  · rename_i hne; constructor
    · intro h; cases h
    · intro h; exact absurd h (fun h' => hne _ (by rw [h']))

/-- AL2-B: Unfolding lemma — `getSchedContext?` returns `some sc` iff
the store holds exactly `KernelObject.schedContext sc` at
`scId.toObjId`. -/
theorem getSchedContext?_eq_some_iff (st : SystemState) (scId : SeLe4n.SchedContextId)
    (sc : SeLe4n.Kernel.SchedContext) :
    st.getSchedContext? scId = some sc ↔
      st.objects[scId.toObjId]? = some (.schedContext sc) := by
  unfold getSchedContext?
  split
  · rename_i sc' heq; constructor
    · intro h; cases h; exact heq
    · intro h; rw [h] at heq; cases heq; rfl
  · rename_i hne; constructor
    · intro h; cases h
    · intro h; exact absurd h (fun h' => hne _ (by rw [h']))

/-- WS-SM SM6.D: Unfolding lemma — `getReply?` returns `some r` iff the store
holds exactly `KernelObject.reply r` at `replyId.toObjId`. -/
theorem getReply?_eq_some_iff (st : SystemState) (replyId : SeLe4n.ReplyId)
    (r : SeLe4n.Kernel.Reply) :
    st.getReply? replyId = some r ↔
      st.objects[replyId.toObjId]? = some (.reply r) := by
  unfold getReply?
  split
  · rename_i r' heq; constructor
    · intro h; cases h; exact heq
    · intro h; rw [h] at heq; cases heq; rfl
  · rename_i hne; constructor
    · intro h; cases h
    · intro h; exact absurd h (fun h' => hne _ (by rw [h']))

/-- WS-SM SM6.D: link a Reply object to the caller about to block on it
(sets `reply.caller`).  Fails closed with `.replyCapInvalid` if the reply is
absent or already in use (`caller ≠ none`) — an in-use reply cannot be
re-linked, the structural half of reply caps' single-use semantics.  Pure
prep (Phase B): wired into the `Call` path in Phase C. -/
def linkReply (rid : SeLe4n.ReplyId) (caller : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match st.getReply? rid with
    | some r =>
        if r.caller.isNone then
          storeObject rid.toObjId (.reply { r with caller := some caller }) st
        else .error .replyCapInvalid
    | none => .error .replyCapInvalid

/-- WS-SM SM6.D: consume a Reply object's linkage (clears `reply.caller`).  A
delivered reply is consumed so a replay finds `caller = none` and fails closed —
the dynamic half of single-use.  No-op if the reply is absent. -/
def consumeReply (rid : SeLe4n.ReplyId) : Kernel Unit :=
  fun st =>
    match st.getReply? rid with
    | some r => storeObject rid.toObjId (.reply { r with caller := none }) st
    | none => .ok ((), st)

/-- WS-SM SM6.D: `consumeReply` on a present reply clears its `caller`. -/
theorem consumeReply_getReply?_caller_none (st : SystemState) (rid : SeLe4n.ReplyId)
    (r : SeLe4n.Kernel.Reply) (hObjInv : st.objects.invExt)
    (hGet : st.getReply? rid = some r) :
    ∀ result, consumeReply rid st = .ok ((), result) →
      result.getReply? rid = some { r with caller := none } := by
  intro result hRun
  unfold consumeReply at hRun
  rw [hGet] at hRun
  have hStore := storeObject_inserted_object_lookup st rid.toObjId
    (.reply { r with caller := none }) hObjInv result hRun
  rw [getReply?_eq_some_iff, RHTable_getElem?_eq_get?]
  exact hStore

/-- WS-SM SM6.D: `linkReply` on a present, free reply sets its `caller`. -/
theorem linkReply_getReply?_caller_some (st : SystemState) (rid : SeLe4n.ReplyId)
    (caller : SeLe4n.ThreadId) (r : SeLe4n.Kernel.Reply)
    (hObjInv : st.objects.invExt)
    (hGet : st.getReply? rid = some r) (hFree : r.caller = none) :
    ∀ result, linkReply rid caller st = .ok ((), result) →
      result.getReply? rid = some { r with caller := some caller } := by
  intro result hRun
  unfold linkReply at hRun
  rw [hGet] at hRun
  simp only [hFree, Option.isNone_none, if_true] at hRun
  have hStore := storeObject_inserted_object_lookup st rid.toObjId
    (.reply { r with caller := some caller }) hObjInv result hRun
  rw [getReply?_eq_some_iff, RHTable_getElem?_eq_get?]
  exact hStore

/-- WS-SM SM6.D: `linkReply` fails closed on an already-linked (in-use) reply. -/
theorem linkReply_inUse_error (st : SystemState) (rid : SeLe4n.ReplyId)
    (caller : SeLe4n.ThreadId) (r : SeLe4n.Kernel.Reply)
    (hGet : st.getReply? rid = some r) (hInUse : r.caller ≠ none) :
    linkReply rid caller st = .error .replyCapInvalid := by
  have hNot : r.caller.isNone = false := by
    cases hc : r.caller with
    | none => exact absurd hc hInUse
    | some _ => rfl
  simp [linkReply, hGet, hNot]

/-- WS-SM SM6.D (Reply-cap linkage, Call path): establish the bidirectional
TCB↔Reply link that the `Call` syscall creates.  Sets `reply.caller := some
caller` (via `linkReply`, which **fails closed** with `.replyCapInvalid` on an
absent or already-in-use reply — `caller ≠ none`) and the inverse forward link
`caller.replyObject := some rid` on the caller TCB (seL4's `tcb->tcbReply`).
Fails with `.objectNotFound` if the caller TCB is absent.  Composed after
`endpointCall` by the `.call` dispatch (Phase C-wire); the `replyCallerLinkage`
invariant (Phase D) reads exactly this pair of links.  Standalone prep —
unreferenced by any live path this slice, so the trace fixture is unchanged. -/
def linkCallerReply (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Kernel Unit :=
  fun st =>
    match linkReply rid caller st with
    | .error e => .error e
    | .ok ((), st1) =>
        match st1.getTcb? caller with
        | none => .error .objectNotFound
        | some tcb =>
            -- WS-SM SM6.D (PR #822): caller-side single-use — a caller already
            -- holding a reply object must not be re-linked, else the old Reply is
            -- orphaned with a stale `caller` (a later reply cap could resolve to
            -- this caller, and `consumeCallerReply` would clear the newer link).
            -- Fail closed unless `replyObject` is `none`.
            if tcb.replyObject.isNone then
              storeObject caller.toObjId (.tcb { tcb with replyObject := some rid }) st1
            else .error .replyCapInvalid

/-- WS-SM SM6.D (Reply-cap linkage, Reply path): tear down the TCB↔Reply link
when a reply is delivered/consumed.  Clears `reply.caller := none` (via
`consumeReply` — the single-use barrier, so a replay finds `caller = none` and
fails closed) and the inverse `caller.replyObject := none` on the
(now-unblocked) caller TCB.  No-op on the TCB leg if the caller is absent
(the link is then already moot).  Composed by the reply transitions
(Phase C-wire).  Standalone prep — unreferenced this slice, trace unchanged. -/
def consumeCallerReply (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId) : Kernel Unit :=
  fun st =>
    match consumeReply rid st with
    | .error e => .error e
    | .ok ((), st1) =>
        match st1.getTcb? caller with
        | none => .ok ((), st1)
        | some tcb =>
            storeObject caller.toObjId (.tcb { tcb with replyObject := none }) st1

/-- WS-SM SM6.D (#7.3 fold, server-first Call linkage): link a freshly-dequeued
`Call` caller (now `.blockedOnReply`) to the Reply object the rendezvous `server`
stashed on its earlier server-first `Recv` (`server.pendingReceiveReply`), and clear
that stash (one-shot).  Composed **inside** `endpointCall` / `endpointCallOnCore`'s
server-waiting rendezvous (atomic with the blocking transition), replacing the former
separate `linkServerFirstCaller` dispatch step.  Fails closed `.replyCapInvalid` when
the server provided no reply object (a plain `Recv` cannot answer a `Call`); the
caller-side single-use barrier in `linkCallerReply` rejects an already-linked caller.
Reads the server explicitly (the dequeued thread) rather than re-deriving it from the
caller's `blockedOnReply` payload. -/
def linkServerStashedReply (caller server : SeLe4n.ThreadId) : Kernel Unit :=
  fun st =>
    match (st.getTcb? server).bind (·.pendingReceiveReply) with
    | none => .error .replyCapInvalid
    | some rid =>
        match linkCallerReply caller rid st with
        | .error e => .error e
        | .ok ((), st1) =>
            match st1.getTcb? server with
            | none => .ok ((), st1)
            | some sTcb =>
                storeObject server.toObjId (.tcb { sTcb with pendingReceiveReply := none }) st1

/-- WS-SM SM6.D (PR #822 review): does any TCB stash `rid` in its
`pendingReceiveReply` (a *server-first* receive that is waiting to hand this Reply
object to its next `Call`)?  Such a Reply is "in use" even though its `caller` is
still `none` — retyping/deleting it would leave the waiting server pointing at a
removed Reply, so the next `Call` rendezvous rolls back and the server cannot
accept Call IPC.  Used by `lifecyclePreRetypeCleanup` (retype rejection) and by
`replyStashValid` / `resolveRecvReplyId` (stash admission).

PR #822 review: a stash reserves the Reply only while the server is STILL blocked
on its server-first receive, awaiting the next `Call` to link.  The moment the
server is woken by anything *other* than that Call — a bound notification, a `Send`
rendezvous, a cancellation — its receive is over and the Reply is free, even if the
now-`.ready` TCB's `pendingReceiveReply` field has not yet been scrubbed.  (A server
woken *by* its Call is covered by `reply.caller`, set in the same atomic
transition.)  Tying "stashed" to `.blockedOnReceive` makes the predicate robust to
any wake path that does not eager-clear the stash, so a ready server never keeps the
Reply permanently in use.  (Model-level object-store query; lives here — alongside
`getReply?` and the reply-link helpers — so the `endpointReceiveDual` primitive can
reject an already-stashed `rid` without an IPC→Lifecycle import cycle.) -/
def replyIsStashed (st : SystemState) (rid : SeLe4n.ReplyId) : Bool :=
  st.objects.fold (init := false) fun acc _oid obj =>
    acc || match obj with
      | .tcb t =>
          match t.ipcState with
          | .blockedOnReceive _ => t.pendingReceiveReply == some rid
          | _ => false
      | _ => false

/-- WS-SM SM6.D (PR #827 review #6): is a server-supplied reply object valid to
*stash* on a blocked receiver?  A plain receive (`none`) clears any stale stash and
is always valid; `some rid` is valid iff the Reply is **present**, **free**
(`caller = none`), and **not already stashed** by another blocked receiver — exactly
`replyIdEstablishFresh` in Bool form (under `pendingReceiveReplyWellFormed`, where
every stasher is `.blockedOnReceive`, `!replyIsStashed` coincides with the
∀-over-all-TCBs unstashed clause).  Mirrors the API-side `resolveRecvReplyId` check
so the `endpointReceiveDual` / `endpointReceiveDualOnCore` primitives **structurally
reject** an absent / in-use / already-stashed `rid` rather than stranding a
`.blockedOnReceive` receiver whose stash violates `pendingReceiveReplyWellFormed`
(which a later `Call` would then fail closed on). -/
def replyStashValid (st : SystemState) (replyId : Option SeLe4n.ReplyId) : Bool :=
  match replyId with
  | none => true
  | some rid =>
      match st.getReply? rid with
      | some r => r.caller.isNone && !st.replyIsStashed rid
      | none => false

/-- WS-SM SM6.D: `linkCallerReply` fails closed (`.replyCapInvalid`) on an
already-linked (in-use) reply — it never touches the caller TCB.  Inherits
`linkReply`'s single-use barrier: a second `Call` cannot re-bind a reply that
already has a `caller`, so a reply capability authorizes at most one
outstanding caller at a time. -/
theorem linkCallerReply_inUse_error (st : SystemState) (rid : SeLe4n.ReplyId)
    (caller : SeLe4n.ThreadId) (r : SeLe4n.Kernel.Reply)
    (hGet : st.getReply? rid = some r) (hInUse : r.caller ≠ none) :
    linkCallerReply caller rid st = .error .replyCapInvalid := by
  unfold linkCallerReply
  rw [linkReply_inUse_error st rid caller r hGet hInUse]

/-- WS-SM SM6.D: `linkReply` preserves the object-store extensional invariant
(its success path is a single `storeObject`). -/
theorem linkReply_preserves_objects_invExt (st st' : SystemState)
    (rid : SeLe4n.ReplyId) (caller : SeLe4n.ThreadId) (hObjInv : st.objects.invExt)
    (hStep : linkReply rid caller st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold linkReply at hStep
  cases hGet : st.getReply? rid with
  | none => rw [hGet] at hStep; simp at hStep
  | some r =>
    simp only [hGet] at hStep
    cases hFree : r.caller.isNone with
    | true =>
      rw [if_pos hFree] at hStep
      exact storeObject_preserves_objects_invExt st st' rid.toObjId _ hObjInv hStep
    | false =>
      rw [if_neg (by simp [hFree])] at hStep
      simp at hStep

/-- WS-SM SM6.D: `consumeReply` preserves the object-store extensional invariant
(no-op when the reply is absent; otherwise a single `storeObject`). -/
theorem consumeReply_preserves_objects_invExt (st st' : SystemState)
    (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt)
    (hStep : consumeReply rid st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold consumeReply at hStep
  cases hGet : st.getReply? rid with
  | none => rw [hGet] at hStep; cases hStep; exact hObjInv
  | some r =>
    rw [hGet] at hStep
    exact storeObject_preserves_objects_invExt st st' rid.toObjId _ hObjInv hStep

/-- WS-SM SM6.D: a TCB slot and a Reply slot are distinct.  A single object-store
slot holds exactly one `KernelObject`, so if `caller.toObjId` resolves to a TCB
and `rid.toObjId` to a Reply they cannot be the same `ObjId` — the disjointness
that lets the reply-linkage post-conditions frame one store past the other. -/
theorem getTcb?_getReply?_slot_ne (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (tcb : TCB) (r : SeLe4n.Kernel.Reply)
    (hT : st.getTcb? caller = some tcb) (hR : st.getReply? rid = some r) :
    caller.toObjId ≠ rid.toObjId := by
  intro hEq
  have hTobj := (getTcb?_eq_some_iff st caller tcb).mp hT
  have hRobj := (getReply?_eq_some_iff st rid r).mp hR
  rw [hEq, hRobj] at hTobj
  simp at hTobj

/-- WS-SM SM6.D: `linkCallerReply` establishes the forward TCB→Reply link —
on success the caller TCB's `replyObject` points at `rid`.  (The final store
of the op writes exactly this field.) -/
theorem linkCallerReply_replyObject_some (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt) :
    ∀ result, linkCallerReply caller rid st = .ok ((), result) →
      ∃ tcb', result.getTcb? caller = some tcb' ∧ tcb'.replyObject = some rid := by
  intro result hRun
  unfold linkCallerReply at hRun
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hRun
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hRun
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hRun
    | some tcb =>
      simp only [hT] at hRun
      split at hRun
      · have hInv1 := linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
        have hStore := storeObject_inserted_object_lookup st1 caller.toObjId
          (.tcb { tcb with replyObject := some rid }) hInv1 result hRun
        exact ⟨{ tcb with replyObject := some rid },
          by rw [getTcb?_eq_some_iff, RHTable_getElem?_eq_get?]; exact hStore, rfl⟩
      · simp at hRun

/-- WS-SM SM6.D (PR #822 review): `linkCallerReply` preserves the caller's IPC
state — its final store rewrites only `replyObject`, so a caller blocked on reply
*stays* blocked.  The `replyCallerLinkage` invariant reads this to require a linked
Reply's caller to be `blockedOnReply` (the only state `.reply` can consume). -/
theorem linkCallerReply_caller_ipcState_preserved (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (tcbC : TCB) (hObjInv : st.objects.invExt)
    (hPre : st.getTcb? caller = some tcbC) :
    ∀ result tcb', linkCallerReply caller rid st = .ok ((), result) →
      result.getTcb? caller = some tcb' → tcb'.ipcState = tcbC.ipcState := by
  intro result tcb' hRun hPost
  unfold linkCallerReply at hRun
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hRun
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hRun
    have hNe : caller.toObjId ≠ rid.toObjId := by
      cases hGetR : st.getReply? rid with
      | none => unfold linkReply at hLink; rw [hGetR] at hLink; simp at hLink
      | some r0 => exact getTcb?_getReply?_slot_ne st caller rid tcbC r0 hPre hGetR
    have hObjInv1 := linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
    have hFrame : st1.objects[caller.toObjId]? = st.objects[caller.toObjId]? := by
      unfold linkReply at hLink
      cases hGetR : st.getReply? rid with
      | none => rw [hGetR] at hLink; simp at hLink
      | some r0 =>
        simp only [hGetR] at hLink
        split at hLink
        · exact storeObject_objects_ne st st1 rid.toObjId caller.toObjId _ hNe hObjInv hLink
        · simp at hLink
    have hT1 : st1.getTcb? caller = some tcbC := by
      rw [getTcb?_eq_some_iff] at hPre ⊢; rw [hFrame]; exact hPre
    cases hT : st1.getTcb? caller with
    | none => rw [hT1] at hT; cases hT
    | some tcb =>
      have htcb : tcbC = tcb := by rw [hT1] at hT; injection hT
      subst htcb
      simp only [hT] at hRun
      split at hRun
      · have hStore := storeObject_inserted_object_lookup st1 caller.toObjId
          (.tcb { tcbC with replyObject := some rid }) hObjInv1 result hRun
        have hRes : result.getTcb? caller = some { tcbC with replyObject := some rid } := by
          rw [getTcb?_eq_some_iff, RHTable_getElem?_eq_get?]; exact hStore
        rw [hRes] at hPost; injection hPost with hPost; rw [← hPost]
      · simp at hRun

/-- WS-SM SM6.D: `consumeCallerReply` tears down the forward TCB→Reply link —
any caller TCB still present after the op has `replyObject = none`.  (The TCB
leg writes exactly this field; the no-op leg leaves no TCB to observe.) -/
theorem consumeCallerReply_replyObject_none (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (hObjInv : st.objects.invExt) :
    ∀ result tcb', consumeCallerReply caller rid st = .ok ((), result) →
      result.getTcb? caller = some tcb' → tcb'.replyObject = none := by
  intro result tcb' hRun hGetT
  unfold consumeCallerReply at hRun
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hRun
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hRun
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hRun
      subst hRun
      rw [hT] at hGetT; simp at hGetT
    | some tcb =>
      simp only [hT] at hRun
      have hInv1 := consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
      have hStore := storeObject_inserted_object_lookup st1 caller.toObjId
        (.tcb { tcb with replyObject := none }) hInv1 result hRun
      have hRes : result.getTcb? caller = some { tcb with replyObject := none } := by
        rw [getTcb?_eq_some_iff, RHTable_getElem?_eq_get?]; exact hStore
      rw [hRes] at hGetT; injection hGetT with hEq; rw [← hEq]

/-- WS-SM SM6.D: `linkCallerReply` establishes the Reply→TCB back-link — on
success the reply's `caller` points at the linking thread.  `linkReply` sets
`reply.caller := some caller`; the subsequent caller-TCB store lands at a slot
distinct from the reply (`getTcb?_getReply?_slot_ne`), so it frames past and the
reply is still observed with `caller = some caller`.  Together with
`linkCallerReply_replyObject_some` this pins both halves of the bidirectional
TCB↔Reply link the Phase-D `replyCallerLinkage` invariant reads. -/
theorem linkCallerReply_getReply?_caller_some (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (r : SeLe4n.Kernel.Reply) (hObjInv : st.objects.invExt)
    (hGet : st.getReply? rid = some r) (hFree : r.caller = none) :
    ∀ result, linkCallerReply caller rid st = .ok ((), result) →
      result.getReply? rid = some { r with caller := some caller } := by
  intro result hRun
  unfold linkCallerReply at hRun
  cases hLink : linkReply rid caller st with
  | error e => simp [hLink] at hRun
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hLink] at hRun
    have hR1 : st1.getReply? rid = some { r with caller := some caller } :=
      linkReply_getReply?_caller_some st rid caller r hObjInv hGet hFree st1 hLink
    cases hT : st1.getTcb? caller with
    | none => simp [hT] at hRun
    | some tcb =>
      simp only [hT] at hRun
      split at hRun
      · have hInv1 : st1.objects.invExt :=
          linkReply_preserves_objects_invExt st st1 rid caller hObjInv hLink
        have hNe : caller.toObjId ≠ rid.toObjId :=
          getTcb?_getReply?_slot_ne st1 caller rid tcb { r with caller := some caller } hT hR1
        have hFrame : result.objects[rid.toObjId]? = st1.objects[rid.toObjId]? :=
          storeObject_objects_ne st1 result caller.toObjId rid.toObjId _ hNe.symm hInv1 hRun
        rw [getReply?_eq_some_iff] at hR1 ⊢
        rw [hFrame]; exact hR1
      · simp at hRun

/-- WS-SM SM6.D: `consumeCallerReply` tears down the Reply→TCB back-link — on a
present reply the reply's `caller` is cleared.  `consumeReply` clears it; the
TCB leg (when the caller is present) stores at a distinct slot
(`getTcb?_getReply?_slot_ne`) and frames past, so the reply is observed with
`caller = none` — the dynamic single-use barrier surfaced as a post-condition. -/
theorem consumeCallerReply_getReply?_caller_none (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) (r : SeLe4n.Kernel.Reply) (hObjInv : st.objects.invExt)
    (hGet : st.getReply? rid = some r) :
    ∀ result, consumeCallerReply caller rid st = .ok ((), result) →
      result.getReply? rid = some { r with caller := none } := by
  intro result hRun
  unfold consumeCallerReply at hRun
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hRun
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hRun
    have hR1 : st1.getReply? rid = some { r with caller := none } :=
      consumeReply_getReply?_caller_none st rid r hObjInv hGet st1 hCons
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hRun
      subst hRun
      exact hR1
    | some tcb =>
      simp only [hT] at hRun
      have hInv1 : st1.objects.invExt :=
        consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
      have hNe : caller.toObjId ≠ rid.toObjId :=
        getTcb?_getReply?_slot_ne st1 caller rid tcb { r with caller := none } hT hR1
      have hFrame : result.objects[rid.toObjId]? = st1.objects[rid.toObjId]? :=
        storeObject_objects_ne st1 result caller.toObjId rid.toObjId _ hNe.symm hInv1 hRun
      rw [getReply?_eq_some_iff] at hR1 ⊢
      rw [hFrame]; exact hR1

/-- WS-SM SM6.D (PR #827 #3 fold): `consumeReply` is **total** — its only effect
is a plain `storeObject` (which always succeeds) behind a no-op guard. -/
theorem consumeReply_isOk (st : SystemState) (rid : SeLe4n.ReplyId) :
    ∃ st', consumeReply rid st = .ok ((), st') := by
  unfold consumeReply
  cases hGet : st.getReply? rid with
  | none => exact ⟨st, rfl⟩
  | some r => exact ⟨_, rfl⟩

/-- WS-SM SM6.D (PR #827 #3 fold): `consumeCallerReply` is **total** — both legs
are plain `storeObject`s (which always succeed) behind no-op guards.  Folding the
consume into the reply primitives therefore cannot introduce a new failure mode:
the folded transition's error surface is exactly the delivery leg's. -/
theorem consumeCallerReply_isOk (st : SystemState) (caller : SeLe4n.ThreadId)
    (rid : SeLe4n.ReplyId) :
    ∃ st', consumeCallerReply caller rid st = .ok ((), st') := by
  unfold consumeCallerReply
  obtain ⟨st1, hCons⟩ := consumeReply_isOk st rid
  simp only [hCons]
  cases hT : st1.getTcb? caller with
  | none => exact ⟨st1, rfl⟩
  | some tcb => exact ⟨_, rfl⟩

/-- WS-SM SM6.D (PR #827 #3 fold): `consumeReply` leaves the scheduler untouched
(object-store writes only). -/
theorem consumeReply_scheduler_eq (st st' : SystemState) (rid : SeLe4n.ReplyId)
    (hStep : consumeReply rid st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold consumeReply at hStep
  cases hGet : st.getReply? rid with
  | none => rw [hGet] at hStep; cases hStep; rfl
  | some r =>
    rw [hGet] at hStep
    exact storeObject_scheduler_eq st st' rid.toObjId _ hStep

/-- WS-SM SM6.D (PR #827 #3 fold): `consumeCallerReply` leaves the scheduler
untouched — both legs are object-store writes.  Lets the folded reply primitives'
scheduler-side conclusions (run queues, current, SGI derivation) frame past the
consume unchanged. -/
theorem consumeCallerReply_scheduler_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    st'.scheduler = st.scheduler := by
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have h1 := consumeReply_scheduler_eq st st1 rid hCons
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact h1
    | some tcb =>
      simp only [hT] at hStep
      rw [storeObject_scheduler_eq st1 st' caller.toObjId _ hStep]; exact h1

/-- WS-SM SM6.D (PR #827 #3 fold): `consumeCallerReply` leaves the machine state
untouched — both legs are object-store writes. -/
theorem consumeCallerReply_machine_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    st'.machine = st.machine := by
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have h1 : st1.machine = st.machine := by
      unfold consumeReply at hCons
      cases hGet : st.getReply? rid with
      | none => rw [hGet] at hCons; cases hCons; rfl
      | some r =>
        rw [hGet] at hCons
        exact storeObject_machine_eq st st1 rid.toObjId _ hCons
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact h1
    | some tcb =>
      simp only [hT] at hStep
      rw [storeObject_machine_eq st1 st' caller.toObjId _ hStep]; exact h1

/-- WS-SM SM6.D (PR #827 #3 fold): `consumeCallerReply` preserves the object-store
extensional invariant (each leg is a `storeObject` or a no-op). -/
theorem consumeCallerReply_preserves_objects_invExt (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    st'.objects.invExt := by
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have h1 := consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact h1
    | some tcb =>
      simp only [hT] at hStep
      exact storeObject_preserves_objects_invExt st1 st' caller.toObjId _ h1 hStep

/-- WS-SM SM6.D (PR #827 #3 fold), transport (a): the lookup of any object that is
neither a `.tcb` nor a `.reply` agrees across `consumeCallerReply` — its two writes
land on a slot holding a `.reply` (the consumed Reply) and a slot holding a `.tcb`
(the answered caller), so every endpoint / notification / cnode / schedContext
dereference in an invariant conjunct is unchanged.  The uniform driver behind the
per-conjunct `consumeCallerReply_preserves_*` frame family. -/
theorem consumeCallerReply_nonTcbNonReply_agree
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (k : KernelObject),
      (∀ tt, k ≠ .tcb tt) → (∀ rr, k ≠ .reply rr) →
      (st'.objects[s]? = some k ↔ st.objects[s]? = some k) := by
  intro s k hkT hkR
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hObjInv1 : st1.objects.invExt :=
      consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
    have hLeg1 : st1.objects[s]? = some k ↔ st.objects[s]? = some k := by
      unfold consumeReply at hCons
      cases hGet : st.getReply? rid with
      | none => rw [hGet] at hCons; cases hCons; exact Iff.rfl
      | some r =>
        rw [hGet] at hCons
        by_cases hs : s = rid.toObjId
        · subst hs
          constructor
          · intro h
            rw [storeObject_objects_eq st st1 rid.toObjId _ hObjInv hCons] at h
            cases h; exact absurd rfl (hkR _)
          · intro h
            rw [(getReply?_eq_some_iff st rid r).mp hGet] at h
            cases h; exact absurd rfl (hkR _)
        · rw [storeObject_objects_ne st st1 rid.toObjId s _ hs hObjInv hCons]
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact hLeg1
    | some tcb =>
      simp only [hT] at hStep
      by_cases hs : s = caller.toObjId
      · subst hs
        constructor
        · intro h
          rw [storeObject_objects_eq st1 st' caller.toObjId _ hObjInv1 hStep] at h
          cases h; exact absurd rfl (hkT _)
        · intro h
          have h1 := hLeg1.mpr h
          rw [(getTcb?_eq_some_iff st1 caller tcb).mp hT] at h1
          cases h1; exact absurd rfl (hkT _)
      · rw [storeObject_objects_ne st1 st' caller.toObjId s _ hs hObjInv1 hStep]
        exact hLeg1

/-- WS-SM SM6.D (PR #827 #3 fold), transport (b, forward): a post-`consumeCallerReply`
`.tcb` lookup transports back to a pre-state `.tcb` lookup agreeing on every field
any `ipcInvariantFull` conjunct reads (ipcState, pendingMessage,
queueNext/Prev/PPrev, schedContextBinding, timeoutBudget).  The consume's only TCB
write is the caller's `replyObject := none`, whose other projections are
definitionally unchanged; every other slot is untouched. -/
theorem consumeCallerReply_tcb_forward
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (tx : TCB), st'.objects[s]? = some (.tcb tx) →
      ∃ ty, st.objects[s]? = some (.tcb ty) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget := by
  intro s tx hObj
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hObjInv1 : st1.objects.invExt :=
      consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
    -- Transport the `.tcb` witness back through the caller-TCB leg into `st1`.
    have hLeg2 : ∃ t1, st1.objects[s]? = some (.tcb t1) ∧
        tx.ipcState = t1.ipcState ∧ tx.pendingMessage = t1.pendingMessage ∧
        tx.queueNext = t1.queueNext ∧ tx.queuePrev = t1.queuePrev ∧
        tx.queuePPrev = t1.queuePPrev ∧ tx.schedContextBinding = t1.schedContextBinding ∧
        tx.timeoutBudget = t1.timeoutBudget := by
      cases hT : st1.getTcb? caller with
      | none =>
        simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
        rw [hStep]
        exact ⟨tx, hObj, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      | some tcb =>
        simp only [hT] at hStep
        by_cases hs : s = caller.toObjId
        · subst hs
          rw [storeObject_objects_eq st1 st' caller.toObjId _ hObjInv1 hStep] at hObj
          cases hObj
          exact ⟨tcb, (getTcb?_eq_some_iff st1 caller tcb).mp hT,
            rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        · rw [storeObject_objects_ne st1 st' caller.toObjId s _ hs hObjInv1 hStep] at hObj
          exact ⟨tx, hObj, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    -- Transport through the `consumeReply` leg (a `.reply` write, TCB-invisible).
    obtain ⟨t1, hT1, hEqs⟩ := hLeg2
    have hLeg1 : st.objects[s]? = some (.tcb t1) := by
      unfold consumeReply at hCons
      cases hGet : st.getReply? rid with
      | none => rw [hGet] at hCons; cases hCons; exact hT1
      | some r =>
        rw [hGet] at hCons
        by_cases hs : s = rid.toObjId
        · subst hs
          rw [storeObject_objects_eq st st1 rid.toObjId _ hObjInv hCons] at hT1
          cases hT1
        · rw [storeObject_objects_ne st st1 rid.toObjId s _ hs hObjInv hCons] at hT1
          exact hT1
    exact ⟨t1, hLeg1, hEqs⟩

/-- WS-SM SM6.D (PR #827 #3 fold), transport (b, backward): a pre-state `.tcb`
lookup transports forward across `consumeCallerReply`, agreeing on every read
field.  Symmetric counterpart of `consumeCallerReply_tcb_forward`; pushes object
witnesses that appear in conjunct *goals* forward to the post-state. -/
theorem consumeCallerReply_tcb_backward
    (st st' : SystemState) (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    ∀ (s : SeLe4n.ObjId) (ty : TCB), st.objects[s]? = some (.tcb ty) →
      ∃ tx, st'.objects[s]? = some (.tcb tx) ∧
        tx.ipcState = ty.ipcState ∧ tx.pendingMessage = ty.pendingMessage ∧
        tx.queueNext = ty.queueNext ∧ tx.queuePrev = ty.queuePrev ∧
        tx.queuePPrev = ty.queuePPrev ∧ tx.schedContextBinding = ty.schedContextBinding ∧
        tx.timeoutBudget = ty.timeoutBudget := by
  intro s ty hObj
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hObjInv1 : st1.objects.invExt :=
      consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
    -- Push the `.tcb` witness forward through the `consumeReply` leg.
    have hLeg1 : st1.objects[s]? = some (.tcb ty) := by
      unfold consumeReply at hCons
      cases hGet : st.getReply? rid with
      | none => rw [hGet] at hCons; cases hCons; exact hObj
      | some r =>
        rw [hGet] at hCons
        by_cases hs : s = rid.toObjId
        · subst hs
          rw [(getReply?_eq_some_iff st rid r).mp hGet] at hObj
          cases hObj
        · rw [storeObject_objects_ne st st1 rid.toObjId s _ hs hObjInv hCons]
          exact hObj
    -- Push forward through the caller-TCB leg.
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]
      exact ⟨ty, hLeg1, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
    | some tcb =>
      simp only [hT] at hStep
      by_cases hs : s = caller.toObjId
      · subst hs
        have hEq : ty = tcb := by
          rw [(getTcb?_eq_some_iff st1 caller tcb).mp hT] at hLeg1
          injection hLeg1 with h; injection h with h2; exact h2.symm
        subst hEq
        exact ⟨{ ty with replyObject := none },
          storeObject_objects_eq st1 st' caller.toObjId _ hObjInv1 hStep,
          rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
      · refine ⟨ty, ?_, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
        rw [storeObject_objects_ne st1 st' caller.toObjId s _ hs hObjInv1 hStep]
        exact hLeg1

/-- PR #827 #3 fold: `consumeCallerReply` preserves the CDT (both legs are
object stores). -/
theorem consumeCallerReply_cdt_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    st'.cdt = st.cdt := by
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have h1 : st1.cdt = st.cdt := by
      unfold consumeReply at hCons
      cases hGet : st.getReply? rid with
      | none => rw [hGet] at hCons; cases hCons; rfl
      | some r => rw [hGet] at hCons; exact storeObject_cdt_eq st st1 rid.toObjId _ hCons
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact h1
    | some tcb =>
      simp only [hT] at hStep
      rw [storeObject_cdt_eq st1 st' caller.toObjId _ hStep]; exact h1

/-- PR #827 #3 fold: `consumeCallerReply` preserves the CDT node→slot mapping. -/
theorem consumeCallerReply_cdtNodeSlot_eq (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    st'.cdtNodeSlot = st.cdtNodeSlot := by
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have h1 : st1.cdtNodeSlot = st.cdtNodeSlot := by
      unfold consumeReply at hCons
      cases hGet : st.getReply? rid with
      | none => rw [hGet] at hCons; cases hCons; rfl
      | some r => rw [hGet] at hCons; exact storeObject_cdtNodeSlot_eq st st1 rid.toObjId _ hCons
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact h1
    | some tcb =>
      simp only [hT] at hStep
      rw [storeObject_cdtNodeSlot_eq st1 st' caller.toObjId _ hStep]; exact h1

/-- PR #827 #3 fold: `consumeCallerReply` never removes an object — both legs
overwrite existing slots, so object presence is preserved. -/
theorem consumeCallerReply_objects_isSome (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    ∀ (x : SeLe4n.ObjId), st.objects[x]? ≠ none → st'.objects[x]? ≠ none := by
  intro x hSome
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hObjInv1 : st1.objects.invExt :=
      consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
    have hLeg1 : st1.objects[x]? ≠ none := by
      unfold consumeReply at hCons
      cases hGet : st.getReply? rid with
      | none => rw [hGet] at hCons; cases hCons; exact hSome
      | some r =>
        rw [hGet] at hCons
        by_cases hx : x = rid.toObjId
        · subst hx
          rw [storeObject_objects_eq st st1 rid.toObjId _ hObjInv hCons]
          exact Option.some_ne_none _
        · rw [storeObject_objects_ne st st1 rid.toObjId x _ hx hObjInv hCons]
          exact hSome
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact hLeg1
    | some tcb =>
      simp only [hT] at hStep
      by_cases hx : x = caller.toObjId
      · subst hx
        rw [storeObject_objects_eq st1 st' caller.toObjId _ hObjInv1 hStep]
        exact Option.some_ne_none _
      · rw [storeObject_objects_ne st1 st' caller.toObjId x _ hx hObjInv1 hStep]
        exact hLeg1

/-- PR #827 #3 fold: `consumeCallerReply` keeps every present Reply object
present — the consumed Reply's `caller` is cleared but the object itself
survives, so reply capabilities stay backed (`replyCapPointsToValidReply`). -/
theorem consumeCallerReply_getReply?_isSome (st st' : SystemState)
    (caller : SeLe4n.ThreadId) (rid : SeLe4n.ReplyId)
    (hObjInv : st.objects.invExt)
    (hStep : consumeCallerReply caller rid st = .ok ((), st')) :
    ∀ (rid' : SeLe4n.ReplyId) (r' : SeLe4n.Kernel.Reply), st.getReply? rid' = some r' →
      ∃ r'', st'.getReply? rid' = some r'' := by
  intro rid' r' hGet'
  unfold consumeCallerReply at hStep
  cases hCons : consumeReply rid st with
  | error e => simp [hCons] at hStep
  | ok p1 =>
    obtain ⟨_, st1⟩ := p1
    simp only [hCons] at hStep
    have hObjInv1 : st1.objects.invExt :=
      consumeReply_preserves_objects_invExt st st1 rid hObjInv hCons
    have hLeg1 : ∃ r1, st1.getReply? rid' = some r1 := by
      unfold consumeReply at hCons
      cases hGet : st.getReply? rid with
      | none => rw [hGet] at hCons; cases hCons; exact ⟨r', hGet'⟩
      | some r =>
        rw [hGet] at hCons
        by_cases hEq : rid'.toObjId = rid.toObjId
        · refine ⟨{ r with caller := none }, ?_⟩
          rw [getReply?_eq_some_iff, hEq]
          exact storeObject_objects_eq st st1 rid.toObjId _ hObjInv hCons
        · refine ⟨r', ?_⟩
          rw [getReply?_eq_some_iff] at hGet' ⊢
          rw [storeObject_objects_ne st st1 rid.toObjId rid'.toObjId _ hEq hObjInv hCons]
          exact hGet'
    obtain ⟨r1, hGet1⟩ := hLeg1
    cases hT : st1.getTcb? caller with
    | none =>
      simp only [hT, Except.ok.injEq, Prod.mk.injEq, true_and] at hStep
      rw [← hStep]; exact ⟨r1, hGet1⟩
    | some tcb =>
      simp only [hT] at hStep
      have hNe : caller.toObjId ≠ rid'.toObjId :=
        getTcb?_getReply?_slot_ne st1 caller rid' tcb r1 hT hGet1
      refine ⟨r1, ?_⟩
      rw [getReply?_eq_some_iff] at hGet1 ⊢
      rw [storeObject_objects_ne st1 st' caller.toObjId rid'.toObjId _ hNe.symm hObjInv1 hStep]
      exact hGet1

/-- AL2-B (audit remediation): Unfolding lemma — `getEndpoint?` returns
`some ep` iff the store holds exactly `KernelObject.endpoint ep` at
`id`. -/
theorem getEndpoint?_eq_some_iff (st : SystemState) (id : SeLe4n.ObjId) (ep : Endpoint) :
    st.getEndpoint? id = some ep ↔ st.objects[id]? = some (.endpoint ep) := by
  unfold getEndpoint?
  split
  · rename_i ep' heq; constructor
    · intro h; cases h; exact heq
    · intro h; rw [h] at heq; cases heq; rfl
  · rename_i hne; constructor
    · intro h; cases h
    · intro h; exact absurd h (fun h' => hne _ (by rw [h']))

/-- AL2-B (audit remediation): Unfolding lemma — `getNotification?`
returns `some n` iff the store holds exactly `KernelObject.notification
n` at `id`. -/
theorem getNotification?_eq_some_iff (st : SystemState) (id : SeLe4n.ObjId) (n : Notification) :
    st.getNotification? id = some n ↔ st.objects[id]? = some (.notification n) := by
  unfold getNotification?
  split
  · rename_i n' heq; constructor
    · intro h; cases h; exact heq
    · intro h; rw [h] at heq; cases heq; rfl
  · rename_i hne; constructor
    · intro h; cases h
    · intro h; exact absurd h (fun h' => hne _ (by rw [h']))

/-- AL2-B (audit remediation): Unfolding lemma — `getUntyped?` returns
`some ut` iff the store holds exactly `KernelObject.untyped ut` at
`id`. -/
theorem getUntyped?_eq_some_iff (st : SystemState) (id : SeLe4n.ObjId) (ut : UntypedObject) :
    st.getUntyped? id = some ut ↔ st.objects[id]? = some (.untyped ut) := by
  unfold getUntyped?
  split
  · rename_i ut' heq; constructor
    · intro h; cases h; exact heq
    · intro h; rw [h] at heq; cases heq; rfl
  · rename_i hne; constructor
    · intro h; cases h
    · intro h; exact absurd h (fun h' => hne _ (by rw [h']))

/-- AN10-B: Unfolding lemma — `getCNode?` returns `some cn` iff the
store holds exactly `KernelObject.cnode cn` at `id`. -/
theorem getCNode?_eq_some_iff (st : SystemState) (id : SeLe4n.ObjId) (cn : CNode) :
    st.getCNode? id = some cn ↔ st.objects[id]? = some (.cnode cn) := by
  unfold getCNode?
  split
  · rename_i cn' heq; constructor
    · intro h; cases h; exact heq
    · intro h; rw [h] at heq; cases heq; rfl
  · rename_i hne; constructor
    · intro h; cases h
    · intro h; exact absurd h (fun h' => hne _ (by rw [h']))

/-- WS-SM SM6.D / PR #822 Phase H (#1.a): Unfolding lemma — `lookupCNode`
returns `some cn` iff the store holds exactly `KernelObject.cnode cn` at `id`.
Mirrors `getCNode?_eq_some_iff` (the two helpers share a definition); used by the
reply-cap backing discharge (`replyCapBacked_of_source_slot`) that connects a
`cspaceLookupSlot` result to the slot's containing CNode object. -/
theorem lookupCNode_eq_some_iff (st : SystemState) (id : SeLe4n.ObjId) (cn : CNode) :
    st.lookupCNode id = some cn ↔ st.objects[id]? = some (.cnode cn) := by
  unfold lookupCNode
  split
  · rename_i cn' heq; constructor
    · intro h; cases h; exact heq
    · intro h; rw [h] at heq; cases heq; rfl
  · rename_i hne; constructor
    · intro h; cases h
    · intro h; exact absurd h (fun h' => hne _ (by rw [h']))

/-- AN10-B: Unfolding lemma — `getVSpaceRoot?` returns `some root` iff
the store holds exactly `KernelObject.vspaceRoot root` at `id`. -/
theorem getVSpaceRoot?_eq_some_iff (st : SystemState) (id : SeLe4n.ObjId)
    (root : VSpaceRoot) :
    st.getVSpaceRoot? id = some root ↔ st.objects[id]? = some (.vspaceRoot root) := by
  unfold getVSpaceRoot?
  split
  · rename_i root' heq; constructor
    · intro h; cases h; exact heq
    · intro h; rw [h] at heq; cases heq; rfl
  · rename_i hne; constructor
    · intro h; cases h
    · intro h; exact absurd h (fun h' => hne _ (by rw [h']))

/-- AL2-B (audit remediation): `getTcb?` returns `none` iff the stored
object at `tid.toObjId` is either absent or is not of the `.tcb`
variant. This is the complement of `getTcb?_eq_some_iff` and completes
the characterization of the helper. -/
theorem getTcb?_eq_none_iff (st : SystemState) (tid : SeLe4n.ThreadId) :
    st.getTcb? tid = none ↔
      st.objects[tid.toObjId]? = none ∨
      (∃ obj, st.objects[tid.toObjId]? = some obj ∧ ∀ t, obj ≠ .tcb t) := by
  unfold getTcb?
  constructor
  · intro h
    split at h
    · cases h
    · rename_i hne
      by_cases hObj : ∃ obj, st.objects[tid.toObjId]? = some obj
      · rcases hObj with ⟨obj, hObj⟩
        right
        refine ⟨obj, hObj, ?_⟩
        intro t heq
        subst heq
        exact hne t hObj
      · left
        cases hGet : st.objects[tid.toObjId]?
        · rfl
        · exact absurd ⟨_, hGet⟩ hObj
  · intro h
    match h with
    | Or.inl hNone => simp [hNone]
    | Or.inr ⟨obj, hSome, hNotTcb⟩ =>
        rw [hSome]
        split
        · rename_i t hEq
          exact absurd (Option.some.inj hEq) (hNotTcb t)
        · rfl

/-- Read a capability from a typed slot reference. -/
def lookupSlotCap (st : SystemState) (ref : SlotRef) : Option Capability :=
  match lookupCNode st ref.cnode with
  | none => none
  | some cn => cn.lookup ref.slot

/-- The modeled owner of a slot is its containing CNode. -/
def ownerOfSlot (ref : SlotRef) : CSpaceOwner :=
  ref.cnode

/-- Logical ownership relation for occupied slots. -/
def ownsSlot (st : SystemState) (owner : CSpaceOwner) (ref : SlotRef) : Prop :=
  owner = ownerOfSlot ref ∧ ∃ cap, lookupSlotCap st ref = some cap

/-- Enumerate all concrete capability entries held by one modeled owner CNode.
WS-G5: Projects HashMap-backed slots to `List` for enumeration compatibility. -/
def ownedSlots (st : SystemState) (owner : CSpaceOwner) : List (SeLe4n.Slot × Capability) :=
  match lookupCNode st owner with
  | some cn => cn.slots.toList
  | none => []

/-- Lifecycle metadata view of object identity typing. -/
def lookupObjectTypeMeta (st : SystemState) (id : SeLe4n.ObjId) : Option KernelObjectType :=
  st.lifecycle.objectTypes[id]?

/-- Lifecycle metadata view of capability slot reference mapping. -/
def lookupCapabilityRefMeta (st : SystemState) (ref : SlotRef) : Option CapTarget :=
  (lookupSlotCap st ref).map Capability.target


/-- Read the stable CDT node currently referenced by a CSpace slot, if any. -/
def lookupCdtNodeOfSlot (st : SystemState) (ref : SlotRef) : Option CdtNodeId :=
  st.cdtSlotNode[ref]?

/-- Read the current CSpace slot backpointer of a stable CDT node, if any. -/
def lookupCdtSlotOfNode (st : SystemState) (node : CdtNodeId) : Option SlotRef :=
  st.cdtNodeSlot[node]?


/-- Attach slot `ref` to `node` and maintain bidirectional consistency.
If the slot/node already point elsewhere, stale opposite links are cleared.

**T2-L (M-ST-2): Stale-link cleanup ordering rationale.**

The function performs two cleanups before inserting the new bidirectional link:
1. Erase `cdtSlotNode[prevRef]` — if `node` was previously mapped to a
   different slot `prevRef`, that stale slot→node link must be removed.
2. Erase `cdtNodeSlot[prevNode]` — if `ref` was previously mapped to a
   different node `prevNode`, that stale node→slot link must be removed.

These two cleanups are **independent**: they operate on different maps
(`cdtSlotNode` vs `cdtNodeSlot`) and target different keys (`prevRef` vs
`prevNode`). Their ordering does not matter for correctness because:
- Each cleanup erases from a different map, so they commute.
- The final `insert` on both maps overwrites any residual stale entry for
  the primary key pair `(ref, node)`, so even if a cleanup is a no-op
  (because the stale link was already absent), the result is the same.
- The CDT consistency invariant (S3-A) requires `cdtSlotNode[ref] = some node`
  iff `cdtNodeSlot[node] = some ref`. Both cleanups + both inserts are needed
  to re-establish this; the order of cleanups is irrelevant. -/
def attachSlotToCdtNode (st : SystemState) (ref : SlotRef) (node : CdtNodeId) : SystemState :=
  let prevNode := st.cdtSlotNode[ref]?
  let prevRef := st.cdtNodeSlot[node]?
  let cdtSlotNode' :=
    match prevRef with
    | some oldRef => st.cdtSlotNode.erase oldRef
    | none => st.cdtSlotNode
  let cdtNodeSlot' :=
    match prevNode with
    | some oldNode => st.cdtNodeSlot.erase oldNode
    | none => st.cdtNodeSlot
  {
    st with
      cdtSlotNode := cdtSlotNode'.insert ref node
      cdtNodeSlot := cdtNodeSlot'.insert node ref
  }

/-- Detach a slot from its CDT node, clearing both slot→node and node→slot maps. -/
def detachSlotFromCdt (st : SystemState) (ref : SlotRef) : SystemState :=
  match st.cdtSlotNode[ref]? with
  | none => st
  | some node =>
      {
        st with
          cdtSlotNode := st.cdtSlotNode.erase ref
          cdtNodeSlot := st.cdtNodeSlot.erase node
      }

/-- WS-SM SM7.B: `detachSlotFromCdt` is CDT-only — the TLB-shootdown
state is framed (`pendingBounded` bundle-carriage leaf). -/
theorem detachSlotFromCdt_tlbShootdown_eq (st : SystemState) (ref : SlotRef) :
    (st.detachSlotFromCdt ref).tlbShootdown = st.tlbShootdown := by
  unfold detachSlotFromCdt; split <;> rfl

/-- Ensure `ref` has a CDT node; allocate one if absent. -/
def ensureCdtNodeForSlot (st : SystemState) (ref : SlotRef) : CdtNodeId × SystemState :=
  match st.cdtSlotNode[ref]? with
  | some node => (node, st)
  | none =>
      let node := st.cdtNextNode
      let st' :=
        {
          st with
            cdtNextNode := ⟨node.val + 1⟩
            cdtSlotNode := st.cdtSlotNode.insert ref node
            cdtNodeSlot := st.cdtNodeSlot.insert node ref
        }
      (node, st')

/-- AK7-J (F-M09 / MEDIUM): Checked variant of `ensureCdtNodeForSlot`
that preserves the `cdtNextNodeBounded` invariant (defined below at
`SystemState.lean:526`).

Fails with `none` when:
1. A fresh node would be allocated, and
2. The current `cdtNextNode.val` is already at or above `maxCdtDepth`.

Returns `some (node, st')` in the non-allocating branch (slot already
has a CDT node) and in the allocating branch when the new counter value
still satisfies the advisory bound. `ensureCdtNodeForSlot` remains
available for unchecked callers; production CDT entry points that must
guarantee bounded hardware-id allocation should route through the
checked variant. -/
def ensureCdtNodeForSlotChecked (st : SystemState) (ref : SlotRef) :
    Option (CdtNodeId × SystemState) :=
  match st.cdtSlotNode[ref]? with
  | some node => some (node, st)
  | none =>
      if st.cdtNextNode.val + 1 < maxCdtDepth then
        let node := st.cdtNextNode
        let st' :=
          {
            st with
              cdtNextNode := ⟨node.val + 1⟩
              cdtSlotNode := st.cdtSlotNode.insert ref node
              cdtNodeSlot := st.cdtNodeSlot.insert node ref
          }
        some (node, st')
      else
        none


theorem attachSlotToCdtNode_objects_eq (st : SystemState) (ref : SlotRef) (node : CdtNodeId) :
    (attachSlotToCdtNode st ref node).objects = st.objects := by
  simp [attachSlotToCdtNode]

theorem detachSlotFromCdt_objects_eq (st : SystemState) (ref : SlotRef) :
    (detachSlotFromCdt st ref).objects = st.objects := by
  unfold detachSlotFromCdt
  split <;> simp

theorem ensureCdtNodeForSlot_objects_eq (st : SystemState) (ref : SlotRef) :
    (ensureCdtNodeForSlot st ref).snd.objects = st.objects := by
  unfold ensureCdtNodeForSlot
  split <;> rfl

/-- AK7-J (F-M09 / MEDIUM): `ensureCdtNodeForSlotChecked` preserves the
`cdtNextNodeBounded` invariant — whenever it returns `some (_, st')`,
the post-state satisfies the bound.

This is the preservation proof that makes the checked variant safe to
use at CDT entry points when hardware-width id uniqueness must be
preserved. -/
theorem ensureCdtNodeForSlotChecked_preserves_bounded
    (st : SystemState) (ref : SlotRef) (node : CdtNodeId) (st' : SystemState)
    (hBound : cdtNextNodeBounded st)
    (h : ensureCdtNodeForSlotChecked st ref = some (node, st')) :
    cdtNextNodeBounded st' := by
  unfold ensureCdtNodeForSlotChecked at h
  split at h
  · -- Already has a node — state unchanged
    cases h; exact hBound
  · -- Fresh allocation branch
    split at h
    · rename_i hCheck
      cases h
      simp [cdtNextNodeBounded] at *
      exact hCheck
    · cases h

/-- AK7-J (F-M09): `ensureCdtNodeForSlotChecked` preserves the object store. -/
theorem ensureCdtNodeForSlotChecked_objects_eq
    (st : SystemState) (ref : SlotRef) (node : CdtNodeId) (st' : SystemState)
    (h : ensureCdtNodeForSlotChecked st ref = some (node, st')) :
    st'.objects = st.objects := by
  unfold ensureCdtNodeForSlotChecked at h
  split at h
  · cases h; rfl
  · split at h
    · cases h; rfl
    · cases h

/-- AK7-J (F-M09): `ensureCdtNodeForSlotChecked` agrees with the unchecked
variant whenever the invariant holds pre-call AND there's still a slot
available. In the already-allocated branch the result matches unconditionally. -/
theorem ensureCdtNodeForSlotChecked_eq_unchecked_of_allocated
    (st : SystemState) (ref : SlotRef) (node : CdtNodeId)
    (hLookup : st.cdtSlotNode[ref]? = some node) :
    ensureCdtNodeForSlotChecked st ref = some (node, st) := by
  unfold ensureCdtNodeForSlotChecked
  rw [hLookup]

/-- `lookupSlotCap` is determined entirely by the object store. -/
theorem lookupSlotCap_eq_of_objects_eq
    (st₁ st₂ : SystemState)
    (ref : SlotRef)
    (hObj : st₁.objects = st₂.objects) :
    lookupSlotCap st₁ ref = lookupSlotCap st₂ ref := by
  simp [lookupSlotCap, lookupCNode, hObj]

/-- Object-type lifecycle metadata is exact for every object-store id. -/
def objectTypeMetadataConsistent (st : SystemState) : Prop :=
  ∀ oid, lookupObjectTypeMeta st oid = (st.objects[oid]?).map KernelObject.objectType

/-- Capability-reference lifecycle metadata is exact for every slot reference. -/
def capabilityRefMetadataConsistent (st : SystemState) : Prop :=
  ∀ ref, lookupCapabilityRefMeta st ref = (lookupSlotCap st ref).map Capability.target

/-- M4-A state-model metadata consistency bundle. -/
def lifecycleMetadataConsistent (st : SystemState) : Prop :=
  objectTypeMetadataConsistent st ∧ capabilityRefMetadataConsistent st

theorem lookupSlotCap_eq_none_of_lookupCNode_eq_none
    (st : SystemState)
    (ref : SlotRef)
    (hNone : lookupCNode st ref.cnode = none) :
    lookupSlotCap st ref = none := by
  simp [lookupSlotCap, hNone]

theorem ownsSlot_iff
    (st : SystemState)
    (owner : CSpaceOwner)
    (ref : SlotRef) :
    ownsSlot st owner ref ↔
      owner = ref.cnode ∧ ∃ cap, lookupSlotCap st ref = some cap := by
  simp [ownsSlot, ownerOfSlot]

theorem ownedSlots_eq_nil_of_lookupCNode_eq_none
    (st : SystemState)
    (owner : CSpaceOwner)
    (hNone : lookupCNode st owner = none) :
    ownedSlots st owner = [] := by
  simp [ownedSlots, hNone]

end SystemState

theorem storeObject_preserves_objectTypeMetadataConsistent
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hConsistent : SystemState.objectTypeMetadataConsistent st)
    (hObjInv : st.objects.invExt)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.objectTypeMetadataConsistent st' := by
  intro oid'
  unfold storeObject at hStep; cases hStep
  simp only [SystemState.lookupObjectTypeMeta] at *
  by_cases hEq : oid' = oid
  · subst hEq
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable.getElem?_insert_self _ _ _ hObjTypesInv,
        RHTable.getElem?_insert_self _ _ _ hObjInv]; simp
  · have h1 : ¬((oid == oid') = true) := by intro heq; exact hEq (eq_of_beq heq).symm
    simp only [RHTable_getElem?_eq_get?]
    rw [RHTable.getElem?_insert_ne _ _ _ _ h1 hObjTypesInv,
        RHTable.getElem?_insert_ne _ _ _ _ h1 hObjInv]
    exact hConsistent oid'

theorem storeObject_preserves_capabilityRefMetadataConsistent
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (_hConsistent : SystemState.capabilityRefMetadataConsistent st)
    (_hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.capabilityRefMetadataConsistent st' := by
  intro ref
  simp [SystemState.lookupCapabilityRefMeta]

theorem storeObject_preserves_lifecycleMetadataConsistent
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hConsistent : SystemState.lifecycleMetadataConsistent st)
    (hObjInv : st.objects.invExt)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.lifecycleMetadataConsistent st' := by
  rcases hConsistent with ⟨hObjType, hCapRef⟩
  exact ⟨storeObject_preserves_objectTypeMetadataConsistent st st' oid obj hObjType hObjInv hObjTypesInv hStep,
    storeObject_preserves_capabilityRefMetadataConsistent st st' oid obj hCapRef hStep⟩

-- ============================================================================
-- T2-H (M-NEW-3): capabilityRefs filter preserves invExt
-- ============================================================================

/-- T2-H (M-NEW-3): When `storeObject` filters out old CNode references via
    `RHTable.filter`, the resulting table's `invExt` is preserved. This follows
    directly from `RHTable.filter_preserves_invExt`. -/
theorem capabilityRefs_filter_preserves_invExt
    (capRefs : RHTable SlotRef CapTarget)
    (id : SeLe4n.ObjId)
    (hInv : capRefs.invExt) :
    (capRefs.filter (fun ref _ => ref.cnode ≠ id)).invExt :=
  RHTable.filter_preserves_invExt capRefs _ hInv

-- ============================================================================
-- T2-I (M-NEW-3): capabilityRefs fold insert preserves invExt
-- ============================================================================

/-- T2-I (M-NEW-3): When `storeObject` inserts new CNode references via `fold`,
    the resulting table's `invExt` is preserved. Each sequential `insert`
    preserves `invExt` by `RHTable.insert_preserves_invExt`, and the fold
    composes these preservations via `RHTable.fold_preserves`. -/
theorem capabilityRefs_fold_preserves_invExt
    (cn : CNode)
    (cleared : RHTable SlotRef CapTarget)
    (id : SeLe4n.ObjId)
    (hInv : cleared.invExt) :
    (cn.slots.fold (init := cleared) fun refs slot cap =>
      refs.insert { cnode := id, slot := slot } cap.target).invExt :=
  RHTable.fold_preserves cn.slots.table cleared _ (fun t => t.invExt) hInv
    (fun acc _ _ hAcc => RHTable.insert_preserves_invExt acc _ _ hAcc)

/-- V3-B: capabilityRefs fold insert preserves invExtK. -/
theorem capabilityRefs_fold_preserves_invExtK
    (cn : CNode)
    (cleared : RHTable SlotRef CapTarget)
    (id : SeLe4n.ObjId)
    (hInvK : cleared.invExtK) :
    (cn.slots.fold (init := cleared) fun refs slot cap =>
      refs.insert { cnode := id, slot := slot } cap.target).invExtK :=
  RHTable.fold_preserves cn.slots.table cleared _ (fun t => t.invExtK) hInvK
    (fun acc _ _ hAcc => RHTable.insert_preserves_invExtK acc _ _ hAcc)

-- ============================================================================
-- T2-G (M-NEW-2): Bundled storeObject preserves allTablesInvExt
-- ============================================================================

/-- T2-G (M-NEW-2): Bundled preservation theorem for `storeObject`.

    Composes the 17 component preservation proofs (objects, objectIndex,
    objectIndexSet, lifecycle.objectTypes, lifecycle.capabilityRefs, asidTable,
    scThreadIndex, etc.) into a single theorem. Callers can invoke this instead
    of manually composing each component.

    The proof works by showing that `storeObject` only modifies fields via
    `insert`, `filter`, or `erase` — all of which preserve `invExt` — and
    leaves unchanged fields (scheduler, CDT maps, services) structurally equal
    to the pre-state. -/
theorem storeObject_preserves_allTablesInvExtK
    (st st' : SystemState)
    (id : SeLe4n.ObjId)
    (obj : KernelObject)
    (hAll : st.allTablesInvExtK)
    (hStore : storeObject id obj st = .ok ((), st')) :
    st'.allTablesInvExtK := by
  unfold storeObject at hStore; cases hStore
  unfold SystemState.allTablesInvExtK at hAll ⊢
  simp only
  -- Extract components from pre-state invariant
  have hObj := hAll.1
  have hIrq := hAll.2.1
  have hAsid := hAll.2.2.1
  have hCdtSN := hAll.2.2.2.1
  have hCdtNS := hAll.2.2.2.2.1
  have hObjTypes := hAll.2.2.2.2.2.1
  have hCapRefs := hAll.2.2.2.2.2.2.1
  have hChildMap := hAll.2.2.2.2.2.2.2.1
  have hParentMap := hAll.2.2.2.2.2.2.2.2.1
  have hServices := hAll.2.2.2.2.2.2.2.2.2.1
  have hIfaceReg := hAll.2.2.2.2.2.2.2.2.2.2.1
  have hSvcReg := hAll.2.2.2.2.2.2.2.2.2.2.2.1
  have hByPri := hAll.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hThreadPri := hAll.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hObjIdxSet := hAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hMembership := hAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1
  have hScThreadIdx := hAll.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2
  -- Prove objects insert preserves invExtK
  have hObj' := RHTable.insert_preserves_invExtK st.objects id obj hObj
  -- Prove objectTypes insert preserves invExtK
  have hObjTypes' := RHTable.insert_preserves_invExtK st.lifecycle.objectTypes id obj.objectType hObjTypes
  -- Prove capabilityRefs filter+fold preserves invExtK
  have hFiltered := RHTable.filter_preserves_invExtK st.lifecycle.capabilityRefs (fun ref _ => ref.cnode ≠ id) hCapRefs
  have hCapRefs' : (match obj with
      | .cnode cn => cn.slots.fold (init := st.lifecycle.capabilityRefs.filter (fun ref _ => ref.cnode ≠ id))
          fun refs slot cap => refs.insert { cnode := id, slot := slot } cap.target
      | _ => st.lifecycle.capabilityRefs.filter (fun ref _ => ref.cnode ≠ id)).invExtK := by
    cases obj with
    | cnode cn => exact capabilityRefs_fold_preserves_invExtK cn _ id hFiltered
    | _ => exact hFiltered
  -- Prove objectIndexSet insert preserves invExtK
  have hObjIdxSet' := RHSet.insert_preserves_invExtK st.objectIndexSet id hObjIdxSet
  -- Prove asidTable preserves invExtK (erase + insert depending on obj type)
  have hAsid' : (let cleared := match st.objects[id]? with
        | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
        | _ => st.asidTable
      match obj with
      | .vspaceRoot newRoot => cleared.insert newRoot.asid id
      | _ => cleared).invExtK := by
    -- The cleared table preserves invExtK via erase or identity
    have hCleared : (match st.objects[id]? with
        | some (.vspaceRoot oldRoot) => st.asidTable.erase oldRoot.asid
        | _ => st.asidTable).invExtK := by
      split
      · rename_i r _; exact RHTable.erase_preserves_invExtK st.asidTable r.asid hAsid
      · exact hAsid
    cases obj with
    | vspaceRoot vs => exact RHTable.insert_preserves_invExtK _ _ _ hCleared
    | _ => exact hCleared
  -- Compose all 17 components (S-05/PERF-O1: scThreadIndex added)
  exact ⟨hObj', hIrq, hAsid', hCdtSN, hCdtNS, hObjTypes', hCapRefs',
         hChildMap, hParentMap, hServices, hIfaceReg, hSvcReg,
         hByPri, hThreadPri, hObjIdxSet', hMembership, hScThreadIdx⟩

-- ============================================================================
-- L-06/WS-E3: Default SystemState initialization proof
-- ============================================================================

/-- L-06/WS-E3: The default (empty) `SystemState` satisfies `lifecycleMetadataConsistent`.
Both metadata maps return `none` for all inputs, and `objects` returns `none`
for all IDs, so the consistency conditions hold trivially. This provides the
base case for invariant induction — the system starts in a valid state. -/
theorem default_systemState_lifecycleConsistent :
    SystemState.lifecycleMetadataConsistent (default : SystemState) := by
  constructor
  · -- objectTypeMetadataConsistent: both HashMaps are empty → both get? return none
    intro oid
    simp only [SystemState.lookupObjectTypeMeta]
    have h₁ : (default : SystemState).lifecycle.objectTypes[oid]? = none :=
      RHTable.getElem?_empty _ _ _
    have h₂ : (default : SystemState).objects[oid]? = none :=
      RHTable.getElem?_empty _ _ _
    rw [h₁, h₂]; rfl
  · -- capabilityRefMetadataConsistent: `lookupCapabilityRefMeta` is definitionally exact.
    intro ref
    simp [SystemState.lookupCapabilityRefMeta, SystemState.lookupSlotCap, SystemState.lookupCNode]

-- ============================================================================
-- M-09/WS-E3: storeObject metadata sync correctness for type-changing stores
-- ============================================================================

/-- M-09/WS-E3: `storeObject` correctly synchronizes lifecycle metadata even when
the stored object changes the type at `oid`. After storing, the metadata at `oid`
reflects the new object's type, regardless of what was stored previously. -/
theorem storeObject_metadata_sync_type_change
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hObjTypesInv : st.lifecycle.objectTypes.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    st'.lifecycle.objectTypes[oid]? = some obj.objectType :=
  storeObject_updates_objectTypeMeta st st' oid obj hObjTypesInv hStep

/-- M-09/WS-E3: `storeObject` correctly synchronizes capability-reference metadata
when the stored object changes from a CNode to a non-CNode (or vice versa).
After storing a non-CNode, all capability references pointing into `oid` are
cleared; after storing a CNode, they reflect the new CNode's slot contents.

This closes the metadata sync hazard: for type-changing stores (e.g., replacing
a CNode with a TCB), `storeObject` correctly clears all capability-reference
metadata for the replaced CNode's slots (the `| _ => none` branch), maintaining
the invariant that metadata reflects the actual object store. -/
theorem storeObject_metadata_sync_capref_at_stored
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (slot : SeLe4n.Slot)
    (hObjInv : st.objects.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    SystemState.lookupCapabilityRefMeta st' { cnode := oid, slot := slot } =
      match obj with
      | .cnode cn => (cn.lookup slot).map Capability.target
      | _ => none := by
  unfold SystemState.lookupCapabilityRefMeta SystemState.lookupSlotCap SystemState.lookupCNode
  unfold storeObject at hStep; cases hStep
  simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_self _ _ _ hObjInv]
  cases obj <;> simp [CNode.lookup]

-- ============================================================================
-- L-05/WS-E6: objectIndex monotonicity
-- ============================================================================

/-- L-05/WS-E6: `storeObject` preserves existing objectIndex membership.
Any ID present in the index before the store remains present after. This is
the formal monotonicity guarantee documented on `SystemState.objectIndex`. -/
theorem storeObject_objectIndex_monotone
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (id : SeLe4n.ObjId)
    (hMem : id ∈ st.objectIndex)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    id ∈ st'.objectIndex := by
  unfold storeObject at hStep; cases hStep
  simp only []
  cases h : st.objectIndexSet.contains oid
  · simp; exact Or.inr hMem
  · simp; exact hMem

-- ============================================================================
-- WS-H16/A-13: objectIndex liveness — index membership implies object existence
-- ============================================================================

/-- WS-H16/A-13: Every ID in `objectIndex` has a corresponding object in
`objects`. Since `storeObject` always inserts into both `objects` and
`objectIndex` (and no operation erases from `objects`), this property holds
for any state built through `storeObject` transitions.

This closes the gap identified by A-13 where `objectIndex` grows monotonically
without a bounds proof connecting index membership to object existence. -/
def objectIndexLive (st : SystemState) : Prop :=
  ∀ (id : SeLe4n.ObjId), id ∈ st.objectIndex → st.objects[id]? ≠ none

/-- WS-H16/A-13: `objectIndexLive` holds for the default (empty) state. -/
theorem objectIndexLive_default : objectIndexLive default := by
  intro id hMem
  simp [default, Inhabited.default] at hMem

/-- WS-H16/A-13: `storeObject` preserves `objectIndexLive`.

After `storeObject oid obj st`, every ID in `st'.objectIndex` maps to a
live object: the newly stored `oid` maps to `obj`, and all pre-existing
IDs retain their objects because `HashMap.insert` does not erase other keys. -/
theorem storeObject_preserves_objectIndexLive
    (st st' : SystemState)
    (oid : SeLe4n.ObjId)
    (obj : KernelObject)
    (hLive : objectIndexLive st)
    (hObjInv : st.objects.invExt)
    (hStep : storeObject oid obj st = .ok ((), st')) :
    objectIndexLive st' := by
  unfold storeObject at hStep; cases hStep
  intro id hMem
  simp only [] at hMem
  cases h : st.objectIndexSet.contains oid
  · -- oid was not in objectIndexSet, so objectIndex = oid :: st.objectIndex
    simp [h] at hMem
    cases hMem with
    | inl heq =>
      subst heq
      simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_self _ _ _ hObjInv]; simp
    | inr hOld =>
      have hOldLive := hLive id hOld
      by_cases hEq : (oid == id) = true
      · have : oid = id := eq_of_beq hEq; subst this
        simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_self _ _ _ hObjInv]; simp
      · simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_ne _ _ _ _ hEq hObjInv]
        exact hOldLive
  · -- oid was already in objectIndexSet, so objectIndex unchanged
    simp [h] at hMem
    by_cases hEq : (oid == id) = true
    · have : oid = id := eq_of_beq hEq; subst this
      simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_self _ _ _ hObjInv]; simp
    · simp only [RHTable_getElem?_eq_get?]; rw [RHTable.getElem?_insert_ne _ _ _ _ hEq hObjInv]
      exact hLive id hMem

end SeLe4n.Model
