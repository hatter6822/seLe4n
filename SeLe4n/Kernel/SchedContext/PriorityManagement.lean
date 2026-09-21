-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations

/-! # D2: Priority Management Operations

Implements `setPriorityOp` and `setMCPriorityOp` as capability-controlled
operations for modifying thread scheduling priority through the SchedContext
subsystem. In seL4's MCS model, priority is a property of the scheduling
context, not the thread directly.

## MCP Authority Model

The Maximum Controlled Priority (MCP) ceiling prevents privilege escalation:
a thread can only set another thread's priority up to its own MCP. This
ensures the authority hierarchy is monotonically non-increasing.

## Priority Update Path

- If the target thread has a bound SchedContext (`.bound` or `.donated`),
  the SchedContext's priority is updated (it owns the scheduling priority).
- If unbound, the TCB's priority field is updated directly.

## Run Queue Migration

When priority changes for a thread currently in the run queue, the thread
is removed and re-inserted at the new priority bucket to maintain correct
scheduling order.

## AN5-D (SC-M02) — Closure-form preservation theorems

The NI projection-preservation theorems for `setPriorityOp` and
`setMCPriorityOp` live in `InformationFlow/Invariant/Operations.lean`
(not in `SchedContext/Invariant/PriorityPreservation.lean` — that file
holds the *authority* preservation theorems `setPriority_authority_bounded`
/ `setMCPriority_authority_bounded` and the non-closure frame lemmas).
The projection theorems carry an `hSchedProj` closure hypothesis
representing the optional preemption-schedule call:

```lean
theorem setPriorityOp_preserves_projection
    … (hSchedProj : ∀ stMid stFinal, …) : …
```

This is structurally the same pattern as the `H-07` finding for
information-flow projection theorems.

**Discharge plan**: AN6-A performs the substantive discharge of
projection closure-form theorems. The priority-management closure form
follows the same recipe: frame lemmas in
`Scheduler/Operations/Preservation.lean` (specifically
`schedule_preserves_schedulerInvariantBundle` and its domain/EDF
companions) compose to eliminate the closure. AN5-D retains the
closure-form version at this phase; AN6-A's discharge recipe applies
here unchanged. -/

namespace SeLe4n.Kernel.SchedContext.PriorityManagement

open SeLe4n
open SeLe4n.Kernel.Concurrency (bootCoreId)
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- D2-D: validatePriorityAuthority
-- ============================================================================

/-- AK8-D (WS-AK / C-M05): Hardware priority ceiling. Matches seL4 MCS and
the `MAX_PRIORITY = 255` constant exposed by the Rust ABI (`sele4n-types`)
and `decodeSchedContextConfigureArgsChecked` (AK3-J). Any priority value
above this cap cannot be encoded into the platform's 8-bit priority register
file and would be truncated at the ABI boundary — validation rejects it
instead. -/
def maxHardwarePriority : Nat := 255

/-- D2-D: Validate that the caller has sufficient MCP authority to assign
the given priority. Returns `illegalAuthority` if `targetPriority > caller.mcp`.
This is the MCP ceiling check — the primary defense against priority escalation.

**AK8-D (WS-AK / C-M05) — MCP bound rationale:** `maxControlledPriority` is
an unbounded `Nat` in the Lean model. Standard seL4 MCS semantics allow a
root task with `maxControlledPriority = ∞` to set arbitrary priority on any
child; that matches the reference specification (seL4 Manual §5.2 —
"Priorities and MCPs") and is a deliberate design choice rather than a bug.

However, the ABI transport layer truncates priorities to 8 bits (matching
ARM GIC-400 `IPRIORITYR` and seL4's `seL4_MaxPrio = 255`). To surface this
truncation point explicitly at the model layer, we additionally validate
`targetPriority ≤ maxHardwarePriority`. This produces the same
`illegalAuthority` result as the MCP ceiling violation and matches the
existing `decodeSchedContextConfigureArgsChecked` bound from AK3-J. -/
def validatePriorityAuthority (callerTcb : TCB) (targetPriority : SeLe4n.Priority)
    : Except KernelError Unit :=
  if targetPriority.val > maxHardwarePriority then .error .illegalAuthority
  else if targetPriority.val ≤ callerTcb.maxControlledPriority.val then .ok ()
  else .error .illegalAuthority

/-- AK8-D (WS-AK / C-M05): Soundness — if `validatePriorityAuthority`
succeeds, the target priority fits in the platform's 8-bit priority
register width. This witnesses that every priority assigned via the
priority-management API path is representable in hardware, independent of
how the Lean-level `maxControlledPriority` is configured. -/
theorem validatePriorityAuthority_bound
    (callerTcb : TCB) (newPri : SeLe4n.Priority)
    (h : validatePriorityAuthority callerTcb newPri = .ok ()) :
    newPri.val ≤ maxHardwarePriority := by
  unfold validatePriorityAuthority at h
  by_cases hLt : newPri.val > maxHardwarePriority
  · simp [hLt] at h
  · exact Nat.le_of_not_lt hLt

-- ============================================================================
-- D2-E: setPriorityOp
-- ============================================================================

/-- Helper: get the current base priority of a thread, resolving through its
**priority source** (`SchedContextBinding.ownScId?`).  Returns the
SchedContext priority for a `.bound` thread and the TCB priority for an
`.unbound` or `.donated` one.

**WS-OD (v0.35.3)**: this is `SystemState.threadBasePriority`, by definition
rather than by resemblance — the tree answers "what priority does this thread
run at" in one place, and `setPriorityOp`'s pre/post reading is that answer.
The `.donated` arm reads the TCB because a donee runs on the donor's budget,
deadline and domain but at its own scheduling band; before the split it read
the donor's reservation, which is what let `updatePrioritySource` write it.

**Invariant dependency**: for a `.bound` thread this requires
`schedContextBindingConsistent` (Invariant/Defs.lean) to guarantee the
referenced SchedContext exists. If it does not (invariant violation), the
function defensively falls back to `tcb.priority`. This fallback path is
dead code when system invariants hold.

**AK8-E (WS-AK / C-M06) — Error-surfacing variant**: this lookup-tolerant
signature is preserved for backward compatibility and for proof contexts
where the `schedContextBindingConsistent` invariant has already been
established at the call site. Production dispatch paths should prefer
`getCurrentPriorityChecked` (below), which surfaces the "bound to
non-existent SchedContext" case as `.error .objectNotFound` rather
than silently masking it. -/
def getCurrentPriority (st : SystemState) (tcb : TCB)
    : SeLe4n.Priority :=
  st.threadBasePriority tcb

/-- WS-OD (v0.35.3): `getCurrentPriority` *is* the canonical resolver — held by
`rfl`, so the priority-management API and the scheduler cannot answer the
question differently. -/
theorem getCurrentPriority_eq_threadBasePriority (st : SystemState) (tcb : TCB) :
    getCurrentPriority st tcb = st.threadBasePriority tcb := rfl

/-- WS-OD (v0.35.3): a **donated** thread's current priority is its own,
whatever the donor's reservation holds. -/
@[simp] theorem getCurrentPriority_donated (st : SystemState) (tcb : TCB)
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    (h : tcb.schedContextBinding = .donated scId owner) :
    getCurrentPriority st tcb = tcb.priority := by
  simp [getCurrentPriority, SystemState.threadBasePriority, h]

/-- AK8-E (WS-AK / C-M06): Error-surfacing variant of `getCurrentPriority`.

Returns `.error .objectNotFound` if the TCB's `schedContextBinding` is
`.bound scId` but the referenced SchedContext is not present in the object
store (indicating a `schedContextBindingConsistent` invariant violation).
Returns `.ok sc.priority` when the binding resolves cleanly, and
`.ok tcb.priority` for unbound **and donated** threads — since WS-OD
(v0.35.3) a donee's priority is its own, so no lookup can fail on that arm
(`getCurrentPriorityChecked_donated`).

The error variant reuses `.objectNotFound` (rather than introducing a new
`.schedContextNotFound` variant) to keep the Rust ABI discriminant range
stable at 49 entries — the missing-binding scenario is a genuine
"referenced object not in store" case and matches the semantics of the
existing variant.

This variant is the preferred entry point for production kernel-entry paths
that read priority for a potentially-bound TCB (e.g., preemption checks in
`setPriorityOp`/`setMCPriorityOp`). The untagged lookup-tolerant
`getCurrentPriority` remains available for proof-layer code where the
binding invariant is established as a precondition. -/
def getCurrentPriorityChecked (st : SystemState) (tcb : TCB)
    : Except KernelError SeLe4n.Priority :=
  -- WS-OD (v0.35.3): classify through the priority source, so this checked
  -- reader and `getCurrentPriority` cannot disagree about which arm consults
  -- the object store (`getCurrentPriorityChecked_ok_eq_getCurrentPriority`).
  match tcb.schedContextBinding.ownScId? with
  | some scId =>
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    match st.getSchedContext? scId with
    -- WS-RR (`v0.35.133`): the THREAD's base, at every binding.  The lookup
    -- survives because its FAILURE is the error this variant exists to surface
    -- (a `.bound` binding naming an absent reservation is a
    -- `schedContextBindingConsistent` violation); what it no longer decides is
    -- the priority.
    | some _  => .ok tcb.priority
    | none    => .error .objectNotFound
  | none => .ok tcb.priority

/-- AK8-E (C-M06): Soundness — when `getCurrentPriorityChecked` returns
`.ok p`, the result matches the lookup-tolerant `getCurrentPriority`. This
allows existing proofs that reason about `getCurrentPriority` to transport
to the checked variant's success case. -/
theorem getCurrentPriorityChecked_ok_eq_getCurrentPriority
    (st : SystemState) (tcb : TCB) (p : SeLe4n.Priority)
    (hOk : getCurrentPriorityChecked st tcb = .ok p) :
    getCurrentPriority st tcb = p := by
  cases hb : tcb.schedContextBinding with
  | unbound =>
    -- no priority source: both readers take `tcb.priority`
    simp only [getCurrentPriorityChecked, getCurrentPriority,
      SystemState.threadBasePriority, hb,
      SchedContextBinding.ownScId?] at hOk ⊢
    exact Except.ok.inj hOk
  | donated scId owner =>
    -- WS-OD (v0.35.3): likewise — a donee's priority is its own, so this arm
    -- consults no object store and cannot error.
    simp only [getCurrentPriorityChecked, getCurrentPriority,
      SystemState.threadBasePriority, hb,
      SchedContextBinding.ownScId?] at hOk ⊢
    exact Except.ok.inj hOk
  | bound scId =>
    cases hSc : st.getSchedContext? scId with
    | none =>
      simp only [getCurrentPriorityChecked, hb,
        SchedContextBinding.ownScId?, hSc] at hOk
      cases hOk
    | some sc =>
      simp only [getCurrentPriorityChecked, getCurrentPriority,
        SystemState.threadBasePriority, hb,
        SchedContextBinding.ownScId?, hSc] at hOk ⊢
      exact Except.ok.inj hOk

/-- WS-OD (v0.35.3): the checked reader cannot fail on a **donated** thread —
its priority is its own, so there is no lookup left to miss.  Before the split
a donee whose donor's SchedContext had been retyped away read
`.error .objectNotFound` from a syscall that had nothing to do with that
object. -/
@[simp] theorem getCurrentPriorityChecked_donated (st : SystemState) (tcb : TCB)
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    (h : tcb.schedContextBinding = .donated scId owner) :
    getCurrentPriorityChecked st tcb = .ok tcb.priority := by
  simp [getCurrentPriorityChecked, h]

/-- Helper: update the priority of a thread's **priority source** — the object
`SchedContextBinding.ownScId?` names — and store it.  Returns the
updated state.

**WS-OD (v0.35.3) — the write follows the read, and a donee's priority is its
own.**  A `.donated` thread's priority now lands in **its own TCB**, not in the
donor's SchedContext.  Writing the reservation was an authority crossing: the
donor's scheduling context is the *client's* object, and
`.tcbSetPriority` / `.tcbSetMCPriority` are authorised by a TCB write
capability on the **target** plus the caller's MCP headroom — neither of which
says anything about the client.  A caller holding a TCB capability on a passive
server could therefore retune the priority of every client that had called it,
and the effect outlived the call: `returnDonatedSchedContext` hands the
reservation back with the rewritten field, so the client resumed at a band it
never asked for.  Reachable at call depth 1 and, since the donation chain
became transitive, at every depth.  Registered in
`docs/REGISTERED_DEBT.md` §C and closed here.

Writing the TCB is also the only spelling that makes the syscall *work*: with
the read split (`SystemState.threadBasePriority`) a write to the donor's
reservation would no longer be observed by the scheduler at all, so a
`.tcbSetPriority` on a donee would silently do nothing while corrupting an
unrelated object.

**Invariant dependency**: for a `.bound` thread, requires
`schedContextBindingConsistent` to guarantee the SchedContext exists.
If it does not (invariant violation), the function defensively returns
the state unchanged. This no-op path is dead code when invariants hold.

**Both arms are the typed in-place rewrite** (`v0.35.71`): the reservation
through `SystemState.updateSchedContext`, whose identity-on-absent arm *is*
the defensive no-op above, and the thread through `SystemState.updateTcb`.
The record handed in classifies the binding; the write rewrites the record
the store holds, so a caller that resolved `tcb` at an earlier state cannot
write a stale copy of it back. -/
def updatePrioritySource (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (newPriority : SeLe4n.Priority) : SystemState :=
  match tcb.schedContextBinding.ownScId? with
  | some scId =>
    -- `.bound`: the base priority is the TCB's, and the reservation carries the
    -- band it was configured to; this writes both.
    --
    -- **WS-RR (`v0.35.133`): do not read the SchedContext write as redundant.**
    -- Until that cut `SystemState.threadBasePriority` read `sc.priority` here
    -- while `TCB.boostedPriority` -- the bucket every run-queue *insert* is keyed
    -- by (`enqueueRunnableOnCore`, `preemptCurrentOnCore`) -- read `tcb.priority`,
    -- so the two writes were the two halves of one base.  With one home the TCB
    -- write is what changes the thread's band and the SchedContext write is what
    -- keeps `boundThreadPriorityConsistent` true -- the statement that a
    -- reservation's configured band tracks its bound thread's.  Dropping it would
    -- leave the mirror stale at the old value for the next `schedContextBind` of
    -- this reservation to propagate back, since that operation writes
    -- `tcb.priority := sc.priority`.  (`schedContextConfigure` writes its
    -- caller's argument to both homes, so it is not a route back; naming it here
    -- was wrong and is corrected at `v0.35.136`.)
    --
    -- `boundThreadPriorityConsistent` is the agreement between them,
    -- `schedContextBind` establishes it and
    -- `schedContextConfigureBoundPropagate` maintains it; until `v0.35.98` this
    -- arm wrote the reservation alone, so the syscall whose entire job is to
    -- change a priority was the one writer that broke it.  Measured on the
    -- live per-core path: `.tcbSetPriority` demoted a bound thread from 50 to
    -- 10, `migrateRunQueueBucketOnCore` re-bucketed it at 10, and its first
    -- wake re-inserted it at `tcb.boostedPriority` -- **50**, the band the
    -- demotion had just removed -- permanently, since every later wake reads
    -- the same stale field.  A demotion that does not stick is a
    -- temporal-isolation break in the mixed-criticality deployments MCS exists
    -- for; a promotion that does not stick is the latency failure in the other
    -- direction.
    --
    -- The SchedContext first and the thread second, mirroring
    -- `schedContextBind`'s order, so the two establish the same agreement the
    -- same way round.  Each half is an identity where its object is absent, so
    -- the arm is total and a dangling `.bound` (an invariant violation) still
    -- gets the TCB write rather than being silently dropped whole.
    (st.updateSchedContext scId fun sc => { sc with priority := newPriority }).updateTcb tid
      fun t => { t with priority := newPriority }
  | none =>
    -- `.unbound` and `.donated`: the thread's own TCB, which is its only home.
    st.updateTcb tid fun t => { t with priority := newPriority }

/-- **The frame belongs to the write** (`v0.35.98`).  `updatePrioritySource`
moves objects and nothing else, at either binding — stated once here rather than
re-derived per field, because the `.bound` arm became a *pair* of writes in this
cut and six consumers were each running their own two-branch case analysis over
its shape.  Every `_scheduler_eq` / `_lifecycle_eq` / … transport lemma in
`SchedContext/Invariant/PriorityPreservation.lean` is now one application of
this, so a third write added to either arm costs them nothing. -/
theorem updatePrioritySource_only_modifies_objects
    (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (newPriority : SeLe4n.Priority) :
    ∃ objects', updatePrioritySource st tid tcb newPriority
      = { st with objects := objects' } := by
  unfold updatePrioritySource
  split
  · rw [SystemState.updateTcb_eq_objects_update,
      SystemState.updateSchedContext_eq_objects_update]
    exact ⟨_, rfl⟩
  · rw [SystemState.updateTcb_eq_objects_update]
    exact ⟨_, rfl⟩

/-- WS-OD (v0.35.3): the payoff — a priority update on a **donated** thread
writes that thread's own TCB and nothing else, so the donor's reservation is
untouched.  Stated as an exact equation on the resulting state rather than as
an inequality about the SchedContext, because "does not write object `X`" is
satisfied by an operation that writes object `Y` instead and this says *which*
object is written. -/
theorem updatePrioritySource_donated (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (newPriority : SeLe4n.Priority)
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    (h : tcb.schedContextBinding = .donated scId owner)
    (hTcb : st.getTcb? tid = some tcb) :
    updatePrioritySource st tid tcb newPriority =
      { st with objects :=
          st.objects.insert tid.toObjId (.tcb { tcb with priority := newPriority }) } := by
  unfold updatePrioritySource
  rw [show tcb.schedContextBinding.ownScId? = none by simp [h]]
  exact SystemState.updateTcb_eq_of_some hTcb _

/-- WS-OD (v0.35.3): the security statement, in the form the finding was
reported in — a priority update on a donee leaves the **donor's** scheduling
context byte-for-byte unchanged.  Requires only `invExt` on the object store
(`v0.35.71`): the typed rewrite fires only at a key holding a TCB, so it can
reach no SchedContext at any key — the key-distinctness hypothesis the raw
insert needed (`tid.toObjId ≠ scId.toObjId`, which `objectIndexBounded` gave on
a reachable state) is gone, and with it the one way this statement could have
been vacuous. -/
theorem updatePrioritySource_donated_preserves_donor_schedContext
    (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) (newPriority : SeLe4n.Priority)
    {scId : SeLe4n.SchedContextId} {owner : SeLe4n.ThreadId}
    (h : tcb.schedContextBinding = .donated scId owner)
    (hExt : st.objects.invExt) :
    (updatePrioritySource st tid tcb newPriority).getSchedContext? scId =
      st.getSchedContext? scId := by
  unfold updatePrioritySource
  rw [show tcb.schedContextBinding.ownScId? = none by simp [h]]
  exact SystemState.updateTcb_getSchedContext? st tid _ hExt scId

/-- Helper: if a thread is in the run queue, remove it and re-insert at
the effective priority (new base priority with PIP boost applied). This
maintains correct run queue bucket placement.

AI3-B (M-22): The insertion priority accounts for PIP boost. When a thread
has an active `pipBoost`, the RunQueue placement uses
`max(newPriority, pipBoost)` to ensure PIP-boosted threads retain elevated
scheduling band after priority changes. Without this, a `setPriorityOp` on
a PIP-boosted thread would drop it to the new base priority, causing
priority inversion for the entire blocking chain. -/
def migrateRunQueueBucketOnCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (newPriority : SeLe4n.Priority) (homeCore : Concurrency.CoreId) : SystemState :=
  if tid ∈ (st.scheduler.runQueueOnCore homeCore) then
    let rq := (st.scheduler.runQueueOnCore homeCore).remove tid
    -- AI3-B (M-22): Apply PIP boost to new priority.
    -- AK2-J (S-M08): The defensive fallback (TCB missing — unreachable under
    -- `runnableThreadsAreTCBs`) now takes the max of `newPriority` and the
    -- RunQueue's cached priority for `tid`. Any PIP boost previously recorded
    -- in the RunQueue is therefore preserved rather than silently erased.
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    -- `Priority.raisedBy` (`Prelude.lean`) is the one reading of "a base raised
    -- by an inherited boost"; the base here is the *new* priority rather than
    -- the thread's stored one, which is exactly why the helper takes its base as
    -- a parameter.  The fallback raises by the RunQueue's cached priority, which
    -- carries any boost recorded there, so it is the same question with a
    -- different source for the boost.
    let effectivePrio := match st.getTcb? tid with
      | some tcb => newPriority.raisedBy tcb.pipBoost
      | none =>
        newPriority.raisedBy
          ((st.scheduler.runQueueOnCore homeCore).threadPriority[tid]?)
    let rq := rq.insert tid effectivePrio
    { st with scheduler := st.scheduler.setRunQueueOnCore homeCore rq }
  else
    st

/-- D2-E / WS-SM SM8.B: the boot-core instance, kept as the name the pre-SMP
single-core proof surface uses.  Definitionally `migrateRunQueueBucketOnCore …
bootCoreId`, so every existing statement about it is unchanged. -/
def migrateRunQueueBucket (st : SystemState) (tid : SeLe4n.ThreadId)
    (newPriority : SeLe4n.Priority) : SystemState :=
  migrateRunQueueBucketOnCore st tid newPriority bootCoreId

/-- WS-SM SM8.B: the bridge, `rfl`. -/
@[simp] theorem migrateRunQueueBucket_eq_onCore (st : SystemState) (tid : SeLe4n.ThreadId)
    (newPriority : SeLe4n.Priority) :
    migrateRunQueueBucket st tid newPriority
      = migrateRunQueueBucketOnCore st tid newPriority bootCoreId := rfl

/-- D2-E: Set the scheduling priority of a target thread.

Sequence:
1. Look up caller TCB, validate MCP authority
2. Look up target TCB
3. Update priority on SchedContext (if bound) or TCB (if unbound)
4. If target is in run queue, perform bucket migration (remove + re-insert)
5. If target is current and priority decreased, trigger reschedule

Returns `invalidArgument` if caller or target is not a TCB.
Returns `illegalAuthority` if `newPriority > caller.maxControlledPriority`.

**AL8 (WS-AL / AK7-E.cascade) — Type-level validity discipline**: both
`callerTid` and `targetTid` have type `ValidThreadId`. The Lean type
system forbids any caller from feeding `ThreadId.sentinel` for either
argument. Uses `vCallerTid.val` / `vTargetTid.val` directly in the body
so `split at` tactics in preservation proofs work cleanly. -/
def setPriorityOp (st : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newPriority : SeLe4n.Priority) : Except KernelError SystemState :=
  -- E1: Caller TCB lookup + MCP authority check
  -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration. Both
  -- original `_ => .error .invalidArgument` arms collapsed wrong-variant
  -- and absent into the same error code, so migration is
  -- semantics-preserving.
  match st.getTcb? vCallerTid.val with
  | some callerTcb =>
    match validatePriorityAuthority callerTcb newPriority with
    | .error e => .error e
    | .ok () =>
      -- E2: Target TCB lookup
      match st.getTcb? vTargetTid.val with
      | some targetTcb =>
        -- E3: Update priority source (SchedContext or TCB)
        let oldPriority := getCurrentPriority st targetTcb
        let st := updatePrioritySource st vTargetTid.val targetTcb newPriority
        -- E4: Run queue bucket migration
        let st := migrateRunQueueBucket st vTargetTid.val newPriority
        -- E5: Conditional preemption check
        -- If target is current and priority decreased, reschedule
        if (st.scheduler.currentOnCore bootCoreId) == some vTargetTid.val &&
           newPriority.val < oldPriority.val then
          match schedule st with
          | .ok ((), st') => .ok st'
          | .error e => .error e
        else
          .ok st
      | none => .error .invalidArgument
  | none => .error .invalidArgument

-- ============================================================================
-- D2-F: setMCPriorityOp
-- ============================================================================

/-- D2-F: Set the Maximum Controlled Priority (MCP) of a target thread.

The MCP ceiling determines the maximum priority a thread can assign to
other threads (or itself). Reducing MCP may retroactively cap the thread's
current priority (seL4 behavior).

Sequence:
1. Look up caller TCB, validate `newMCP ≤ caller.maxControlledPriority`
2. Look up target TCB, update `maxControlledPriority := newMCP`
3. If target's current priority exceeds new MCP, cap it to MCP
4. If priority was capped and target is in run queue, perform bucket migration

Returns `invalidArgument` if caller or target is not a TCB.
Returns `illegalAuthority` if `newMCP > caller.maxControlledPriority`.

**AL8 (WS-AL / AK7-E.cascade)**: `callerTid` / `targetTid` are
`ValidThreadId` for compile-time sentinel rejection. -/
def setMCPriorityOp (st : SystemState) (vCallerTid vTargetTid : SeLe4n.ValidThreadId)
    (newMCP : SeLe4n.Priority) : Except KernelError SystemState :=
  -- F1: Caller MCP authority validation (reuses validatePriorityAuthority for consistency)
  -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration. Both
  -- original `_ => .error .invalidArgument` arms collapsed wrong-variant
  -- and absent into the same error code, so migration is
  -- semantics-preserving.
  match st.getTcb? vCallerTid.val with
  | some callerTcb =>
    match validatePriorityAuthority callerTcb newMCP with
    | .error e => .error e
    | .ok () =>
      -- F2: Target TCB lookup + MCP update
      match st.getTcbWitnessed? vTargetTid.val with
      | some ⟨targetTcb, hTarget⟩ =>
        let targetTcb' := { targetTcb with maxControlledPriority := newMCP }
        -- `v0.35.71`: the looked-up record is read again below (the capping
        -- rule and the priority-source update), so the lookup is the witnessed
        -- one and the ceiling write is the typed rewrite under its proof.
        let st := st.rewriteObject vTargetTid.val.toObjId (.tcb targetTcb')
          (SystemState.rewriteAdmissible_tcb hTarget targetTcb')
        -- F3: Priority capping — if current priority exceeds new MCP, cap it
        let currentPrio := getCurrentPriority st targetTcb'
        if currentPrio.val > newMCP.val then
          -- Cap priority to MCP ceiling
          let st := updatePrioritySource st vTargetTid.val targetTcb' newMCP
          -- F4: Run queue migration + preemption check for capped priority
          let st := migrateRunQueueBucket st vTargetTid.val newMCP
          if (st.scheduler.currentOnCore bootCoreId) == some vTargetTid.val then
            match schedule st with
            | .ok ((), st') => .ok st'
            | .error e => .error e
          else
            .ok st
        else
          .ok st
      | none => .error .invalidArgument
  | none => .error .invalidArgument

end SeLe4n.Kernel.SchedContext.PriorityManagement
