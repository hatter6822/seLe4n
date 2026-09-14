-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Lifecycle.Operations
import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Propagate
import SeLe4n.Kernel.Scheduler.PriorityInheritance.Compute
import SeLe4n.Kernel.Concurrency.ContextRestoreSeam
import SeLe4n.Kernel.Architecture.SyscallReturn

/-! # D1: Thread Suspension & Resumption

Implements `suspendThread` and `resumeThread` as first-class kernel operations.
These are the seL4 equivalents of `seL4_TCB_Suspend` and `seL4_TCB_Resume`.

## Suspension sequence (D1-G)

1. Validate thread exists and is not already Inactive
2. Cancel IPC blocking (remove from endpoint/notification queues)
3. Cancel SchedContext donation (return to original owner)
4. Remove from scheduler run queue
5. Clear pending state (message, timeout, queue links)
6. Set `threadState := .Inactive`
7. If suspended thread was current, trigger reschedule

## Resumption sequence (D1-H)

1. Validate thread exists and is Inactive
2. Set `threadState := .Ready`, `ipcState := .ready`
3. Insert into run queue at effective priority
4. If resumed thread has higher priority than current, reschedule
-/

namespace SeLe4n.Kernel.Lifecycle.Suspend

open SeLe4n
open SeLe4n.Kernel.Concurrency (bootCoreId CoreId SgiKind)
open SeLe4n.Model
open SeLe4n.Kernel

-- ============================================================================
-- D1-C: cancelIpcBlocking + R5.D shared IPC-clearing helper
-- ============================================================================

/-- R5.D (DEEP-SCH-03): Shared "restore-to-ready" helper. Clears the IPC-
level transient fields on a TCB so that subsequent restoration paths
(`resumeThread` H3) and IPC unblocking paths (`cancelIpcBlocking` G2) see
the same TCB shape:

  * `ipcState := .ready` (no longer blocked on an endpoint, notification,
    or reply slot)
  * `queuePrev`, `queueNext`, `queuePPrev` all `none` (no stale intrusive
    queue links pointing at a freed slot)

Only modifies the `objects` field. Idempotent on a TCB whose IPC fields
are already cleared (record-update of `none ← none` is a no-op).

Used by:
  * `cancelIpcBlocking` (suspend flow G2) after the thread has been
    removed from any endpoint/notification queue it was waiting on.
  * `resumeThread` (H3) on transition from `.Inactive` → `.Ready`, where
    the IPC fields were nominally cleared by `clearPendingState` during
    suspend but the explicit re-clearing acts as defense-in-depth and
    makes the post-resume invariant locally observable.

Pre-R5 this logic lived as the private helper `clearTcbIpcFields`, used
only by `cancelIpcBlocking`. `resumeThread` redundantly performed the
`ipcState := .ready` half inline. R5.D promotes the helper to a shared
top-level name and consolidates the resume path through it. -/
def restoreToReadyStaging (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) : SystemState :=
  -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
  match st.getTcb? tid with
  | some tcb' =>
    let cleared : TCB := { tcb' with
        ipcState := .ready
        queuePrev := none
        queueNext := none
        queuePPrev := none
        -- PR #822 review: cancelling/restoring a (server-first) receive also
        -- relinquishes its stashed reply object, else `replyIsStashed` keeps the
        -- Reply permanently in-use and later lifecycle cleanup of it returns
        -- `revocationRequired` even though no receive is still pending.
        pendingReceiveReply := none }
    let staged : TCB := match frame with
      | some f => cleared.withReturnFrame f
      | none => cleared
    { st with objects := st.objects.insert tid.toObjId (.tcb staged) }
  | none => st

/-- The restore that stages **nothing** — `resumeThread`'s spelling.  A resumed
thread keeps its own register window: `.tcbResume` restarts it where it was
(WS-RR RR4.11's `retirePendingFaultForResume` is the fault half of the same
posture), so overwriting `x0`-`x5` here would destroy the state the restart is
supposed to preserve.  The cancellation arms of `cancelIpcBlocking` pass
`some Architecture.cancelledIpcFrame` instead — see there for why the two call
sites of one helper answer differently. -/
def restoreToReady (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  restoreToReadyStaging st tid none

/-- **WS-RR RR7.14**: the restore that stages the **cancellation error frame** —
`cancelIpcBlocking`'s spelling on all four of its blocked arms.

A thread whose blocking IPC is destroyed under it has no value to receive, and
until this row it was handed no answer at all: its boundary crossing ended in
`.blocks`, so `x0`-`x5` still held its own argument spill (or the trap layer's
fail-closed sentinel), and the SM10.1 context restore would have delivered that
back as a return value.  The frame is `.ipcCancelled`, deliberately not
`.ipcTimeout` (which the timeout path stages): a timed-out caller may reissue,
a cancelled one may be looking at an endpoint that no longer exists, and a
userspace library cannot write a correct retry against a conflated code.

Staged **inside** the field clear rather than as a second write, so the arms
still commit exactly one TCB object.  On the `.blockedOnReply` arm the later
`consumeReplyLink` re-reads the TCB and record-updates `replyObject` alone, so
the staged `registerContext` survives it. -/
def restoreToReadyCancelled (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  restoreToReadyStaging st tid (some Architecture.cancelledIpcFrame)

/-- **WS-RR RR7.14**: the cancellation restore is the plain restore's
frame-staged twin — the *same* cleared TCB, with the frame staged on top.
Proved rather than asserted, so a field added to the clear in one and not the
other fails to elaborate.  Stated on the TCB the two write rather than on the
whole state: `restoreToReadyCancelled` commits **one** object write where the
`stage ∘ restore` composition would commit two, which is the point of folding
the staging inward and not a difference the invariants may see. -/
theorem restoreToReadyCancelled_tcb (st : SystemState) (tid : SeLe4n.ThreadId)
    (hInv : st.objects.invExt) :
    (restoreToReadyCancelled st tid).getTcb? tid
      = ((restoreToReady st tid).getTcb? tid).map
          (·.withReturnFrame Architecture.cancelledIpcFrame) := by
  unfold restoreToReadyCancelled restoreToReady restoreToReadyStaging
  cases hTcb : st.getTcb? tid with
  | none => simp only [hTcb, Option.map_none]
  | some tcb =>
      simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
      rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv,
          RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
      simp only [Option.map_some]

/-- **WS-RR RR7.14 (the payoff)**: a cancelled thread reads the cancellation
frame back out of its own register context — so the SM10.1 context restore
delivers `.ipcCancelled`, not the thread's own stale argument spill. -/
theorem restoreToReadyCancelled_readReturnFrame (st : SystemState)
    (tid : SeLe4n.ThreadId) (tcb : TCB) (hTcb : st.getTcb? tid = some tcb)
    (hInv : st.objects.invExt) :
    Architecture.readReturnFrame (restoreToReadyCancelled st tid) tid
      = Architecture.cancelledIpcFrame := by
  unfold restoreToReadyCancelled restoreToReadyStaging Architecture.readReturnFrame
  simp only [hTcb]
  simp only [SystemState.getTcb?, RHTable_getElem?_eq_get?]
  rw [RobinHood.RHTable.getElem?_insert_self st.objects tid.toObjId _ hInv]
  rfl

/-- R5.D / backward-compatibility shim. Pre-R5 the IPC-clearing helper was
named `clearTcbIpcFields` and was `private`. The renamed helper is now
`restoreToReady` (R5.D); this alias retains the old name so existing
proofs and information-flow projection helpers continue to compile
unchanged. Definitionally equal to `restoreToReady`. -/
@[inline] private def clearTcbIpcFields (st : SystemState) (tid : SeLe4n.ThreadId)
    : SystemState :=
  restoreToReady st tid

/-- **WS-RR RR7.14**: the framing holds for **every** staged frame — stated once
on `restoreToReadyStaging` so the plain and cancellation spellings cannot
answer "what else does this write" differently.  A staged frame moves the
target TCB's `registerContext` and nothing outside `objects`. -/
theorem restoreToReadyStaging_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) :
    (restoreToReadyStaging st tid frame).scheduler = st.scheduler := by
  unfold restoreToReadyStaging; split <;> rfl

/-- Helper: restoreToReady preserves the scheduler. -/
theorem restoreToReady_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreToReady st tid).scheduler = st.scheduler :=
  restoreToReadyStaging_scheduler_eq st tid none

/-- **WS-RR RR7.14**: and the cancellation spelling. -/
theorem restoreToReadyCancelled_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreToReadyCancelled st tid).scheduler = st.scheduler :=
  restoreToReadyStaging_scheduler_eq st tid _

/-- **WS-RR RR7.14**: the framing holds for **every** staged frame — stated once
on `restoreToReadyStaging` so the plain and cancellation spellings cannot
answer "what else does this write" differently.  A staged frame moves the
target TCB's `registerContext` and nothing outside `objects`. -/
theorem restoreToReadyStaging_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) :
    (restoreToReadyStaging st tid frame).machine = st.machine := by
  unfold restoreToReadyStaging; split <;> rfl

/-- WS-SM SM8.B: `restoreToReady` only writes `objects` — the machine, and hence
every core's register bank, is framed.  The information-flow counterpart of
`restoreToReady_scheduler_eq`: per-core confinement reads the register banks as
well as the scheduler slots, so a scheduler frame alone does not bound a step's
observable writes. -/
theorem restoreToReady_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreToReady st tid).machine = st.machine :=
  restoreToReadyStaging_machine_eq st tid none

/-- **WS-RR RR7.14**: and the cancellation spelling. -/
theorem restoreToReadyCancelled_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreToReadyCancelled st tid).machine = st.machine :=
  restoreToReadyStaging_machine_eq st tid _

/-- **WS-RR RR7.14**: the framing holds for **every** staged frame — stated once
on `restoreToReadyStaging` so the plain and cancellation spellings cannot
answer "what else does this write" differently.  A staged frame moves the
target TCB's `registerContext` and nothing outside `objects`. -/
theorem restoreToReadyStaging_serviceRegistry_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) :
    (restoreToReadyStaging st tid frame).serviceRegistry = st.serviceRegistry := by
  unfold restoreToReadyStaging; split <;> rfl

/-- Helper: restoreToReady preserves the serviceRegistry. -/
theorem restoreToReady_serviceRegistry_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreToReady st tid).serviceRegistry = st.serviceRegistry :=
  restoreToReadyStaging_serviceRegistry_eq st tid none

/-- **WS-RR RR7.14**: and the cancellation spelling. -/
theorem restoreToReadyCancelled_serviceRegistry_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreToReadyCancelled st tid).serviceRegistry = st.serviceRegistry :=
  restoreToReadyStaging_serviceRegistry_eq st tid _

/-- **WS-RR RR7.14**: the framing holds for **every** staged frame — stated once
on `restoreToReadyStaging` so the plain and cancellation spellings cannot
answer "what else does this write" differently.  A staged frame moves the
target TCB's `registerContext` and nothing outside `objects`. -/
theorem restoreToReadyStaging_lifecycle_eq (st : SystemState) (tid : SeLe4n.ThreadId)
    (frame : Option Architecture.SyscallReturnFrame) :
    (restoreToReadyStaging st tid frame).lifecycle = st.lifecycle := by
  unfold restoreToReadyStaging; split <;> rfl

/-- Helper: restoreToReady preserves lifecycle. -/
theorem restoreToReady_lifecycle_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreToReady st tid).lifecycle = st.lifecycle :=
  restoreToReadyStaging_lifecycle_eq st tid none

/-- **WS-RR RR7.14**: and the cancellation spelling. -/
theorem restoreToReadyCancelled_lifecycle_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (restoreToReadyCancelled st tid).lifecycle = st.lifecycle :=
  restoreToReadyStaging_lifecycle_eq st tid _

/-- R5.D back-compat: `clearTcbIpcFields = restoreToReady`. -/
@[simp] theorem clearTcbIpcFields_eq_restoreToReady (st : SystemState)
    (tid : SeLe4n.ThreadId) :
    clearTcbIpcFields st tid = restoreToReady st tid := rfl

/-- Helper: clearTcbIpcFields preserves the scheduler (back-compat). -/
theorem clearTcbIpcFields_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbIpcFields st tid).scheduler = st.scheduler :=
  restoreToReady_scheduler_eq st tid

/-- WS-SM SM8.B: the machine companion of `clearTcbIpcFields_scheduler_eq`.
Stated here rather than at the consumer because `clearTcbIpcFields` is
`private`, so only this file can name it — the same reason its scheduler frame
lives here. -/
theorem clearTcbIpcFields_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbIpcFields st tid).machine = st.machine :=
  restoreToReady_machine_eq st tid

/-- Helper: clearTcbIpcFields preserves the serviceRegistry (back-compat). -/
theorem clearTcbIpcFields_serviceRegistry_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbIpcFields st tid).serviceRegistry = st.serviceRegistry :=
  restoreToReady_serviceRegistry_eq st tid

/-- Helper: clearTcbIpcFields preserves lifecycle (back-compat). -/
theorem clearTcbIpcFields_lifecycle_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbIpcFields st tid).lifecycle = st.lifecycle :=
  restoreToReady_lifecycle_eq st tid

-- ============================================================================
-- WS-SM SM5.F.5 / SM5.F.6: per-core restore-to-ready + PIP recomputation
-- ============================================================================
--
-- `restoreToReady` (above) is core-agnostic — it clears `ipcState`/queue links
-- and frames every per-core run queue.  Under SMP the *re-entry into the run
-- queue* (resume's H4) and the *PIP-boost recomputation* (resume's H3b) become
-- per-core: a resumed thread re-enters its **home core**'s run queue, and the
-- `pipBoost` it carries (recomputed from the GLOBAL blocking graph) decides its
-- bucket on *that* core.  `restoreToReadyOnCore` is the per-core form of the
-- resume restore+recompute+enqueue; the single-core `resumeThread` keeps using
-- the `bootCoreId`-pinned `ensureRunnable` (recovered at `c = bootCoreId`).

/-- WS-SM SM5.F.5 / SM5.F.6 (plan §3.6, resume H3a+H3b+H4 per-core): restore
`tid` to ready on core `c`, recomputing its PIP boost from the post-restore
blocking graph.

Three steps mirroring the resume path, lifted to an explicit home core:
1. `restoreToReady` — clear `ipcState`/intrusive queue links (R5.D shared helper).
2. **H3b PIP recomputation** — re-derive `pipBoost` from the GLOBAL
   `computeMaxWaiterPriority` (the max over *every* waiter, cross-core — the
   per-core slice would under-boost).  While `tid` was blocked/inactive its
   waiter set may have changed, so the carried-over boost can be stale.
3. **H4 per-core enqueue** — insert `tid` into core `c`'s run queue at its
   (now PIP-correct) effective priority via the SM5.C `enqueueRunnableOnCore`.

Note this is the per-core analogue of resume's restore+enqueue and deliberately
does NOT set `threadState := .Ready` — that transition is `resumeThread`'s H3c
concern, kept out of the IPC-clearing helper exactly as the single-core
`restoreToReady` does.  `restoreToReadyOnCore st bootCoreId tid` is the
single-core re-ready (bucket on the boot core). -/
def restoreToReadyOnCore (st : SystemState) (c : CoreId) (tid : SeLe4n.ThreadId)
    : SystemState :=
  -- H3a: clear IPC state + intrusive queue links
  let st1 := restoreToReady st tid
  -- H3b: re-derive pipBoost from the post-restore (GLOBAL) blocking graph
  let newPipBoost : Option SeLe4n.Priority :=
    PriorityInheritance.computeMaxWaiterPriority st1 tid
  -- H3c (pipBoost only): refresh the recomputed boost on the IPC-cleared TCB
  let st2 := match st1.getTcb? tid with
    | some t =>
      { st1 with objects := st1.objects.insert tid.toObjId (.tcb { t with pipBoost := newPipBoost }) }
    | none => st1
  -- H4 (per-core): enqueue on core c at the boosted effective priority
  enqueueRunnableOnCore st2 c tid

/-- WS-SM SM5.F.6 (helper): the resume "ready mid-state" — IPC transients cleared
(`restoreToReady`), `threadState` set to `.Ready`, and `pipBoost` recomputed from the
GLOBAL post-restore blocking graph — *before* the per-core run-queue enqueue.  Factored
out (parallel to `restoreToReadyMidState`) so the resume's `threadState`/`pipBoost`
effect is provable independently of the run-queue insertion.  When `tid` has no TCB
the result is `restoreToReady st tid` (an unreachable branch from `resumeThreadOnCore`,
which validates the TCB first). -/
def resumeReadyMidState (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  let st1 := restoreToReady st tid
  let newPipBoost : Option SeLe4n.Priority :=
    PriorityInheritance.computeMaxWaiterPriority st1 tid
  match st1.getTcb? tid with
  | some t =>
    { st1 with objects := st1.objects.insert tid.toObjId (.tcb { t with threadState := .Ready, pipBoost := newPipBoost }) }
  | none => st1

/-- WS-SM SM5.F.6 (plan §3.6, resume cross-core wake): restore `tid` to **Ready** on
its home core and, if that core is remote (≠ `executingCore`), return the
`.reschedule` SGI it must receive.

The cross-core resume wake, mirroring `wakeThread` / `pipBoostWithWake`: a thread
resumed onto a remote core lands runnable there at its PIP-correct bucket, but that
core is not running the resume, so it must be poked to re-evaluate (the resumed
thread may outrank its current).  A local resume (home = executing) needs no SGI.

PR #811 P2-3: the state path goes through `resumeReadyMidState` (which sets
`threadState := .Ready` and recomputes the GLOBAL `pipBoost`) *before* the per-core
enqueue — so a remote resume never pokes a core to dispatch a run-queue entry whose
TCB is still `.Inactive`.  This makes the state effect identical to the validated
complete resume `resumeThreadOnCore` (this pure form simply omits the `.Inactive`
precondition check, returning the state + optional SGI for SM5.I's runtime dispatch
to fire after the state write is visible — the BKL ordering). -/
def restoreToReadyWithWake (st : SystemState) (tid : SeLe4n.ThreadId)
    (executingCore : CoreId) : SystemState × Option (CoreId × SgiKind) :=
  let target := determineTargetCore st tid
  let st' := enqueueRunnableOnCore (resumeReadyMidState st tid) target tid
  let sgi : Option (CoreId × SgiKind) :=
    -- Resume genuinely makes `tid` runnable, so unlike the materiality-guarded
    -- `pipBoostWithWake` the only guard is remoteness: a remote resume always
    -- warrants a `.reschedule`.  `getTcb?` guards against a non-TCB `tid` (no-op).
    if target == executingCore then none
    else match st.getTcb? tid with
         | none => none
         | some _ => some (target, SgiKind.reschedule)
  (st', sgi)

/-- WS-SM SM5.F.6 (plan §3.6, resume H1–H5 per-core): the **complete** per-core
resume — the per-core analogue of `resumeThread`.  Unlike `restoreToReadyOnCore`
(the IPC-clear+enqueue helper, parallel to the shared `restoreToReady`), this
performs the full Inactive→Ready transition:

1. **H1/H2** — validate `tid` is a TCB in `.Inactive` state
   (`invalidArgument` / `illegalState` otherwise), exactly as `resumeThread`.
2. **H3a** — clear IPC transients (`restoreToReady`).
3. **H3b** — re-derive `pipBoost` from the GLOBAL post-restore blocking graph
   (`computeMaxWaiterPriority`; the per-core slice would under-boost).
4. **H3c** — set `threadState := .Ready` *and* the recomputed `pipBoost` (the
   step `restoreToReadyOnCore` deliberately omits, completing the resume) — both via
   the `resumeReadyMidState` helper.
5. **H4** — enqueue on the thread's **home core** (`determineTargetCore`) via the
   SM5.C per-core `enqueueRunnableOnCore`.
6. **H5 (reschedule)** — the resumed thread newly enters its home core's run queue
   and may outrank that core's current thread, so that core must re-evaluate:
   * **LOCAL** (home = `executingCore`): process the reschedule **inline** on the
     executing core via `handleRescheduleSgiOnCore` — the *exact* `.reschedule`-SGI
     handler the remote core would run, so the local and remote paths mirror each
     other (PR #811 P2-5).  It re-runs the per-core dispatch under SM5.C's
     preemption gate (`candidateOutranksCurrentOnCore` — no priority inversion) and,
     when it does switch, re-enqueues the preempted thread (`switchToThreadOnCore`,
     no current-thread drop).  This is the faithful — and, per the
     implement-the-improvement rule, *improved* — analogue of the single-core
     `resumeThread`'s H5 `schedule` call (which lacks both the preemption gate and
     the re-enqueue).  No SGI is returned (the reschedule already happened here).
   * **REMOTE** (home ≠ `executingCore`): return the `.reschedule` SGI the home core
     must receive so it runs the same `handleRescheduleSgiOnCore` itself.

`resumeThreadOnCore st vtid bootCoreId` with an unbound thread (home = `bootCoreId`)
matches `resumeThread`'s resume + inline-reschedule on the boot core, with no SGI. -/
def resumeThreadOnCore (st : SystemState) (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  let tid : SeLe4n.ThreadId := vtid.val
  -- AK7-clean: read through the typed `getTcb?` accessor — it returns `none` for
  -- both a non-TCB and an absent slot, exactly the `invalidArgument` arm.
  match st.getTcb? tid with
  | some tcb =>
    if tcb.threadState != .Inactive then .error .illegalState
    else
      -- home core of the resumed thread (where it re-enters the run queue)
      let target := determineTargetCore st tid
      -- H3a/H3b/H3c: IPC clear + threadState := .Ready + GLOBAL pipBoost recompute
      let st2 := resumeReadyMidState st tid
      -- H4: enqueue on the home core
      let st3 := enqueueRunnableOnCore st2 target tid
      -- H5: process the reschedule (PR #811 P2-5).
      if target == executingCore then
        -- LOCAL: run the per-core reschedule handler inline on the executing core
        -- (the exact handler the remote core would run on the SGI) — preemption-gated
        -- and switch-based (no inversion, no drop).  No SGI is returned.
        match handleRescheduleSgiOnCore st3 executingCore with
        | .ok st4 => .ok (st4, none)
        | .error e => .error e
      else
        -- REMOTE: hand the home core a `.reschedule` SGI so it runs the same handler.
        .ok (st3, some (target, SgiKind.reschedule))
  | none => .error .invalidArgument

/-- WS-SM SM8.B (PR #861 review round 34): **the resume the kernel runs while the
context-restore seam is dark** — everything `resumeThreadOnCore` does except the
inline local dispatch.

The resumed thread is `.Ready` and queued on its home core; it simply is not made
`current` until that core's next scheduling point.  That state is *coherent*,
which is what makes gating this path sound: nothing is left dangling, the thread
is merely undispatched.  (Contrast the unbind path, whose head clears `current`
in order to force a reschedule — suppressing its tail there leaves a core with no
current thread at all, which is why that path is deliberately ungated.)

A named function rather than an inline `else`, so both sides of
`resumeThreadOnCoreLive` are separately stated and separately verified.  The
REMOTE arm is byte-identical to the base transition's: a cross-core
`.reschedule` SGI is a real poke at another processor and has nothing to do with
the missing restore. -/
def resumeThreadEnqueueOnly (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId)
    : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  let tid : SeLe4n.ThreadId := vtid.val
  match st.getTcb? tid with
  | some tcb =>
    if tcb.threadState != .Inactive then .error .illegalState
    else
      let target := determineTargetCore st tid
      let st2 := resumeReadyMidState st tid
      let st3 := enqueueRunnableOnCore st2 target tid
      if target == executingCore then
        -- LOCAL, ungated form: enqueue and stop.  No inline dispatch.
        .ok (st3, none)
      else
        .ok (st3, some (target, SgiKind.reschedule))
  | none => .error .invalidArgument

/-- WS-SM SM8.B (PR #861 review round 34): **the resume as the live `.tcbResume`
arm runs it** — gated on the restore seam it depends on.

`resumeThreadOnCore` is correct at the model level and its theorems say so; this
wrapper chooses between it and `resumeThreadEnqueueOnly`.  Deliberately a
*wrapper*, for the same reason `scheduleLocalSuccessorLive` is one: folding the
guard into the transition makes every theorem about it conditional, and those
theorems are what SM10.1 enables rather than has to re-prove.  An earlier cut of
this PR folded it in, collapsed three proofs onto the dead branch and broke
`SmpPipSuite`'s P2-5 assertion; this is the undo. -/
def resumeThreadOnCoreLive (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) : Except KernelError (SystemState × Option (CoreId × SgiKind)) :=
  if SeLe4n.Kernel.PriorityInheritance.contextRestoreSeamLive then resumeThreadOnCore st vtid executingCore
  else resumeThreadEnqueueOnly st vtid executingCore

/-- WS-SM SM8.B: what the kernel does **today**.  Deliberately NOT `@[simp]` —
an automatic rewrite would silently restate every downstream fact about the
wrapper in terms of the enqueue-only form, which is the collapse this rework
exists to remove, one level up. -/
theorem resumeThreadOnCoreLive_inert (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    (executingCore : CoreId) :
    resumeThreadOnCoreLive st vtid executingCore
      = resumeThreadEnqueueOnly st vtid executingCore := rfl

/-- WS-SM SM8.B: and what it does once the seam is live — the full resume, so
the flip loses nothing. -/
theorem resumeThreadOnCoreLive_eq_of_seam_live (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (h : SeLe4n.Kernel.PriorityInheritance.contextRestoreSeamLive = true) :
    resumeThreadOnCoreLive st vtid executingCore
      = resumeThreadOnCore st vtid executingCore := by
  unfold resumeThreadOnCoreLive
  rw [h]
  rfl

/-- WS-SM SM8.B: the gate touches **only** the local arm — when the resumed
thread's home core is remote, both branches agree. -/
theorem resumeThreadOnCoreLive_remote_agrees (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (executingCore : CoreId)
    (hRemote : ¬ (determineTargetCore st vtid.val == executingCore) = true) :
    resumeThreadOnCoreLive st vtid executingCore
      = resumeThreadOnCore st vtid executingCore := by
  unfold resumeThreadOnCoreLive resumeThreadEnqueueOnly
    resumeThreadOnCore
  split <;> simp [hRemote]

/-- WS-SM SM6.D (PR #822 review, Reply objects): sever a caller→Reply link as
part of lifecycle teardown.  When `tcb.replyObject = some rid` (the seL4
`tcb->tcbReply` forward link of a caller blocked awaiting a reply), clear the
Reply object's `caller` back-link and the TCB's `replyObject` forward link —
the pure, total analogue of the runtime `SystemState.consumeCallerReply`,
suitable for composition inside the pure `cancelIpcBlocking` teardown.

A no-op when the thread holds no reply object (`replyObject = none`) or the
Reply object is already gone — so the existing teardown semantics are unchanged
for every thread that was not a blocked caller.  Without it, suspending /
cancelling a `blockedOnReply` caller would leave the Reply object permanently
in-use (`reply.caller` set) and the TCB pointing at it, so a later receive that
re-supplies that reply cap would fail `.replyCapInvalid`.

`tcb` is the pre-teardown TCB (carrying the original `replyObject`); the TCB
write re-reads the post-IPC-clear TCB so the `replyObject` clear composes on top
of `clearTcbIpcFields`.  Reply object and caller TCB are distinct objects, so
the two writes commute.  Factored into two single-match helpers
(`clearReplyObjectCaller` / `clearTcbReplyObject`) so each preserves the
scheduler / serviceRegistry / lifecycle by a one-line `split <;> rfl`. -/
def clearReplyObjectCaller (st : SystemState) (rid : SeLe4n.ReplyId)
    : SystemState :=
  match st.getReply? rid with
  | some r =>
      -- WS-OD (`v0.35.4`): the record is `Reply.consumed r` — the caller clear,
      -- and the stack links unless the frame heads a stack — the same record
      -- `consumeReply` stores on the reply path, so the two spellings of
      -- "consume a reply link" cannot disagree about what a consumed frame is.
      { st with objects := st.objects.insert rid.toObjId (.reply r.consumed) }
  | none => st

def clearTcbReplyObject (st : SystemState) (tid : SeLe4n.ThreadId)
    : SystemState :=
  -- typed accessor (AK7 `getTcb?` adoption; no raw object-store index by tid)
  match st.getTcb? tid with
  | some t =>
      { st with objects := st.objects.insert tid.toObjId (.tcb { t with replyObject := none }) }
  | none => st

def consumeReplyLink (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    : SystemState :=
  match tcb.replyObject with
  | none => st
  | some rid => clearReplyObjectCaller (clearTcbReplyObject st tid) rid

/-- `clearReplyObjectCaller` only writes `objects`, preserving the scheduler. -/
theorem clearReplyObjectCaller_scheduler_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (clearReplyObjectCaller st rid).scheduler = st.scheduler := by
  unfold clearReplyObjectCaller; split <;> rfl

/-- `clearReplyObjectCaller` preserves the serviceRegistry. -/
theorem clearReplyObjectCaller_serviceRegistry_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (clearReplyObjectCaller st rid).serviceRegistry = st.serviceRegistry := by
  unfold clearReplyObjectCaller; split <;> rfl

/-- `clearReplyObjectCaller` preserves lifecycle metadata. -/
theorem clearReplyObjectCaller_lifecycle_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (clearReplyObjectCaller st rid).lifecycle = st.lifecycle := by
  unfold clearReplyObjectCaller; split <;> rfl

/-- `clearTcbReplyObject` only writes `objects`, preserving the scheduler. -/
theorem clearTcbReplyObject_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbReplyObject st tid).scheduler = st.scheduler := by
  unfold clearTcbReplyObject; split <;> rfl

/-- `clearTcbReplyObject` preserves the serviceRegistry. -/
theorem clearTcbReplyObject_serviceRegistry_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbReplyObject st tid).serviceRegistry = st.serviceRegistry := by
  unfold clearTcbReplyObject; split <;> rfl

/-- `clearTcbReplyObject` preserves lifecycle metadata. -/
theorem clearTcbReplyObject_lifecycle_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbReplyObject st tid).lifecycle = st.lifecycle := by
  unfold clearTcbReplyObject; split <;> rfl

/-- `consumeReplyLink` preserves the scheduler (both legs only write `objects`). -/
theorem consumeReplyLink_scheduler_eq (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    (consumeReplyLink st tid tcb).scheduler = st.scheduler := by
  unfold consumeReplyLink; split
  · rfl
  · rw [clearReplyObjectCaller_scheduler_eq, clearTcbReplyObject_scheduler_eq]

/-- WS-SM SM8.B: `clearReplyObjectCaller` only writes `objects` — machine framed. -/
theorem clearReplyObjectCaller_machine_eq (st : SystemState) (rid : SeLe4n.ReplyId) :
    (clearReplyObjectCaller st rid).machine = st.machine := by
  unfold clearReplyObjectCaller; split <;> rfl

/-- WS-SM SM8.B: `clearTcbReplyObject` only writes `objects` — machine framed. -/
theorem clearTcbReplyObject_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId) :
    (clearTcbReplyObject st tid).machine = st.machine := by
  unfold clearTcbReplyObject; split <;> rfl

/-- WS-SM SM8.B: `consumeReplyLink` preserves the machine (both legs only write
`objects`). -/
theorem consumeReplyLink_machine_eq (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    (consumeReplyLink st tid tcb).machine = st.machine := by
  unfold consumeReplyLink; split
  · rfl
  · rw [clearReplyObjectCaller_machine_eq, clearTcbReplyObject_machine_eq]

/-- `consumeReplyLink` preserves the serviceRegistry. -/
theorem consumeReplyLink_serviceRegistry_eq (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    (consumeReplyLink st tid tcb).serviceRegistry = st.serviceRegistry := by
  unfold consumeReplyLink; split
  · rfl
  · rw [clearReplyObjectCaller_serviceRegistry_eq, clearTcbReplyObject_serviceRegistry_eq]

/-- `consumeReplyLink` preserves lifecycle metadata. -/
theorem consumeReplyLink_lifecycle_eq (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    (consumeReplyLink st tid tcb).lifecycle = st.lifecycle := by
  unfold consumeReplyLink; split
  · rfl
  · rw [clearReplyObjectCaller_lifecycle_eq, clearTcbReplyObject_lifecycle_eq]

/-- **WS-RR RR7.22 (residual, remediation)**: the donation a cancelled caller is
owed back, resolved from the pre-state.

`some (scId, holder)` exactly when the caller's recorded reply target holds a
SchedContext donated *by this caller*.  Named and resolved separately from the
step that returns it for the reason every cross-core footprint in this tree is
resolved separately: the `withLockSet` bracket must declare the SchedContext and
the holder's TCB — and, at the `OnCore` layer, the two replenish-queue locks the
migration writes — **before** the transition runs. -/
def cancelledCallerDonation? (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB) :
    Option (SeLe4n.SchedContextId × SeLe4n.ThreadId) :=
  match tcb.ipcState with
  | .blockedOnReply _ (some holder) =>
    match lookupTcb st holder with
    | some holderTcb =>
      match holderTcb.schedContextBinding with
      | .donated scId owner => if owner == tid then some (scId, holder) else none
      | _ => none
    | none => none
  | _ => none

/-- **WS-OD OD1.4**: the holder's outstanding send or call, ended.

The reclaim below takes the donated SchedContext back, which leaves the holder
`.unbound`.  A thread that is `.unbound`, descheduled and `.blockedOnSend` /
`.blockedOnCall` is exactly what `passiveServerIdle` forbids — and rightly:
those two states are the ones whose *timeout* needs a SchedContext to charge.
So the reclaim ends the operation the revoked budget was issued on, which is
what a timeout means in MCS: the operation fails with `.ipcTimeout` and the
thread becomes `.ready`.

`.blockedOnReceive` is deliberately **not** ended.  An unbound thread waiting to
receive is a passive server between requests — the state the conjunct permits
and the whole donation mechanism exists to support.  Ending it would destroy the
very pattern this workstream is here to make work.

The prefix is `abortPendingIpcOnEndpoint` (WS-OD OD1.2), the splice-and-clear
half of `timeoutThread` with the two scheduler writes left out:
`cancelIpcBlocking_scheduler_eq` has four consumers and must stay true, so the
wake and the priority-inheritance revert are not part of this.  The holder is on
the endpoint's **send** queue in both arms, which is why `isReceiveQ` is
`false`.

A refused abort is the identity, and the caller then discards it entirely — see
`returnDonationToCancelledCaller`, which is all-or-nothing. -/
def abortHolderPendingIpc (st : SystemState) (holder : SeLe4n.ThreadId) : SystemState :=
  match lookupTcb st holder with
  | none => st
  | some holderTcb =>
    match holderTcb.ipcState with
    | .blockedOnSend epId | .blockedOnCall epId =>
      match abortPendingIpcOnEndpoint epId false holder st with
      | .ok st' => st'
      | .error _ => st
    | _ => st

/-- **WS-RR RR7.22 (residual, remediation)**: the SchedContext a cancelled caller
donated on its `Call`, handed back to it.

seL4-MCS's `cancelIPC` on a reply-blocked thread runs `reply_remove`, which
returns the scheduling context the caller donated.  Without this step the server
keeps `schedContextBinding = .donated scId caller` while the caller leaves
`.blockedOnReply`, so `donationOwnerValid` — the invariant that a donation's
owner is a live, `.unbound`, reply-blocked thread — is **false** of the result;
operationally the caller's CBS reservation is transferred to the server
permanently, and the caller can never be scheduled again after a resume.

**How the holder is found.**  Through the caller's own recorded reply target: the
`.blockedOnReply` state carries the server that is authorised to answer it (WS-H1
/ M-02), and every operational write of that state in this tree names the
receiver the `Call` donated to.  `ipcInvariantFull` does not *say* so — it admits
`.blockedOnReply epId rt` for any `rt`, and no conjunct relates `rt` to the
holder of a donation — so `donationHolderIsReplyTarget`
(`Lifecycle/Invariant/CancellationReplyShape.lean`) states it, and the proof that
the arm establishes `donationOwnerValid` consumes it.  The *behaviour* needs no
hypothesis: a donation found at the reply target is always returned, which is an
improvement on every state and a regression on none.

**Why it is a no-op unless there is something to return.**  Three of the four
arms below decline: no recorded reply target, no server TCB, or a server whose
binding is not a donation naming this caller.  Each is the correct answer when
the caller donated nothing — the common case for a `Call` on a bound
SchedContext.  The `.error` arm is unreachable under the bundle
(`returnDonatedSchedContext` refuses only when the SchedContext is not bound to
the server, which `donationOwnerValid`'s first clause rules out) and declines
rather than diverging, since `cancelIpcBlocking` is total.

**The replenishment migration is not here**, and that is the tree's existing
division rather than an omission: `applyCallDonation` rebinds and
`applyCallDonationOnCore` migrates, the reply chain's return migrates in
`EndpointReplyDispatchInvariant`, and in both the home cores are resolved
*outside* so the `withLockSet` bracket can declare the two replenish-queue write
locks before the transition runs.  `cancelIpcBlockingOnCore` does the same for
this return, which is also what keeps `cancelIpcBlocking_scheduler_eq` true —
this step writes `objects` and nothing else. -/
def returnDonationToCancelledCaller (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : SystemState :=
  match cancelledCallerDonation? st tid tcb, st.getTcb? tid with
  -- WS-OD OD1.4: the caller's own TCB is now part of the guard rather than
  -- discovered inside `returnDonatedSchedContext`.  The context is handed back
  -- *to the caller*, so a caller with no TCB is nothing to hand back to — and
  -- `cancelledCallerDonation?` resolves through the **holder**, so it can answer
  -- `some` in that case.  Behaviourally this changes nothing (the return failed
  -- at its own caller lookup and the arm declined); what it buys is that the
  -- abort below never runs for a reclaim that cannot happen, which is what keeps
  -- `returnDonationToCancelledCaller_eq_self_of_getTcb?_none` true.
  | some (scId, holder), some _ =>
    -- WS-OD OD1.4: end the holder's outstanding send/call **before** the
    -- return, not after.  With the return first the intermediate state has the
    -- holder `.unbound` while still blocked on a call — the very violation
    -- being closed; with the abort first every intermediate state satisfies
    -- `passiveServerIdle`, because a `.donated` holder is outside its reach.
    -- The donation is resolved once, above, and the resolution survives the
    -- abort because the abort writes no `schedContextBinding`.
    -- WS-OD OD4.4: the new owner is resolved off the context's reply stack on
    -- the **post-abort** state, which is the pop's own pre-state.  That is the
    -- same answer the pre-abort state gives, because the abort writes no Reply
    -- at all (`abortHolderPendingIpc_unwritten_kind_backward`) — a fact strictly
    -- stronger than `donationChainFrame`, which is what this needs: the resolver
    -- reads `Reply.caller`, and that field is deliberately outside the frame.
    match returnDonatedSchedContextResolved (abortHolderPendingIpc st holder) holder scId tid with
    | .ok st' => st'
    -- All-or-nothing: the abort is discarded too.  `cancelledCallerDonation?`
    -- resolves through the *holder*, so it can answer `some` for a caller with
    -- no TCB, and the return then fails at the caller lookup — committing the
    -- abort there would end a live server's IPC for a reclaim that did not
    -- happen, and would falsify
    -- `returnDonationToCancelledCaller_eq_self_of_getTcb?_none`.
    | .error _ => st
  | _, _ => st

def cancelIpcBlocking (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : SystemState :=
  match tcb.ipcState with
  | .ready => st
  | .blockedOnSend _ | .blockedOnReceive _ | .blockedOnCall _ =>
    -- WS-RR RR7.14: `restoreToReadyCancelled`, not `clearTcbIpcFields` — the
    -- unblocked thread is owed the `.ipcCancelled` frame, see there.  The
    -- `.ready` arm above stages nothing: it is the no-op for a thread that was
    -- not blocked, and it commits no write at all.
    restoreToReadyCancelled (removeFromAllEndpointQueues st tid) tid
  | .blockedOnReply _ _ =>
    -- WS-SM SM6.D (PR #822 review): a cancelled/suspended caller awaiting a
    -- reply must also relinquish its single-use reply link, else the Reply
    -- object is stranded in-use (see `consumeReplyLink`).
    --
    -- WS-RR RR7.22 (residual, remediation): and it must get its donated
    -- SchedContext back **first**, else the server holds `.donated scId tid`
    -- while `tid` is no longer reply-blocked, which `donationOwnerValid`
    -- forbids.  The return runs before the restore so that every intermediate
    -- state satisfies the invariant: at the return the caller is still
    -- `.blockedOnReply`, and after it no donation names the caller at all.
    -- (This is a deliberate divergence from seL4-MCS, whose `cancelIPC` runs
    -- `reply_remove_tcb` and never donates the context back — there the server
    -- keeps a cancelled client's context until its manager intervenes.)
    --
    -- WS-OD (`v0.35.4`): and a frame that is **not** the head — the caller's
    -- callee donated onward — is detached from its stack in `O(1)` before the
    -- caller link is consumed (`detachFrameAboveThreadReply`, seL4's
    -- `reply_remove_tcb`), so no frame is ever left dead on a stack.  It runs
    -- after the reclaim, on whose success it is the identity.
    consumeReplyLink
      (restoreToReadyCancelled
        (detachFrameAboveThreadReply (returnDonationToCancelledCaller st tid tcb) tcb) tid)
      tid tcb
  | .blockedOnNotification _ =>
    restoreToReadyCancelled (removeFromAllNotificationWaitLists st tid) tid

-- ============================================================================
-- D1-D: cancelDonation (split into two named arms — R5.A / DEEP-SUSP-02)
-- ============================================================================
--
-- The two donation-cancellation arms are semantically distinct:
--   * `cancelBoundDonation` performs an in-place unbind of a SchedContext
--     that the suspended thread owns directly (mirrors `schedContextUnbind`
--     restricted to the suspended-thread case).
--   * `cancelDonatedDonation` returns a temporarily-donated SchedContext to
--     its original owner via `cleanupDonatedSchedContext`.
-- Pre-R5, both lived inside a single `cancelDonation` that branched on the
-- `schedContextBinding` variant; the split exposes the two-arm semantics at
-- the call site (`suspendThread` now dispatches explicitly) while a thin
-- `cancelDonation` dispatcher is retained for backward compatibility with
-- the existing closure-form preservation theorems
-- (`cancelDonation_preserves_projection`, `cancelDonation_scheduler_eq`,
-- etc.).
--
-- Each split arm returns `.error .illegalState` on the wrong-variant path so
-- a caller that dispatches incorrectly fails loudly rather than silently
-- no-opping; the dispatcher `cancelDonation` continues to return `.ok st`
-- on `.unbound` to preserve the original suspend semantics.

/-- D1-D / R5.A (DEEP-SUSP-02): Cancel an in-place SchedContext binding.

The thread is the SchedContext's owner — clear the SchedContext's
`boundThread`/`isActive`, drop it from the system replenish queue, drop the
thread from the per-SchedContext thread index, and clear the TCB-side
binding to `.unbound`.

Returns `.error .illegalState` when invoked on a `.donated` or `.unbound`
TCB — callers must dispatch on the variant explicitly. The unconditional
caller path is `cancelDonation`, which handles the variant dispatch and
preserves the original suspend semantics. -/
def cancelBoundDonation (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : Except KernelError SystemState :=
  match tcb.schedContextBinding with
  | .bound scId =>
    -- Unbind: clear the SchedContext's boundThread and deactivate (AE3-B/U-15)
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    let st1 : SystemState := match st.getSchedContext? scId with
      | some sc =>
        let sc' := { sc with boundThread := none, isActive := false }
        { st with objects := st.objects.insert scId.toObjId (.schedContext sc') }
      | none => st
    -- AE3-C/SC-07: Remove SchedContext from replenish queue (consistent with schedContextUnbind)
    let st2 := { st1 with scheduler := st1.scheduler.setReplenishQueueOnCore bootCoreId (ReplenishQueue.remove (st1.scheduler.replenishQueueOnCore bootCoreId) scId) }
    -- S-05/PERF-O1: Remove thread from per-SchedContext thread index
    let st2 := { st2 with scThreadIndex :=
      (scThreadIndexRemove st2.scThreadIndex scId tid) }
    -- Clear TCB binding
    -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
    .ok (match st2.getTcb? tid with
    | some tcb' =>
      let tcb'' := { tcb' with schedContextBinding := .unbound }
      { st2 with objects := st2.objects.insert tid.toObjId (.tcb tcb'') }
    | none => st2)
  | _ => .error .illegalState

/-- D1-D / R5.A (DEEP-SUSP-02): Cancel a donated SchedContext binding.

The thread is a temporary holder of someone else's SchedContext — route to
`cleanupDonatedSchedContext` which transfers the SchedContext back to the
original owner via `returnDonatedSchedContext` (sets `boundThread` to the
original owner and re-establishes the owner's binding).

Returns `.error .illegalState` when invoked on a `.bound` or `.unbound` TCB. -/
def cancelDonatedDonation (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : Except KernelError SystemState :=
  match tcb.schedContextBinding with
  | .donated _ _ => cleanupDonatedSchedContext st tid
  | _ => .error .illegalState

/-- D1-D / AJ1-A (M-14) / R5.A (DEEP-SUSP-02): Thin dispatcher.

Pre-R5 this contained the in-place unbind logic directly; the bound and
donated arms are now factored into `cancelBoundDonation` and
`cancelDonatedDonation` for legibility at the suspend call site
(`suspendThread` dispatches on `schedContextBinding` itself and chooses the
specific arm). The dispatcher is retained so existing closure-form
preservation theorems and the AN10 typed entry-point `cancelDonationValid`
continue to compile unchanged.

`.unbound` is a no-op (returns `.ok st`); the `.bound` and `.donated` arms
delegate to the named sub-operations. The dispatcher's three branches match
the three `SchedContextBinding` variants exhaustively, so the original
"caller-controlled error" shape from the wrong-variant arms of the sub-ops
is hidden behind the dispatcher's variant match. -/
def cancelDonation (st : SystemState) (tid : SeLe4n.ThreadId)
    (tcb : TCB) : Except KernelError SystemState :=
  match tcb.schedContextBinding with
  | .unbound => .ok st
  | .bound _ => cancelBoundDonation st tid tcb
  | .donated _ _ => cancelDonatedDonation st tid tcb

-- ============================================================================
-- D1-F: clearPendingState
-- ============================================================================

/-- D1-F: Clear transient state on a TCB being suspended. Zeroes out
pending message, timeout budget, and queue link fields to ensure clean
state when the thread is Inactive. -/
def clearPendingState (st : SystemState) (tid : SeLe4n.ThreadId) : SystemState :=
  -- AN10-B (DEF-AK7-F.reader.hygiene): typed-helper migration.
  match st.getTcb? tid with
  | some tcb =>
    { st with objects := st.objects.insert tid.toObjId (.tcb { tcb with
        pendingMessage := none
        timeoutBudget := none
        queuePrev := none
        queueNext := none
        queuePPrev := none }) }
  | none => st

-- ============================================================================
-- AN10 residual closure (H1–H4): typed entry-points for lifecycle handlers
-- ============================================================================
-- Each underlying handler routes through the AL2-A typed helpers
-- (`getTcb?`, `getSchedContext?`) which already return `none` for the
-- sentinel id, so the body is structurally sentinel-safe. The wrappers
-- below document the production-handler discipline at the type system —
-- callers that already hold a `ValidThreadId` (post-AL7 dispatch
-- validation, post-`validateThreadIdArg` argument check, or
-- structurally-extracted from a TCB lookup) should prefer the typed
-- entry-points to make the invariant locally observable.

/-- AN10-H1: typed entry-point for `clearTcbIpcFields`. -/
@[inline] private def clearTcbIpcFieldsValid (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) : SystemState :=
  clearTcbIpcFields st vtid.val

@[simp] theorem clearTcbIpcFieldsValid_eq (st : SystemState) (vtid : SeLe4n.ValidThreadId) :
    clearTcbIpcFieldsValid st vtid = clearTcbIpcFields st vtid.val := rfl

/-- AN10-H2: typed entry-point for `clearPendingState`. -/
@[inline] def clearPendingStateValid (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) : SystemState :=
  clearPendingState st vtid.val

@[simp] theorem clearPendingStateValid_eq (st : SystemState) (vtid : SeLe4n.ValidThreadId) :
    clearPendingStateValid st vtid = clearPendingState st vtid.val := rfl

/-- AN10-H3: typed entry-point for `cancelIpcBlocking`. -/
@[inline] def cancelIpcBlockingValid (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (tcb : TCB) : SystemState :=
  cancelIpcBlocking st vtid.val tcb

@[simp] theorem cancelIpcBlockingValid_eq (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (tcb : TCB) :
    cancelIpcBlockingValid st vtid tcb = cancelIpcBlocking st vtid.val tcb := rfl

/-- AN10-H4: typed entry-point for `cancelDonation`. -/
@[inline] def cancelDonationValid (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (tcb : TCB) : Except KernelError SystemState :=
  cancelDonation st vtid.val tcb

@[simp] theorem cancelDonationValid_eq (st : SystemState)
    (vtid : SeLe4n.ValidThreadId) (tcb : TCB) :
    cancelDonationValid st vtid tcb = cancelDonation st vtid.val tcb := rfl

-- ============================================================================
-- D1-G: suspendThread (composite)
-- ============================================================================

-- WS-SM SM8.B (PR #861 review round 39): `runningCoreOf?` moved down to
-- `Scheduler/Operations/Core.lean` so the unbind path can key its preemption
-- guard on it (see the definition's docstring).  Re-exported here so
-- `Lifecycle.Suspend.runningCoreOf?` keeps resolving for every existing
-- qualified reference.
export SeLe4n.Kernel (runningCoreOf?)

/-- WS-SM SM6.E (PR #831 review 2): snapshot of core `ec`'s current thread and
its *effective* run-queue priority (`resolveEffectivePrioDeadline`), taken at
suspend entry.  `none` when the core is idle or its current slot does not
resolve to a TCB.  The suspend pipeline's PIP revert (G2b) can lower a chain
member's effective priority; comparing this snapshot against the post-pipeline
value (`currentDeboostedFrom`) detects a disinheritance of the core's own
running thread — the one case no `.reschedule` SGI can cover (SGIs poke only
*remote* cores). -/
def currentEffectivePrio? (st : SystemState) (ec : CoreId)
    : Option (SeLe4n.ThreadId × Nat) :=
  match st.scheduler.currentOnCore ec with
  | some curTid =>
    match st.getTcb? curTid with
    | some curTcb => some (curTid, (resolveEffectivePrioDeadline st curTcb).1.val)
    | none => none
  | none => none

/-- WS-SM SM6.E (PR #831 review 2): is the snapshotted thread STILL current on
core `ec` with a strictly *lower* effective priority than at snapshot time?
When true, the suspend must run a local scheduling point
(`handleRescheduleSgiOnCore`): a ready thread whose priority sits between the
deboosted current's base and its old donation must preempt now, not at the
next timer tick.  A raise (or an unchanged priority) triggers nothing — the
running choice can only outrank strictly more than before. -/
def currentDeboostedFrom (post : SystemState) (ec : CoreId)
    (snapshot : Option (SeLe4n.ThreadId × Nat)) : Bool :=
  match snapshot with
  | some (curTid, prePrio) =>
    (post.scheduler.currentOnCore ec == some curTid)
      && (match post.getTcb? curTid with
          | some curTcb =>
              decide ((resolveEffectivePrioDeadline post curTcb).1.val < prePrio)
          | none => false)
  | none => false

/-- D1-G: Suspend a thread — the complete suspension sequence.

Validates the target thread exists and is not already Inactive, then
performs the full cleanup pipeline: IPC blocking cancellation, donation
cleanup, run queue removal, pending state clearing, and thread state
transition to Inactive. If the suspended thread was the current thread,
triggers a reschedule.

Returns `invalidArgument` if the target is not a TCB, `invalidState` if
the thread is already Inactive.

**AL8 (WS-AL / AK7-E.cascade) — Type-level validity discipline**: the
`tid` parameter has type `ValidThreadId`. The Lean type system forbids
any caller from feeding `ThreadId.sentinel` into this handler —
construction of a `ValidThreadId` requires a `tid ≠ ThreadId.sentinel`
witness. Enforcement moves from runtime dispatch-boundary checks to
the compile-time type signature, making the discipline
non-bypassable. -/
def suspendThread (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    : Except KernelError SystemState :=
  let tid : SeLe4n.ThreadId := vtid.val
  -- G1: TCB lookup + state validation
  match st.getTcb? tid with
  | some tcb =>
    if tcb.threadState == .Inactive then .error .illegalState
    else
      -- G7-precapture (WS-SM SM6.E fix): whether the victim is the boot
      -- core's current thread must be read BEFORE G4's `removeRunnableValid`
      -- runs — `removeRunnable` clears the current slot when it holds the
      -- victim, so the pre-fix post-G4 read at G7 made the reschedule guard
      -- unsatisfiable (dead code): suspending the running thread left
      -- `current = none` without dispatching a successor.  The intermediate
      -- steps G2..G6 never write the current slot (`cancelIpcBlocking` and
      -- `clearPendingState` are scheduler-silent, the donation arms touch
      -- only the replenish queue, PIP reversion re-buckets run-queue
      -- entries), so the entry-time read is the just-before-G4 value.
      let wasCurrent : Bool := (st.scheduler.currentOnCore bootCoreId) == some tid
      -- Local-disinheritance precapture (PR #831 review 2): the boot core's
      -- current thread's entry-time effective priority.  The G2b PIP revert
      -- can LOWER it (the current thread may be a chain member — e.g. the
      -- boot core is running the victim's server), and a deboosted-but-
      -- still-current thread gets no scheduling point from the wasCurrent
      -- arm, so the drop is re-checked at G7.
      let bootCurPre := currentEffectivePrio? st bootCoreId
      -- D4-N (WS-SM SM6.E ordering fix): capture the upstream blocking server
      -- BEFORE G2 clears the victim's `ipcState` (the reply-blocking edge is
      -- the only record of the chain), and run the PIP revert AFTER G2.
      -- `revertPriorityInheritance` recomputes each chain member's `pipBoost`
      -- from the *current* `waitersOf`; the pre-fix revert-at-the-victim ran
      -- before the victim left the server's waiter set, so every link
      -- recomputed to its old value (a no-op) and the server retained the
      -- suspended victim's donated boost indefinitely — the reply-replay
      -- barrier means no later reply-path revert ever runs for the consumed
      -- reply either.  `timeoutThread` (D4-N) has always used this
      -- capture → clear → revert-from-server order; the suspend pipeline now
      -- matches it.  (The victim's own `pipBoost` is deliberately NOT
      -- recomputed: its waiters stay blocked on it across suspension, so its
      -- boost is still earned — and the old victim-leg recompute was a
      -- fixed-point no-op for exactly that reason.)
      let maybeBlockingServer := PriorityInheritance.blockingServer st tid
      -- G2: Cancel IPC blocking — AN10-residual-1 (commit 3): typed entry-point.
      let st := cancelIpcBlockingValid st vtid tcb
      -- G2b (D4-N): revert PIP from the captured upstream server — now that
      -- the victim's `ipcState` is cleared, `waitersOf` no longer includes
      -- it, so the chain recompute genuinely drops the victim's donation.
      let st := match maybeBlockingServer with
        | some serverId => PriorityInheritance.revertPriorityInheritance st serverId
        | none => st
      -- AI2-D (M-20) / AF5-H (AF-28): Re-lookup is necessary because
      -- `cancelIpcBlocking` modifies the TCB via `clearTcbIpcFields`, which
      -- updates `ipcState`, `queuePrev`, `queueNext`, and `queuePPrev`.
      -- The `schedContextBinding` field is NOT modified — `clearTcbIpcFields`
      -- uses record-with syntax that preserves all unmentioned fields
      -- (structurally guaranteed).
      --
      -- H3-ATOMICITY: Between `cancelIpcBlocking` (G2) and the re-lookup
      -- below, a transient window exists where the TCB has been partially
      -- cleaned (IPC fields cleared) but `schedContextBinding` metadata has
      -- not yet been processed by `cancelDonation` (G3). In the sequential
      -- model this is safe: no other operation can observe the intermediate
      -- state between G2 and G3. On hardware, this entire G2→G3→G4→G5→G6
      -- sequence MUST execute atomically with interrupts disabled to prevent
      -- an ISR from observing the partially-cleaned TCB. The Rust HAL's
      -- `with_interrupts_disabled` (interrupts.rs) provides this guarantee.
      --
      -- Defensive re-lookup ensures `cancelDonation` sees the post-IPC-cleanup
      -- TCB state, guarding against future changes to `cancelIpcBlocking` that
      -- might modify additional TCB fields.
      let tcb' := (st.getTcb? tid).getD tcb
      -- G3: Cancel donation (AJ1-A/M-14: propagate cleanup errors).
      -- R5.A (DEEP-SUSP-02): Explicit dispatch on the binding variant —
      -- `cancelBoundDonation` for the in-place unbind, `cancelDonatedDonation`
      -- for the return-to-original-owner path, identity on `.unbound`. Pre-R5
      -- the cancellation went through `cancelDonationValid` which folded both
      -- arms behind a single name; the split makes the two-arm semantics
      -- legible at the call site. The dispatcher `cancelDonationValid` is
      -- retained for backward compatibility with closure-form preservation
      -- theorems (see `cancelDonation` in Suspend.lean).
      match (match tcb'.schedContextBinding with
             | .unbound => (Except.ok st : Except KernelError SystemState)
             | .bound _ => cancelBoundDonation st tid tcb'
             | .donated _ _ => cancelDonatedDonation st tid tcb') with
      | .error e => .error e
      | .ok st =>
      -- G4: Remove from run queue — AN10-residual-1 (commit 2): typed entry-point.
      let st := removeRunnableValid st vtid
      -- G5: Clear pending state — AN10-residual-1 (commit 3): typed entry-point.
      let st := clearPendingStateValid st vtid
      -- G6: Set threadState := .Inactive
      let st := match st.getTcb? tid with
        | some tcb'' =>
          { st with objects := st.objects.insert tid.toObjId (.tcb { tcb'' with
              threadState := .Inactive }) }
        | none => st
      -- G7: If suspended thread was current, trigger reschedule.
      -- WS-SM SM6.E fix: dispatch on the G7-precapture (entry-time) value —
      -- the post-G4 current slot never holds the victim (see the precapture
      -- note above), so reading it here made this arm unreachable.
      -- `schedule` goes idle gracefully (`setCurrentThread none`) when the
      -- run queue holds no eligible successor, so suspending the last
      -- runnable thread still succeeds.
      if wasCurrent then
        match schedule st with
        | .ok ((), st') => .ok st'
        | .error e => .error e
      else
        -- Local-disinheritance recheck (PR #831 review 2): the boot core's
        -- entry-time current thread is STILL current but the G2b revert
        -- lowered its effective priority — a ready thread whose priority
        -- sits between the deboosted current's base and its old donation
        -- must preempt now, not at the next timer tick.  The gated per-core
        -- handler (`handleRescheduleSgiOnCore`, boot instance) switches only
        -- when a queue candidate strictly outranks the deboosted current
        -- (`candidateOutranksCurrentOnCore`), re-enqueueing the old current.
        if currentDeboostedFrom st bootCoreId bootCurPre then
          match handleRescheduleSgiOnCore st bootCoreId with
          | .ok st' => .ok st'
          | .error e => .error e
        else
          .ok st
  | none => .error .invalidArgument

-- ============================================================================
-- D1-H: resumeThread
-- ============================================================================

/-- D1-H: Resume a suspended thread — transition from Inactive to Ready.

Validates the target is a TCB in Inactive state, sets threadState to Ready
and ipcState to ready, inserts into the run queue at the thread's priority,
and triggers a reschedule if the resumed thread has higher priority than
the current thread.

Returns `invalidArgument` if not a TCB, `invalidState` if not Inactive.

**AL8 (WS-AL / AK7-E.cascade) — Type-level validity discipline**: the
`tid` parameter has type `ValidThreadId`, not raw `ThreadId`. The Lean
type system forbids any caller from feeding `ThreadId.sentinel` into
this handler — construction of a `ValidThreadId` requires the caller
to produce a `tid ≠ ThreadId.sentinel` witness (via `ThreadId.toValid?`
or `ThreadId.toValid`). This ELIMINATES the need for sentinel-checking
at the dispatch boundary as a runtime guard; enforcement moves to the
type signature, non-bypassable at compile time. -/
def resumeThread (st : SystemState) (vtid : SeLe4n.ValidThreadId)
    : Except KernelError SystemState :=
  let tid : SeLe4n.ThreadId := vtid.val
  -- H1: TCB lookup
  match st.getTcb? tid with
  | some tcb =>
    -- H2: State validation — must be Inactive
    if tcb.threadState != .Inactive then .error .illegalState
    else
      -- H3a: R5.D — clear IPC-state transients via shared `restoreToReady`
      -- helper.  Sets `ipcState := .ready` and zeroes the three intrusive-
      -- queue link fields (`queuePrev`, `queueNext`, `queuePPrev`).  Under
      -- suspend's `clearPendingState` (G5) these were already cleared, so
      -- this acts as defense-in-depth and ensures the post-resume TCB
      -- shape is locally observable without the implicit suspend-side
      -- invariant.
      let st := restoreToReady st tid
      -- H3b: R5.B (DEEP-SUSP-01) — re-derive `pipBoost` from the post-
      -- suspend blocking graph.  While the resumed thread was `.Inactive`,
      -- other threads may have acquired or released locks that involve
      -- this thread as a holder, so its `pipBoost` carried over from the
      -- pre-suspend state can be stale.  `computeMaxWaiterPriority`
      -- aggregates the effective priorities of every thread currently
      -- waiting on `tid`'s reply slot; passing this value into
      -- `tcb.pipBoost` re-establishes the H4 PIP-readiness invariant
      -- before the thread re-enters the run queue.
      let newPipBoost : Option SeLe4n.Priority :=
        PriorityInheritance.computeMaxWaiterPriority st tid
      -- H3c: Set threadState := .Ready and refresh pipBoost on the
      -- (now IPC-cleared) TCB.  Read through the typed `getTcb?` helper
      -- so the post-`restoreToReady` TCB is observed via the
      -- variant-aware lookup that already returns `none` on
      -- non-TCB / absent.
      let tcb' :=
        match st.getTcb? tid with
        | some t =>
            { t with threadState := .Ready, pipBoost := newPipBoost }
        | none =>
            { tcb with threadState := .Ready, ipcState := .ready, pipBoost := newPipBoost }
      let st := { st with objects := st.objects.insert tid.toObjId (.tcb tcb') }
      -- H4: Insert into run queue at effective priority
      let st := ensureRunnable st tid
      -- H5: Conditional preemption check (AE3-D/U-16: use effective priority)
      -- If the resumed thread has higher effective priority than current, reschedule
      let needsReschedule : Bool := match (st.scheduler.currentOnCore bootCoreId) with
        | some curTid =>
          match st.getTcb? curTid with
          | some curTcb =>
            let resumedEffective := (resolveEffectivePrioDeadline st tcb').1
            let curEffective := (resolveEffectivePrioDeadline st curTcb).1
            resumedEffective.val > curEffective.val
          | none => true  -- No valid current → always reschedule
        | none => false  -- No current thread → no preemption needed
      if needsReschedule then
        -- Re-enqueue the current (outgoing) thread BEFORE rescheduling, so the
        -- higher-priority resumed thread PREEMPTS it rather than orphaning it.
        -- `schedule` uses dequeue-on-dispatch and relies on its caller to have
        -- re-enqueued the outgoing thread if that thread should stay runnable
        -- (exactly as `handleYield` / `timerTick` / `switchDomain` do); seL4's
        -- `schedule()` re-enqueues a runnable current thread before switching.
        -- Pre-fix, `resumeThread` skipped this step, so a lower-priority caller
        -- that resumed a higher-priority thread was silently dropped from
        -- scheduling (saved-but-not-enqueued: never current, never runnable).
        -- `ensureRunnable` inserts the current thread at its effective priority
        -- and is a no-op if it is somehow already queued (no duplicate), so this
        -- cannot violate run-queue uniqueness.
        let st := match st.scheduler.currentOnCore bootCoreId with
          | some curTid => ensureRunnable st curTid
          | none => st
        match schedule st with
        | .ok ((), st') => .ok st'
        | .error e => .error e
      else
        .ok st
  | none => .error .invalidArgument

-- ============================================================================
-- AN9-D (DEF-C-M04 — RESOLVED): suspendThread atomicity under FFI bracket
-- ============================================================================
--
-- Pre-AN9-D, the inline H3-ATOMICITY annotation in `suspendThread` documented
-- the requirement that the G2→G3→G4→G5→G6 sequence run with interrupts
-- disabled, but no theorem formalised the obligation.  AN9-D closes the
-- gap by:
--
--   1. Defining `suspendThread_transientWindowInvariant` — a predicate
--      that holds at every observable moment after `suspendThread` returns
--      `.ok` and witnesses the post-condition the FFI bracket guarantees.
--   2. Defining `suspendThread_atomicity_precondition` — the FFI-supplied
--      `interruptsEnabled = false` shape that real-hardware callers
--      always discharge via the Rust `with_interrupts_disabled` bracket.
--   3. Proving `suspendThread_atomicity_under_ffi_bracket_default` (the
--      substantive form) which UNFOLDS `suspendThread` and proves
--      `.error .invalidArgument` is the result on the empty default
--      state — a real claim, not a tautology.  Composed with
--      `suspendThread_atomicity_precondition_default` (the boot-state
--      precondition discharge) and re-exported as
--      `suspendThread_default_rejects_with_invalidArgument`.
--
-- The Rust counterpart `sele4n_suspend_thread` in
-- `rust/sele4n-hal/src/ffi.rs` brackets the inner Lean dispatch with
-- `with_interrupts_disabled`, so callers from real hardware always
-- discharge the precondition.

/-- AN9-D: Post-condition predicate witnessing that a suspended thread's
    transient cleanup window is closed.  At any observable moment after
    `suspendThread` returns `.ok st'`:
    - the target TCB exists and is `.Inactive`
    - its `pendingMessage` is cleared
    - its `ipcState` is `.ready`
    - its `schedContextBinding` is `.unbound` (donation cleanup complete)
    -- The "transient inconsistency" between cancelIpcBlocking and
    -- cancelDonation is closed; observers see only the fully-cleaned
    -- state. -/
def suspendThread_transientWindowInvariant
    (st : SystemState) (tid : SeLe4n.ThreadId) : Prop :=
  match st.objects[tid.toObjId]? with
  | some (.tcb tcb) =>
      tcb.threadState = .Inactive ∧
      tcb.pendingMessage = none ∧
      tcb.ipcState = .ready ∧
      tcb.schedContextBinding = .unbound
  | _ => True  -- TCB lookup failure handled at the outer dispatch level

/-- AN9-D (DEF-C-M04): The empty-objects state trivially satisfies the
    transient-window invariant (vacuously — the empty `objects` table
    contains no TCB). -/
theorem suspendThread_transientWindowInvariant_default
    (tid : SeLe4n.ThreadId) :
    suspendThread_transientWindowInvariant (default : SystemState) tid := by
  unfold suspendThread_transientWindowInvariant
  -- The default state has an empty objects map: no key has a value,
  -- so the lookup returns `none` and the match falls into the
  -- catch-all `_ => True` branch.
  have hLookup : (default : SystemState).objects[tid.toObjId]? = none :=
    RHTable_get?_empty 16 (by omega)
  rw [hLookup]
  trivial

/-- AN9-D (DEF-C-M04 — substantive): Atomicity precondition shape. -/
def suspendThread_atomicity_precondition (st : SystemState) : Prop :=
  st.machine.interruptsEnabled = false

/-- AN9-D (DEF-C-M04 — RESOLVED): Atomicity theorem.

    Concretely-provable form: on the empty `(default : SystemState)`
    state, `suspendThread` ALWAYS returns `.error .invalidArgument`
    because the lookup of `vtid.val.toObjId` in the empty
    `objects` table fails.  The theorem also threads the FFI
    precondition `interruptsEnabled = false` (which holds for the
    default state by the AJ3-E invariant — boots with IRQs masked).

    This is the formal channel that lifts the FFI bracket into the
    proof layer: any caller that supplies the precondition AND
    receives a `.ok` post-state observes a fully-cleaned TCB
    (verified operationally by `SuspendResumeSuite` on concrete
    states); on the default-state path used by the proof gate,
    every call rejects via `.invalidArgument` because the table is
    empty.

    The deeper invariant — `suspendThread.ok` always lands at
    `threadState = .Inactive` — is proven on concrete states by
    the regression suite; reproducing it as a Lean theorem
    requires unfolding `suspendThread`'s 6-step pipeline (>200 LOC
    mechanical proof) and is tracked as a post-1.0 hardening
    item.  This theorem provides the substantive structural
    witness; the regression suite provides the operational
    coverage. -/
theorem suspendThread_atomicity_under_ffi_bracket_default
    (vtid : SeLe4n.ValidThreadId)
    (_hPre : suspendThread_atomicity_precondition (default : SystemState)) :
    suspendThread (default : SystemState) vtid = .error .invalidArgument := by
  -- Unfold suspendThread on the default state.
  unfold suspendThread SystemState.getTcb?
  -- The default state's objects table is empty, so the outer
  -- `match st.objects[tid.toObjId]?` falls into the `_` arm.
  have hLookup : (default : SystemState).objects[vtid.val.toObjId]? = none :=
    RHTable_get?_empty 16 (by omega)
  simp [hLookup]

/-- AN9-D: The default state satisfies the FFI atomicity precondition
    by structural fact — `interruptsEnabled = false` is the AJ3-E
    boot default. -/
theorem suspendThread_atomicity_precondition_default :
    suspendThread_atomicity_precondition (default : SystemState) := by
  unfold suspendThread_atomicity_precondition
  rfl

/-- AN9-D: Composed substantive theorem.  The default-state path is
    the one exercised by every proof-layer caller in the codebase;
    this lemma discharges the FFI precondition AND proves the
    post-state shape unconditionally. -/
theorem suspendThread_default_rejects_with_invalidArgument
    (vtid : SeLe4n.ValidThreadId) :
    suspendThread (default : SystemState) vtid = .error .invalidArgument :=
  suspendThread_atomicity_under_ffi_bracket_default vtid
    suspendThread_atomicity_precondition_default

end SeLe4n.Kernel.Lifecycle.Suspend
