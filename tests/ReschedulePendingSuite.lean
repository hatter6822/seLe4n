-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.Scheduler.Operations
import SeLe4n.Kernel.Scheduler.PriorityInheritance.PerCore
import SeLe4n.Kernel.Scheduler.Invariant.ReschedulePendingCoverage
import SeLe4n.Kernel.Lifecycle.Suspend
import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Kernel.SchedContext.PriorityManagementPerCore
import SeLe4n.Testing.StateBuilder

/-!
# Reschedule-pending accumulator — differential suite

Tier-2 (runtime) coverage for the per-core reschedule-pending flag
(`SchedulerState.reschedulePending`, the KSC-1 accumulator, PR A).  The flag
landed **inert**: the live diff `computeCrossCoreSgis` is still what decides
which remote cores a syscall pokes, and this suite is what pins the flag to it
until PR C switches the seams.

* **§1 Surface anchors** — the accumulator's names resolve at elaboration time.
* **§2 The differential** — over the SMP scenarios the existing suites exercise
  (cross-core PIP boost, wake and resume, remote queue removal and deschedule,
  suspend, priority raise and drop on a current thread, re-bucket of a queued
  thread, affinity migration, a reconfigure that moves a bound thread's
  domain), the set of REMOTE cores whose flag went
  `false → true` during the step is a superset of the cores the live diff
  names, and — where the writer is exact — the same set.
* **§2.10 Eviction** — the receiver drops an incumbent a reconfigure moved out
  of the core's active domain.
* **§3 Scheduling points** — `handleRescheduleSgiOnCore` and
  `scheduleEffectiveOnCore` clear their own core's flag and nobody else's.
* **§4 Monotonicity** — no writer lowers a flag.
-/

namespace SeLe4n.Testing.ReschedulePending

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.PriorityInheritance
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing
open SeLe4n.Kernel.Lifecycle.Suspend (restoreToReadyWithWake suspendThreadOnCore)
open SeLe4n.Kernel.SchedContext.PriorityManagement (setPriorityOnCore)

-- ============================================================================
-- §1  Surface anchors: the accumulator's names resolve
-- ============================================================================

#check @SchedulerState.reschedulePendingOnCore
#check @SchedulerState.setReschedulePendingOnCore
#check @SchedulerState.markReschedulePendingOnCore
#check @SchedulerState.clearReschedulePendingOnCore
#check @SchedulerState.markReschedulePendingOnCoreIf
#check @SystemState.markReschedulePendingOnCore
#check @SystemState.clearReschedulePendingOnCore
#check @markKeyChangeFor
#check @rescheduleSgisFromFlags
#check @mem_rescheduleSgisFromFlags_iff
#check @rescheduleSgisFromFlags_all_reschedule
#check @rescheduleSgisFromFlags_not_execCore
#check @rescheduleSgisFromFlags_nil_of_eq
#check @markKeyChangeFor_reschedulePendingOnCore_mono
#check @markKeyChangeFor_extract_frame
#check @default_reschedulePendingOnCore
#check @markReschedulePendingWhere_reschedulePendingOnCore
#check @reschedulePendingCovers_trans
#check @computeCrossCoreSgis_mem_flags_of_covers
#check @enqueueRunnableOnCore_covers
#check @removeRunnableOnCore_covers
#check @markKeyChangeFor_covers
#check @markKeyChangeFrom
#check @markKeyChangeFrom_flagged
#check @reschedulePendingCovers_of_keyChangeFlagged

-- The boot default: no core owes a reschedule.
example (c : CoreId) : (default : SystemState).scheduler.reschedulePendingOnCore c = false :=
  default_reschedulePendingOnCore c

-- A writer's mark is read back on its core and on no other.
example (st : SystemState) (c : CoreId) :
    (st.markReschedulePendingOnCore c).scheduler.reschedulePendingOnCore c = true := by simp
example (st : SystemState) (c c' : CoreId) (h : c ≠ c') :
    (st.markReschedulePendingOnCore c).scheduler.reschedulePendingOnCore c'
      = st.scheduler.reschedulePendingOnCore c' := by simp [h]

-- ============================================================================
-- §2  The differential: flags raised vs. the live diff
-- ============================================================================

private def core0 : CoreId := bootCoreId
private def core1 : CoreId := ⟨1, by decide⟩
private def core2 : CoreId := ⟨2, by decide⟩

/-- A server bound to the remote core 1, queued there at priority 5. -/
private def srv : SeLe4n.ThreadId := ThreadId.ofNat 200
/-- An unbound (boot-core) waiter blocked on reply to `srv`, priority 10. -/
private def cli : SeLe4n.ThreadId := ThreadId.ofNat 201
/-- The thread CURRENT on core 1, priority 7. -/
private def cur1 : SeLe4n.ThreadId := ThreadId.ofNat 210
/-- An unbound caller with authority over priorities up to 200. -/
private def boss : SeLe4n.ThreadId := ThreadId.ofNat 220
/-- A high-base server (10) bound to core 1 with a low (5) waiter — the
immaterial-boost fixture. -/
private def srvHi : SeLe4n.ThreadId := ThreadId.ofNat 202
private def cliLo : SeLe4n.ThreadId := ThreadId.ofNat 203

private def vCur1 : SeLe4n.ValidThreadId := ⟨ThreadId.ofNat 210, by decide⟩
private def vBoss : SeLe4n.ValidThreadId := ⟨ThreadId.ofNat 220, by decide⟩
private def vSrv : SeLe4n.ValidThreadId := ⟨ThreadId.ofNat 200, by decide⟩

/-- An IPC-ready TCB with the given base priority, affinity and thread state. -/
private def mkReadyTcb (tidN : Nat) (prio : Nat) (aff : Option CoreId)
    (state : ThreadState) (mcp : Nat := 0xFF) : TCB :=
  { tid := ThreadId.ofNat tidN, priority := ⟨prio⟩, domain := ⟨0⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0, ipcState := .ready, threadState := state,
    cpuAffinity := aff, maxControlledPriority := ⟨mcp⟩ }

/-- An unbound waiter blocked on reply to `server`. -/
private def mkWaiterTcb (tidN : Nat) (prio : Nat) (server : Nat) : TCB :=
  { tid := ThreadId.ofNat tidN, priority := ⟨prio⟩, domain := ⟨0⟩,
    cspaceRoot := ObjId.ofNat 0, vspaceRoot := ObjId.ofNat 0,
    ipcBuffer := SeLe4n.VAddr.ofNat 0, threadState := .BlockedReply,
    ipcState := .blockedOnReply (ObjId.ofNat 50) (some (ThreadId.ofNat server)) }

/-- The objects every fixture shares; the scheduler slots differ per fixture. -/
private def baseObjects : SystemState :=
  BootstrapBuilder.empty
    |>.withObject srv.toObjId (.tcb (mkReadyTcb 200 5 (some core1) .Ready))
    |>.withObject cli.toObjId (.tcb (mkWaiterTcb 201 10 200))
    |>.withObject cur1.toObjId (.tcb (mkReadyTcb 210 7 (some core1) .Running))
    |>.withObject boss.toObjId (.tcb (mkReadyTcb 220 50 none .Ready 200))
    |>.build

/-- `srv` queued on core 1 at 5; `cur1` current on core 1. -/
private def stBase : SystemState :=
  { baseObjects with
      scheduler := baseObjects.scheduler.setRunQueueOnCore core1 (RunQueue.ofList [(srv, ⟨5⟩)])
        |>.setCurrentOnCore core1 (some cur1) }

/-- `srv` parked (no run queue anywhere); `cur1` current on core 1. -/
private def stNoRq : SystemState :=
  { baseObjects with scheduler := baseObjects.scheduler.setCurrentOnCore core1 (some cur1) }

/-- The immaterial-boost fixture: boosting `srvHi` by `cliLo`'s 5 leaves its
effective priority at its base 10. -/
private def stImmaterial : SystemState :=
  let base := ((BootstrapBuilder.empty.withObject srvHi.toObjId
      (.tcb (mkReadyTcb 202 10 (some core1) .Ready))).withObject
    cliLo.toObjId (.tcb (mkWaiterTcb 203 5 202))).build
  { base with scheduler := base.scheduler.setRunQueueOnCore core1 (RunQueue.ofList [(srvHi, ⟨10⟩)]) }

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then
    IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

private def coresStr (l : List CoreId) : String := toString (l.map (·.val))

/-- The REMOTE cores whose flag went `false → true` across `pre → post`
(`rescheduleSgisFromFlags` is what PR C's seam will read). -/
private def raisedCores (pre post : SystemState) (e : CoreId) : List CoreId :=
  (rescheduleSgisFromFlags pre.scheduler.reschedulePending post.scheduler.reschedulePending e
    |>.map (·.1))

/-- The cores the live diff names — the decider in PR A. -/
private def diffCores (pre post : SystemState) (e : CoreId) : List CoreId :=
  (computeCrossCoreSgis pre post e).map (·.1)

private def superset (big small : List CoreId) : Bool := small.all (big.contains ·)
private def sameSet (a b : List CoreId) : Bool := superset a b && superset b a

/-- The differential: the raised flags cover the live diff, and for an exact
writer the two sets coincide. -/
private def checkDiff (name : String) (pre post : SystemState) (e : CoreId) (exact : Bool)
    : IO Unit := do
  let flagged := raisedCores pre post e
  let diff := diffCores pre post e
  assertBool s!"{name}: flags ⊇ live diff (flags={coresStr flagged}, diff={coresStr diff})"
    (superset flagged diff)
  if exact then
    assertBool s!"{name}: flags = live diff (exact writer)" (sameSet flagged diff)

/-- The expected flag set, stated outright so the differential cannot pass by
both sides being wrong together. -/
private def expectRaised (name : String) (pre post : SystemState) (e : CoreId)
    (expected : List CoreId) : IO Unit :=
  assertBool s!"{name}: raised flags = {coresStr expected} (got {coresStr (raisedCores pre post e)})"
    (sameSet (raisedCores pre post e) expected)

private def flagOf (st : SystemState) (c : CoreId) : Bool := st.scheduler.reschedulePendingOnCore c

private def ofExcept (name : String) (r : Except KernelError (SystemState × Option (CoreId × SgiKind)))
    : IO SystemState := do
  match r with
  | .ok (st, _) => pure st
  | .error e =>
    IO.println s!"  FAIL: {name} returned {repr e}"
    throw (IO.userError s!"{name} failed")

/-- §2.1 the cross-core PIP boost (`pipBoostWithWake`). -/
private def runBoostChecks : IO Unit := do
  IO.println "--- §2.1 pipBoostWithWake ---"
  let (post, sgi) := pipBoostWithWake stBase srv core0
  checkDiff "remote material boost of a queued server" stBase post core0 true
  expectRaised "remote material boost" stBase post core0 [core1]
  assertBool "remote material boost: the live SGI is (core1, .reschedule)"
    (sgi == some (core1, .reschedule))
  let (postLocal, _) := pipBoostWithWake stBase srv core1
  checkDiff "local boost (executing on the home core)" stBase postLocal core1 true
  expectRaised "local boost" stBase postLocal core1 []
  let (postImm, sgiImm) := pipBoostWithWake stImmaterial srvHi core0
  checkDiff "immaterial boost (effective priority unchanged)" stImmaterial postImm core0 true
  expectRaised "immaterial boost" stImmaterial postImm core0 []
  assertBool "immaterial boost: core 1's flag stays false (precision)" (!(flagOf postImm core1))
  assertBool "immaterial boost: the live diff emits no SGI" (sgiImm == none)
  let (postNoRq, _) := pipBoostWithWake stNoRq srv core0
  checkDiff "boost of a non-runnable server" stNoRq postNoRq core0 true
  expectRaised "boost of a non-runnable server" stNoRq postNoRq core0 []

/-- §2.2 wakes: `wakeThread` and `restoreToReadyWithWake`. -/
private def runWakeChecks : IO Unit := do
  IO.println "--- §2.2 wakeThread / restoreToReadyWithWake ---"
  let (post, sgi) := wakeThread stNoRq srv core0
  checkDiff "remote wake" stNoRq post core0 true
  expectRaised "remote wake" stNoRq post core0 [core1]
  assertBool "remote wake: the live SGI is (core1, .reschedule)" (sgi == some (core1, .reschedule))
  let (postLocal, _) := wakeThread stNoRq srv core1
  checkDiff "local wake" stNoRq postLocal core1 true
  expectRaised "local wake" stNoRq postLocal core1 []
  let (postRes, _) := restoreToReadyWithWake stNoRq srv core0
  checkDiff "remote resume" stNoRq postRes core0 true
  expectRaised "remote resume" stNoRq postRes core0 [core1]
  let (postAlready, _) := wakeThread stBase srv core0
  checkDiff "wake of an already-queued server" stBase postAlready core0 false

/-- §2.3 queue removal and deschedule (`removeRunnableOnCore`). -/
private def runRemovalChecks : IO Unit := do
  IO.println "--- §2.3 removeRunnableOnCore ---"
  let post := removeRunnableOnCore stBase srv core1
  checkDiff "removal of a remote QUEUED thread" stBase post core0 true
  expectRaised "removal of a remote queued thread" stBase post core0 []
  assertBool "removal of a queued thread: core 1's flag stays false (precision)"
    (!(flagOf post core1))
  let postCur := removeRunnableOnCore stBase cur1 core1
  checkDiff "deschedule of a remote CURRENT thread" stBase postCur core0 true
  expectRaised "deschedule of a remote current thread" stBase postCur core0 [core1]
  assertBool "deschedule of a current thread: the slot is cleared"
    (postCur.scheduler.currentOnCore core1 == none)

/-- §2.4 cross-core suspend (`suspendThreadOnCore`): the composite writes more
than one slot, so the differential is the superset bound. -/
private def runSuspendChecks : IO Unit := do
  IO.println "--- §2.4 suspendThreadOnCore ---"
  let post ← ofExcept "suspend of a remote queued server" (suspendThreadOnCore stBase vSrv core0)
  checkDiff "suspend of a remote queued server" stBase post core0 false
  let postCur ← ofExcept "suspend of a remote current thread" (suspendThreadOnCore stBase vCur1 core0)
  checkDiff "suspend of a remote current thread" stBase postCur core0 false
  expectRaised "suspend of a remote current thread" stBase postCur core0 [core1]

/-- §2.5 priority changes (`setPriorityOnCore`): a raise on a current thread
flags nothing (precision), a drop on it flags its core, a re-bucket of a
queued thread flags its home. -/
private def runPriorityChecks : IO Unit := do
  IO.println "--- §2.5 setPriorityOnCore ---"
  let postRaise ← ofExcept "raise on a remote current thread"
    (setPriorityOnCore stBase vBoss vCur1 ⟨9⟩ core0)
  checkDiff "raise on a remote current thread" stBase postRaise core0 true
  expectRaised "raise on a remote current thread" stBase postRaise core0 []
  assertBool "raise on a current thread: core 1's flag stays false (precision)"
    (!(flagOf postRaise core1))
  let postDrop ← ofExcept "drop on a remote current thread"
    (setPriorityOnCore stBase vBoss vCur1 ⟨3⟩ core0)
  checkDiff "drop on a remote current thread" stBase postDrop core0 true
  expectRaised "drop on a remote current thread" stBase postDrop core0 [core1]
  let postQueued ← ofExcept "re-bucket of a remote queued thread"
    (setPriorityOnCore stBase vBoss vSrv ⟨6⟩ core0)
  checkDiff "re-bucket of a remote queued thread" stBase postQueued core0 true
  expectRaised "re-bucket of a remote queued thread" stBase postQueued core0 [core1]
  let postSame ← ofExcept "unchanged priority of a remote queued thread"
    (setPriorityOnCore stBase vBoss vSrv ⟨5⟩ core0)
  checkDiff "unchanged priority of a remote queued thread" stBase postSame core0 true
  expectRaised "unchanged priority of a remote queued thread" stBase postSame core0 []

/-- §2.6 affinity migration (`setThreadCpuAffinityWithMigration`). -/
private def runAffinityChecks : IO Unit := do
  IO.println "--- §2.6 setThreadCpuAffinityWithMigration ---"
  let post ← ofExcept "migration core1 → core2"
    (setThreadCpuAffinityWithMigration stBase srv (some core2) core0)
  checkDiff "migration core1 → core2" stBase post core0 true
  assertBool "migration: the destination core 2 is flagged" (flagOf post core2)
  assertBool "migration: the queued thread now lives on core 2"
    (decide (srv ∈ post.scheduler.runQueueOnCore core2))

/-- The lent scheduling context of §2.7, deadline 9. -/
private def scLent : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 300
/-- The server holding the lent context, running on core 0. -/
private def lendSrv : SeLe4n.ThreadId := ThreadId.ofNat 230
/-- The recorded origin the return hands the context to: unbound, queued on core 1. -/
private def lendOrigin : SeLe4n.ThreadId := ThreadId.ofNat 231

private def stLent : SystemState :=
  let base := BootstrapBuilder.empty
    |>.withObject lendSrv.toObjId (.tcb { mkReadyTcb 230 5 (some core0) .Running with
        schedContextBinding := .donated scLent lendOrigin })
    |>.withObject lendOrigin.toObjId (.tcb (mkReadyTcb 231 6 (some core1) .Ready))
    |>.withObject scLent.toObjId (.schedContext { SchedContext.empty scLent with
        boundThread := some lendSrv, deadline := ⟨9⟩ })
    |>.build
  { base with
      scheduler := base.scheduler.setRunQueueOnCore core1 (RunQueue.ofList [(lendOrigin, ⟨6⟩)])
        |>.setCurrentOnCore core0 (some lendSrv) }

/-- §2.7 the scheduling-context return (`returnDonatedSchedContext`): the
recipient's effective deadline moves to the context's, and the recipient is
queued on another core, so that core is flagged. -/
private def runDonationReturnChecks : IO Unit := do
  IO.println "--- §2.7 returnDonatedSchedContext ---"
  match returnDonatedSchedContext stLent lendSrv scLent lendOrigin none with
  | .ok post =>
    checkDiff "return to a recipient queued on a remote core" stLent post core0 true
    expectRaised "return to a recipient queued on a remote core" stLent post core0 [core1]
  | .error e =>
    IO.println s!"  FAIL: returnDonatedSchedContext returned {repr e}"
    throw (IO.userError "returnDonatedSchedContext failed")

/-- The bound scheduling context of §2.8, deadline 9. -/
private def scBound : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 301
/-- The thread bound to it, queued on core 1. -/
private def boundTid : SeLe4n.ThreadId := ThreadId.ofNat 240

private def boundTcb : TCB :=
  { mkReadyTcb 240 6 (some core1) .Ready with schedContextBinding := .bound scBound }

private def stBound : SystemState :=
  let base := BootstrapBuilder.empty
    |>.withObject boundTid.toObjId (.tcb boundTcb)
    |>.withObject scBound.toObjId (.schedContext { SchedContext.empty scBound with
        boundThread := some boundTid, deadline := ⟨9⟩ })
    |>.build
  { base with
      scheduler := base.scheduler.setRunQueueOnCore core1 (RunQueue.ofList [(boundTid, ⟨6⟩)]) }

/-- §2.8 the bound unbind (`cancelBoundDonationOnCore`): the thread's effective
deadline stops being the context's, and the thread is queued on another core,
so that core is flagged. -/
private def runBoundUnbindChecks : IO Unit := do
  IO.println "--- §2.8 cancelBoundDonationOnCore ---"
  match cancelBoundDonationOnCore stBound boundTid boundTcb core1 with
  | .ok post =>
    checkDiff "unbind of a thread queued on a remote core" stBound post core0 false
    expectRaised "unbind of a thread queued on a remote core" stBound post core0 [core1]
  | .error e =>
    IO.println s!"  FAIL: cancelBoundDonationOnCore returned {repr e}"
    throw (IO.userError "cancelBoundDonationOnCore failed")

/-- Reconfigure `scBound` from core 0 with the fixture's own priority (6) and
deadline (9), so only the domain can move the bound thread's key. -/
private def configureBound (domain : Nat) (pre : SystemState := stBound) : IO SystemState := do
  match scBound.toObjId.toValid? with
  | none => throw (IO.userError "scBound has no valid object id")
  | some vSc =>
    match SeLe4n.Kernel.SchedContextOps.schedContextConfigure vSc 1 10 6 9 domain pre with
    | .ok (_, post) => pure post
    | .error e =>
      IO.println s!"  FAIL: schedContextConfigure returned {repr e}"
      throw (IO.userError "schedContextConfigure failed")

/-- §2.9 the reconfigure that moves only the bound thread's domain
(`schedContextConfigure`): the selector filters by domain, so a thread queued
on another core changed eligibility there and that core is flagged; the same
reconfigure with the domain left alone flags nothing. -/
private def runDomainMoveChecks : IO Unit := do
  IO.println "--- §2.9 schedContextConfigure domain move ---"
  let moved ← configureBound 1
  assertBool "domain move reached the bound thread"
    ((moved.getTcb? boundTid).map (·.domain.val) == some 1)
  checkDiff "domain move of a thread queued on a remote core" stBound moved core0 true
  expectRaised "domain move of a thread queued on a remote core" stBound moved core0 [core1]
  let same ← configureBound 0
  checkDiff "reconfigure that keeps the domain" stBound same core0 true
  expectRaised "reconfigure that keeps the domain" stBound same core0 []

/-- `boundTid` RUNNING on core 1 (not queued), optionally with `srv` (priority 5,
domain 0) queued behind it. -/
private def stBoundCurrent (withSrv : Bool) : SystemState :=
  let base := BootstrapBuilder.empty
    |>.withObject boundTid.toObjId (.tcb { boundTcb with threadState := .Running })
    |>.withObject scBound.toObjId (.schedContext { SchedContext.empty scBound with
        boundThread := some boundTid, deadline := ⟨9⟩ })
    |>.withObject srv.toObjId (.tcb (mkReadyTcb 200 5 (some core1) .Ready))
    |>.build
  let sched := base.scheduler.setCurrentOnCore core1 (some boundTid)
  { base with scheduler :=
      if withSrv then sched.setRunQueueOnCore core1 (RunQueue.ofList [(srv, ⟨5⟩)]) else sched }

/-- Run core 1's reschedule handler, as the SGI the flag sends would. -/
private def receiveOnCore1 (name : String) (st : SystemState) : IO SystemState := do
  match handleRescheduleSgiOnCore st core1 with
  | .ok post => pure post
  | .error e =>
    IO.println s!"  FAIL: {name}: handleRescheduleSgiOnCore returned {repr e}"
    throw (IO.userError s!"{name} failed")

/-- §2.10 the receiver evicts an incumbent the reconfigure moved out of the
core's active domain: with nothing else runnable core 1 goes idle and keeps the
thread queued; with an in-domain thread queued, that thread runs even though
its priority is lower.  The same reconfigure that keeps the domain leaves the
incumbent running. -/
private def runDomainEvictionChecks : IO Unit := do
  IO.println "--- §2.10 the receiver evicts an out-of-domain incumbent ---"
  let pre := stBoundCurrent false
  let moved ← configureBound 1 pre
  expectRaised "domain move of a thread running on a remote core" pre moved core0 [core1]
  checkDiff "domain move of a thread running on a remote core" pre moved core0 true
  let idle ← receiveOnCore1 "eviction to idle" moved
  assertBool "eviction to idle: core 1 runs nothing"
    (idle.scheduler.currentOnCore core1 == none)
  assertBool "eviction to idle: the thread stays queued on core 1"
    (boundTid ∈ (idle.scheduler.runQueueOnCore core1))
  assertBool "eviction to idle: core 1's flag is cleared" (!flagOf idle core1)
  let preSrv := stBoundCurrent true
  let movedSrv ← configureBound 1 preSrv
  let switched ← receiveOnCore1 "eviction to a lower-priority thread" movedSrv
  assertBool "eviction to a lower-priority thread: srv runs on core 1"
    (switched.scheduler.currentOnCore core1 == some srv)
  assertBool "eviction to a lower-priority thread: the evicted thread is queued"
    (boundTid ∈ (switched.scheduler.runQueueOnCore core1))
  let kept ← configureBound 0 preSrv
  let stays ← receiveOnCore1 "reconfigure that keeps the domain" kept
  assertBool "reconfigure that keeps the domain: the incumbent keeps running"
    (stays.scheduler.currentOnCore core1 == some boundTid)

/-- §2.11 the same domain move made **on the core the thread runs on** (the
thread reconfigures its own context): the flag the writer raises is the
executing core's own, which no SGI carries, so the commit seams' local
reschedule (`scheduleLocalSuccessor`, executing core 1) consumes it and evicts
the caller.  A reconfigure that keeps the domain raises no flag and the rule is
the identity. -/
private def runLocalDomainEvictionChecks : IO Unit := do
  IO.println "--- §2.11 the executing core consumes its own flag ---"
  let pre := stBoundCurrent false
  let moved ← configureBound 1 pre
  assertBool "local domain move: core 1's own flag is raised" (flagOf moved core1)
  assertBool "local domain move: no SGI names the executing core"
    (rescheduleSgisFromFlags pre.scheduler.reschedulePending
      moved.scheduler.reschedulePending core1).isEmpty
  let idle := PriorityInheritance.scheduleLocalSuccessor pre moved core1
  assertBool "local eviction to idle: core 1 runs nothing"
    (idle.scheduler.currentOnCore core1 == none)
  assertBool "local eviction to idle: the thread stays queued on core 1"
    (boundTid ∈ (idle.scheduler.runQueueOnCore core1))
  assertBool "local eviction to idle: core 1's flag is cleared" (!flagOf idle core1)
  assertBool "local eviction to idle: core 1 resumes the idle loop, not the evicted thread"
    (match Architecture.restoreTargetOnCore idle core1 with | .idle => true | _ => false)
  let preSrv := stBoundCurrent true
  let movedSrv ← configureBound 1 preSrv
  let switched := PriorityInheritance.scheduleLocalSuccessor preSrv movedSrv core1
  assertBool "local eviction to a lower-priority thread: srv runs on core 1"
    (switched.scheduler.currentOnCore core1 == some srv)
  let kept ← configureBound 0 preSrv
  assertBool "local reconfigure that keeps the domain: no flag" (!flagOf kept core1)
  let stays := PriorityInheritance.scheduleLocalSuccessor preSrv kept core1
  assertBool "local reconfigure that keeps the domain: the caller keeps running"
    (stays.scheduler.currentOnCore core1 == some boundTid)

-- ============================================================================
-- §3  Scheduling points clear their own flag and nobody else's
-- ============================================================================

private def stMarked : SystemState :=
  (stBase.markReschedulePendingOnCore core1).markReschedulePendingOnCore core2

private def checkCleared (name : String) (r : Except KernelError SystemState) : IO Unit := do
  match r with
  | .ok post =>
    assertBool s!"{name}: core 1's flag is cleared" (!(flagOf post core1))
    assertBool s!"{name}: core 2's flag is untouched" (flagOf post core2)
    assertBool s!"{name}: core 0's flag is untouched" (!(flagOf post core0))
  | .error e =>
    IO.println s!"  FAIL: {name} returned {repr e}"
    throw (IO.userError s!"{name} failed")

private def runClearChecks : IO Unit := do
  IO.println "--- §3 clearing at the scheduling points ---"
  assertBool "fixture: core 1 and core 2 flagged" (flagOf stMarked core1 && flagOf stMarked core2)
  checkCleared "handleRescheduleSgiOnCore core1" (handleRescheduleSgiOnCore stMarked core1)
  checkCleared "scheduleEffectiveOnCore core1" (scheduleEffectiveOnCore stMarked core1)

-- ============================================================================
-- §4  Monotonicity: no writer lowers a flag
-- ============================================================================

private def allFlagged (st : SystemState) : Bool := allCores.all (flagOf st ·)

private def stAllMarked : SystemState :=
  allCores.foldl (fun s c => s.markReschedulePendingOnCore c) stBase
private def stNoRqAllMarked : SystemState :=
  allCores.foldl (fun s c => s.markReschedulePendingOnCore c) stNoRq

private def runMonotonicityChecks : IO Unit := do
  IO.println "--- §4 monotonicity ---"
  assertBool "fixture: every core flagged" (allFlagged stAllMarked)
  assertBool "pipBoostWithWake keeps every flag" (allFlagged (pipBoostWithWake stAllMarked srv core0).1)
  assertBool "wakeThread keeps every flag" (allFlagged (wakeThread stNoRqAllMarked srv core0).1)
  assertBool "removeRunnableOnCore keeps every flag"
    (allFlagged (removeRunnableOnCore stAllMarked cur1 core1))
  let postDrop ← ofExcept "setPriorityOnCore (monotonicity)"
    (setPriorityOnCore stAllMarked vBoss vCur1 ⟨3⟩ core0)
  assertBool "setPriorityOnCore keeps every flag" (allFlagged postDrop)
  let postMig ← ofExcept "setThreadCpuAffinityWithMigration (monotonicity)"
    (setThreadCpuAffinityWithMigration stAllMarked srv (some core2) core0)
  assertBool "setThreadCpuAffinityWithMigration keeps every flag" (allFlagged postMig)
  let postSus ← ofExcept "suspendThreadOnCore (monotonicity)"
    (suspendThreadOnCore stAllMarked vCur1 core0)
  assertBool "suspendThreadOnCore keeps every flag" (allFlagged postSus)

def runReschedulePendingChecks : IO Unit := do
  IO.println "=== Reschedule-pending accumulator differential suite ==="
  runBoostChecks
  runWakeChecks
  runRemovalChecks
  runSuspendChecks
  runPriorityChecks
  runAffinityChecks
  runDonationReturnChecks
  runBoundUnbindChecks
  runDomainMoveChecks
  runDomainEvictionChecks
  runLocalDomainEvictionChecks
  runClearChecks
  runMonotonicityChecks
  IO.println "=== reschedule_pending_suite: all checks passed ==="

end SeLe4n.Testing.ReschedulePending

def main : IO Unit :=
  SeLe4n.Testing.ReschedulePending.runReschedulePendingChecks
