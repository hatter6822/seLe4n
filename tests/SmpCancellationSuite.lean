-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.Cancellation
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM6.E — Cross-core cancellation test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM6.E
"Cancellation across cores" deliverable
(`docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.1, §5).

* **§1 Surface anchors** — every public SM6.E symbol resolves at elaboration
  time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply the headline theorems (the
  `cancellation_cross_core_correct` flagship, SGI emission, 2PL atomicity)
  to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_cancellation_suite` exercises the
  actual `cancelIpcBlockingOnCore` / `cancelDonationOnCore` /
  `lockSet_cancelIpcBlocking` computations on the SM6.E cancellation
  scenarios: cancelling endpoint-blocked / notification-blocked /
  reply-blocked victims homed on a remote core, descheduling an actively
  running remote victim (SGI) vs a local one (no SGI), the per-core
  donation-cancellation arms (bound unbind with home-core replenish-queue
  purge; donated return-to-owner), the dispatcher identity on `.unbound`,
  the state-resolved lock-set footprints, and the `withLockSet` bracket's
  operational atomicity.
-/

namespace SeLe4n.Testing.SmpCancellation

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Kernel.Lifecycle.Suspend
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM6.E public symbol resolves
-- ============================================================================

-- SM6.E.5 the per-core deschedule primitive (wakeThread dual) + its surface:
#check @descheduleThread
#check @descheduleThread_state_eq
#check @descheduleThread_objects_eq
#check @descheduleThread_emits_sgi_if_remote_current
#check @descheduleThread_no_sgi_if_local
#check @descheduleThread_no_sgi_if_not_current
#check @descheduleThread_no_sgi_if_ghost
#check @descheduleThread_descheduled_on_home
#check @descheduleThread_independent_of_other_core

-- SM6.E.1/.5 cross-core cancellation transitions + reductions:
#check @cancelIpcBlockingOnCore
#check @cancelIpcBlockingOnCore_state_eq
#check @cancelIpcBlockingOnCore_objects_eq
#check @cancelIpcBlockingOnCore_eq_descheduleThread
#check @cancelIpcBlockingOnCore_ready_eq_descheduleThread

-- SM6.E.3 per-core donation cancellation + the bootCore bridge:
#check @cancelBoundDonationOnCore
#check @cancelBoundDonationOnCore_bootCoreId
#check @cancelDonationOnCore

-- SM6.E.5 SGI emission of the composite:
#check @cancelIpcBlockingOnCore_emits_sgi_if_remote_current
#check @cancelIpcBlockingOnCore_no_sgi_if_local
#check @cancelIpcBlockingOnCore_no_sgi_if_not_current
#check @cancelIpcBlockingOnCore_no_sgi_if_ghost

-- SM6.E.1/.3 lock-set footprints + pre-resolution + state-resolved forms:
#check @cancelBlockedEndpoint?
#check @cancelBlockedNotification?
#check @cancelConsumedReply?
#check @cancelBindingSc?
#check @cancelDonatedOwner?
#check @lockSet_cancelIpcBlocking
#check @lockSet_cancelDonation
#check @lockSet_cancelIpcBlockingOnCore
#check @lockSet_cancelDonationOnCore

-- SM6.E.1/.3 lock-set hierarchical correctness:
#check @lockSet_consistent_cancelIpcBlocking
#check @lockSet_consistent_cancelDonation
#check @cancelIpcBlockingOnCore_lockSet_correct
#check @cancelDonationOnCore_lockSet_correct
#check @lockSet_cancelIpcBlockingOnCore_correct
#check @lockSet_cancelDonationOnCore_correct

-- SM6.E write coverage (cancellation footprints + the enclosing suspend
-- footprint, member-by-member):
#check @mem_insertOrMerge_write_of_mem_write
#check @mem_write_lockSetExtendOpt
#check @lockSet_cancelIpcBlocking_victim_tcb_write_mem
#check @lockSet_cancelIpcBlocking_blocked_endpoint_write_mem
#check @lockSet_cancelIpcBlocking_blocked_notification_write_mem
#check @lockSet_cancelIpcBlocking_consumed_reply_write_mem
#check @lockSet_cancelDonation_victim_tcb_write_mem
#check @lockSet_cancelDonation_binding_sc_write_mem
#check @lockSet_cancelDonation_donated_owner_tcb_write_mem
#check @lockSet_tcbSuspend_victim_tcb_write_mem
#check @lockSet_tcbSuspend_blocked_endpoint_write_mem
#check @lockSet_tcbSuspend_blocked_notification_write_mem
#check @lockSet_tcbSuspend_binding_sc_write_mem
#check @lockSet_tcbSuspend_donated_owner_tcb_write_mem
#check @lockSet_tcbSuspend_consumed_reply_write_mem

-- SM6.E.2/.4 2PL atomicity (single-core + cross-core forms):
#check @cancelIpcBlocking_atomic_under_lockSet
#check @cancelIpcBlockingOnCore_atomic_under_lockSet
#check @cancelDonation_atomic_under_lockSet
#check @cancelDonationOnCore_atomic_under_lockSet

-- SM6.E invariant preservation + per-core donation frames:
#check @cancelIpcBlocking_preserves_objects_invExt
#check @cancelIpcBlockingOnCore_preserves_objects_invExt
#check @cancelBoundDonation_preserves_objects_invExt
#check @cancelBoundDonationOnCore_preserves_objects_invExt
#check @cancelDonatedDonation_preserves_objects_invExt
#check @cancelDonation_preserves_objects_invExt
#check @cancelDonationOnCore_preserves_objects_invExt
#check @cancelDonatedDonation_scheduler_eq
#check @cancelBoundDonationOnCore_runQueue_current_eq
#check @cancelBoundDonationOnCore_replenishQueue_purged
#check @cancelBoundDonationOnCore_replenishQueue_ne
#check @cancelDonationOnCore_runQueue_current_eq

-- SM6.E cleanup-primitive invExt lemmas (CleanupPreservation):
#check @spliceOutMidQueueNode_preserves_objects_invExt
#check @removeFromAllEndpointQueues_preserves_objects_invExt
#check @removeFromAllNotificationWaitLists_preserves_objects_invExt
#check @cleanupDonatedSchedContext_preserves_objects_invExt

-- SM6.E flagship:
#check @cancellation_cross_core_correct

-- ============================================================================
-- §2  Elaboration-time examples: headline theorems applied
-- ============================================================================

section ElaborationExamples

variable (victim : SeLe4n.ThreadId) (tcb tcb0 : TCB) (ec : CoreId)
variable (st s : SystemState)
variable (blEp blN : Option SeLe4n.ObjId) (r? : Option SeLe4n.ReplyId)
variable (sc? : Option SeLe4n.SchedContextId) (ot? : Option SeLe4n.ThreadId)

/-- SM6.E.5: the flagship's remote-poke conjunct applies. -/
example (h1 : st.getTcb? victim = some tcb0)
    (h2 : st.scheduler.currentOnCore (determineTargetCore st victim) = some victim)
    (h3 : determineTargetCore st victim ≠ ec) :
    (cancelIpcBlockingOnCore victim tcb ec st).2
      = some (determineTargetCore st victim, SgiKind.reschedule) :=
  (cancellation_cross_core_correct victim tcb tcb0 ec st h1 h2 h3).1

/-- SM6.E.5: the flagship's home-core deschedule conjunct applies. -/
example (h1 : st.getTcb? victim = some tcb0)
    (h2 : st.scheduler.currentOnCore (determineTargetCore st victim) = some victim)
    (h3 : determineTargetCore st victim ≠ ec) :
    victim ∉ (cancelIpcBlockingOnCore victim tcb ec st).1.scheduler.runQueueOnCore
        (determineTargetCore st victim) :=
  (cancellation_cross_core_correct victim tcb tcb0 ec st h1 h2 h3).2.1

/-- SM6.E.5: the flagship's object-level fidelity conjunct applies. -/
example (h1 : st.getTcb? victim = some tcb0)
    (h2 : st.scheduler.currentOnCore (determineTargetCore st victim) = some victim)
    (h3 : determineTargetCore st victim ≠ ec) :
    (cancelIpcBlockingOnCore victim tcb ec st).1.objects
      = (cancelIpcBlocking st victim tcb).objects :=
  (cancellation_cross_core_correct victim tcb tcb0 ec st h1 h2 h3).2.2.2.2

/-- SM6.E.2: the single-core atomicity theorem applies (2PL bracket shape). -/
example :
    withLockSet (lockSet_cancelIpcBlocking victim blEp blN r?) ec
        (fun st => (cancelIpcBlocking st victim tcb, ())) s
      = (releaseAll ec
          (lockSet_cancelIpcBlocking victim blEp blN r?).lockAcquireSequence.reverse
          (cancelIpcBlocking
            (acquireAll ec (lockSet_cancelIpcBlocking victim blEp blN r?).lockAcquireSequence s)
            victim tcb),
         ()) :=
  cancelIpcBlocking_atomic_under_lockSet victim tcb ec blEp blN r? s

/-- SM6.E.4: the donation atomicity companion applies (dispatcher form). -/
example :
    withLockSet (lockSet_cancelDonation victim sc? ot?) ec
        (cancelDonationOnCore victim tcb) s
      = (releaseAll ec
          (lockSet_cancelDonation victim sc? ot?).lockAcquireSequence.reverse
          (cancelDonationOnCore victim tcb
            (acquireAll ec (lockSet_cancelDonation victim sc? ot?).lockAcquireSequence s)).1,
         (cancelDonationOnCore victim tcb
            (acquireAll ec (lockSet_cancelDonation victim sc? ot?).lockAcquireSequence s)).2) :=
  cancelDonationOnCore_atomic_under_lockSet victim tcb ec sc? ot? s

/-- SM6.E.1: `objects.invExt` transports through the cross-core cancellation. -/
example (hInv : st.objects.invExt) :
    (cancelIpcBlockingOnCore victim tcb ec st).1.objects.invExt :=
  cancelIpcBlockingOnCore_preserves_objects_invExt victim tcb ec st hInv

end ElaborationExamples

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM6.E cancellation scenarios
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

private def core1 : CoreId := ⟨1, by decide⟩

private def epId : SeLe4n.ObjId := ⟨700⟩
private def nId : SeLe4n.ObjId := ⟨701⟩
private def rId : SeLe4n.ReplyId := ⟨702⟩
private def scId : SeLe4n.SchedContextId := SeLe4n.SchedContextId.ofNat 703
private def cnRoot : SeLe4n.ObjId := ⟨300⟩
private def victimTid : SeLe4n.ThreadId := ⟨710⟩
private def ownerTid : SeLe4n.ThreadId := ⟨711⟩
private def bystanderTid : SeLe4n.ThreadId := ⟨712⟩

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := ⟨310⟩, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
    cpuAffinity := aff }

/-- The victim's TCB as stored in `st` (`default` when absent — assertions on
absent lookups fail loudly through the field checks). -/
private def victimTcb (st : SystemState) : TCB :=
  (st.getTcb? victimTid).getD (mkTcb 710 30 none)

-- ----------------------------------------------------------------------------
-- Scenario A: victim homed on core 1, blocked on an endpoint call
-- (driven through the real `endpointCallOnCore` block path).
-- ----------------------------------------------------------------------------

/-- Base: an endpoint (no receiver) + a core1-homed victim + a bystander,
victim runnable on the boot core (it will block itself via `.call`). -/
private def stCallBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject epId (.endpoint {})
    |>.withObject victimTid.toObjId (.tcb (mkTcb 710 30 (some core1)))
    |>.withObject bystanderTid.toObjId (.tcb (mkTcb 712 20 none))
    |>.withRunnable [victimTid, bystanderTid]
    |>.build)

/-- Drive the victim into `.blockedOnCall epId` via the real cross-core call
(block path: no receiver waiting). -/
private def stCallBlocked? : Option SystemState :=
  match endpointCallOnCore epId victimTid IpcMessage.empty bootCoreId stCallBase with
  | (st, .ok none) => some st
  | _ => none

private def runEndpointCancelChecks : IO Unit := do
  IO.println "--- §3.1 SM6.E.5 cancel an endpoint-blocked victim (remote home, no SGI) ---"
  match stCallBlocked? with
  | some st =>
      let tcb := victimTcb st
      assertBool "setup: victim is .blockedOnCall on the endpoint"
        (decide (tcb.ipcState = .blockedOnCall epId))
      -- Pre-resolution names the endpoint (and nothing else).
      assertBool "cancelBlockedEndpoint? resolves the blocked-on endpoint"
        (decide (cancelBlockedEndpoint? tcb = some epId))
      assertBool "cancelBlockedNotification?/cancelConsumedReply? resolve none"
        (decide (cancelBlockedNotification? tcb = none ∧ cancelConsumedReply? tcb = none))
      let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      -- A blocked victim is not current anywhere: no SGI even though its home
      -- core (core 1) is remote.
      assertBool "cancelling a blocked (non-running) remote victim surfaces no SGI"
        (decide (sgi = none))
      -- The victim's IPC teardown: .ready + cleared queue links.
      assertBool "victim ipcState is .ready after cancellation"
        (match st'.getTcb? victimTid with
         | some t => decide (t.ipcState = .ready ∧ t.queuePrev = none ∧ t.queueNext = none)
         | none => false)
      -- The endpoint's send queue no longer references the victim.
      assertBool "endpoint send queue is emptied of the victim"
        (match st'.objects[epId]? with
         | some (.endpoint ep) =>
             decide (ep.sendQ.head ≠ some victimTid ∧ ep.sendQ.tail ≠ some victimTid)
         | _ => false)
      -- Object-level fidelity: same objects as the single-core teardown.
      assertBool "cross-core post-objects = single-core cancelIpcBlocking objects"
        (((cancelIpcBlocking st victimTid tcb).objects[victimTid.toObjId]?
            == st'.objects[victimTid.toObjId]?)
         && ((cancelIpcBlocking st victimTid tcb).objects[epId]?
            == st'.objects[epId]?))
      -- State-resolved lock-set: victim TCB write + endpoint write, permitted + Nodup.
      let ls := lockSet_cancelIpcBlockingOnCore st victimTid
      assertBool "state-resolved cancel lock-set kinds all permitted (.tcbSuspend)"
        (decide (∀ p ∈ ls.pairs, p.fst.kind ∈ permittedKinds .tcbSuspend))
      assertBool "state-resolved cancel lock-set keys are duplicate-free"
        (decide ((ls.pairs.map (·.fst)).Nodup))
      assertBool "victim TCB write lock is in the cancel footprint"
        (decide ((tcbLock victimTid, AccessMode.write) ∈ ls.pairs))
      assertBool "blocked endpoint write lock is in the cancel footprint"
        (decide ((endpointLock epId, AccessMode.write) ∈ ls.pairs))
      assertBool "no notification/reply lock in the endpoint-blocked footprint"
        (decide ((notificationLock nId, AccessMode.write) ∉ ls.pairs
          ∧ (replyLock rId, AccessMode.write) ∉ ls.pairs))
  | none => assertBool "setup: endpointCallOnCore block path succeeded" false

-- ----------------------------------------------------------------------------
-- Scenario B: victim blocked on a notification (driven through the real
-- `notificationWaitOnCore` block path), homed on core 1.
-- ----------------------------------------------------------------------------

private def stNtfnBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject nId (.notification { state := .idle, waitingThreads := SeLe4n.NoDupList.empty })
    |>.withObject victimTid.toObjId (.tcb (mkTcb 710 30 (some core1)))
    |>.withRunnable [victimTid]
    |>.build)

private def stNtfnBlocked? : Option SystemState :=
  match notificationWaitOnCore nId victimTid bootCoreId stNtfnBase with
  | (st, .ok none) => some st
  | _ => none

private def runNotificationCancelChecks : IO Unit := do
  IO.println "--- §3.2 SM6.E.5 cancel a notification-blocked victim ---"
  match stNtfnBlocked? with
  | some st =>
      let tcb := victimTcb st
      assertBool "setup: victim is .blockedOnNotification"
        (decide (tcb.ipcState = .blockedOnNotification nId))
      assertBool "cancelBlockedNotification? resolves the notification"
        (decide (cancelBlockedNotification? tcb = some nId))
      let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      assertBool "cancelling a notification-blocked victim surfaces no SGI"
        (decide (sgi = none))
      assertBool "victim ipcState is .ready after cancellation"
        (match st'.getTcb? victimTid with
         | some t => decide (t.ipcState = .ready)
         | none => false)
      assertBool "the victim is dropped from the notification's waiter list"
        (match st'.objects[nId]? with
         | some (.notification ntfn) => decide (victimTid ∉ ntfn.waitingThreads.val)
         | _ => false)
      -- State-resolved lock-set picks the notification write lock.
      let ls := lockSet_cancelIpcBlockingOnCore st victimTid
      assertBool "blocked notification write lock is in the cancel footprint"
        (decide ((notificationLock nId, AccessMode.write) ∈ ls.pairs))
  | none => assertBool "setup: notificationWaitOnCore block path succeeded" false

-- ----------------------------------------------------------------------------
-- Scenario C: victim blocked awaiting a reply, holding a live reply link.
-- ----------------------------------------------------------------------------

private def stReplyBlocked : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject epId (.endpoint {})
    |>.withObject rId.toObjId (.reply { replyId := rId, caller := some victimTid })
    |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
        ipcState := .blockedOnReply epId (some ownerTid),
        replyObject := some rId })
    |>.build)

private def runReplyCancelChecks : IO Unit := do
  IO.println "--- §3.3 SM6.E.5 cancel a reply-blocked victim (reply link consumed) ---"
  let tcb := victimTcb stReplyBlocked
  assertBool "cancelConsumedReply? resolves the victim's reply object"
    (decide (cancelConsumedReply? tcb = some rId))
  let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb bootCoreId stReplyBlocked
  assertBool "cancelling a reply-blocked victim surfaces no SGI"
    (decide (sgi = none))
  assertBool "victim ipcState is .ready and its reply forward link is cleared"
    (match st'.getTcb? victimTid with
     | some t => decide (t.ipcState = .ready ∧ t.replyObject = none)
     | none => false)
  assertBool "the Reply object's caller back-link is severed"
    (match st'.getReply? rId with
     | some r => decide (r.caller = none)
     | none => false)
  -- State-resolved lock-set picks the reply write lock (the SM6.E footprint
  -- extension closing the SM6.D reply-fold gap).
  let ls := lockSet_cancelIpcBlockingOnCore stReplyBlocked victimTid
  assertBool "consumed Reply write lock is in the cancel footprint"
    (decide ((replyLock rId, AccessMode.write) ∈ ls.pairs))
  assertBool "reply-extended footprint kinds all permitted (.tcbSuspend now covers .reply)"
    (decide (∀ p ∈ ls.pairs, p.fst.kind ∈ permittedKinds .tcbSuspend))
  -- The enclosing suspend footprint also covers the reply write.
  assertBool "suspend footprint covers the consumed Reply write lock"
    (decide ((replyLock rId, AccessMode.write) ∈
      (lockSet_tcbSuspend bystanderTid cnRoot victimTid none none none none
        (some rId)).pairs))

-- ----------------------------------------------------------------------------
-- Scenario D: actively RUNNING victim on a remote core (cross-core suspend).
-- ----------------------------------------------------------------------------

private def stRunningRemote : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb (mkTcb 710 30 (some core1)))
      |>.withObject bystanderTid.toObjId (.tcb (mkTcb 712 20 none))
      |>.withRunnable [bystanderTid]
      |>.build)
  { base with scheduler := base.scheduler.setCurrentOnCore core1 (some victimTid) }

private def runRemoteRunningCancelChecks : IO Unit := do
  IO.println "--- §3.4 SM6.E.5 cancel a victim RUNNING on a remote core (SGI) ---"
  let tcb := victimTcb stRunningRemote
  assertBool "setup: victim is current on core 1"
    (decide (stRunningRemote.scheduler.currentOnCore core1 = some victimTid))
  assertBool "setup: the victim's home core resolves to core 1"
    (decide (determineTargetCore stRunningRemote victimTid = core1))
  let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb bootCoreId stRunningRemote
  -- (1) remote poke
  assertBool "cancelling a remotely-running victim fires a reschedule SGI to core 1"
    (decide (sgi = some (core1, SgiKind.reschedule)))
  -- (2) full home-core deschedule
  assertBool "victim is cleared from core 1's current slot"
    (decide (st'.scheduler.currentOnCore core1 ≠ some victimTid))
  assertBool "victim is not in core 1's run queue"
    (decide (victimTid ∉ st'.scheduler.runQueueOnCore core1))
  -- (3) per-core locality: boot core untouched
  assertBool "boot core's run queue and current slot are untouched"
    (decide (bystanderTid ∈ st'.scheduler.runQueueOnCore bootCoreId)
      && decide (st'.scheduler.currentOnCore bootCoreId
        = stRunningRemote.scheduler.currentOnCore bootCoreId))
  -- The `.ready` arm: the composite reduces to the pure deschedule.
  assertBool "a .ready victim's cancellation equals the pure descheduleThread"
    (let d := descheduleThread stRunningRemote victimTid bootCoreId
     decide (sgi = d.2 ∧ st'.scheduler.currentOnCore core1 = d.1.scheduler.currentOnCore core1))

private def runLocalRunningCancelChecks : IO Unit := do
  IO.println "--- §3.5 SM6.E.5 cancel a victim running on the executing core (no SGI) ---"
  -- Same fixture, but the cancel runs ON core 1 (the victim's own core).
  let tcb := victimTcb stRunningRemote
  let (st', sgi) := cancelIpcBlockingOnCore victimTid tcb core1 stRunningRemote
  assertBool "cancelling on the victim's own core surfaces no SGI"
    (decide (sgi = none))
  assertBool "victim is still cleared from core 1's current slot (local deschedule)"
    (decide (st'.scheduler.currentOnCore core1 ≠ some victimTid))

-- ----------------------------------------------------------------------------
-- Scenario E: donation cancellation — bound arm, remote home core.
-- ----------------------------------------------------------------------------

private def mkSc (bound : Option SeLe4n.ThreadId) (active : Bool) : SchedContext :=
  { scId := scId, boundThread := bound,
    budget := ⟨1000⟩, period := ⟨1000⟩,
    priority := ⟨10⟩, deadline := ⟨0⟩, domain := ⟨0⟩,
    budgetRemaining := ⟨1000⟩, isActive := active, replenishments := [] }

private def stBoundDonation : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
          schedContextBinding := .bound scId })
      |>.withObject scId.toObjId (.schedContext (mkSc (some victimTid) true))
      |>.build)
  -- Seed a pending replenishment for the SC on the victim's home core (core 1),
  -- per the SM5.H affinity discipline.
  let rq1 := (base.scheduler.replenishQueueOnCore core1).insert scId 42
  { base with scheduler := base.scheduler.setReplenishQueueOnCore core1 rq1 }

private def runBoundDonationCancelChecks : IO Unit := do
  IO.println "--- §3.6 SM6.E.3 bound-donation cancel (home-core replenish purge) ---"
  let tcb := victimTcb stBoundDonation
  assertBool "cancelBindingSc? resolves the bound SC"
    (decide (cancelBindingSc? tcb = some scId ∧ cancelDonatedOwner? tcb = none))
  assertBool "setup: core 1's replenish queue holds the SC's entry"
    ((stBoundDonation.scheduler.replenishQueueOnCore core1).entries.any
      (fun e => e.1 == scId))
  let (st', res) := cancelDonationOnCore victimTid tcb stBoundDonation
  assertBool "bound-donation cancel succeeds"
    (match res with | .ok () => true | .error _ => false)
  assertBool "victim's binding is cleared to .unbound"
    (match st'.getTcb? victimTid with
     | some t => decide (t.schedContextBinding = .unbound)
     | none => false)
  assertBool "the SC is deactivated and unbound"
    (match st'.getSchedContext? scId with
     | some sc => decide (sc.boundThread = none ∧ sc.isActive = false)
     | none => false)
  -- The per-core purge: the entry is removed from the HOME core's queue
  -- (the single-core arm would have purged bootCore's queue and left this).
  assertBool "the SC's replenishment is purged from core 1's queue (home core)"
    (!(st'.scheduler.replenishQueueOnCore core1).entries.any (fun e => e.1 == scId))
  assertBool "boot core's replenish queue is untouched"
    (decide ((st'.scheduler.replenishQueueOnCore bootCoreId).entries
      = (stBoundDonation.scheduler.replenishQueueOnCore bootCoreId).entries))
  -- No scheduler run-queue/current disturbance on any core.
  assertBool "run queues and current slots are untouched on both cores"
    (decide (st'.scheduler.currentOnCore bootCoreId
        = stBoundDonation.scheduler.currentOnCore bootCoreId)
      && decide (st'.scheduler.currentOnCore core1
        = stBoundDonation.scheduler.currentOnCore core1)
      && decide ((victimTid ∈ st'.scheduler.runQueueOnCore core1)
        ↔ (victimTid ∈ stBoundDonation.scheduler.runQueueOnCore core1)))
  -- Lock-set: victim TCB write + SC write, permitted + Nodup.
  let ls := lockSet_cancelDonationOnCore stBoundDonation victimTid
  assertBool "donation lock-set kinds all permitted (.tcbSuspend)"
    (decide (∀ p ∈ ls.pairs, p.fst.kind ∈ permittedKinds .tcbSuspend))
  assertBool "SC write lock is in the donation footprint"
    (decide ((schedContextLock scId, AccessMode.write) ∈ ls.pairs))

-- ----------------------------------------------------------------------------
-- Scenario F: donation cancellation — donated arm (return to original owner).
-- ----------------------------------------------------------------------------

private def stDonated : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject victimTid.toObjId (.tcb { mkTcb 710 30 (some core1) with
        schedContextBinding := .donated scId ownerTid })
    |>.withObject ownerTid.toObjId (.tcb (mkTcb 711 25 none))
    |>.withObject scId.toObjId (.schedContext (mkSc (some victimTid) true))
    |>.build)

private def runDonatedDonationCancelChecks : IO Unit := do
  IO.println "--- §3.7 SM6.E.3 donated-donation cancel (return to owner) ---"
  let tcb := victimTcb stDonated
  assertBool "cancelBindingSc?/cancelDonatedOwner? resolve the donated SC + owner"
    (decide (cancelBindingSc? tcb = some scId ∧ cancelDonatedOwner? tcb = some ownerTid))
  let (st', res) := cancelDonationOnCore victimTid tcb stDonated
  assertBool "donated-donation cancel succeeds"
    (match res with | .ok () => true | .error _ => false)
  assertBool "the SC is returned to the original owner"
    (match st'.getSchedContext? scId with
     | some sc => decide (sc.boundThread = some ownerTid)
     | none => false)
  assertBool "the owner's binding is re-established to .bound"
    (match st'.getTcb? ownerTid with
     | some t => decide (t.schedContextBinding = .bound scId)
     | none => false)
  assertBool "the victim's binding is cleared to .unbound"
    (match st'.getTcb? victimTid with
     | some t => decide (t.schedContextBinding = .unbound)
     | none => false)
  -- Owner TCB write lock in the footprint (the plan row's "receiver TCB").
  let ls := lockSet_cancelDonationOnCore stDonated victimTid
  assertBool "original-owner TCB write lock is in the donation footprint"
    (decide ((tcbLock ownerTid, AccessMode.write) ∈ ls.pairs))

-- ----------------------------------------------------------------------------
-- Scenario G: dispatcher identity + ghost victim + bracket atomicity.
-- ----------------------------------------------------------------------------

private def runDispatcherEdgeChecks : IO Unit := do
  IO.println "--- §3.8 SM6.E dispatcher identity, ghost victim, bracket atomicity ---"
  -- `.unbound` dispatcher identity.
  let tcbU := mkTcb 710 30 none
  let stU :=
    (BootstrapBuilder.empty
      |>.withObject victimTid.toObjId (.tcb tcbU)
      |>.build)
  let (stU', resU) := cancelDonationOnCore victimTid tcbU stU
  assertBool "cancelDonationOnCore on .unbound is the identity (.ok, state preserved)"
    ((match resU with | .ok () => true | .error _ => false)
      && (match stU'.getTcb? victimTid with
          | some t => t == tcbU
          | none => false))
  -- Ghost victim: unresolvable tid → no SGI, objects untouched.
  let ghost : SeLe4n.ThreadId := ⟨999⟩
  let (stG, sgiG) := cancelIpcBlockingOnCore ghost (mkTcb 999 1 none) bootCoreId stU
  assertBool "ghost victim: no SGI and untouched victim object"
    (decide (sgiG = none)
      && (match stG.getTcb? victimTid with
          | some t => t == tcbU
          | none => false))
  -- `withLockSet` bracket: the business outcome equals the bare transition's
  -- (locks acquired and released around the same pure step — operational
  -- witness of `cancelIpcBlockingOnCore_atomic_under_lockSet`).
  match stCallBlocked? with
  | some st =>
      let tcb := victimTcb st
      let bare := cancelIpcBlockingOnCore victimTid tcb bootCoreId st
      let bracketed := withLockSet (lockSet_cancelIpcBlockingOnCore st victimTid)
        bootCoreId (cancelIpcBlockingOnCore victimTid tcb bootCoreId) st
      assertBool "withLockSet bracket returns the same SGI decision"
        (decide (bracketed.2 = bare.2))
      assertBool "withLockSet bracket commits the same victim teardown"
        (match bracketed.1.getTcb? victimTid, bare.1.getTcb? victimTid with
         | some a, some b => decide (a.ipcState = b.ipcState ∧ a.ipcState = .ready)
         | _, _ => false)
  | none => assertBool "setup: bracket fixture available" false

-- ============================================================================
-- Aggregate runner
-- ============================================================================

def runSmpCancellationChecks : IO Unit := do
  IO.println "=== SmpCancellationSuite (WS-SM SM6.E cancellation across cores) ==="
  runEndpointCancelChecks
  runNotificationCancelChecks
  runReplyCancelChecks
  runRemoteRunningCancelChecks
  runLocalRunningCancelChecks
  runBoundDonationCancelChecks
  runDonatedDonationCancelChecks
  runDispatcherEdgeChecks
  IO.println "SmpCancellationSuite: all checks passed."

end SeLe4n.Testing.SmpCancellation

def main : IO Unit :=
  SeLe4n.Testing.SmpCancellation.runSmpCancellationChecks
