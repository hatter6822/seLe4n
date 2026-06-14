-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallNI
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallInvariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallEntry
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallNiPerCore
import SeLe4n.Kernel.SyscallDispatchEntry
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM6.A — Cross-core endpoint call test suite

Tier-2 (runtime) + Tier-3 (surface anchor) coverage for the WS-SM Phase SM6.A
"Endpoint call across cores" deliverable
(`docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §3.2, §5).

* **§1 Surface anchors** — every public SM6.A symbol resolves at elaboration
  time (rename/removal fails the build).
* **§2 Elaboration-time examples** — apply each headline theorem (SGI emission,
  per-core blocking, reply linkage, lock-set correctness, donation extension,
  atomicity, cross-core NI) to verified inputs.
* **§3 Runtime assertions** — `lake exe smp_cross_core_call_suite` exercises the
  actual `endpointCallOnCore` / `removeRunnableOnCore` / `lockSet_endpointCall`
  computations on the SM6.A cross-core call scenarios: the lock-set footprint
  and donation extension, the WithCaps lock-set, per-core caller blocking, the
  no-receiver path, and the local vs remote rendezvous SGI emission.
-/

namespace SeLe4n.Testing.SmpCrossCoreCall

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (Tier-3): every SM6.A public symbol resolves
-- ============================================================================

-- SM6.A.1 production transitions:
#check @endpointCallOnCore
#check @removeRunnableOnCore
#check @endpointCallReceiver?
#check @endpointCallDonatedSc?
#check @lockSet_endpointCallOnCore
#check @lockSet_endpointCallOnCore_correct
#check @lockSet_endpointCallWithCaps
#check @removeRunnableOnCore_bootCoreId

-- SM6.A.1 path-reduction lemmas:
#check @endpointCallOnCore_rendezvous_eq
#check @endpointCallOnCore_noReceiver_eq

-- SM6.A.2/.5/.8/.9 lock-set theorems:
#check @endpointCallOnCore_lockSet_correct
#check @lockSet_endpointCall_donation_extension
#check @endpointCallWithCaps_lockSet_correct
#check @endpointCallOnCore_atomic_under_lockSet

-- SM6.A.3 cross-core wake (plan Theorem 3.2.1):
#check @endpointCallOnCore_emits_sgi_if_remote_receiver
#check @endpointCallOnCore_no_sgi_if_local_receiver
#check @endpointCallOnCore_noReceiver_no_sgi

-- SM6.A.4/.6 blocking + reply linkage:
#check @endpointCallOnCore_perCore_blocking
#check @endpointCallOnCore_reply_linkage_under_lockSet

-- SM6.A.7 cross-core non-interference (boot-core projectState):
#check @endpointCallOnCore_call_path_NI
#check @enqueueRunnableOnCore_preserves_projection
#check @removeRunnableOnCore_preserves_projection
#check @wakeThread_preserves_projection

-- SM6.A.7 per-core / ∀-core non-interference (lowEquivalent_smp on every core):
#check @endpointCallOnCore_call_path_NI_smp
#check @endpointQueuePopHead_machine_eq
#check @removeRunnableOnCore_projectCurrentOnCore_high
#check @removeRunnableOnCore_preserves_projectionOnCore

-- SM6.A.1 IPC invariant preservation:
#check @endpointCallOnCore_preserves_objects_invExt
#check @endpointCallOnCore_preserves_ipcInvariant
#check @enqueueRunnableOnCore_objects_getElem_eq_of_ready

-- SM6.A.1 full IPC-invariant-bundle preservation (dual-queue + bounds + badges
-- derived; the lookup-only congruences that carry them):
#check @endpointCallOnCore_preserves_dualQueueSystemInvariant
#check @endpointCallOnCore_preserves_allPendingMessagesBounded
#check @endpointCallOnCore_preserves_badgeWellFormed
#check @endpointCallOnCore_preserves_ipcInvariantFull
#check @dualQueueSystemInvariant_of_getElem_eq

-- SM6.A.6/.9 lock-set membership + invariant preservation through the 2PL bracket:
#check @lockSet_endpointCall_caller_tcb_write_mem
#check @endpointCallOnCore_withLockSet_preserves_objects_invExt

-- SM6.A.5/.8/.10 WithCaps + donation + live FFI seam:
#check @endpointCallWithCapsOnCore
#check @endpointCallCrossCoreDispatch
#check @endpointCallCrossCoreEntry
#check @endpointCallWithCapsOnCore_no_caps
#check @endpointCallCrossCoreDispatch_no_receiver

-- SM6.A info-flow-checked cross-core dispatch (the op the live checked `.call`
-- arm now routes through; the SMP stack is production at v0.31.66):
#check @endpointCallCrossCoreDispatchChecked
#check @endpointCallCrossCoreDispatchChecked_flow_denied
#check @endpointCallCrossCoreDispatchChecked_flow_allowed

-- SM6.A live `.call`: the executing core derived from live state (the caller is
-- the current thread on its core) — no hardware-core parameter threaded:
#check @determineExecutingCore
#check @determineExecutingCore_sound

-- SM6.A live SGI-dispatch seam: the cross-core-aware syscall dispatch entry +
-- its body-shape marker + the single-core inertness (trace-safety) witness:
#check @syscallDispatchCrossCoreEntry
#check @syscallDispatchCrossCoreEntry_def
#check @syscallDispatchCrossCoreEntry_sgis_nil_single_core

-- ============================================================================
-- §2  Elaboration-time examples (Tier-3): theorems apply to typed inputs
-- ============================================================================

/-- SM6.A.3: a rendezvous unblocking a remote receiver emits the reschedule SGI. -/
example (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (recvTcb0 recvTcb'' : TCB) (st' st'' st4 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hTcb'' : st''.getTcb? receiver = some recvTcb'')
    (hRemote : determineTargetCore st'' receiver ≠ executingCore) :
    (endpointCallOnCore endpointId caller msg executingCore st).2
      = .ok (some (determineTargetCore st'' receiver, SgiKind.reschedule)) :=
  endpointCallOnCore_emits_sgi_if_remote_receiver endpointId caller msg executingCore st ep
    receiver recvTcb0 recvTcb'' st' st'' st4 hSz1 hSz2 hObj hHead hPop hStore hCallerStore
    hTcb'' hRemote

/-- SM6.A.9: the call is a single 2PL-atomic step under its lock-set. -/
example (endpointId cnRoot : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (receiver? : Option SeLe4n.ThreadId)
    (donatedSc? : Option SeLe4n.SchedContextId) (s : SystemState) :
    (withLockSet (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?)
        executingCore (endpointCallOnCore endpointId caller msg executingCore) s).2
      = (endpointCallOnCore endpointId caller msg executingCore
          (acquireAll executingCore
            (lockSet_endpointCall caller cnRoot endpointId receiver? donatedSc?).lockAcquireSequence s)).2 := by
  rw [endpointCallOnCore_atomic_under_lockSet]

/-- SM6.A.7: a cross-core call between high principals is invisible to a low observer. -/
example (ctx : LabelingContext) (observer : IfObserver)
    (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
    (executingCore : CoreId) (st : SystemState) (ep : Endpoint)
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hObjInv : st.objects.invExt)
    (hEndpointHigh : objectObservable ctx observer endpointId = false)
    (hReceiverHigh : threadObservable ctx observer receiver = false)
    (hReceiverObjHigh : objectObservable ctx observer receiver.toObjId = false)
    (hCallerHigh : threadObservable ctx observer caller = false)
    (hCallerObjHigh : objectObservable ctx observer caller.toObjId = false)
    (hNextHigh : ∀ nextTid, recvTcb0.queueNext = some nextTid →
        objectObservable ctx observer nextTid.toObjId = false) :
    projectState ctx observer (endpointCallOnCore endpointId caller msg executingCore st).1
      = projectState ctx observer st :=
  endpointCallOnCore_call_path_NI ctx observer endpointId caller msg executingCore st ep receiver
    recvTcb0 st' st'' st4 hSz1 hSz2 hObj hHead hPop hStore hCallerStore hObjInv hEndpointHigh
    hReceiverHigh hReceiverObjHigh hCallerHigh hCallerObjHigh hNextHigh

-- ============================================================================
-- §3  Runtime assertions (Tier-2): the SM6.A cross-core call scenarios
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

private def core1 : CoreId := ⟨1, by decide⟩

private def epId : SeLe4n.ObjId := ⟨400⟩
private def cnRoot : SeLe4n.ObjId := ⟨300⟩
private def destCnode : SeLe4n.ObjId := ⟨301⟩
private def scId : SeLe4n.SchedContextId := ⟨410⟩
private def callerTid : SeLe4n.ThreadId := ⟨401⟩
private def recvLocalTid : SeLe4n.ThreadId := ⟨402⟩
private def recvRemoteTid : SeLe4n.ThreadId := ⟨403⟩

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := ⟨310⟩, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
    cpuAffinity := aff }

/-- Endpoint + unbound caller + unbound (local) receiver + core1-bound (remote) receiver. -/
private def stBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject epId (.endpoint {})
    |>.withObject callerTid.toObjId (.tcb (mkTcb 401 40 none))
    |>.withObject recvLocalTid.toObjId (.tcb (mkTcb 402 30 none))
    |>.withObject recvRemoteTid.toObjId (.tcb (mkTcb 403 30 (some core1)))
    |>.withRunnable [callerTid]
    |>.build)

/-- Drive the receiver onto the endpoint's receive queue (it blocks, no sender). -/
private def stWithReceiver (recv : SeLe4n.ThreadId) : Option SystemState :=
  match endpointReceiveDual epId recv stBase with
  | .ok (_, st) => some st
  | .error _ => none

/-- The optional SGI surfaced by a cross-core call (`none` on a kernel error). -/
private def callSgi (st : SystemState) (ec : CoreId) : Option (CoreId × SgiKind) :=
  match (endpointCallOnCore epId callerTid IpcMessage.empty ec st).2 with
  | .ok sgi => sgi
  | .error _ => none

private def runLockSetChecks : IO Unit := do
  IO.println "--- §3.1 SM6.A.2/.5/.8 lock-set footprint ---"
  -- SM6.A.2: every declared lock has a kind permitted for `.call`.
  assertBool "endpointCall lock-set kinds all permitted (caller W, cnode R, endpoint W)"
    (decide (∀ p ∈ (lockSet_endpointCall callerTid cnRoot epId (some recvRemoteTid)
        (some scId)).pairs, p.fst.kind ∈ permittedKinds .call))
  -- SM6.A.2: keys are duplicate-free.
  assertBool "endpointCall lock-set keys are duplicate-free"
    (decide ((lockSet_endpointCall callerTid cnRoot epId (some recvRemoteTid)
        (some scId)).pairs.map (·.fst)).Nodup)
  -- SM6.A.5: donating extends the footprint by exactly the SC write lock.
  assertBool "donation extends the lock-set by the SchedContext write lock"
    (decide (lockSet_endpointCall callerTid cnRoot epId (some recvRemoteTid) (some scId)
      = lockSetExtendOpt (lockSet_endpointCall callerTid cnRoot epId (some recvRemoteTid) none)
          (some (schedContextLock scId, .write))))
  -- SM6.A.6: the caller-TCB *write* lock — covering the reply-blocked-state
  -- write — is concretely a declared member of the footprint (the membership
  -- behind `lockSet_endpointCall_caller_tcb_write_mem`, on distinct caller/recv).
  assertBool "caller-TCB write lock is in the endpointCall footprint"
    (decide ((tcbLock callerTid, AccessMode.write) ∈
      (lockSet_endpointCall callerTid cnRoot epId (some recvRemoteTid) (some scId)).pairs))
  -- SM6.A.8: the WithCaps lock-set is still hierarchically correct.
  assertBool "endpointCallWithCaps lock-set kinds all permitted (adds dest CNode W)"
    (decide (∀ p ∈ (lockSet_endpointCallWithCaps callerTid cnRoot destCnode epId
        (some recvRemoteTid) (some scId)).pairs, p.fst.kind ∈ permittedKinds .call))
  -- SM6.A.1/.2: the runtime acquires a *state-resolved* lock-set — the receiver
  -- and donated SC pre-resolved from `st` via `endpointCallReceiver?` /
  -- `endpointCallDonatedSc?`.  On the empty base state both resolve to `none`.
  assertBool "endpointCallReceiver? resolves none on an endpoint with no waiter"
    (decide (endpointCallReceiver? stBase epId = none))
  assertBool "endpointCallDonatedSc? resolves none for an unbound caller"
    (decide (endpointCallDonatedSc? stBase callerTid = none))
  assertBool "state-resolved call lock-set kinds all permitted"
    (decide (∀ p ∈ (lockSet_endpointCallOnCore stBase epId callerTid cnRoot).pairs,
        p.fst.kind ∈ permittedKinds .call))

private def runBlockingChecks : IO Unit := do
  IO.println "--- §3.2 SM6.A.1/.4 per-core caller blocking ---"
  -- SM6.A.1: removeRunnableOnCore at the boot core is the legacy removeRunnable
  -- (the bridge `removeRunnableOnCore_bootCoreId` holds by `rfl`; observe it on the
  -- boot run queue, since `SystemState` has no `DecidableEq`).
  assertBool "removeRunnableOnCore bootCore matches removeRunnable on the boot run queue"
    (((removeRunnableOnCore stBase callerTid bootCoreId).scheduler.runQueueOnCore bootCoreId).toList
      == ((removeRunnable stBase callerTid).scheduler.runQueueOnCore bootCoreId).toList)
  -- SM6.A.4: the caller is removed from its own core's run queue.
  assertBool "removeRunnableOnCore deschedules the caller from its core's run queue"
    (!((removeRunnableOnCore stBase callerTid bootCoreId).scheduler.runQueueOnCore bootCoreId).contains callerTid)
  -- SM6.A.4: a sibling core's run queue is untouched (per-core locality).
  assertBool "removeRunnableOnCore on core 1 leaves the boot core's run queue intact"
    ((removeRunnableOnCore stBase callerTid core1).scheduler.runQueueOnCore bootCoreId |>.contains callerTid)

private def runNoReceiverChecks : IO Unit := do
  IO.println "--- §3.3 SM6.A.1 no-receiver path (blockedOnCall) ---"
  let (st', res) := endpointCallOnCore epId callerTid IpcMessage.empty bootCoreId stBase
  -- No receiver waiting ⇒ no cross-core wake ⇒ no SGI.
  assertBool "no-receiver call surfaces no SGI"
    (match res with | .ok none => true | _ => false)
  -- The caller transitions to blockedOnCall and leaves the run queue.
  assertBool "no-receiver call blocks the caller as blockedOnCall"
    (match st'.getTcb? callerTid with
     | some t => decide (t.ipcState = .blockedOnCall epId)
     | none => false)
  assertBool "no-receiver call removes the caller from the boot run queue"
    (!(st'.scheduler.runQueueOnCore bootCoreId).contains callerTid)
  -- SM6.A.5/.8: WithCaps + the full cross-core dispatch agree with the bare call
  -- on the no-receiver path (no caps to transfer; no donation without a server).
  assertBool "no-receiver WithCaps cross-core call also surfaces no SGI"
    (match (endpointCallWithCapsOnCore epId callerTid IpcMessage.empty AccessRightSet.empty
        cnRoot (SeLe4n.Slot.ofNat 0) bootCoreId stBase).2 with
     | .ok (_, none) => true | _ => false)
  assertBool "no-receiver cross-core dispatch performs no donation (= WithCaps)"
    (match (endpointCallCrossCoreDispatch epId callerTid IpcMessage.empty AccessRightSet.empty
        cnRoot (SeLe4n.Slot.ofNat 0) bootCoreId stBase).2 with
     | .ok (_, none) => true | _ => false)

private def runRendezvousChecks : IO Unit := do
  IO.println "--- §3.4 SM6.A.3 rendezvous SGI (local vs remote) ---"
  -- Local receiver (unbound ⇒ home = boot core = executing core): no SGI.
  match stWithReceiver recvLocalTid with
  | some st =>
      assertBool "rendezvous with a local (unbound) receiver surfaces no SGI"
        (match callSgi st bootCoreId with | none => true | _ => false)
  | none => assertBool "rendezvous setup (local receiver) succeeded" false
  -- Remote receiver (core1-bound): a reschedule SGI is fired to core 1.
  match stWithReceiver recvRemoteTid with
  | some st =>
      -- SM6.A.1: the pre-resolution helper picks up the waiting receiver, so the
      -- state-resolved lock-set includes its TCB write lock.
      assertBool "endpointCallReceiver? resolves the waiting receiver"
        (decide (endpointCallReceiver? st epId = some recvRemoteTid))
      assertBool "rendezvous with a core1-bound receiver fires a reschedule SGI to core 1"
        (match callSgi st bootCoreId with
         | some (tgt, kind) => decide (tgt = core1 ∧ kind = SgiKind.reschedule)
         | none => false)
      -- The caller blocks on its own core awaiting the reply.
      let (st', _) := endpointCallOnCore epId callerTid IpcMessage.empty bootCoreId st
      assertBool "rendezvous blocks the caller as blockedOnReply (reply linkage)"
        (match st'.getTcb? callerTid with
         | some t => decide (t.ipcState = .blockedOnReply epId (some recvRemoteTid))
         | none => false)
  | none => assertBool "rendezvous setup (remote receiver) succeeded" false

def runSmpCrossCoreCallChecks : IO Unit := do
  IO.println "WS-SM SM6.A — Cross-core endpoint call suite"
  IO.println "===================================="
  runLockSetChecks
  runBlockingChecks
  runNoReceiverChecks
  runRendezvousChecks
  IO.println "===================================="
  IO.println "All SM6.A cross-core call checks PASS."

end SeLe4n.Testing.SmpCrossCoreCall

def main : IO Unit :=
  SeLe4n.Testing.SmpCrossCoreCall.runSmpCrossCoreCallChecks
