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
import SeLe4n.Kernel.IPC.CrossCore.NotificationInvariant
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyInvariant
import SeLe4n.Kernel.IPC.Invariant.Reachability
import SeLe4n.Kernel.IPC.Invariant.DispatchPayoff
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
-- PR #822 review: the server-first stashed reply the rendezvous links, resolved into
-- the Call footprint so the folded `linkServerStashedReply` reply write is 2PL-covered:
#check @endpointCallServerFirstReply?
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
-- SM6.D (PR #827 review): the stashed reply object's write lock is a declared
-- member of the WithCaps `.call` footprint (server-first link serialised by 2PL).
#check @lockSet_endpointCallWithCaps_reply_write_mem

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
    (receiver : SeLe4n.ThreadId) (recvTcb0 recvTcb'' : TCB) (st' st'' st4 st5 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hLink : SystemState.linkServerStashedReply caller receiver st4 = .ok ((), st5))
    (hTcb'' : st''.getTcb? receiver = some recvTcb'')
    (hRemote : determineTargetCore st'' receiver ≠ executingCore) :
    (endpointCallOnCore endpointId caller msg executingCore st).2
      = .ok (some (determineTargetCore st'' receiver, SgiKind.reschedule)) :=
  endpointCallOnCore_emits_sgi_if_remote_receiver endpointId caller msg executingCore st ep
    receiver recvTcb0 recvTcb'' st' st'' st4 st5 hSz1 hSz2 hObj hHead hPop hStore hCallerStore
    hLink hTcb'' hRemote

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
    (receiver : SeLe4n.ThreadId) (recvTcb0 : TCB) (st' st'' st4 st5 : SystemState)
    (hSz1 : ¬ msg.registers.size > maxMessageRegisters)
    (hSz2 : ¬ msg.caps.size > maxExtraCaps)
    (hObj : st.objects[endpointId]? = some (.endpoint ep))
    (hHead : ep.receiveQ.head = some receiver)
    (hPop : endpointQueuePopHead endpointId true st = .ok (receiver, recvTcb0, st'))
    (hStore : storeTcbIpcStateAndMessage st' receiver .ready (some msg) = .ok st'')
    (hCallerStore : storeTcbIpcStateAndMessage (wakeThread st'' receiver executingCore).1
        caller (.blockedOnReply endpointId (some receiver)) none = .ok st4)
    (hLink : SystemState.linkServerStashedReply caller receiver st4 = .ok ((), st5))
    (hObjInv : st.objects.invExt)
    (hObjSetInv : st.objectIndexSet.table.invExt)
    (hIdxComplete : objectIndexSetComplete st)
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
    recvTcb0 st' st'' st4 st5 hSz1 hSz2 hObj hHead hPop hStore hCallerStore hLink hObjInv
    hObjSetInv hIdxComplete hEndpointHigh
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
private def replyId : SeLe4n.ReplyId := ⟨420⟩

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := ⟨310⟩, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
    cpuAffinity := aff }

/-- Endpoint + unbound caller + unbound (local) receiver + core1-bound (remote)
receiver + a free Reply object the server supplies on its `Recv`. -/
private def stBase : SystemState :=
  (BootstrapBuilder.empty
    |>.withObject epId (.endpoint {})
    |>.withObject callerTid.toObjId (.tcb (mkTcb 401 40 none))
    |>.withObject recvLocalTid.toObjId (.tcb (mkTcb 402 30 none))
    |>.withObject recvRemoteTid.toObjId (.tcb (mkTcb 403 30 (some core1)))
    |>.withObject replyId.toObjId (.reply { replyId := replyId })
    |>.withRunnable [callerTid]
    |>.build)

/-- Drive the receiver onto the endpoint's receive queue (it blocks, no sender),
supplying a Reply object so a later `Call` rendezvous can link to its stash (the
#7.3b fold makes the rendezvous itself perform that link, atomically). -/
private def stWithReceiver (recv : SeLe4n.ThreadId) : Option SystemState :=
  match endpointReceiveDual epId recv (some replyId) stBase with
  | .ok (_, st) => some st
  | .error _ => none

/-- Like `stWithReceiver` but the server supplies NO Reply object (a plain `Recv`):
a later `Call` rendezvous has no stash to link and must fail closed. -/
private def stWithReceiverNoReply (recv : SeLe4n.ThreadId) : Option SystemState :=
  match endpointReceiveDual epId recv none stBase with
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
  -- PR #822 review (finding 6J… server-first reply lock): once the server-first
  -- stashed reply is resolved, its per-object **write** lock is a declared member of
  -- the Call footprint, so the folded `linkServerStashedReply` reply write is 2PL-covered.
  assertBool "server-first reply write lock is in the endpointCall footprint"
    (decide ((replyLock (⟨700⟩ : SeLe4n.ReplyId), AccessMode.write) ∈
      (lockSet_endpointCall callerTid cnRoot epId (some recvRemoteTid) (some scId)
        (some (⟨700⟩ : SeLe4n.ReplyId))).pairs))
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
      -- #7.3b fold: the rendezvous ATOMICALLY links the caller to the server's
      -- stashed Reply object and clears the stash — no separate dispatch step.
      assertBool "rendezvous links the caller to the server's stashed reply object"
        (match st'.getReply? replyId, st'.getTcb? callerTid with
         | some r, some t => decide (r.caller = some callerTid ∧ t.replyObject = some replyId)
         | _, _ => false)
      assertBool "rendezvous clears the server's reply stash (one-shot)"
        ((st'.getTcb? recvRemoteTid).all (fun t => decide (t.pendingReceiveReply = none)))
  | none => assertBool "rendezvous setup (remote receiver) succeeded" false
  -- #7.3b fold (fail-closed): a Call rendezvous with a server that supplied NO Reply
  -- object (plain Recv) cannot be answered — the fold makes `endpointCallOnCore`
  -- itself fail closed, with no intermediate `.blockedOnReply` caller and no SGI.
  match stWithReceiverNoReply recvRemoteTid with
  | some st =>
      let (st', res) := endpointCallOnCore epId callerTid IpcMessage.empty bootCoreId st
      assertBool "no-stash rendezvous fails closed with replyCapInvalid"
        (match res with | .error .replyCapInvalid => true | _ => false)
      assertBool "no-stash rendezvous leaves the caller unblocked (no green intermediate)"
        ((st'.getTcb? callerTid).any (fun t => decide (t.ipcState = .ready)))
      assertBool "no-stash rendezvous surfaces no SGI"
        (match res with | .error _ => true | _ => false)
  | none => assertBool "rendezvous setup (no-reply receiver) succeeded" false

-- ============================================================================
-- §SM6.D  Per-core IPC invariant bundle (surface anchors + witnesses)
-- ============================================================================
--
-- WS-SM SM6.D coverage: the per-core bundle definitions (SM6.D.1, D.3–D.6),
-- the exact-decomposition bridges, the six per-operation preservation
-- theorems (SM6.D.2) plus the cross-core call flagship, and the home-core /
-- wake-target coherence.  Elaboration-time: every symbol resolves and every
-- headline theorem applies to typed inputs.  Runtime: `threadHomeCore`
-- agrees with the operational `determineTargetCore` on the suite fixtures.

-- SM6.D.1 bundle + SMP aggregate + bridges:
#check @ipcInvariantFull_perCore
#check @ipcInvariantFull_smp
#check @ipcInvariantFull_smp_at
#check @ipcInvariantFull_perCore_of_full
#check @ipcInvariantFull_of_smp
#check @ipcInvariantCore_of_smp
#check @ipcInvariantFull_smp_iff_full_and_passive_smp
#check @default_ipcInvariantFull_perCore
#check @default_ipcInvariantFull_smp
#check @threadHomeCore
#check @determineTargetCore_eq_threadHomeCore
-- SM6.D.3–D.6 named per-core conjuncts + exactness:
#check @ipcStateQueueMembershipConsistent_perCore
#check @endpointQueueNoDup_perCore
#check @queueNextBlockingConsistent_perCore
#check @queueHeadBlockedConsistent_perCore
#check @ipcStateQueueMembershipConsistent_smp_iff
#check @endpointQueueNoDup_smp_iff
#check @queueNextBlockingConsistent_smp_iff
#check @queueHeadBlockedConsistent_smp_iff
-- SM6.D.2 per-operation preservation (the six operations + companions):
#check @endpointSendDual_preserves_ipcInvariantFull_perCore
#check @endpointReceiveDual_preserves_ipcInvariantFull_perCore
#check @endpointCall_preserves_ipcInvariantFull_perCore
#check @endpointReply_preserves_ipcInvariantFull_perCore
#check @endpointReplyRecv_preserves_ipcInvariantFull_perCore
#check @notificationSignal_preserves_ipcInvariantFull_perCore
#check @notificationWait_preserves_ipcInvariantFull_perCore
#check @endpointCallOnCore_preserves_ipcInvariantFull_perCore
#check @endpointCallOnCore_preserves_passiveServerIdle_perCore
-- SM6.D.2 per-core passive-server frame machinery:
#check @passiveServerIdleFrameOnCore
#check @passiveServerIdle_perCore_of_frameOnCore
#check @endpointCallOnCore_passiveServerIdleFrameOnCore
-- SM6.D completion — the lookup-congruence transfer layer:
#check @ipcInvariantFull_of_getElem_eq
#check @OffSchedulerAgrees
#check @wakeThread_offSchedulerAgrees_of_ready
#check @storeTcbIpcStateAndMessage_offSchedulerAgrees
#check @consumeCallerReply_offSchedulerAgrees
#check @passiveServerIdleFrameOnCore_boot_iff
-- SM6.D completion — cross-core (OnCore) whole-bundle closures + flagships:
#check @notificationSignalOnCore_post_agrees
#check @notificationWaitOnCore_post_agrees
#check @notificationSignalOnCore_preserves_ipcInvariantFull
#check @notificationWaitOnCore_preserves_ipcInvariantFull
#check @notificationSignalOnCore_preserves_ipcInvariantFull_perCore
#check @notificationWaitOnCore_preserves_ipcInvariantFull_perCore
#check @endpointReplyOnCore_post_agrees
#check @endpointReceiveDualOnCore_post_agrees
#check @endpointReplyOnCore_preserves_ipcInvariantFull
#check @endpointReceiveDualOnCore_preserves_ipcInvariantFull
#check @endpointReplyOnCore_preserves_ipcInvariantFull_perCore
#check @endpointReceiveDualOnCore_preserves_ipcInvariantFull_perCore
#check @endpointReplyOnCore_reuse_freshens
#check @endpointReplyRecvOnCore_preserves_ipcInvariantFull
#check @endpointReplyRecvOnCore_preserves_ipcInvariantFull_perCore
-- WS-RR RR3.12 — the reply chain's relaxed-invariant surface:
#check @donationOwnerValidExcept
#check @donationOwnerFrameExcept
#check @ipcInvariantFullExceptDonationOwner
#check @endpointReply_preserves_ipcInvariantFullExceptDonationOwner
#check @endpointReplyOnCore_preserves_ipcInvariantFullExceptDonationOwner
#check @returnDonatedSchedContext_establishes_donationOwnerValid_of_except
#check @donationOwnerValid_of_except_of_no_donation_owned_by
#check @donationOwnerValidExcept_implies_donationChainAcyclic
#check @applyReplyDonation_establishes_ipcInvariantFull_of_except
#check @applyReplyDonationOnCore_establishes_ipcInvariantFull_of_except
#check @returnDonatedSchedContext_establishes_ipcInvariantFull_of_except
#check @endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull
-- WS-RR RR3.13/RR3.14 — the pre-state side: the bundles' preconditions, derived:
#check @ipcReachable
#check @ipcReachable_default
#check @readyThread_endpointQueueFresh
#check @readyThread_ownsNoDonation
#check @sendTailCrossQueueFresh
#check @recvTailCrossQueueFresh
-- SM6.D completion — the capability-carrying (WithCaps) trio:
#check @ipcUnwrapCaps_passiveServerIdleFrameOnCore
#check @endpointSendDualWithCaps_preserves_ipcInvariantFull_perCore
#check @endpointReceiveDualWithCaps_preserves_ipcInvariantFull_perCore
#check @endpointCallWithCaps_preserves_ipcInvariantFull_perCore
-- WS-RR RR3.11 — the in-flight badge surface the WithCaps bundles now establish from:
#check @messageCapBadgesValid
#check @pendingMessageCapBadgesWellFormed
#check @pendingMessagesSatisfy
#check @endpointReceiveDual_preserves_pendingMessageCapBadgesWellFormed
#check @endpointSendDualWithCaps_preserves_badgeWellFormed
#check @endpointReceiveDualWithCaps_preserves_badgeWellFormed
#check @endpointCallWithCaps_preserves_badgeWellFormed
#check @endpointCallWithCaps_preserves_dualQueueSystemInvariant
-- WS-RR RR3.11 — instance/congruence surface of the in-flight family (kept
-- complete alongside the boundedness instances even where no composite consumes
-- them yet; the dispatch payoffs below are the designated consumers):
#check @allPendingMessagesBounded_iff_pendingMessagesSatisfy
#check @pendingMessageCapBadgesWellFormed_of_getElem_eq
#check @cleanupPreReceiveDonation_preserves_pendingMessageCapBadgesWellFormed
-- WS-RR RR3.12 — the relaxed donation-owner family mirrors the unrelaxed one:
#check @donationOwnerValidExcept_of_objects_eq
-- WS-RR RR3.15–RR3.21 — the per-arm dispatch bundle layer (production,
-- `IPC/Invariant/DispatchArmPreservation.lean`), anchored at its
-- dispatch-facing terminals plus the two named disciplines the packs quantify:
#check @retypeTargetDetached
#check @retypeReplacementFresh
#check @threadIpcFieldsQuiescent
#check @cspaceDeleteSlot_preserves_ipcInvariantFull
#check @cspaceMintWithCdt_preserves_ipcInvariantFull
#check @mintReplyCapWithCdt_preserves_ipcInvariantFull
#check @lifecycleRetypeDirectWithCleanupShootdownPerCoreIcache_preserves_ipcInvariantFull
#check @vspaceMapPageCheckedWithShootdownFromStatePerCore_preserves_ipcInvariantFull
#check @vspaceUnmapPageWithShootdownAndIcacheBroadcast_preserves_ipcInvariantFull
#check @vspaceUnifyInstructionPage_preserves_ipcInvariantFull
#check @registerService_preserves_ipcInvariantFull
#check @revokeService_preserves_ipcInvariantFull
#check @schedContextConfigure_preserves_ipcInvariantFull
#check @schedContextBind_preserves_ipcInvariantFull
#check @schedContextUnbindOnCore_preserves_ipcInvariantFull
#check @setPriorityOnCore_preserves_ipcInvariantFull
#check @setIPCBufferOp_preserves_ipcInvariantFull
#check @writeReturnFrameToTcb_preserves_ipcInvariantFull
#check @suspendThreadOnCore_preserves_ipcInvariantFull
#check @resumeThreadOnCoreLive_preserves_ipcInvariantFull
-- WS-RR RR3.22 — the composition layer: the return-frame staging writes and
-- the replyRecv three-stage composite:
#check @stageDeliveredMessage_preserves_ipcInvariantFull
#check @stageWokenDelivery_preserves_ipcInvariantFull
#check @stageWokenSendCompletion_preserves_ipcInvariantFull
#check @replyRecvBody_preserves_ipcInvariantFull
-- WS-RR RR3.23–RR3.25 — the dispatch payoffs and their pre-state packs
-- (the capability tier production in `API.lean`; the two dispatch tiers
-- staged in `IPC/Invariant/DispatchPayoff.lean` with the call-chain surface):
#check @capabilityDispatchQuiescence
#check @dispatchCapabilityOnly_preserves_ipcInvariantFull
#check @syscallDispatchQuiescence
#check @dispatchWithCap_preserves_ipcInvariantFull
#check @dispatchSyscall_preserves_ipcInvariantFull
-- WS-RR RR3.22 (third item) — the flow-checked dispatch tier: the checked
-- dispatcher's payoffs (mirrored arms reduced to the unchecked payoff, the
-- four SM9 arms closed from their frames), and the packs' inhabitation
-- witnesses, whose state is built through the retype and binding levers:
#check @checkedSyscallDispatchQuiescence
#check @dispatchWithCapChecked_preserves_ipcInvariantFull
#check @dispatchSyscallChecked_preserves_ipcInvariantFull
#check @syscallDispatchQuiescence_inhabited
#check @checkedSyscallDispatchQuiescence_inhabited
-- The per-arm witness family (PR #886 review): each indexed pack field is
-- exercised with its premises firing — the signal confinement and thread
-- quiescence on present objects, retype detachedness of the decoded target,
-- the send/receive/call stages by evaluating the transitions, the mint badge
-- by computing the decoder, the reply arm to the lever boundary against a
-- stored reply, and the checked tier's declassifying confinement:
#check @syscallDispatchQuiescence_inhabited_signal
#check @syscallDispatchQuiescence_inhabited_retype
#check @syscallDispatchQuiescence_inhabited_send
#check @syscallDispatchQuiescence_inhabited_receive
#check @syscallDispatchQuiescence_inhabited_call
#check @syscallDispatchQuiescence_inhabited_mint
#check @syscallDispatchQuiescence_inhabited_reply
#check @checkedSyscallDispatchQuiescence_inhabited_declassifySignal

/-- SM6.D.1 exact decomposition: the ∀-core bundle is equivalent to the global
bundle plus the per-core passive-idle slices — nothing is weakened. -/
example (st : SystemState) :
    ipcInvariantFull_smp st ↔ ipcInvariantFull st ∧ passiveServerIdle_smp st :=
  ipcInvariantFull_smp_iff_full_and_passive_smp st

/-- SM6.D.3 exactness: the ∀-core queue-membership slices recover exactly the
global conjunct. -/
example (st : SystemState) :
    (∀ c, ipcStateQueueMembershipConsistent_perCore st c) ↔
      ipcStateQueueMembershipConsistent st :=
  ipcStateQueueMembershipConsistent_smp_iff st

/-- SM6.D: the bundle's thread-domain restriction is the operational wake
target — the slices partition threads by the core the wake path delivers to. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) :
    determineTargetCore st tid = threadHomeCore tcb :=
  determineTargetCore_eq_threadHomeCore hTcb

/-- SM6.D.2 (representative): `notificationSignal` preserves every core's
bundle view. -/
example (st st' : SystemState) (ntfnId : SeLe4n.ObjId) (badge : SeLe4n.Badge)
    (hInv : ipcInvariantFull_smp st) (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hStep : notificationSignal ntfnId badge st = .ok ((), st'))
    (c : CoreId) :
    ipcInvariantFull_perCore st' c :=
  notificationSignal_preserves_ipcInvariantFull_perCore st st' ntfnId badge hInv hObjInv
    hNWC hAllBudgetsNone hStep c

/-- SM6.D: the freshly-booted system satisfies every core's bundle view. -/
example (c : CoreId) : ipcInvariantFull_perCore (default : SystemState) c :=
  default_ipcInvariantFull_perCore c

/-- SM6.D completion (representative): the **cross-core** signal preserves
every core's bundle view, unconditionally over success/failure. -/
example (st : SystemState) (ntfnId : SeLe4n.ObjId) (badge : SeLe4n.Badge) (ec c : CoreId)
    (hInv : ipcInvariantFull_smp st) (hObjInv : st.objects.invExt)
    (hNWC : notificationWaiterConsistent st)
    (hAllBudgetsNone : allTimeoutBudgetsNone st) :
    ipcInvariantFull_perCore (notificationSignalOnCore ntfnId badge ec st).1 c :=
  notificationSignalOnCore_preserves_ipcInvariantFull_perCore ntfnId badge ec st hInv hObjInv
    hNWC hAllBudgetsNone c

/-- SM6.D completion (representative): the **cross-core** reply preserves the
whole twenty-conjunct bundle for any reply-cap holder (delegated authority
included — the recorded server's single-core effect carries across the
off-scheduler agreement dichotomy). -/
example (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (ec : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st) (hObjInv : st.objects.invExt)
    -- WS-RR RR3.12: a **pre**-state condition, where the retired `hDOV'` was a
    -- post-state one no donating reply satisfies.
    (hNoDonationOwnedBy : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
      (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId target)
    (hAllBudgetsNone : allTimeoutBudgetsNone st) :
    ipcInvariantFull (endpointReplyOnCore replier target msg ec st).1 :=
  endpointReplyOnCore_preserves_ipcInvariantFull replier target msg ec st hInv hObjInv
    hNoDonationOwnedBy hAllBudgetsNone

/-- WS-RR RR3.12: the cross-core reply's **unconditional** bundle statement — the
one that holds on the donating path too, with `donationOwnerValid` relaxed at the
answered caller.  No hypothesis about the result at all; the relaxation is exactly
the transient the donation return closes. -/
example (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (ec : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st) (hObjInv : st.objects.invExt)
    (hAllBudgetsNone : allTimeoutBudgetsNone st) :
    ipcInvariantFullExceptDonationOwner
      (endpointReplyOnCore replier target msg ec st).1 target :=
  endpointReplyOnCore_preserves_ipcInvariantFullExceptDonationOwner replier target msg ec st
    hInv hObjInv hAllBudgetsNone

/-- WS-RR RR3.14: the reachability bundle is **inhabited** — the boot state
satisfies it.  Without this the pre-state conditions the de-threaded bundles now
carry could be an unsatisfiable conjunction, and every theorem taking them would
be vacuous: the failure shape de-threading exists to remove, one level up. -/
example : ipcReachable (default : SystemState) := ipcReachable_default

/-- WS-RR RR3.13: the enqueueing bundles' freshness precondition is a
**consequence**, not an assumption — a `.ready` thread cannot head or tail any
endpoint queue, because every head and tail is blocked. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hInv : ipcInvariantFull st)
    (hTcb : st.objects[tid.toObjId]? = some (.tcb tcb))
    (hReady : tcb.ipcState = .ready) :
    ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some tid ∧ ep.sendQ.tail ≠ some tid ∧
      ep.receiveQ.head ≠ some tid ∧ ep.receiveQ.tail ≠ some tid :=
  readyThread_endpointQueueFresh st tid tcb hInv.queueHeadBlockedConsistent
    hInv.endpointQueueTailBlockedConsistent hTcb hReady

/-- WS-RR RR3.13: so is the cross-queue tail freshness the enqueue establishers
carry — an endpoint's send-queue tail tails nothing else, from
`ipcInvariantFull` alone. -/
example (st : SystemState) (endpointId : SeLe4n.ObjId) (hInv : ipcInvariantFull st) :
    ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId →
          ep'.receiveQ.tail ≠ some tailTid) :=
  sendTailCrossQueueFresh st endpointId hInv.dualQueueSystemInvariant
    hInv.endpointQueueTailBlockedConsistent

/-- WS-RR RR3.12 (payoff): the **live** cross-core `.reply` dispatch preserves the
whole twenty-conjunct bundle on the *donating* path — the seL4-MCS path the previous
statement was vacuous on.  Nothing about the result is assumed: `hDonationReturned`
says only that whatever the answered caller donated is what the recorded reply server
returns, a fact about the pre-state and the operation's arguments. -/
example (replier target : SeLe4n.ThreadId) (msg : IpcMessage) (ec : CoreId)
    (st : SystemState)
    (hInv : ipcInvariantFull st) (hObjInv : st.objects.invExt)
    (hDonationReturned : ∀ (expected : SeLe4n.ThreadId),
      recordedReplyServer? st target = some expected →
      ∀ (s : SeLe4n.ThreadId) (sTcb : TCB) (sc : SeLe4n.SchedContextId),
        st.objects[s.toObjId]? = some (.tcb sTcb) →
        sTcb.schedContextBinding = .donated sc target →
        replyDonationReturn? st expected = some (sc, target))
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hServerIdleAllowed : ∀ (expected : SeLe4n.ThreadId), recordedReplyServer? st target
        = some expected →
      ∀ tcb, st.getTcb? expected = some tcb → passiveServerIdleAllowed tcb.ipcState) :
    ipcInvariantFull (endpointReplyCrossCoreDispatch replier target msg ec st).1 :=
  endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull replier target msg ec st hInv
    hObjInv hDonationReturned hAllBudgetsNone hServerIdleAllowed

/-- WS-RR RR3.12: the donation return **upgrades** the relaxed invariant back to the
full one — the other half of the reply chain's honest statement, and the reason the
relaxation is a transient rather than a weakening. -/
example (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (stcb : TCB)
    (hServerObj : st.objects[serverTid.toObjId]? = some (.tcb stcb))
    (hServerBind : stcb.schedContextBinding = .donated scId originalOwner)
    (hUnique : donationOwnerUnique st)
    (hInv : donationOwnerValidExcept st originalOwner)
    (h : returnDonatedSchedContext st serverTid scId originalOwner = .ok st') :
    donationOwnerValid st' :=
  returnDonatedSchedContext_establishes_donationOwnerValid_of_except st st' serverTid scId
    originalOwner hObjInv stcb hServerObj hServerBind hUnique hInv h

/-- SM6.D completion (seL4-MCS one-object reuse): the composed cross-core
`replyRecv` accepts a reply object that is *in use by the answered caller* —
the reply leg's folded consume frees it before the receive leg re-stashes it.
The disjunctive `hReplyIdValid` premise's reuse arm is exercised here. -/
example (endpointId : SeLe4n.ObjId) (receiver replyTarget : SeLe4n.ThreadId)
    (msg : IpcMessage) (rid : SeLe4n.ReplyId) (ec c : CoreId) (st : SystemState)
    (hInv : ipcInvariantFull_smp st) (hObjInv : st.objects.invExt)
    (hNoDonationOwnedBy : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB)
      (scId : SeLe4n.SchedContextId),
      st.objects[tid.toObjId]? = some (.tcb tcb) →
      tcb.schedContextBinding ≠ .donated scId replyTarget)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshReceiver : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some receiver ∧ ep.sendQ.tail ≠ some receiver ∧
      ep.receiveQ.head ≠ some receiver ∧ ep.receiveQ.tail ≠ some receiver)
    (hRecvTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.receiveQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId → ep'.sendQ.tail ≠ some tailTid))
    -- the reuse arm: `rid` is the answered caller's in-use reply object
    (hUnstashed : ∀ (tid : SeLe4n.ThreadId) (tcb : TCB), st.getTcb? tid = some tcb →
        tcb.pendingReceiveReply ≠ some rid)
    (hPresent : ∃ r, st.getReply? rid = some r)
    (hLinked : ∃ tcbT, st.getTcb? replyTarget = some tcbT ∧ tcbT.replyObject = some rid)
    (hReceiverNotRecv : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hReceiverReady : ∀ (tcb : TCB), st.getTcb? receiver = some tcb →
        tcb.ipcState = .ready) :
    ipcInvariantFull_perCore
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg (some rid) ec st).1 c :=
  endpointReplyRecvOnCore_preserves_ipcInvariantFull_perCore endpointId receiver replyTarget
    msg (some rid) ec st hInv hObjInv hNoDonationOwnedBy hAllBudgetsNone
    hFreshReceiver hRecvTailFresh
    (fun rid' hRid' => Or.inr (by
      obtain rfl : rid = rid' := Option.some.inj hRid'
      exact ⟨hUnstashed, hPresent, hLinked⟩))
    hReceiverNotRecv hReceiverReady c

/-- SM6.D completion (representative): the capability-carrying send — the
transition behind the **live** `.send` dispatch — preserves every core's
bundle view. -/
example (endpointId : SeLe4n.ObjId) (sender : SeLe4n.ThreadId)
    (msg : IpcMessage) (endpointRights : AccessRightSet)
    (senderCspaceRoot : SeLe4n.ObjId) (receiverSlotBase : SeLe4n.Slot)
    (st st' : SystemState) (summary : CapTransferSummary) (c : CoreId)
    (hInv : ipcInvariantFull_smp st) (hObjInv : st.objects.invExt)
    -- WS-RR RR3.11: one condition on the syscall's own message argument, where the
    -- retired `hDualQueue'` / `hBadge'` were post-state conjuncts the bundle now
    -- establishes.
    (hMsgCaps : messageCapBadgesValid msg)
    (hAllBudgetsNone : allTimeoutBudgetsNone st)
    (hFreshSender : ∀ (epId : SeLe4n.ObjId) (ep : Endpoint),
      st.objects[epId]? = some (.endpoint ep) →
      ep.sendQ.head ≠ some sender ∧ ep.sendQ.tail ≠ some sender ∧
      ep.receiveQ.head ≠ some sender ∧ ep.receiveQ.tail ≠ some sender)
    (hSendTailFresh : ∀ (ep : Endpoint) (tailTid : SeLe4n.ThreadId),
      st.objects[endpointId]? = some (.endpoint ep) →
      ep.sendQ.tail = some tailTid →
      ∀ (epId' : SeLe4n.ObjId) (ep' : Endpoint),
        st.objects[epId']? = some (.endpoint ep') →
        (epId' ≠ endpointId →
          ep'.sendQ.tail ≠ some tailTid ∧ ep'.receiveQ.tail ≠ some tailTid) ∧
        (epId' = endpointId → ep'.receiveQ.tail ≠ some tailTid))
    (hSenderNotRecv : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep, tcb.ipcState ≠ .blockedOnReceive ep)
    (hSenderNotReply : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        ∀ ep rt, tcb.ipcState ≠ .blockedOnReply ep rt)
    (hSenderNotUnbound : ∀ (tcb : TCB), st.getTcb? sender = some tcb →
        tcb.schedContextBinding ≠ .unbound)
    (hStep : endpointSendDualWithCaps endpointId sender msg endpointRights
             senderCspaceRoot receiverSlotBase st = .ok (summary, st')) :
    ipcInvariantFull_perCore st' c :=
  endpointSendDualWithCaps_preserves_ipcInvariantFull_perCore endpointId sender msg
    endpointRights senderCspaceRoot receiverSlotBase st st' summary hInv hObjInv
    hMsgCaps hAllBudgetsNone hFreshSender hSendTailFresh
    hSenderNotRecv hSenderNotReply hSenderNotUnbound hStep c

/-- SM6.D runtime: `threadHomeCore` and `determineTargetCore` agree on the
suite fixtures (pinned → home core, unpinned → boot core). -/
private def runPerCoreBundleChecks : IO Unit := do
  IO.println "--- §SM6.D per-core bundle home-core coherence ---"
  assertBool "unpinned thread is homed on the boot core"
    (decide (threadHomeCore (mkTcb 401 40 none) = bootCoreId))
  assertBool "core1-pinned thread is homed on core 1"
    (decide (threadHomeCore (mkTcb 403 30 (some core1)) = core1))
  assertBool "determineTargetCore agrees with threadHomeCore (unpinned caller)"
    (decide (determineTargetCore stBase callerTid = threadHomeCore (mkTcb 401 40 none)))
  assertBool "determineTargetCore agrees with threadHomeCore (core1-pinned receiver)"
    (decide (determineTargetCore stBase recvRemoteTid = threadHomeCore (mkTcb 403 30 (some core1))))
  assertBool "determineTargetCore routes the remote receiver's wake to core 1"
    (decide (determineTargetCore stBase recvRemoteTid = core1))

def runSmpCrossCoreCallChecks : IO Unit := do
  IO.println "WS-SM SM6.A — Cross-core endpoint call suite"
  IO.println "===================================="
  runLockSetChecks
  runBlockingChecks
  runNoReceiverChecks
  runRendezvousChecks
  runPerCoreBundleChecks
  IO.println "===================================="
  IO.println "All SM6.A cross-core call checks PASS."

end SeLe4n.Testing.SmpCrossCoreCall

def main : IO Unit :=
  SeLe4n.Testing.SmpCrossCoreCall.runSmpCrossCoreCallChecks
