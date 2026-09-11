-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n - A Lean Microkernel
  Copyright (C) 2026 Adam Hall
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
-- §1 Surface anchors (Tier-3): every SM6.A public symbol resolves
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
-- WS-OD OD3.11: the one TCB a rendezvous-or-block writes besides its two
-- principals -- the promoted head on a pop, the old tail on an enqueue.
#check @endpointQueueStructureNeighbor?
#check @sendSideQueueStructureNeighbor?
#check @sendSideQueueStructureNeighbor?_rendezvous
#check @sendSideQueueStructureNeighbor?_block
#check @lockSet_endpointCallOnCore_covers_queueNeighbour
#check @lockSet_endpointSendOnCore_covers_queueNeighbour
#check @lockSetForSyscall_call_covers_queueNeighbour
#check @lockSetForSyscall_send_covers_queueNeighbour
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
-- §2 Elaboration-time examples (Tier-3): theorems apply to typed inputs
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
-- §3 Runtime assertions (Tier-2): the SM6.A cross-core call scenarios
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!" PASS: {name}"
  else
    IO.println s!" FAIL: {name}"
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
  -- SM6.A.5: donating extends the footprint by exactly the SC write lock —
  -- **and, since WS-OD OD3.5, by the state-level lock as well**, because
  -- `donateSchedContext` maintains `SystemState.scThreadIndex`, an `RHTable`
  -- whose insert may rehash and which therefore does not decompose by object.
  -- This mirrors `lockSet_endpointCall_donation_extension`; the two must not
  -- drift.
  assertBool "donation extends the lock-set by the SchedContext and state-level write locks"
    (decide (lockSet_endpointCall callerTid cnRoot epId (some recvRemoteTid) (some scId)
      = lockSetExtendOpt
          (lockSetExtendOpt
            (lockSet_endpointCall callerTid cnRoot epId (some recvRemoteTid) none)
            (some (schedContextLock scId, .write)))
          (some (stateLevelLock, .write))))
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
  -- `endpointCallDonatedSc?`. On the empty base state both resolve to `none`.
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
        (SeLe4n.Slot.ofNat 0) bootCoreId stBase).2 with
     | .ok (_, none) => true | _ => false)
  assertBool "no-receiver cross-core dispatch performs no donation (= WithCaps)"
    (match (endpointCallCrossCoreDispatch epId callerTid IpcMessage.empty AccessRightSet.empty
        (SeLe4n.Slot.ofNat 0) bootCoreId stBase).2 with
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
-- §SM6.D Per-core IPC invariant bundle (surface anchors + witnesses)
-- ============================================================================
--
-- WS-SM SM6.D coverage: the per-core bundle definitions (SM6.D.1, D.3–D.6),
-- the exact-decomposition bridges, the six per-operation preservation
-- theorems (SM6.D.2) plus the cross-core call flagship, and the home-core /
-- wake-target coherence. Elaboration-time: every symbol resolves and every
-- headline theorem applies to typed inputs. Runtime: `threadHomeCore`
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
-- WS-OD OD2 — the donation chain: the predicate, its walk, its frame family,
-- and the two witnesses that keep it from being discharged only vacuously.
#check @donationChainWellFormed
#check @donationChainFrom
#check @replyStackLinksAt?
#check @donationChainFrame
#check @donationChainWellFormed_of_frame
#check @donationChainWellFormed_of_no_donations
#check @donationChainWitness_wellFormed
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
#check @syscallDispatchQuiescence_inhabited_bind
#check @syscallDispatchQuiescence_inhabited_unbind
#check @syscallDispatchQuiescence_inhabited_suspend
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
answered caller. No hypothesis about the result at all; the relaxation is exactly
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
satisfies it. Without this the pre-state conditions the de-threaded bundles now
carry could be an unsatisfiable conjunction, and every theorem taking them would
be vacuous: the failure shape de-threading exists to remove, one level up. -/
example : ipcReachable (default : SystemState) := ipcReachable_default

/-- WS-OD OD2.4: the donation-chain conjunct **decides** rather than refuses.
When this witness was written every reachable state discharged the conjunct
vacuously — the donation pop was the only transition writing the three
reply-stack fields, and its writing arm needs a stack nothing then constructed —
and a conjunct that only ever fires vacuously is one nobody has checked against
the structure it constrains: an over-strong one would look identical from that
side.  The witness is the state a depth-2 Call chain leaves, and it satisfies the
predicate whole, completeness clause included.  Since OD4.1 (`v0.35.2`) the push
builds that shape on a live path, so this is the reachable state rather than a
construction ahead of one — which is why the witness was worth having first. -/
example : donationChainWellFormed donationChainWitness :=
  donationChainWitness_wellFormed

/-- WS-OD OD2.4: ...and the walk from the context's own head returns the whole
stack, innermost first — computed, not asserted. -/
example :
    donationChainFrom donationChainWitness donationChainWitnessContext 2
        (some donationChainWitnessInner)
      = some [donationChainWitnessInner, donationChainWitnessOuter] :=
  donationChainWitness_chain

/-! ### WS-OD OD3.8 — the pop, exercised on the depth-2 witness

The pop's chain-preservation theorem has two arms, and only one of them is
reachable on any state this tree produces: with no context heading a stack the
`head? = none` arm frames the chain outright and says nothing about the reply
links.  A theorem exercised only on that arm would be indistinguishable from one
whose `some` arm is wrong, which is the shape OD2.4's witness exists to refuse —
so the witness is popped here, and the state the pop leaves is shown to satisfy
the predicate whole and to head exactly the tail of the stack it started with. -/

private theorem witnessChainContextObject :
    donationChainWitness.getSchedContext? donationChainWitnessContext
      = some witnessChainSchedContext := by
  rw [SystemState.getSchedContext?_eq_some_iff, donationChainWitness_lookup_cases]
  rw [show (donationChainWitnessInner.toObjId == donationChainWitnessContext.toObjId) = false from
        by decide,
      show (donationChainWitnessOuter.toObjId == donationChainWitnessContext.toObjId) = false from
        by decide]
  simp

private theorem witnessChainOuterObject :
    donationChainWitness.objects[donationChainWitnessOuter.toObjId]?
      = some (.reply witnessChainOuterReply) := by
  rw [donationChainWitness_lookup_cases]
  rw [show (donationChainWitnessInner.toObjId == donationChainWitnessOuter.toObjId) = false from
        by decide,
      show (donationChainWitnessOuter.toObjId == donationChainWitnessOuter.toObjId) = true from
        by decide]
  simp

private theorem witnessChainValidatedHead :
    donationHeadOf? donationChainWitness donationChainWitnessContext
        witnessChainSchedContext
      = .ok (some (donationChainWitnessInner, witnessChainInnerReply)) := by
  have hInner : donationChainWitness.getReply? donationChainWitnessInner
      = some witnessChainInnerReply := by
    rw [SystemState.getReply?_eq_some_iff, donationChainWitness_lookup_cases]
    simp
  unfold donationHeadOf?
  rw [show witnessChainSchedContext.scReply = some donationChainWitnessInner from rfl]
  simp only []
  rw [hInner]
  simp [witnessChainInnerReply]

/-- WS-OD OD3.8: **the pop preserves the chain on a stack that is actually two
frames deep.**  The head the operation clears is the inner call's reply, and the
context is left heading the outer one — the `head? = some` arm, which no state
this tree reaches exercises. -/
theorem donationChainWitness_pop_wellFormed
    (owner : SeLe4n.ThreadId) {s1 s2 : SystemState}
    (hS1 : storeObject donationChainWitnessContext.toObjId
      (.schedContext { witnessChainSchedContext with
          boundThread := some owner, scReply := some donationChainWitnessOuter })
      donationChainWitness = .ok ((), s1))
    (hClear : storeDonationHeadClear (some donationChainWitnessInner) s1 = .ok s2) :
    donationChainWellFormed s2 :=
  donationHeadPop_preserves_donationChainWellFormed
    (head? := some (donationChainWitnessInner, witnessChainInnerReply))
    donationChainWitness_objects_invExt donationChainWitness_wellFormed
    witnessChainContextObject witnessChainValidatedHead hS1 hClear

/-- WS-OD OD3.8: ...and the stack the popped context heads is **exactly the tail**
of the one it headed before — computed on the post-state's own object store, not
read off the invariant.  With `donationChainWitness_chain` on the other side, the
pop is seen to consume one frame and leave the rest intact. -/
theorem donationChainWitness_pop_chain
    (owner : SeLe4n.ThreadId) {s1 s2 : SystemState}
    (hS1 : storeObject donationChainWitnessContext.toObjId
      (.schedContext { witnessChainSchedContext with
          boundThread := some owner, scReply := some donationChainWitnessOuter })
      donationChainWitness = .ok ((), s1))
    (hClear : storeDonationHeadClear (some donationChainWitnessInner) s1 = .ok s2) :
    donationChainFrom s2 donationChainWitnessContext 1 (some donationChainWitnessOuter)
      = some [donationChainWitnessOuter] := by
  have hInv1 := SeLe4n.Model.storeObject_preserves_objects_invExt
    donationChainWitness s1 _ _ donationChainWitness_objects_invExt hS1
  obtain ⟨r0, _, hS2⟩ := storeDonationHeadClear_some_ok hClear
  have hOuter1 : s1.objects[donationChainWitnessOuter.toObjId]?
      = some (.reply witnessChainOuterReply) := by
    rw [SeLe4n.Model.storeObject_objects_ne donationChainWitness s1 _ _ _
      (by decide) donationChainWitness_objects_invExt hS1]
    exact witnessChainOuterObject
  have hOuter2 : s2.objects[donationChainWitnessOuter.toObjId]?
      = some (.reply witnessChainOuterReply) := by
    rw [SeLe4n.Model.storeObject_objects_ne s1 s2 _ _ _ (by decide) hInv1 hS2]
    exact hOuter1
  have hLinks : replyStackLinksAt? s2 donationChainWitnessOuter
      = some (some donationChainWitnessContext, none) := by
    unfold replyStackLinksAt?
    rw [hOuter2]
    simp [replyStackLinks?, witnessChainOuterReply]
  rw [donationChainFrom_succ, hLinks]
  simp

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
statement was vacuous on. Nothing about the result is assumed: `hDonationReturned`
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
      ∀ tcb, st.getTcb? expected = some tcb → passiveServerIdleAllowed tcb.ipcState)
    -- **WS-OD OD4.4**: the donation return resolves its new owner off the
    -- context's reply stack, so the chain's shape at the state that return runs
    -- on — the post-reply-leg store — is an obligation of the composite.  Stated
    -- at that one state rather than at every `SystemState`, which would be
    -- vacuous.
    (hStackValid : ∀ scId serverTid originalOwner,
      replyStackOuterCallerValid (endpointReplyOnCore replier target msg ec st).fst
        scId serverTid originalOwner) :
    ipcInvariantFull (endpointReplyCrossCoreDispatch replier target msg ec st).1 :=
  endpointReplyCrossCoreDispatch_establishes_ipcInvariantFull replier target msg ec st hInv
    hObjInv hDonationReturned hAllBudgetsNone hServerIdleAllowed hStackValid

/-- WS-RR RR3.12: the donation return **upgrades** the relaxed invariant back to the
full one — the other half of the reply chain's honest statement, and the reason the
relaxation is a transient rather than a weakening.

WS-OD OD3.2: the upgrade holds at **both** arms of the widened binding, so the
statement takes an arbitrary `newOwner?` and the depth-≥ 2 obligation
(`donationReturnOuterValid`) rather than restricting itself to the bottom of the
reply stack — a version quantified only over `none` would have said nothing about
the arm OD4.1 (`v0.35.2`) made reachable. -/
example (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (stcb : TCB)
    (hServerObj : st.objects[serverTid.toObjId]? = some (.tcb stcb))
    (hServerBind : stcb.schedContextBinding = .donated scId originalOwner)
    (hUnique : donationOwnerUnique st)
    (hInv : donationOwnerValidExcept st originalOwner)
    (newOwner? : Option SeLe4n.ThreadId)
    (hOuter : donationReturnOuterValid st serverTid originalOwner newOwner?)
    (h : returnDonatedSchedContext st serverTid scId originalOwner newOwner? = .ok st') :
    donationOwnerValid st' :=
  returnDonatedSchedContext_establishes_donationOwnerValid_of_except st st' serverTid scId
    originalOwner hObjInv stcb hServerObj hServerBind hUnique hInv newOwner? hOuter h

/-- WS-OD OD3.2: ...and at the bottom of the reply stack the obligation is
discharged outright, so the shape every call site in the tree produces today needs
no new hypothesis at all. -/
example (st st' : SystemState) (serverTid : SeLe4n.ThreadId)
    (scId : SeLe4n.SchedContextId) (originalOwner : SeLe4n.ThreadId)
    (hObjInv : st.objects.invExt) (stcb : TCB)
    (hServerObj : st.objects[serverTid.toObjId]? = some (.tcb stcb))
    (hServerBind : stcb.schedContextBinding = .donated scId originalOwner)
    (hUnique : donationOwnerUnique st)
    (hInv : donationOwnerValidExcept st originalOwner)
    (h : returnDonatedSchedContext st serverTid scId originalOwner none = .ok st') :
    donationOwnerValid st' :=
  returnDonatedSchedContext_establishes_donationOwnerValid_of_except st st' serverTid scId
    originalOwner hObjInv stcb hServerObj hServerBind hUnique hInv none
    (donationReturnOuterValid_none st serverTid originalOwner) h

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
        tcb.ipcState = .ready)
    -- **WS-OD OD4.4**: the receive leg's pre-receive cleanup pops the receiver's
    -- donation, so the obligation is stated at the store that cleanup runs on —
    -- the reply leg's own post-state.
    (hStackValid : cleanupDonationStackValid
      (endpointReplyOnCore receiver replyTarget msg ec st).1 receiver) :
    ipcInvariantFull_perCore
      (endpointReplyRecvOnCore endpointId receiver replyTarget msg (some rid) ec st).1 c :=
  endpointReplyRecvOnCore_preserves_ipcInvariantFull_perCore endpointId receiver replyTarget
    msg (some rid) ec st hInv hObjInv hNoDonationOwnedBy hStackValid hAllBudgetsNone
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
    (receiverSlotBase : SeLe4n.Slot)
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
             receiverSlotBase st = .ok (summary, st')) :
    ipcInvariantFull_perCore st' c :=
  endpointSendDualWithCaps_preserves_ipcInvariantFull_perCore endpointId sender msg
    endpointRights receiverSlotBase st st' summary hInv hObjInv
    hMsgCaps hAllBudgetsNone hFreshSender hSendTailFresh
    hSenderNotRecv hSenderNotReply hSenderNotUnbound hStep c

/-- **WS-OD OD3.11** fixture (rendezvous branch): two receivers queued, so the
pop the `.call` performs promotes the *second* one to head and writes its TCB. -/
private def stTwoReceivers? : Option SystemState :=
  match endpointReceiveDual epId recvLocalTid (some replyId) stBase with
  | .ok (_, st1) =>
      match endpointReceiveDual epId recvRemoteTid none st1 with
      | .ok (_, st2) => some st2
      | .error _ => none
  | .error _ => none

/-- **WS-OD OD3.11** fixture (blocking branch): one sender already parked, so a
second `.call` enqueues behind it and writes *its* TCB as the old tail. -/
private def stOneParkedSender? : Option SystemState :=
  match endpointCallOnCore epId recvLocalTid IpcMessage.empty bootCoreId stBase with
  | (st1, .ok _) => some st1
  | _ => none

/-- §3.12: **WS-OD OD3.11** — the queue-structure neighbour, on both branches.

`endpointQueuePopHead` relinks the popped thread's successor into the head and
`endpointQueueEnqueue` relinks the enqueueing queue's old tail; the `.send` and
`.call` footprints named neither, so a rendezvous on one core and a
`.tcbSuspend` of the affected neighbour on another had provably disjoint
footprints while both writing that TCB.  Both branches are exercised, and each
is guarded against passing vacuously: the resolver must name a real thread, that
thread's lock must be declared, and the transition must observably rewrite it. -/
private def runQueueNeighbourFootprintChecks : IO Unit := do
  IO.println "--- §3.12 WS-OD OD3.11 queue-structure neighbour footprint ---"
  -- Rendezvous branch: the pop promotes the second receiver.
  match stTwoReceivers? with
  | none => assertBool "setup: two receivers queued" false
  | some st =>
      assertBool "setup: the receive queue is local -> remote"
        (match st.getEndpoint? epId with
         | some ep => decide (ep.receiveQ.head = some recvLocalTid
             ∧ ep.receiveQ.tail = some recvRemoteTid)
         | none => false)
      assertBool "the resolver names the popped receiver's successor"
        (decide (sendSideQueueStructureNeighbor? st epId = some recvRemoteTid))
      let ls := lockSet_endpointCallOnCore st epId callerTid cnRoot
      assertBool "the successor's TCB write lock is declared (rendezvous)"
        (decide ((tcbLock recvRemoteTid, AccessMode.write) ∈ ls.pairs))
      let (st', _) := endpointCallOnCore epId callerTid IpcMessage.empty bootCoreId st
      assertBool "the call rewrites the promoted head's links"
        (match st'.getTcb? recvRemoteTid with
         | some t => decide (t.queuePrev = none ∧ t.queuePPrev = some .endpointHead)
         | none => false)
  -- Blocking branch: the enqueue relinks the old tail.
  match stOneParkedSender? with
  | none => assertBool "setup: one sender parked on the send queue" false
  | some st =>
      assertBool "setup: the send queue holds exactly the parked sender"
        (match st.getEndpoint? epId with
         | some ep => decide (ep.sendQ.head = some recvLocalTid
             ∧ ep.sendQ.tail = some recvLocalTid ∧ ep.receiveQ.head = none)
         | none => false)
      assertBool "the resolver names the send queue's old tail"
        (decide (sendSideQueueStructureNeighbor? st epId = some recvLocalTid))
      let ls := lockSet_endpointCallOnCore st epId callerTid cnRoot
      assertBool "the old tail's TCB write lock is declared (blocking)"
        (decide ((tcbLock recvLocalTid, AccessMode.write) ∈ ls.pairs))
      let (st', _) := endpointCallOnCore epId callerTid IpcMessage.empty bootCoreId st
      assertBool "the call rewrites the old tail's queueNext"
        (match st'.getTcb? recvLocalTid with
         | some t => decide (t.queueNext = some callerTid)
         | none => false)
  -- NEGATIVE: an endpoint with an empty send queue and no receiver has no
  -- neighbour at all -- the caller becomes the sole member, and nothing else is
  -- written.  Mutating by deleting the member would be caught above; this keeps
  -- it and changes the state.
  assertBool "an empty endpoint declares no queue-structure neighbour"
    (decide (sendSideQueueStructureNeighbor? stBase epId = none))
  -- **WS-OD OD3.12**: the receive side is the mirror -- it pops the *send*
  -- queue and blocks on the *receive* queue -- so the same two branches, with
  -- the queues exchanged.
  match stOneParkedSender? with
  | none => assertBool "setup (receive side): one sender parked" false
  | some st =>
      assertBool "the receive-side resolver names the parked sender's successor"
        (decide (receiveSideQueueStructureNeighbor? st epId = none))
      let lsR := lockSet_endpointReceiveOnCore st epId callerTid cnRoot none
      assertBool "a sole parked sender has no successor, so no member is declared"
        (decide (lsR.pairs.all (fun p => p.1 ≠ tcbLock recvRemoteTid)))
  match stTwoReceivers? with
  | none => assertBool "setup (receive side): two receivers queued" false
  | some st =>
      -- With no sender parked, a `.receive` blocks and relinks the *receive*
      -- queue's old tail -- here the second receiver.
      assertBool "the receive-side resolver names the receive queue's old tail"
        (decide (receiveSideQueueStructureNeighbor? st epId = some recvRemoteTid))
      let lsR := lockSet_endpointReceiveOnCore st epId callerTid cnRoot none
      assertBool "the old tail's TCB write lock is declared (receive, blocking)"
        (decide ((tcbLock recvRemoteTid, AccessMode.write) ∈ lsR.pairs))
      match endpointReceiveDualOnCore epId callerTid none bootCoreId st with
      | (st', .ok _) =>
          assertBool "the receive rewrites the old tail's queueNext"
            (match st'.getTcb? recvRemoteTid with
             | some t => decide (t.queueNext = some callerTid)
             | none => false)
      | (_, .error _) => assertBool "the blocking receive succeeds" false

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

-- ---------------------------------------------------------------------------
-- WS-RR RR7.12 — the declared footprint, ACQUIRED at the live syscall seam.
--
-- Everything above exercises transitions; this group exercises the *bracket*.
-- Without it the row would ship a mechanism nobody had seen engage: the smoke
-- and trace tiers pass either way, because the golden fixture drives no syscall
-- whose footprint is declared through this seam.
--
-- `.tcbSuspend` is the arm used, for the same reason SM8.D.5's fixture uses it:
-- it is the one whose whole resolution chain — the single-level CSpace guard,
-- the rights-gated lookup, the sentinel check, the state-resolved optionals —
-- was already exercised, so a failure here is the bracket's and not the
-- resolver's.
-- ---------------------------------------------------------------------------

private def bracketCNode : SeLe4n.ObjId := ⟨430⟩
private def bracketVictim : SeLe4n.ThreadId := ⟨431⟩
private def bracketSlot : SeLe4n.Slot := SeLe4n.Slot.ofNat 1

/-- `.tcbSuspend` requires `.write` on the victim's capability. -/
private def bracketSlotCap : Capability :=
  { target := .object bracketVictim.toObjId,
    rights := AccessRightSet.ofList [.read, .write] }

/-- Depth 4 = `radixWidth`, so the resolution consumes every bit in one hop and
the leaf **is** this root — the single-level shape `abiEntryGate` requires. -/
private def bracketCNodeValue : CNode :=
  { depth := 4, guardWidth := 0, guardValue := 0, radixWidth := 4,
    slots := SeLe4n.UniqueSlotMap.ofListWF [(bracketSlot, bracketSlotCap)] }

/-- A caller whose registers really decode to `.tcbSuspend` (`x7 = 20`) on the
capability at slot 1 (`x0 = 1`). -/
private def bracketCaller : TCB :=
  { mkTcb 401 40 none with
      cspaceRoot := bracketCNode
      registerContext :=
        { pc := ⟨0x1000⟩, sp := ⟨0x8000⟩,
          gpr := fun r => if r.val == 0 then ⟨1⟩ else if r.val == 7 then ⟨20⟩ else ⟨0⟩ } }

private def bracketState : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject bracketCNode (.cnode bracketCNodeValue)
      |>.withObject callerTid.toObjId (.tcb bracketCaller)
      |>.withObject bracketVictim.toObjId (.tcb (mkTcb 431 30 none))
      |>.withRunnable [callerTid]
      |>.withCurrent (some callerTid)
      |>.build)
  base

/-- The ABI words of a `.tcbSuspend` on the capability at slot 1:
`syscallId = 20`, `msgInfo = 0`, `x0 = 1` (the CPtr), `x1..x5 = 0`. -/
private def bracketDecl (st : SystemState) : Option Concurrency.LockSet :=
  declaredLockSetForAbiEntry harnessLabelingContext bootCoreId
    (syscallId := 20) (msgInfo := 0) (x0 := 1) (x1 := 0) (x2 := 0) (x3 := 0) (x4 := 0) (x5 := 0) st

private def bracketPlan (st : SystemState) :
    Option (SeLe4n.ThreadId × SyscallDecodeResult × SystemState) :=
  abiEntryPlan harnessLabelingContext bootCoreId
    (syscallId := 20) (msgInfo := 0) (x0 := 1) (x1 := 0) (x2 := 0) (x3 := 0) (x4 := 0) (x5 := 0) st

/-- The step the bracket wraps, at those same words. -/
private def bracketStepFn (st : SystemState) :=
  syscallDispatchCrossCoreStep harnessLabelingContext bootCoreId
    (syscallId := 20) (msgInfo := 0) (x0 := 1) (x1 := 0) (x2 := 0) (x3 := 0) (x4 := 0) (x5 := 0)
    (ipcBufferAddr := 0) (elr := 0) (spsr := 0) (spEl0 := 0) (x30 := 0) st

/-- Which arm of the bracket this entry takes, as the bracket itself computes
it — `syscallDispatchCrossCoreBracketedStep` is this `match`ed and flattened. -/
private def bracketOutcome (st : SystemState) :=
  runUnderDeclaredLockSet bracketDecl bootCoreId bracketStepFn st

private def bracketRun (st : SystemState) :=
  syscallDispatchCrossCoreBracketedStep harnessLabelingContext bootCoreId
    (syscallId := 20) (msgInfo := 0) (x0 := 1) (x1 := 0) (x2 := 0) (x3 := 0) (x4 := 0) (x5 := 0)
    (ipcBufferAddr := 0) (elr := 0) (spsr := 0) (spEl0 := 0) (x30 := 0) st

/-- `.cspaceMint` (id 4) — an arm this cut leaves undeclared, for the fallback. -/
private def undeclaredRun (st : SystemState) :=
  syscallDispatchCrossCoreBracketedStep harnessLabelingContext bootCoreId
    (syscallId := 4) (msgInfo := 0) (x0 := 1) (x1 := 0) (x2 := 0) (x3 := 0) (x4 := 0) (x5 := 0)
    (ipcBufferAddr := 0) (elr := 0) (spsr := 0) (spEl0 := 0) (x30 := 0) st

private def undeclaredBare (st : SystemState) :=
  syscallDispatchCrossCoreStep harnessLabelingContext bootCoreId
    (syscallId := 4) (msgInfo := 0) (x0 := 1) (x1 := 0) (x2 := 0) (x3 := 0) (x4 := 0) (x5 := 0)
    (ipcBufferAddr := 0) (elr := 0) (spsr := 0) (spEl0 := 0) (x30 := 0) st

private def undeclaredDecl (st : SystemState) : Option Concurrency.LockSet :=
  declaredLockSetForAbiEntry harnessLabelingContext bootCoreId
    (syscallId := 4) (msgInfo := 0) (x0 := 1) (x1 := 0) (x2 := 0) (x3 := 0) (x4 := 0) (x5 := 0) st

/-- **WS-OD OD3.5**: `.replyRecv`'s footprint declares for a delegated reply,
and names the recorded server's TCB.

`replyRecvBody` returns the donation of `(recordedReplyServer? st prevCaller).getD tid`,
which on a delegated reply is not the invoking thread — so the transition writes
that server's TCB while the footprint named neither it nor the second hand-off's
SchedContext.  PR #892 review round 6 answered that by making the arm **refuse**,
because the server's write lock had nowhere to go under a ceiling of nine; this
witness pinned the refusal.  OD3.5 raised the ceiling to eleven and declared both
missing members, so the delegated case is now *covered* rather than excused, and
the property worth pinning inverted: the arm declares, and what it declares names
the delegated server.

The two states still differ in **one field** — the answered caller's recorded
reply target — which is the mutation this pins: keep every operand and change who
the reply was issued to.  What that mutation must now change is the *footprint*,
not the decision to have one. -/
private def runDelegatedReplyRecvFootprintChecks : IO Unit := do
  IO.println "--- WS-OD OD3.5: `.replyRecv` declares for a delegated reply ---"
  let replier : SeLe4n.ThreadId := ⟨2⟩
  let prevCaller : SeLe4n.ThreadId := ⟨3⟩
  let delegate : SeLe4n.ThreadId := ⟨4⟩
  let epId : SeLe4n.ObjId := SeLe4n.ObjId.ofNat 20
  let rid : SeLe4n.ReplyId := ⟨21⟩
  let mkTcb := fun (t : SeLe4n.ThreadId) (ipc : SeLe4n.Model.ThreadIpcState) =>
    SeLe4n.Model.KernelObject.tcb
      { tid := t, priority := ⟨10⟩, domain := ⟨0⟩,
        cspaceRoot := SeLe4n.ObjId.ofNat 0, vspaceRoot := SeLe4n.ObjId.ofNat 0,
        ipcBuffer := SeLe4n.VAddr.ofNat 0, ipcState := ipc }
  -- The reply object answers `prevCaller`; `prevCaller` records `replier` as the
  -- server it is blocked on.  That is the ordinary, non-delegated shape.
  let base : SystemState := { (default : SystemState) with
    objects := (((default : SystemState).objects.insert replier.toObjId
        (mkTcb replier .ready)).insert epId (.endpoint { })).insert rid.toObjId
        (.reply { replyId := rid, caller := some prevCaller }) }
  let stOwn : SystemState := { base with
    objects := base.objects.insert prevCaller.toObjId
      (mkTcb prevCaller (.blockedOnReply epId (some replier))) }
  -- The delegated shape: same operands, same reply object, same everything —
  -- except that the caller records a *different* thread as its server.
  let stDelegated : SystemState := { base with
    objects := base.objects.insert prevCaller.toObjId
      (mkTcb prevCaller (.blockedOnReply epId (some delegate))) }
  let ops : Concurrency.SyscallLockOperands :=
    { caller := replier, targetObject := some epId, targetReply := some rid }
  assertBool "the reply object answers the caller in both states"
    (decide (SeLe4n.Kernel.replyAnsweredCaller? stOwn rid = some prevCaller) &&
     decide (SeLe4n.Kernel.replyAnsweredCaller? stDelegated rid = some prevCaller))
  assertBool "the non-delegated state records the replier as the server"
    (decide (SeLe4n.Kernel.recordedReplyServer? stOwn prevCaller = some replier))
  assertBool "the delegated state records some OTHER thread"
    (decide (SeLe4n.Kernel.recordedReplyServer? stDelegated prevCaller = some delegate))
  assertBool "a non-delegated `.replyRecv` declares a footprint"
    (Concurrency.lockSetForSyscall .replyRecv ops stOwn).isSome
  assertBool "…and so does a delegated one (OD3.5 — round 6's refusal is retired)"
    (Concurrency.lockSetForSyscall .replyRecv ops stDelegated).isSome
  -- The delegated server's TCB write lock is the member OD3.5 added.  It is a
  -- key the non-delegated shape gets for free — there the recorded server IS the
  -- invoking thread, so `insertOrMerge` folds it into the caller's own lock —
  -- and the delegated shape must name separately.
  assertBool "the delegated footprint names the recorded server's TCB write lock"
    (match Concurrency.lockSetForSyscall .replyRecv ops stDelegated with
     | some fp => decide ((tcbLock delegate, AccessMode.write) ∈ fp.pairs)
     | none => false)
  assertBool "…which is a DISTINCT key from the invoking thread's"
    (decide (tcbLock delegate ≠ tcbLock replier))
  -- The mutation's payoff: changing who the reply was issued to changes the
  -- footprint.  A declaration insensitive to the recorded server would satisfy
  -- every assertion above about `stOwn` and still write a TCB it never named.
  assertBool "NEGATIVE: the delegated footprint is not the non-delegated one"
    (match Concurrency.lockSetForSyscall .replyRecv ops stOwn,
           Concurrency.lockSetForSyscall .replyRecv ops stDelegated with
     | some a, some b => !decide (a.pairs = b.pairs)
     | _, _ => false)
  assertBool "NEGATIVE: the non-delegated footprint does not name the delegate"
    (match Concurrency.lockSetForSyscall .replyRecv ops stOwn with
     | some fp => !decide ((tcbLock delegate, AccessMode.write) ∈ fp.pairs)
     | none => false)
  -- Both are inside the ceiling: OD3.5 raised it to eleven precisely so the
  -- delegated shape fits rather than being refused.
  assertBool "both declared footprints are at or under the ceiling"
    (match Concurrency.lockSetForSyscall .replyRecv ops stOwn,
           Concurrency.lockSetForSyscall .replyRecv ops stDelegated with
     | some a, some b => decide (a.size ≤ Concurrency.maxLockSetSize)
                      && decide (b.size ≤ Concurrency.maxLockSetSize)
     | _, _ => false)

/-- WS-RR RR7.12: the bracket, exercised. -/
private def runDeclaredFootprintBracketChecks : IO Unit := do
  IO.println "--- WS-RR RR7.12 the declared footprint at the live syscall seam ---"
  -- The seam declares a footprint for this entry at all — the precondition for
  -- everything else in this group.
  assertBool "the ABI seam declares a footprint for a `.tcbSuspend` decode"
    (decide (bracketDecl bracketState).isSome)
  -- …and it is the resolver's own answer at the operands the entry resolved,
  -- not a set the test supplied.
  assertBool "the declared footprint is `lockSetForSyscall`'s answer at the entry's decode"
    (match bracketPlan bracketState with
     | some (tid, decoded, stFilled) =>
       decide (decoded.syscallId = .tcbSuspend) &&
       (match abiEntryLockOperands decoded tid stFilled with
        | some ops =>
          decide (Concurrency.lockSetForSyscall decoded.syscallId ops stFilled
                    = bracketDecl bracketState) &&
          decide (ops.caller = tid)
        | none => false)
     | none => false)
  -- **The committed arm is taken.** The guard passes on an uncontended state,
  -- so the syscall runs bracketed rather than being refused — the check that
  -- would have caught a bracket that engages and then always declines.
  assertBool "the guard PASSES on an uncontended state (the committed arm is taken)"
    (match bracketDecl bracketState with
     | some fp =>
       let acquired := Concurrency.acquireAll bootCoreId fp.lockAcquireSequence bracketState
       decide (bracketDecl acquired = some fp) &&
       decide (Concurrency.lockSetHeld bootCoreId fp acquired)
     | none => false)
  -- **Which arm**, stated directly rather than inferred from the outcome: the
  -- committed one. Comparing outcome frames would not settle it — a syscall
  -- that legitimately errors returns the same `.illegalState` frame a refusal
  -- does, so a bracket that always declined would look identical.
  assertBool "the bracket takes the COMMITTED arm (not `undeclared`, not `refused`)"
    (match bracketOutcome bracketState with
     | .committed _ => true
     | _ => false)
  -- NEGATIVE: and neither of the other two.
  assertBool "NEGATIVE: the bracket neither falls back nor refuses here"
    (match bracketOutcome bracketState with
     | .undeclared _ => false
     | .refused _ => false
     | .committed _ => true)
  -- **Bracketing does not change what the syscall returns.** The declared
  -- footprint is exclusion, not semantics: the growing and shrinking phases
  -- write lock words and nothing else, so the caller's frame is the frame the
  -- unbracketed step produced.
  assertBool "the bracketed step returns the unbracketed step's frame"
    (let br := bracketRun bracketState
     let ba := bracketStepFn bracketState
     decide (br.1.1.tagWord = ba.1.1.tagWord) &&
     decide (br.1.1.mailboxFrame.x0 = ba.1.1.mailboxFrame.x0) &&
     decide (br.1.1.mailboxFrame.x1 = ba.1.1.mailboxFrame.x1))
  -- The bracket leaves nothing held: the shrinking phase runs on the committed
  -- path too, so the next syscall on these objects is not blocked by this one.
  assertBool "every declared member is released after the bracketed step"
    (match bracketDecl bracketState with
     | some fp =>
       fp.pairs.all (fun p =>
         decide (¬ Concurrency.lockHeld bootCoreId p.1 p.2 (bracketRun bracketState).2))
     | none => false)
  -- The fallback: an UNDECLARED syscall runs bit-identically to the unbracketed
  -- step, which is what makes landing the bracket safe ahead of the remaining
  -- declarations.
  assertBool "an undeclared syscall's bracketed step IS the unbracketed step"
    -- The equality itself is `syscallDispatchCrossCoreBracketedStep_undeclared`,
    -- which is definitional; what a runtime check can add is that the fallback
    -- path is the one this state actually takes, and that the two agree on the
    -- word the ABI returns.
    (have _h := @syscallDispatchCrossCoreBracketedStep_undeclared
     decide (undeclaredDecl bracketState = none) &&
     decide ((undeclaredRun bracketState).1.1.tagWord
               = (undeclaredBare bracketState).1.1.tagWord))

def runSmpCrossCoreCallChecks : IO Unit := do
  IO.println "WS-SM SM6.A — Cross-core endpoint call suite"
  IO.println "===================================="
  runLockSetChecks
  runBlockingChecks
  runNoReceiverChecks
  runRendezvousChecks
  runQueueNeighbourFootprintChecks
  runPerCoreBundleChecks
  runDeclaredFootprintBracketChecks
  runDelegatedReplyRecvFootprintChecks
  IO.println "===================================="
  IO.println "All SM6.A cross-core call checks PASS."

end SeLe4n.Testing.SmpCrossCoreCall

def main : IO Unit :=
  SeLe4n.Testing.SmpCrossCoreCall.runSmpCrossCoreCallChecks
