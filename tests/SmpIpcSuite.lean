-- SPDX-License-Identifier: GPL-3.0-or-later
/-
  seLe4n  - A Lean Microkernel
  Copyright (C) 2026  Adam Hall
  This program comes with ABSOLUTELY NO WARRANTY.
  This is free software, and you are welcome to redistribute it
  under certain conditions. See: https://github.com/hatter6822/seLe4n/blob/main/LICENSE
-/

import SeLe4n.Kernel.IPC.CrossCore.EndpointCall
import SeLe4n.Kernel.IPC.CrossCore.EndpointReply
import SeLe4n.Kernel.IPC.CrossCore.EndpointCallDispatch
import SeLe4n.Kernel.IPC.CrossCore.EndpointReplyDispatch
import SeLe4n.Kernel.IPC.Invariant.PerCoreBundlePreservation
import SeLe4n.Kernel.Scheduler.Operations.PerCoreWcrt
import SeLe4n.Testing.StateBuilder

/-!
# WS-SM SM6.F.1 — Aggregate SMP cross-core IPC suite

The acceptance-gate aggregate suite for WS-SM Phase SM6
(`docs/planning/SMP_CROSS_CORE_IPC_PLAN.md` §8): end-to-end cross-core IPC
round trips on a **4-thread / 4-core** deterministic fixture, composing the
SM6.A/SM6.C transitions with the SM5 per-core scheduler (SGI handler
dispatch) into full client/server message flows.

Where the per-phase suites (`SmpCrossCoreCallSuite`, `SmpCrossCoreReplySuite`)
exercise each transition in isolation, this suite drives **multi-step
pipelines** threaded through the evolving state:

* **§3.1** the 2-thread cross-core IPC round trip (acceptance gate): client A
  on core 0 calls a server homed on core 1; the call wakes the server via a
  `.reschedule` SGI; core 1's handler dispatches it; the server's reply wakes
  the client back on core 0 with the reply payload; core 0's handler resumes it;
* **§3.2** the 4-thread SMP rendezvous (acceptance gate): two client/server
  pairs (cores 0↔1 and 2↔3) complete interleaved round trips with cross-pair
  framing and payload isolation;
* **§3.3** cross-core send/receive rendezvous: a receive from core 1 wakes a
  `blockedOnSend` sender to its home core 2 with an SGI;
* **§3.4** client-first ordering: a call with no receiver blocks the caller
  (`blockedOnCall`); the server's later receive completes the same rendezvous;
* **§3.5** the server steady-state loop: `endpointReplyRecvOnCore` replies to
  the previous client and atomically receives the next, surfacing the union
  of both legs' SGIs;
* **§3.6** fail-closed error paths (absent/wrong-kind objects, oversized
  payloads, replay, no-stash rendezvous) — every error returns the pre-state;
* **§3.7** 2PL lock-set discipline on the live pipeline states (state-resolved
  footprints, hierarchical kinds, SM5.J WCRT bound);
* **§3.8** live-dispatch coherence: `determineExecutingCore` + the full
  `endpointCallCrossCoreDispatch` agree with the bare transition;
* **§9** the deterministic **4-core IPC golden trace** (SM6.F.4), verified
  byte-for-byte against `tests/fixtures/smp_ipc_4core.expected`.

`lake exe smp_ipc_suite` runs all scenarios; an IPC-logic regression flips a
decidable check or diverges the golden trace.
-/

namespace SeLe4n.Testing.SmpIpc

open SeLe4n.Model
open SeLe4n.Kernel
open SeLe4n.Kernel.Concurrency
open SeLe4n.Testing

-- ============================================================================
-- §1  Surface anchors (elaboration-time: rename/removal breaks this suite)
-- ============================================================================

-- The cross-core IPC transitions (SM6.A / SM6.C, production):
#check @endpointCallOnCore
#check @endpointCallWithCapsOnCore
#check @endpointCallCrossCoreDispatch
#check @endpointCallCrossCoreDispatchChecked
#check @endpointReceiveDualOnCore
#check @endpointReplyOnCore
#check @endpointReplyRecvOnCore
#check @endpointReplyCrossCoreDispatch
#check @endpointReplyCrossCoreDispatchChecked
#check @removeRunnableOnCore
#check @determineExecutingCore
#check @determineTargetCore
#check @wakeThread
#check @handleRescheduleSgiOnCore
-- Pre-resolution helpers + state-resolved lock-sets (SM3.B.3 / SM6.A.1):
#check @endpointCallReceiver?
#check @endpointCallDonatedSc?
#check @endpointCallServerFirstReply?
#check @endpointReplyDonation?
#check @lockSet_endpointCallOnCore
#check @lockSet_endpointCallWithCaps
#check @lockSet_endpointReplyOnCore
#check @lockSet_endpointReplyRecvOnCore
-- Acceptance-gate theorems (SGI emission, per-core blocking, delivery, replay):
#check @endpointCallOnCore_emits_sgi_if_remote_receiver
#check @endpointCallOnCore_no_sgi_if_local_receiver
#check @endpointCallOnCore_perCore_blocking
#check @endpointCallOnCore_atomic_under_lockSet
#check @endpointCallOnCore_lockSet_correct
#check @endpointReplyOnCore_remote_wake
#check @endpointReplyOnCore_perCore_delivery
#check @endpointReplyOnCore_replay_rejected
#check @endpointReplyOnCore_atomic_under_lockSet
#check @endpointReplyRecvOnCore_atomic_under_lockSet
#check @endpointReplyRecv_lockSet_correct
#check @endpointReply_donation_chain_length_bounded
-- SM6.D.2: the six IPC operations preserve every core's bundle view (production):
#check @endpointSendDual_preserves_ipcInvariantFull_perCore
#check @endpointReceiveDual_preserves_ipcInvariantFull_perCore
#check @endpointCall_preserves_ipcInvariantFull_perCore
#check @endpointReply_preserves_ipcInvariantFull_perCore
#check @endpointReplyRecv_preserves_ipcInvariantFull_perCore
#check @notificationSignal_preserves_ipcInvariantFull_perCore
#check @notificationWait_preserves_ipcInvariantFull_perCore

-- ============================================================================
-- §2  Elaboration-time witnesses (headline theorems applied to typed inputs)
-- ============================================================================

/-- SM6.A bridge: the per-core deschedule at the boot core is exactly the
single-core primitive (definitional). -/
example (st : SystemState) (tid : SeLe4n.ThreadId) :
    removeRunnableOnCore st tid bootCoreId = removeRunnable st tid :=
  removeRunnableOnCore_bootCoreId st tid

/-- SM6.A.1 rendezvous reduction: on a waiting receiver, the cross-core call is
the receiver wake + caller block, surfacing exactly the wake's SGI. -/
example (endpointId : SeLe4n.ObjId) (caller : SeLe4n.ThreadId) (msg : IpcMessage)
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
    (hLink : SystemState.linkServerStashedReply caller receiver st4 = .ok ((), st5)) :
    endpointCallOnCore endpointId caller msg executingCore st
      = (removeRunnableOnCore st5 caller executingCore,
         .ok (wakeThread st'' receiver executingCore).2) :=
  endpointCallOnCore_rendezvous_eq endpointId caller msg executingCore st ep receiver
    recvTcb0 st' st'' st4 st5 hSz1 hSz2 hObj hHead hPop hStore hCallerStore hLink

/-- SM6.D: the per-core bundle's thread restriction is the operational wake
target — the wake path delivers each thread to its `threadHomeCore`. -/
example (st : SystemState) (tid : SeLe4n.ThreadId) (tcb : TCB)
    (hTcb : st.getTcb? tid = some tcb) :
    determineTargetCore st tid = threadHomeCore tcb :=
  determineTargetCore_eq_threadHomeCore hTcb

-- ============================================================================
-- §3  Runtime scenarios — the deterministic 4-thread / 4-core IPC fixture
-- ============================================================================

private def assertBool (name : String) (b : Bool) : IO Unit := do
  if b then IO.println s!"  PASS: {name}"
  else
    IO.println s!"  FAIL: {name}"
    throw (IO.userError s!"Assertion failed: {name}")

/-- The four RPi5 cores. -/
private def c0 : CoreId := bootCoreId
private def c1 : CoreId := ⟨1, by decide⟩
private def c2 : CoreId := ⟨2, by decide⟩
private def c3 : CoreId := ⟨3, by decide⟩

-- Fixture OIDs (range 800–899 — see the range table in SeLe4n/Testing/Helpers.lean).
private def cnRoot : SeLe4n.ObjId := ⟨800⟩
private def vsRoot : SeLe4n.ObjId := ⟨805⟩
private def epAB : SeLe4n.ObjId := ⟨810⟩
private def epCD : SeLe4n.ObjId := ⟨811⟩
private def clientA : SeLe4n.ThreadId := ⟨821⟩
private def serverB : SeLe4n.ThreadId := ⟨822⟩
private def clientC : SeLe4n.ThreadId := ⟨823⟩
private def serverD : SeLe4n.ThreadId := ⟨824⟩
private def senderE : SeLe4n.ThreadId := ⟨825⟩
private def replyB : SeLe4n.ReplyId := ⟨831⟩
private def replyD : SeLe4n.ReplyId := ⟨832⟩
private def replyB2 : SeLe4n.ReplyId := ⟨833⟩

-- Distinct pinned payloads (payload isolation is asserted on the exact values).
private def callMsgA : IpcMessage :=
  { registers := #[SeLe4n.RegValue.ofNat 11, SeLe4n.RegValue.ofNat 12], caps := #[], badge := none }
private def callMsgC : IpcMessage :=
  { registers := #[SeLe4n.RegValue.ofNat 21], caps := #[], badge := none }
private def replyMsgB : IpcMessage :=
  { registers := #[SeLe4n.RegValue.ofNat 42], caps := #[], badge := none }
private def replyMsgD : IpcMessage :=
  { registers := #[SeLe4n.RegValue.ofNat 84], caps := #[], badge := none }
private def sendMsgE : IpcMessage :=
  { registers := #[SeLe4n.RegValue.ofNat 5], caps := #[], badge := none }

private def mkTcb (tid : Nat) (prio : Nat) (aff : Option CoreId) : TCB :=
  { tid := ⟨tid⟩, priority := ⟨prio⟩, domain := ⟨0⟩, cspaceRoot := cnRoot,
    vspaceRoot := vsRoot, ipcBuffer := SeLe4n.VAddr.ofNat 4096, ipcState := .ready,
    cpuAffinity := aff }

/-- The 4-thread / 4-core IPC workload: two client/server pairs, one per core
pair (client A on core 0 ↔ server B homed core 1; client C on core 2 ↔ server D
homed core 3), each endpoint with a free Reply object the server stashes on its
`Recv`, each thread runnable on its **own** core's run queue.  Client A is
unbound (home = boot core 0); B/C/D are affinity-bound to cores 1/2/3. -/
private def stFourCore : SystemState :=
  let base :=
    (BootstrapBuilder.empty
      |>.withObject epAB (.endpoint {})
      |>.withObject epCD (.endpoint {})
      |>.withObject clientA.toObjId (.tcb (mkTcb 821 40 none))
      |>.withObject serverB.toObjId (.tcb (mkTcb 822 50 (some c1)))
      |>.withObject clientC.toObjId (.tcb (mkTcb 823 40 (some c2)))
      |>.withObject serverD.toObjId (.tcb (mkTcb 824 50 (some c3)))
      |>.withObject replyB.toObjId (.reply { replyId := replyB })
      |>.withObject replyD.toObjId (.reply { replyId := replyD })
      |>.withObject replyB2.toObjId (.reply { replyId := replyB2 })
      |>.build)
  { base with scheduler :=
      ((((base.scheduler.setRunQueueOnCore c0 (RunQueue.ofList [(clientA, ⟨40⟩)])).setRunQueueOnCore
        c1 (RunQueue.ofList [(serverB, ⟨50⟩)])).setRunQueueOnCore
        c2 (RunQueue.ofList [(clientC, ⟨40⟩)])).setRunQueueOnCore
        c3 (RunQueue.ofList [(serverD, ⟨50⟩)])) }

/-- `stFourCore` plus a fifth thread `E` (priority 35, bound to core 2) present
in the object store but in no run queue — the send-rendezvous sender. -/
private def stWithSenderE : SystemState :=
  { stFourCore with objects := stFourCore.objects.insert senderE.toObjId (.tcb (mkTcb 825 35 (some c2))) }

-- Fail-closed Option plumbing for the multi-step pipelines.
private def okPair {α : Type} (r : SystemState × Except KernelError α) :
    Option (SystemState × α) :=
  match r with
  | (st, .ok a) => some (st, a)
  | (_, .error _) => none

private def okExcept {α : Type} (r : Except KernelError α) : Option α :=
  match r with
  | .ok a => some a
  | .error _ => none

/-- The full interleaved 4-thread round-trip pipeline (every intermediate state
+ every surfaced SGI).  Both servers block on their endpoints from their own
cores; both clients call cross-core; each SGI is handled on its target core;
both servers reply cross-core; each reply SGI is handled on its target core. -/
private structure RoundTrip where
  afterRecv   : SystemState
  afterCallA  : SystemState
  sgiCallA    : Option (CoreId × SgiKind)
  afterSgiB   : SystemState
  afterCallC  : SystemState
  sgiCallC    : Option (CoreId × SgiKind)
  afterSgiD   : SystemState
  afterReplyB : SystemState
  sgiReplyB   : Option (CoreId × SgiKind)
  afterSgiA   : SystemState
  afterReplyD : SystemState
  sgiReplyD   : Option (CoreId × SgiKind)
  afterSgiC   : SystemState

private def roundTrip? : Option RoundTrip := do
  let (st1, _) ← okPair (endpointReceiveDualOnCore epAB serverB (some replyB) c1 stFourCore)
  let (afterRecv, _) ← okPair (endpointReceiveDualOnCore epCD serverD (some replyD) c3 st1)
  let (afterCallA, sgiCallA) ← okPair (endpointCallOnCore epAB clientA callMsgA c0 afterRecv)
  let afterSgiB ← okExcept (handleRescheduleSgiOnCore afterCallA c1)
  let (afterCallC, sgiCallC) ← okPair (endpointCallOnCore epCD clientC callMsgC c2 afterSgiB)
  let afterSgiD ← okExcept (handleRescheduleSgiOnCore afterCallC c3)
  let (afterReplyB, sgiReplyB) ← okPair (endpointReplyOnCore serverB clientA replyMsgB c1 afterSgiD)
  let afterSgiA ← okExcept (handleRescheduleSgiOnCore afterReplyB c0)
  let (afterReplyD, sgiReplyD) ← okPair (endpointReplyOnCore serverD clientC replyMsgD c3 afterSgiA)
  let afterSgiC ← okExcept (handleRescheduleSgiOnCore afterReplyD c2)
  pure { afterRecv := afterRecv, afterCallA := afterCallA, sgiCallA := sgiCallA,
         afterSgiB := afterSgiB, afterCallC := afterCallC, sgiCallC := sgiCallC,
         afterSgiD := afterSgiD, afterReplyB := afterReplyB, sgiReplyB := sgiReplyB,
         afterSgiA := afterSgiA, afterReplyD := afterReplyD, sgiReplyD := sgiReplyD,
         afterSgiC := afterSgiC }

/-- The cross-core send/receive rendezvous: blocked sender E (homed core 2) is
woken by a receive executing on core 1.  Returns (post-state, popped sender,
surfaced SGI). -/
private def sendRendezvous? :
    Option (SystemState × SeLe4n.ThreadId × Option (CoreId × SgiKind)) := do
  let ((), st1) ← okExcept (endpointSendDual epAB senderE sendMsgE stWithSenderE)
  let (st2, (sender, sgi)) ← okPair (endpointReceiveDualOnCore epAB serverB none c1 st1)
  pure (st2, sender, sgi)

/-- Decidable predicate: `tid`'s ipcState in `st` equals `expected`. -/
private def ipcStateIs (st : SystemState) (tid : SeLe4n.ThreadId)
    (expected : ThreadIpcState) : Bool :=
  match st.getTcb? tid with
  | some t => decide (t.ipcState = expected)
  | none => false

/-- Decidable predicate: `tid`'s delivered message in `st` equals `expected`. -/
private def pendingMessageIs (st : SystemState) (tid : SeLe4n.ThreadId)
    (expected : Option IpcMessage) : Bool :=
  match st.getTcb? tid with
  | some t => decide (t.pendingMessage = expected)
  | none => false

-- ============================================================================
-- §3.1  The 2-thread cross-core IPC round trip (acceptance gate)
-- ============================================================================

private def runTwoThreadRoundTripChecks : IO Unit := do
  IO.println "--- §3.1 two-thread cross-core IPC round trip (client A core 0 ↔ server B core 1) ---"
  match roundTrip? with
  | none => assertBool "round-trip pipeline succeeded" false
  | some rt =>
    -- The server's receive blocks it on ITS OWN core (removed from core 1's queue).
    assertBool "recv blocks server B as blockedOnReceive"
      (ipcStateIs rt.afterRecv serverB (.blockedOnReceive epAB))
    assertBool "recv deschedules server B from core 1's run queue"
      (!(rt.afterRecv.scheduler.runQueueOnCore c1).contains serverB)
    assertBool "recv stashes the server-supplied reply object on B"
      ((rt.afterRecv.getTcb? serverB).any (fun t => t.pendingReceiveReply == some replyB))
    -- The client's call wakes the server on its HOME core with a reschedule SGI.
    assertBool "call from core 0 fires a reschedule SGI to core 1 (remote receiver)"
      (match rt.sgiCallA with
       | some (tgt, kind) => decide (tgt = c1 ∧ kind = SgiKind.reschedule)
       | none => false)
    assertBool "call delivers the request payload to server B (.ready)"
      (ipcStateIs rt.afterCallA serverB .ready
        && pendingMessageIs rt.afterCallA serverB (some callMsgA))
    assertBool "call enqueues the woken server on core 1 (its home core)"
      ((rt.afterCallA.scheduler.runQueueOnCore c1).contains serverB)
    -- The caller blocks awaiting the reply, descheduled from its own core.
    assertBool "call blocks client A as blockedOnReply (recorded receiver B)"
      (ipcStateIs rt.afterCallA clientA (.blockedOnReply epAB (some serverB)))
    assertBool "call deschedules client A from core 0's run queue"
      (!(rt.afterCallA.scheduler.runQueueOnCore c0).contains clientA)
    assertBool "call links client A to the server's stashed reply object"
      (match rt.afterCallA.getReply? replyB, rt.afterCallA.getTcb? clientA with
       | some r, some t => decide (r.caller = some clientA ∧ t.replyObject = some replyB)
       | _, _ => false)
    -- Core 1's SGI handler dispatches the woken server.
    assertBool "core 1's reschedule handler dispatches server B (current = B)"
      (rt.afterSgiB.scheduler.currentOnCore c1 == some serverB)
    -- The server's reply wakes the client back on core 0 with the reply payload.
    assertBool "reply from core 1 fires a reschedule SGI to core 0 (remote caller)"
      (match rt.sgiReplyB with
       | some (tgt, kind) => decide (tgt = c0 ∧ kind = SgiKind.reschedule)
       | none => false)
    assertBool "reply delivers the reply payload to client A (.ready)"
      (ipcStateIs rt.afterReplyB clientA .ready
        && pendingMessageIs rt.afterReplyB clientA (some replyMsgB))
    assertBool "reply enqueues the woken client on core 0 (its home core)"
      ((rt.afterReplyB.scheduler.runQueueOnCore c0).contains clientA)
    assertBool "reply consumes the caller↔reply linkage (single-use)"
      (match rt.afterReplyB.getReply? replyB, rt.afterReplyB.getTcb? clientA with
       | some r, some t => decide (r.caller = none ∧ t.replyObject = none)
       | _, _ => false)
    -- Core 0's SGI handler resumes the client: the round trip is complete.
    assertBool "core 0's reschedule handler resumes client A (current = A)"
      (rt.afterSgiA.scheduler.currentOnCore c0 == some clientA)
    -- Replay: the delivered reply left A `.ready`, so a second reply fails closed.
    assertBool "a replayed reply after delivery fails closed with replyCapInvalid"
      (match (endpointReplyOnCore serverB clientA replyMsgB c1 rt.afterSgiA).2 with
       | .error .replyCapInvalid => true | _ => false)

-- ============================================================================
-- §3.2  The 4-thread SMP rendezvous (acceptance gate)
-- ============================================================================

private def runFourThreadRendezvousChecks : IO Unit := do
  IO.println "--- §3.2 four-thread SMP rendezvous (pairs 0↔1 and 2↔3, interleaved) ---"
  match roundTrip? with
  | none => assertBool "rendezvous pipeline succeeded" false
  | some rt =>
    -- Pair C↔D completes exactly like pair A↔B (SGIs to cores 3 and 2).
    assertBool "call from core 2 fires a reschedule SGI to core 3 (remote receiver)"
      (match rt.sgiCallC with
       | some (tgt, kind) => decide (tgt = c3 ∧ kind = SgiKind.reschedule)
       | none => false)
    assertBool "core 3's reschedule handler dispatches server D (current = D)"
      (rt.afterSgiD.scheduler.currentOnCore c3 == some serverD)
    assertBool "reply from core 3 fires a reschedule SGI to core 2 (remote caller)"
      (match rt.sgiReplyD with
       | some (tgt, kind) => decide (tgt = c2 ∧ kind = SgiKind.reschedule)
       | none => false)
    assertBool "core 2's reschedule handler resumes client C (current = C)"
      (rt.afterSgiC.scheduler.currentOnCore c2 == some clientC)
    -- Cross-pair framing: pair A↔B's call touches neither pair C↔D's endpoint
    -- nor cores 2/3's run queues.
    assertBool "A's call frames pair C↔D's endpoint (epCD object unchanged)"
      (rt.afterCallA.objects[epCD]? == rt.afterRecv.objects[epCD]?)
    assertBool "A's call frames core 2's run queue"
      ((rt.afterCallA.scheduler.runQueueOnCore c2).toList
        == (rt.afterRecv.scheduler.runQueueOnCore c2).toList)
    assertBool "A's call frames core 3's run queue"
      ((rt.afterCallA.scheduler.runQueueOnCore c3).toList
        == (rt.afterRecv.scheduler.runQueueOnCore c3).toList)
    assertBool "C's call frames pair A↔B's endpoint (epAB object unchanged)"
      (rt.afterCallC.objects[epAB]? == rt.afterSgiB.objects[epAB]?)
    -- Payload isolation: each client got ITS server's reply, each server ITS
    -- client's request — nothing crossed pairs.
    assertBool "payload isolation: A holds B's reply, C holds D's reply"
      (pendingMessageIs rt.afterSgiC clientA (some replyMsgB)
        && pendingMessageIs rt.afterSgiC clientC (some replyMsgD))
    assertBool "payload isolation: B held A's request, D held C's request"
      (pendingMessageIs rt.afterCallC serverB (some callMsgA)
        && pendingMessageIs rt.afterCallC serverD (some callMsgC))
    -- All four threads reach their expected terminal states.
    assertBool "terminal states: both clients .ready, both servers .ready"
      (ipcStateIs rt.afterSgiC clientA .ready && ipcStateIs rt.afterSgiC serverB .ready
        && ipcStateIs rt.afterSgiC clientC .ready && ipcStateIs rt.afterSgiC serverD .ready)
    assertBool "terminal placement: every thread current on its own core"
      (rt.afterSgiA.scheduler.currentOnCore c0 == some clientA
        && rt.afterSgiB.scheduler.currentOnCore c1 == some serverB
        && rt.afterSgiC.scheduler.currentOnCore c2 == some clientC
        && rt.afterSgiD.scheduler.currentOnCore c3 == some serverD)

-- ============================================================================
-- §3.3  Cross-core send/receive rendezvous (sender woken to its home core)
-- ============================================================================

private def runSendReceiveChecks : IO Unit := do
  IO.println "--- §3.3 cross-core send/receive rendezvous (sender E homed core 2, recv on core 1) ---"
  -- The blocked sender is genuinely blocked before the receive.
  match okExcept (endpointSendDual epAB senderE sendMsgE stWithSenderE) with
  | none => assertBool "send setup (E blocks on epAB) succeeded" false
  | some ((), stSent) =>
    assertBool "send blocks sender E as blockedOnSend"
      (ipcStateIs stSent senderE (.blockedOnSend epAB))
    assertBool "the blocked sender is on no run queue (genuinely blocked)"
      (!(stSent.scheduler.runQueueOnCore c2).contains senderE)
  match sendRendezvous? with
  | none => assertBool "send/receive rendezvous pipeline succeeded" false
  | some (st2, sender, sgi) =>
    assertBool "receive pops the blocked sender E" (sender == senderE)
    assertBool "receive from core 1 fires a reschedule SGI to core 2 (E's home core)"
      (match sgi with
       | some (tgt, kind) => decide (tgt = c2 ∧ kind = SgiKind.reschedule)
       | none => false)
    assertBool "the woken sender is enqueued on core 2 (its home core)"
      ((st2.scheduler.runQueueOnCore c2).contains senderE)
    assertBool "the woken sender is NOT enqueued on core 1 (the executing core)"
      (!(st2.scheduler.runQueueOnCore c1).contains senderE)
    assertBool "the woken sender is .ready with its pending message cleared"
      (ipcStateIs st2 senderE .ready && pendingMessageIs st2 senderE none)
    assertBool "the receiver holds the transferred send payload"
      (pendingMessageIs st2 serverB (some sendMsgE))

-- ============================================================================
-- §3.4  Client-first ordering (blockedOnCall, then the server's receive)
-- ============================================================================

private def runClientFirstChecks : IO Unit := do
  IO.println "--- §3.4 client-first ordering (call blocks, receive completes the rendezvous) ---"
  -- A call with NO waiting receiver blocks the caller on its own core.
  match okPair (endpointCallOnCore epAB clientA callMsgA c0 stFourCore) with
  | none => assertBool "no-receiver call succeeded" false
  | some (stCall, sgi0) =>
    assertBool "no-receiver call surfaces no SGI" (sgi0 == none)
    assertBool "no-receiver call blocks client A as blockedOnCall"
      (ipcStateIs stCall clientA (.blockedOnCall epAB))
    assertBool "no-receiver call deschedules client A from core 0"
      (!(stCall.scheduler.runQueueOnCore c0).contains clientA)
    assertBool "the blocked caller joins the endpoint's send queue"
      (match stCall.objects[epAB]? with
       | some (.endpoint ep) => ep.sendQ.head == some clientA
       | _ => false)
    -- The server's later receive (from core 1) completes the SAME rendezvous:
    -- the queued Call sender becomes blockedOnReply linked to the supplied reply.
    match okPair (endpointReceiveDualOnCore epAB serverB (some replyB) c1 stCall) with
    | none => assertBool "server receive after client-first call succeeded" false
    | some (stRecv, (sender, sgiR)) =>
      assertBool "receive pops the queued caller A" (sender == clientA)
      assertBool "a Call rendezvous on receive wakes nobody (no SGI — Call contract)"
        (sgiR == none)
      assertBool "the popped caller transitions to blockedOnReply (recorded receiver B)"
        (ipcStateIs stRecv clientA (.blockedOnReply epAB (some serverB)))
      assertBool "the popped caller is linked to the server-supplied reply object"
        (match stRecv.getReply? replyB, stRecv.getTcb? clientA with
         | some r, some t => decide (r.caller = some clientA ∧ t.replyObject = some replyB)
         | _, _ => false)
      assertBool "the receiving server holds the request payload (.ready)"
        (ipcStateIs stRecv serverB .ready && pendingMessageIs stRecv serverB (some callMsgA))
      -- The reply then completes the round trip exactly as in the server-first order.
      match okPair (endpointReplyOnCore serverB clientA replyMsgB c1 stRecv) with
      | none => assertBool "reply after client-first rendezvous succeeded" false
      | some (stRep, sgiRep) =>
        assertBool "the reply fires a reschedule SGI to core 0 (A's home core)"
          (match sgiRep with
           | some (tgt, kind) => decide (tgt = c0 ∧ kind = SgiKind.reschedule)
           | none => false)
        assertBool "the reply resumes client A with the reply payload"
          (ipcStateIs stRep clientA .ready && pendingMessageIs stRep clientA (some replyMsgB))

-- ============================================================================
-- §3.5  Server steady-state: replyRecv (reply leg + receive leg, SGI union)
-- ============================================================================

private def runReplyRecvLoopChecks : IO Unit := do
  IO.println "--- §3.5 server steady-state replyRecv (reply A, atomically receive C) ---"
  let pipeline : Option (SystemState × Option (CoreId × SgiKind) × SystemState × List (CoreId × SgiKind)) := do
    let (st1, _) ← okPair (endpointReceiveDualOnCore epAB serverB (some replyB) c1 stFourCore)
    let (st2, _) ← okPair (endpointCallOnCore epAB clientA callMsgA c0 st1)
    -- C's call finds no receiver (B was popped by A's rendezvous) → C blocks.
    let (st3, sgiC) ← okPair (endpointCallOnCore epAB clientC callMsgC c2 st2)
    let (st4, sgis) ← okPair (endpointReplyRecvOnCore epAB serverB clientA replyMsgB (some replyB2) c1 st3)
    pure (st3, sgiC, st4, sgis)
  match pipeline with
  | none => assertBool "replyRecv pipeline succeeded" false
  | some (st3, sgiC, st4, sgis) =>
    assertBool "C's call after B was popped blocks C (no receiver ⇒ no SGI)"
      (sgiC == none && ipcStateIs st3 clientC (.blockedOnCall epAB))
    assertBool "replyRecv surfaces exactly the reply-leg SGI (A's wake to core 0)"
      (match sgis with
       | [(tgt, kind)] => decide (tgt = c0 ∧ kind = SgiKind.reschedule)
       | _ => false)
    assertBool "replyRecv's reply leg resumes client A with the reply payload"
      (ipcStateIs st4 clientA .ready && pendingMessageIs st4 clientA (some replyMsgB))
    assertBool "replyRecv's receive leg pops C into blockedOnReply (recorded receiver B)"
      (ipcStateIs st4 clientC (.blockedOnReply epAB (some serverB)))
    assertBool "replyRecv's receive leg links C to the fresh reply object"
      (match st4.getReply? replyB2, st4.getTcb? clientC with
       | some r, some t => decide (r.caller = some clientC ∧ t.replyObject = some replyB2)
       | _, _ => false)
    assertBool "the server holds C's request payload after the combined op"
      (pendingMessageIs st4 serverB (some callMsgC))
    assertBool "the consumed first reply object is free again (caller cleared)"
      (match st4.getReply? replyB with
       | some r => decide (r.caller = none)
       | none => false)

-- ============================================================================
-- §3.6  Fail-closed error paths (pre-state returned on every error)
-- ============================================================================

private def bigMsg : IpcMessage :=
  { registers := Array.replicate (maxMessageRegisters + 1) (SeLe4n.RegValue.ofNat 0),
    caps := #[], badge := none }

private def runErrorPathChecks : IO Unit := do
  IO.println "--- §3.6 fail-closed error paths (absent / wrong-kind / oversized / no-stash) ---"
  -- Absent endpoint: objectNotFound; pre-state returned.
  let (stErr1, res1) := endpointCallOnCore ⟨899⟩ clientA callMsgA c0 stFourCore
  assertBool "call on an absent endpoint fails with objectNotFound"
    (match res1 with | .error .objectNotFound => true | _ => false)
  assertBool "the failed call returns the pre-state (client A still queued on core 0)"
    ((stErr1.scheduler.runQueueOnCore c0).contains clientA
      && ipcStateIs stErr1 clientA .ready)
  -- Wrong-kind object (a Reply object is not an endpoint): invalidCapability.
  assertBool "call on a wrong-kind object fails with invalidCapability"
    (match (endpointCallOnCore replyB.toObjId clientA callMsgA c0 stFourCore).2 with
     | .error .invalidCapability => true | _ => false)
  -- Oversized payload: rejected at the send boundary (deterministic, no truncation).
  assertBool "an oversized call payload fails with ipcMessageTooLarge"
    (match (endpointCallOnCore epAB clientA bigMsg c0 stFourCore).2 with
     | .error .ipcMessageTooLarge => true | _ => false)
  -- Receive-side duals.
  assertBool "receive on an absent endpoint fails with objectNotFound"
    (match (endpointReceiveDualOnCore ⟨899⟩ serverB (some replyB) c1 stFourCore).2 with
     | .error .objectNotFound => true | _ => false)
  assertBool "receive on a wrong-kind object fails with invalidCapability"
    (match (endpointReceiveDualOnCore replyB.toObjId serverB (some replyB) c1 stFourCore).2 with
     | .error .invalidCapability => true | _ => false)
  -- Reply-side duals.
  assertBool "reply to a non-blocked target fails with replyCapInvalid"
    (match (endpointReplyOnCore serverB clientA replyMsgB c1 stFourCore).2 with
     | .error .replyCapInvalid => true | _ => false)
  assertBool "reply to an absent target fails with objectNotFound"
    (match (endpointReplyOnCore serverB ⟨899⟩ replyMsgB c1 stFourCore).2 with
     | .error .objectNotFound => true | _ => false)
  -- replyRecv is all-or-nothing: a failed reply leg returns the pre-state.
  let (stRR, resRR) := endpointReplyRecvOnCore epAB serverB clientA replyMsgB (some replyB) c1 stFourCore
  assertBool "replyRecv with a failed reply leg fails closed"
    (match resRR with | .error .replyCapInvalid => true | _ => false)
  assertBool "the failed replyRecv returns the pre-state (endpoint untouched)"
    (stRR.objects[epAB]? == stFourCore.objects[epAB]?)
  -- No-stash rendezvous: a server that supplied NO reply object cannot answer a Call.
  match okPair (endpointReceiveDualOnCore epAB serverB none c1 stFourCore) with
  | none => assertBool "no-stash receive setup succeeded" false
  | some (stNoStash, _) =>
    assertBool "a Call rendezvous with a no-stash server fails closed with replyCapInvalid"
      (match (endpointCallOnCore epAB clientA callMsgA c0 stNoStash).2 with
       | .error .replyCapInvalid => true | _ => false)

-- ============================================================================
-- §3.7  2PL lock-set discipline on the live pipeline states
-- ============================================================================

private def runLockDisciplineChecks : IO Unit := do
  IO.println "--- §3.7 2PL lock-set discipline (state-resolved footprints, WCRT bound) ---"
  match okPair (endpointReceiveDualOnCore epAB serverB (some replyB) c1 stFourCore) with
  | none => assertBool "lock-set fixture setup succeeded" false
  | some (stWait, _) =>
    -- The pre-resolution helper sees the waiting receiver.
    assertBool "endpointCallReceiver? resolves the waiting server"
      (decide (endpointCallReceiver? stWait epAB = some serverB))
    let callLs := lockSet_endpointCallOnCore stWait epAB clientA cnRoot
    -- The state-resolved call footprint: hierarchically correct, duplicate-free,
    -- covering the woken receiver's TCB write, within the WCRT size bound.
    assertBool "state-resolved call lock-set kinds all permitted"
      (decide (∀ p ∈ callLs.pairs, p.fst.kind ∈ permittedKinds .call))
    assertBool "state-resolved call lock-set keys are duplicate-free"
      (decide (callLs.pairs.map (·.fst)).Nodup)
    assertBool "the woken receiver's TCB write lock is in the call footprint"
      (decide ((tcbLock serverB, AccessMode.write) ∈ callLs.pairs))
    assertBool "the caller's TCB write lock is in the call footprint"
      (decide ((tcbLock clientA, AccessMode.write) ∈ callLs.pairs))
    assertBool "the server-first stashed reply write lock is in the call footprint"
      (decide ((replyLock replyB, AccessMode.write) ∈ callLs.pairs))
    assertBool "call lock-set size within maxLockSetSize"
      (decide (callLs.pairs.length ≤ maxLockSetSize))
    -- SM5.J: an IPC op's lock WCRT is |lockSet| · 3 · tCs (plan §4.1 — lock-set
    -- size is the WCRT factor); the state-resolved call footprint is within the
    -- RPi5 bound maxLockSetSize · 3 · tCs.
    assertBool "call lock-set WCRT within the RPi5 bound (maxLockSetSize · 3 · tCs)"
      (decide (callLs.pairs.length * (3 * 60) ≤ maxLockSetSize * (3 * 60)))
    -- The reply footprint covers the caller-TCB write (the reply-state lifecycle).
    let replyLs := lockSet_endpointReplyOnCore stWait serverB cnRoot clientA
    assertBool "state-resolved reply lock-set kinds all permitted"
      (decide (∀ p ∈ replyLs.pairs, p.fst.kind ∈ permittedKinds .reply))
    assertBool "the reply target's TCB write lock is in the reply footprint"
      (decide ((tcbLock clientA, AccessMode.write) ∈ replyLs.pairs))

-- ============================================================================
-- §3.8  Live-dispatch coherence (determineExecutingCore + full dispatch)
-- ============================================================================

private def runDispatchCoherenceChecks : IO Unit := do
  IO.println "--- §3.8 live-dispatch coherence (determineExecutingCore + cross-core dispatch) ---"
  -- The executing core is derived from the live per-core current slots.
  match okExcept (switchToThreadOnCore stFourCore c2 clientC) with
  | none => assertBool "switch setup (dispatch C on core 2) succeeded" false
  | some stCur =>
    assertBool "determineExecutingCore resolves the caller's current core"
      (determineExecutingCore stCur clientC == c2)
  assertBool "determineExecutingCore falls back to the boot core for a non-current thread"
    (determineExecutingCore stFourCore serverD == bootCoreId)
  -- The full cross-core dispatch (WithCaps + donation + PIP) agrees with the
  -- bare transition on the capless rendezvous: same SGI, same receiver wake.
  match okPair (endpointReceiveDualOnCore epAB serverB (some replyB) c1 stFourCore) with
  | none => assertBool "dispatch fixture setup succeeded" false
  | some (stWait, _) =>
    let (stDisp, resDisp) := endpointCallCrossCoreDispatch epAB clientA callMsgA
      AccessRightSet.empty cnRoot (SeLe4n.Slot.ofNat 0) c0 stWait
    assertBool "cross-core dispatch rendezvous fires the remote reschedule SGI"
      (match resDisp with
       | .ok (_, some (tgt, kind)) => decide (tgt = c1 ∧ kind = SgiKind.reschedule)
       | _ => false)
    assertBool "cross-core dispatch wakes the server with the request payload"
      (ipcStateIs stDisp serverB .ready && pendingMessageIs stDisp serverB (some callMsgA))
    assertBool "cross-core dispatch blocks the caller as blockedOnReply"
      (ipcStateIs stDisp clientA (.blockedOnReply epAB (some serverB)))

-- ============================================================================
-- §9  The deterministic 4-core IPC trace (SM6.F.4 golden fixture)
-- ============================================================================

/-- Human label for a fixture thread id (stable across `ThreadId` internals). -/
private def threadLabel (t : SeLe4n.ThreadId) : String :=
  if t == clientA then "client A" else if t == serverB then "server B"
  else if t == clientC then "client C" else if t == serverD then "server D"
  else if t == senderE then "sender E" else "thread ?"

/-- Label for a surfaced cross-core SGI. -/
private def sgiLabel : Option (CoreId × SgiKind) → String
  | some (tgt, SgiKind.reschedule) => s!"SGI reschedule to core {tgt.val}"
  | some (tgt, _) => s!"SGI other to core {tgt.val}"
  | none => "no SGI (local)"

/-- Label for a thread's IPC state in a state (constructor name only). -/
private def ipcStateLabel (st : SystemState) (tid : SeLe4n.ThreadId) : String :=
  match st.getTcb? tid with
  | some t =>
      match t.ipcState with
      | .ready => "ready"
      | .blockedOnSend _ => "blockedOnSend"
      | .blockedOnReceive _ => "blockedOnReceive"
      | .blockedOnNotification _ => "blockedOnNotification"
      | .blockedOnReply _ _ => "blockedOnReply"
      | .blockedOnCall _ => "blockedOnCall"
  | none => "absent"

/-- Label for a core's current thread in a state. -/
private def currentLabel (st : SystemState) (c : CoreId) : String :=
  match st.scheduler.currentOnCore c with
  | some t => threadLabel t
  | none => "none"

/-- Label for a thread's delivered payload (first message register). -/
private def payloadLabel (st : SystemState) (tid : SeLe4n.ThreadId) : String :=
  match st.getTcb? tid with
  | some t =>
      match t.pendingMessage with
      | some m =>
          match m.registers[0]? with
          | some r => s!"payload register {r.toNat}"
          | none => "empty payload"
      | none => "no payload"
  | none => "absent"

/-- The deterministic 4-core IPC trace — each line is COMPUTED from the live
`endpointReceiveDualOnCore` / `endpointCallOnCore` / `handleRescheduleSgiOnCore`
/ `endpointReplyOnCore` / `endpointSendDual` decisions on the fixture, so an
IPC-logic regression diverges the golden fixture.  Every line carries the
`[smp-ipc-4core]` prefix (the fixture extraction key). -/
private def ipcFourCoreTraceLines : List String :=
  match roundTrip?, sendRendezvous? with
  | some rt, some (stSend, sender, sgiSend) =>
    [ s!"[smp-ipc-4core] server B recv on core 1 leaves B {ipcStateLabel rt.afterRecv serverB}"
    , s!"[smp-ipc-4core] server D recv on core 3 leaves D {ipcStateLabel rt.afterRecv serverD}"
    , s!"[smp-ipc-4core] client A call on core 0 emits {sgiLabel rt.sgiCallA}"
    , s!"[smp-ipc-4core] client A awaits reply as {ipcStateLabel rt.afterCallA clientA}"
    , s!"[smp-ipc-4core] core 1 handler dispatches current = {currentLabel rt.afterSgiB c1}"
    , s!"[smp-ipc-4core] client C call on core 2 emits {sgiLabel rt.sgiCallC}"
    , s!"[smp-ipc-4core] core 3 handler dispatches current = {currentLabel rt.afterSgiD c3}"
    , s!"[smp-ipc-4core] server B reply on core 1 emits {sgiLabel rt.sgiReplyB}"
    , s!"[smp-ipc-4core] client A resumes with {payloadLabel rt.afterReplyB clientA}"
    , s!"[smp-ipc-4core] core 0 handler dispatches current = {currentLabel rt.afterSgiA c0}"
    , s!"[smp-ipc-4core] server D reply on core 3 emits {sgiLabel rt.sgiReplyD}"
    , s!"[smp-ipc-4core] client C resumes with {payloadLabel rt.afterReplyD clientC}"
    , s!"[smp-ipc-4core] core 2 handler dispatches current = {currentLabel rt.afterSgiC c2}"
    , s!"[smp-ipc-4core] send rendezvous pops {threadLabel sender} and emits {sgiLabel sgiSend}"
    , s!"[smp-ipc-4core] woken sender E is {ipcStateLabel stSend senderE} on its home core"
    , s!"[smp-ipc-4core] rendezvous complete: A {ipcStateLabel rt.afterSgiC clientA}, B {ipcStateLabel rt.afterSgiC serverB}, C {ipcStateLabel rt.afterSgiC clientC}, D {ipcStateLabel rt.afterSgiC serverD}" ]
  | _, _ => ["[smp-ipc-4core] PIPELINE ERROR: a cross-core IPC transition failed"]

private def fixturePath : String := "tests/fixtures/smp_ipc_4core.expected"

/-- §9: print the deterministic 4-core IPC trace and verify it byte-for-byte
against the golden fixture.  The lines print before the (strict) verification,
so the fixture is regenerable via `lake exe smp_ipc_suite | grep '^\[smp-ipc-4core\]'`
(the brackets MUST be escaped — unescaped they form a regex character class that
also matches the suite's `---` section headers, corrupting the regenerated
fixture). -/
private def runTraceFixtureCheck : IO Unit := do
  IO.println "--- §9 deterministic 4-core IPC trace (SM6.F.4 fixture) ---"
  for l in ipcFourCoreTraceLines do
    IO.println l
  let expectedContent := String.intercalate "\n" ipcFourCoreTraceLines ++ "\n"
  let fixtureExists ← System.FilePath.pathExists fixturePath
  if !fixtureExists then
    IO.println s!"  FAIL: golden fixture {fixturePath} not found"
    IO.println s!"        regenerate: lake exe smp_ipc_suite | grep '^\\[smp-ipc-4core\\]' > {fixturePath}"
    throw (IO.userError s!"missing fixture {fixturePath}")
  let actual ← IO.FS.readFile fixturePath
  if actual == expectedContent then
    IO.println s!"  PASS: 4-core IPC trace matches golden fixture {fixturePath}"
  else
    IO.println s!"  FAIL: 4-core IPC trace differs from golden fixture {fixturePath}"
    IO.println s!"        the live trace is printed above; regenerate the golden fixture with:"
    IO.println s!"          lake exe smp_ipc_suite | grep '^\\[smp-ipc-4core\\]' > {fixturePath}"
    IO.println s!"          (then refresh {fixturePath}.sha256 — see tests/fixtures/README.md)"
    throw (IO.userError "4-core IPC trace fixture mismatch")

def runSmpIpcChecks : IO Unit := do
  IO.println "WS-SM SM6.F.1 — Aggregate SMP cross-core IPC suite (4 threads / 4 cores)"
  IO.println "===================================="
  runTwoThreadRoundTripChecks
  runFourThreadRendezvousChecks
  runSendReceiveChecks
  runClientFirstChecks
  runReplyRecvLoopChecks
  runErrorPathChecks
  runLockDisciplineChecks
  runDispatchCoherenceChecks
  runTraceFixtureCheck
  IO.println "===================================="
  IO.println "All SM6.F cross-core IPC checks PASS."

end SeLe4n.Testing.SmpIpc

def main : IO Unit :=
  SeLe4n.Testing.SmpIpc.runSmpIpcChecks
